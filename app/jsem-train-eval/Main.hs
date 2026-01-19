{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | 保存されたJSeMProblemDataを使って学習し、prove'関数で速度を比較するプログラム
--
-- 前提: collectTypeCheckTrees-exe でJSeMProblemDataを事前に保存しておく
--
-- 機能:
-- 1. 保存されたJSeMProblemDataを読み込み
-- 2. judgmentとruleのペアで学習
-- 3. 学習したモデルを使ってNeuralWaniを構築
-- 4. テストデータに対してNormalProverとNeuralWaniProverで証明探索を実行
-- 5. 速度を比較してレポート出力

module Main (main) where

import Control.Monad (forM, forM_)
import Control.DeepSeq (rnf)
import Data.Char (isAlphaNum)
import Control.Exception (evaluate, try, SomeException)
import System.Random.Shuffle (shuffleM)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist)
import System.FilePath ((</>))
import qualified Data.Text.Lazy as TL     --text
import qualified Data.Text.Lazy.IO as TL  --text
import Data.Time.LocalTime (getZonedTime, zonedTimeToLocalTime)
import Data.Time.Clock (getCurrentTime, diffUTCTime, NominalDiffTime)
import qualified Data.Time as Time
import qualified Data.ByteString as B     --bytestring
import Data.Store (Store, encode, decode)
import qualified GHC.Generics as G
import Data.Ord (Down(..))
import qualified Data.Map.Strict as Map
import qualified Data.List as List
import qualified Data.List.Split as List
import System.Environment (getArgs)
import System.Mem (performGC, performMajorGC)
import Text.Printf (printf)
import qualified ListT

import qualified DTS.QueryTypes as QT
import qualified DTS.DTTdeBruijn as DTT
import qualified DTS.Prover.Wani.BackwardRules as BR
import qualified DTS.Prover.Wani.Prove as Prove
import qualified DTS.Prover.Wani.WaniBase as WB
import qualified Interface.Tree as I
import qualified Interface.Text as IText
import Data.Maybe (mapMaybe, catMaybes)

-- hasktorch関連のインポート
import Torch.Tensor       (Tensor(..), asValue, asTensor, toDevice)
import Torch.Device       (Device(..), DeviceType(..))
import Torch.Functional   (Dim(..), nllLoss', argmax, KeepDim(..))
import Torch.NN           (sample, flattenParameters)
import Torch.Optim        (mkAdam)
import Torch.Train        (update, saveParams)
import Torch.Serialize    (loadParams)
import Torch.Control      (mapAccumM)

-- 可視化と評価用のツール
import ML.Exp.Chart (drawLearningCurve, drawConfusionMatrix)
import ML.Exp.Classification (showClassificationReport)

-- プロジェクト固有のモジュール
import DTS.Prover.NeuralWani.SplitJudgment (Token(..), getConstantSymbolsFromJudgment, 
                                            getFrequentConstantSymbols, splitJudgment, DelimiterToken(..), 
                                            dttruleToRuleLabel, buildWordMap, WordMap)
import DTS.Prover.NeuralWani.Forward (HypParams(..), Params(..), forward, predictRule)

-- ============================================
-- データ型定義
-- ============================================

-- | JSeM問題から抽出したデータ
-- 1つのJSeM問題に対して、複数の(Judgment, Rule)ペアと1つの推論問題を持つ
data JSeMProblemData = JSeMProblemData
  { jspJsemId          :: String                       -- ^ JSeM ID
  , jspJudgmentRules   :: [(DTT.Judgment, QT.DTTrule)] -- ^ 型チェック証明木から抽出した(Judgment, Rule)ペア
  , jspInferenceQuery  :: Maybe DTT.ProofSearchQuery   -- ^ 推論問題（prove'に渡す問題）
  } deriving (Show, G.Generic, Store)

-- | JSeMファイルごとのデータ
data JSeMFileData = JSeMFileData
  { jfdFileName :: String              -- ^ JSeMファイル名（例: "Adjectives"）
  , jfdProblems :: [JSeMProblemData]   -- ^ そのファイルに含まれる問題データ
  } deriving (Show, G.Generic, Store)

-- | JSeMファイル名のリスト（collectTypeCheckTrees.hsと同じ）
jsemFileNames :: [String]
jsemFileNames = 
  [ "Adjectives"
  , "CompoundAdjective"
  , "GeneralizedQuantifier"
  , "TemporalReference"
  , "Attitudes"
  , "NP"
  , "Verbs"
  , "NominalAnaphora"
  ]

-- | すべてのラベル（RuleLabel）のリスト
allLabels :: [BR.RuleLabel]
allLabels = [minBound..]

-- | すべてのトークンのリスト
allTokens :: [Token]
allTokens = [minBound..]

-- | 元データのフィルタリング用のDTTruleリスト
backwardRules :: [QT.DTTrule]
backwardRules = [QT.PiF, QT.SigmaF, QT.IqF, QT.Var, QT.Con, QT.PiI, QT.SigmaI, QT.PiE, QT.TopI, QT.DisjI, QT.DisjE, QT.DisjF, QT.DNE, QT.EFQ]

formationRules :: [QT.DTTrule]
formationRules = [QT.TypeF, QT.PiF, QT.SigmaF, QT.DisjF, QT.BotF, QT.TopF, QT.EnumF, QT.IqF, QT.NatF]

-- | 証明探索の評価結果
data ProofSearchEvalResult = ProofSearchEvalResult
  { pseJsemId          :: String            -- ^ JSeM ID
  , pseNormalTime      :: NominalDiffTime   -- ^ NormalProverの時間
  , pseNeuralTime      :: NominalDiffTime   -- ^ NeuralWaniProverの時間
  , pseNormalSuccess   :: Bool              -- ^ NormalProverで証明成功したか
  , pseNeuralSuccess   :: Bool              -- ^ NeuralWaniProverで証明成功したか
  } deriving (Show)

-- | Proverの設定
data ProverConfig = ProverConfig
  { cfgMaxDepth     :: Int
  , cfgMaxTime      :: Int
  } deriving (Show)

-- | 評価結果を格納するデータ型
data EvaluationResult = EvaluationResult
  { erPredictions      :: [(BR.RuleLabel, BR.RuleLabel)]  -- ^ (予測, 正解) のペア
  , erCorrectFlags     :: [Bool]                          -- ^ 各予測が正しかったかどうか
  , erAccuracy         :: Double                          -- ^ 精度
  , erClassificationReport :: TL.Text                     -- ^ 分類レポート
  } deriving (Show)

-- ============================================
-- JSeMProblemDataの読み込み
-- ============================================

-- | JSeMProblemDataをファイルまたはディレクトリから読み込み
-- ディレクトリの場合は全てのJSeMファイルを統合して返す
loadJSeMProblemsFromFile :: FilePath -> IO [JSeMProblemData]
loadJSeMProblemsFromFile path = do
  isDir <- doesDirectoryExist path
  if isDir
    then do
      -- ディレクトリの場合: all.bin があればそれを読み込み、なければ個別ファイルを統合
      let allBinPath = path </> "all.bin"
      allBinExists <- doesDirectoryExist allBinPath  -- ファイルの存在チェックは簡易的
      if not allBinExists
        then do
          -- all.binがあれば優先的に使用
          bytes <- try (B.readFile allBinPath) :: IO (Either SomeException B.ByteString)
          case bytes of
            Right bs -> case decode bs of
              Left err -> loadFromPerFile path  -- デコード失敗時は個別ファイルから読み込み
              Right problems -> return problems
            Left _ -> loadFromPerFile path  -- ファイルなければ個別ファイルから読み込み
        else loadFromPerFile path
    else do
      -- 単一ファイルの場合
      bytes <- B.readFile path
      case decode bytes of
        Left err -> error $ "Failed to decode JSeMProblemData: " ++ show err
        Right problems -> return problems
  where
    loadFromPerFile dir = do
      problemsPerFile <- loadAllJSeMProblemsFromDir dir
      return $ concatMap snd problemsPerFile

-- | JSeMFileDataを単一ファイルから読み込み
loadJSeMFileData :: FilePath -> IO JSeMFileData
loadJSeMFileData path = do
  bytes <- B.readFile path
  case decode bytes of
    Left err -> error $ "Failed to decode JSeMFileData from " ++ path ++ ": " ++ show err
    Right fileData -> return fileData

-- | 指定したJSeMファイルのデータをディレクトリから読み込み
loadJSeMProblemsFromDir :: FilePath -> String -> IO [JSeMProblemData]
loadJSeMProblemsFromDir outputDir fileName = do
  let filePath = outputDir </> fileName ++ ".bin"
  fileData <- loadJSeMFileData filePath
  return $ jfdProblems fileData

-- | ディレクトリから全てのJSeMファイルのデータを読み込み
loadAllJSeMProblemsFromDir :: FilePath -> IO [(String, [JSeMProblemData])]
loadAllJSeMProblemsFromDir outputDir = do
  forM jsemFileNames $ \fileName -> do
    let filePath = outputDir </> fileName ++ ".bin"
    fileData <- loadJSeMFileData filePath
    return (jfdFileName fileData, jfdProblems fileData)

-- ============================================
-- ユーティリティ関数
-- ============================================

-- | 規則の出現回数をカウントする関数
countRule :: [BR.RuleLabel] -> [(BR.RuleLabel, Int)]
countRule rules = List.sortOn (Down . snd) $ Map.toList ruleFreqMap
  where
    ruleFreqMap :: Map.Map BR.RuleLabel Int
    ruleFreqMap = foldr (\word acc -> Map.insertWith (+) word 1 acc) Map.empty rules

-- | データセットをラベル（規則）ごとに分割する関数
splitByLabel :: [([Token], BR.RuleLabel)] -> IO [(BR.RuleLabel, [([Token], BR.RuleLabel)])]
splitByLabel dataset = return $ splitByLabel' dataset Map.empty
  where
    splitByLabel' [] acc = Map.toList acc
    splitByLabel' ((tokens', rule):xs) acc =
      let data' = (tokens', rule)
          acc' = Map.insertWith (++) rule [data'] acc
      in splitByLabel' xs acc'

-- | データセットを訓練・検証・テストに分割する関数
smoothData :: [(BR.RuleLabel, [([Token], BR.RuleLabel)])] -> Maybe Int 
           -> IO ([([Token], BR.RuleLabel)], [([Token], BR.RuleLabel)], [([Token], BR.RuleLabel)])
smoothData splittedData threshold = smoothData' splittedData [] [] []
  where
    smoothData' [] trainDataAcc validDataAcc testDataAcc = return (trainDataAcc, validDataAcc, testDataAcc)
    smoothData' ((_, dataList):remainingData) trainDataAcc validDataAcc testDataAcc = do
      shuffledData <- shuffleM dataList
      let limitedData = case threshold of
            Nothing -> shuffledData
            Just threshold' -> take threshold' shuffledData
          (trainData, restData) = splitAt (length limitedData * 8 `div` 10) limitedData
          (validData, testData) = splitAt (length restData * 5 `div` 10) restData
      smoothData' remainingData (trainDataAcc ++ trainData) (validDataAcc ++ validData) (testDataAcc ++ testData)

-- | JSeM問題をシャッフルして分割する関数（問題単位で分割）
splitJSeMProblems :: [JSeMProblemData] -> IO ([JSeMProblemData], [JSeMProblemData], [JSeMProblemData])
splitJSeMProblems problems = do
  shuffled <- shuffleM problems
  let n = length shuffled
      nTrain = n * 8 `div` 10
      nValid = (n - nTrain) * 5 `div` 10
      (train, rest) = splitAt nTrain shuffled
      (valid, test) = splitAt nValid rest
  return (train, valid, test)

-- | 時間をフォーマットする
formatTimeNominal :: NominalDiffTime -> TL.Text
formatTimeNominal t = TL.pack $ printf "%.3f sec" (realToFrac t :: Double)

-- ============================================
-- 学習関連の関数
-- ============================================

-- | モデルの学習を行う関数
trainModel :: Device -> HypParams -> [([Token], BR.RuleLabel)] -> [([Token], BR.RuleLabel)] 
           -> Bool -> Int -> Int -> Tensor -> [TL.Text] 
           -> IO (Params, [(Float, Float)], [TL.Text])
trainModel device hyperParams trainData validData biDirectional iter numberOfBatch learningRate frequentWords = do
  initModel <- sample hyperParams
  let optimizer = mkAdam 0 0.9 0.999 (flattenParameters initModel)

  ((trainedModel), lossesPair) <- mapAccumM [1..iter] (initModel) $ \epoc (model) -> do
    shuffledTrainData <- shuffleM trainData
    let batchedTrainData = List.chunksOf numberOfBatch shuffledTrainData
        batchedTrainData' = if length (last batchedTrainData) < numberOfBatch
                          then init batchedTrainData
                          else batchedTrainData

    ((trainedModel', _), lossPair) <- mapAccumM batchedTrainData' (model, 0 :: Int) $ \dataList (mdl, i) -> do
      performGC
      (sumLoss', losses) <- mapAccumM dataList (0 :: Tensor) $ \dat (accumulatedLoss) -> do
        let output' = forward device mdl (fst dat) biDirectional
        performGC
        let groundTruthIndex = toDevice device (asTensor [(fromEnum $ snd dat) :: Int])
            loss = nllLoss' groundTruthIndex output'
            lossValue = (asValue loss) :: Float
            sumLoss = accumulatedLoss + loss
        return (sumLoss, lossValue)

      (newModel, _) <- update mdl optimizer sumLoss' learningRate
      performGC

      validLosses <- forM validData $ \dataPoint -> do
        let validOutput' = forward device mdl (fst dataPoint) biDirectional
        performGC
        let groundTruthIndex' = toDevice device (asTensor [(fromEnum $ snd dataPoint) :: Int])
            validLossValue = (asValue (nllLoss' groundTruthIndex' validOutput')) :: Float
        return validLossValue

      let validLoss = sum validLosses / fromIntegral (length validLosses)
          trainLoss = sum losses / fromIntegral (length losses)
      print $ "epoch " ++ show epoc ++ " i " ++ show i ++ " trainingLoss " ++ show trainLoss ++ " validLoss " ++ show validLoss
      return ((newModel, i + 1), (trainLoss, validLoss))

    let (trainLoss', validLoss') = unzip lossPair
        avgTrainLoss = sum trainLoss' / fromIntegral (length trainLoss')
        avgValidLoss = sum validLoss' / fromIntegral (length validLoss')
    print $ "epoch " ++ show epoc ++ " avgTrainLoss " ++ show avgTrainLoss ++ " avgValidLoss " ++ show avgValidLoss
    print "----------------"

    return (trainedModel', (avgTrainLoss, avgValidLoss))

  return (trainedModel, lossesPair, frequentWords)

-- ============================================
-- 評価関連の関数
-- ============================================

-- | テストデータに対する予測と評価
evaluateModel :: Device -> Params -> [([Token], BR.RuleLabel)] -> Bool -> IO EvaluationResult
evaluateModel device model testData biDirectional = do
  results <- forM testData $ \(tokens, groundTruthLabel) -> do
    let output' = forward device model tokens biDirectional
        groundTruthIndex = toDevice device (asTensor [(fromEnum groundTruthLabel) :: Int])
        predictedClassIndex = argmax (Dim 1) KeepDim output'
        isCorrect = groundTruthIndex == predictedClassIndex
        predictedLabel = toEnum (asValue predictedClassIndex :: Int) :: BR.RuleLabel
    return (predictedLabel, groundTruthLabel, isCorrect)
  
  let predictions = map (\(pred, gt, _) -> (pred, gt)) results
      correctFlags = map (\(_, _, correct) -> correct) results
      numCorrect = length $ filter id correctFlags
      accuracy = fromIntegral numCorrect / fromIntegral (length correctFlags)
      classReport = TL.fromStrict $ showClassificationReport (length allLabels) predictions
  
  return EvaluationResult
    { erPredictions = predictions
    , erCorrectFlags = correctFlags
    , erAccuracy = accuracy
    , erClassificationReport = classReport
    }

-- ============================================
-- 補助関数
-- ============================================

-- | ファイル名に使えない/使いづらい文字を置換
sanitize :: String -> String
sanitize = map rep
  where
    rep c | isAlphaNum c || c == '-' || c == '_' = c
          | otherwise = '_'

-- | 評価結果をファイルに保存
saveEvaluationReport :: FilePath -> EvaluationResult -> [BR.RuleLabel] -> IO ()
saveEvaluationReport outputDir result labels = do
  let classificationReportFile = outputDir </> "classification-report.txt"
      confusionMatrixFile = outputDir </> "confusion-matrix.png"
  
  TL.writeFile classificationReportFile (erClassificationReport result)
  putStrLn $ "Classification report saved to: " ++ classificationReportFile
  
  drawConfusionMatrix confusionMatrixFile (length labels) (erPredictions result)
  putStrLn $ "Confusion matrix saved to: " ++ confusionMatrixFile
  
  putStrLn $ "Accuracy: " ++ show (erAccuracy result)

-- ============================================
-- 証明探索（評価）関連の関数
-- ============================================

-- | prove' を使って証明探索を実行し、最初の証明木を取得する
runProveWithTree :: QT.ProofSearchSetting -> DTT.ProofSearchQuery
                 -> IO ([I.Tree QT.DTTrule DTT.Judgment], NominalDiffTime)
runProveWithTree setting query = do
  -- 計測に入る前に、クエリを完全評価してGCを実行（ウォームアップ/環境ノイズ除去）
  evaluate $ rnf query
  performMajorGC
  startTime <- getCurrentTime
  
  let prover = Prove.prove' setting
  
  maybeTree <- ListT.head (prover query)
  let trees = case maybeTree of
        Nothing -> []
        Just tree -> [tree]
  
  endTime <- getCurrentTime
  let elapsedTime = diffUTCTime endTime startTime
  
  return (trees, elapsedTime)

-- ============================================
-- 証明木出力関連の関数（evaluate/Main.hs に準拠）
-- ============================================

-- | 証明木をテキストファイルに出力
writeProofTreeText :: FilePath -> I.Tree QT.DTTrule DTT.Judgment -> IO ()
writeProofTreeText filepath tree = do
  let content = IText.toText tree
  TL.writeFile filepath content

-- | 証明木をHTML（MathML）形式でファイルに出力
writeProofTreeHTML :: FilePath -> I.Tree QT.DTTrule DTT.Judgment -> IO ()
writeProofTreeHTML filepath tree = do
  content <- Prove.display tree
  TL.writeFile filepath content

-- | 証明木を複数の形式で出力（全ての証明木を出力）
writeProofTrees :: FilePath -> String -> [I.Tree QT.DTTrule DTT.Judgment] -> IO ()
writeProofTrees baseDir baseName trees = do
  createDirectoryIfMissing True baseDir
  case trees of
    [] -> do
      let noProofFile = baseDir </> (baseName ++ "_no_proof.txt")
      writeFile noProofFile "No proof found."
    _ -> do
      forM_ (zip [1 :: Int ..] trees) $ \(i, tree) -> do
        let txtPath = baseDir </> (baseName ++ printf "_proof_%02d.txt" i)
            htmlPath = baseDir </> (baseName ++ printf "_proof_%02d.html" i)
        writeProofTreeText txtPath tree
        writeProofTreeHTML htmlPath tree

-- | NeuralWaniを構築する関数（学習済みモデルから）
buildNeuralWani :: Device -> Params -> WordMap -> Bool -> DelimiterToken 
                -> (WB.Goal -> [BR.RuleLabel] -> [BR.RuleLabel])
buildNeuralWani device model wordMap biDirectional delimiterToken = 
  \goal availableRuleLabels ->
    let maybeJudgment = WB.goal2NeuralWaniJudgement goal
    in case maybeJudgment of
      Just judgment ->
        let predictedRuleLabels = predictRule device model judgment biDirectional wordMap delimiterToken
            filteredRuleLabels = filter (`elem` availableRuleLabels) predictedRuleLabels
        in filteredRuleLabels
      Nothing -> availableRuleLabels

-- | 単一のJSeM問題に対して証明探索を実行し、時間を計測する
evaluateOneProblem :: ProverConfig 
                   -> (WB.Goal -> [BR.RuleLabel] -> [BR.RuleLabel])  -- ^ NeuralWani関数
                   -> FilePath                                        -- ^ 出力ベースディレクトリ
                   -> Int                                             -- ^ テストケース番号
                   -> JSeMProblemData
                   -> IO (Maybe ProofSearchEvalResult)
evaluateOneProblem config neuralWaniFunc outputBaseDir idx problem = 
  case jspInferenceQuery problem of
    Nothing -> return Nothing
    Just query -> do
      -- 共通データの強制評価 (Warm-up)
      evaluate $ rnf query
      
      -- Normal Proverの設定
      let normalSetting = QT.defaultProofSearchSetting {
                QT.maxDepth = Just (cfgMaxDepth config),
                QT.maxTime = Just (cfgMaxTime config)
                }
      
      -- NeuralWani Proverの設定
      let neuralSetting = QT.defaultProofSearchSetting {
                QT.maxDepth = Just (cfgMaxDepth config),
                QT.maxTime = Just (cfgMaxTime config),
                QT.neuralWani = Just neuralWaniFunc
                }
      
      -- Normal Proverで証明探索
      performMajorGC
      (normalTrees, normalTime) <- runProveWithTree normalSetting query
      let normalSuccess = not (null normalTrees)

      -- NeuralWani Proverで証明探索
      performMajorGC
      (neuralTrees, neuralTime) <- runProveWithTree neuralSetting query
      let neuralSuccess = not (null neuralTrees)

      -- 出力用ベース名の作成（インデックス + JSeM ID をサニタイズ）
      let baseName = printf "%03d_%s" idx (sanitize (jspJsemId problem))

      -- クエリを保存（解けなくても必ず保存）
      let queriesDir = outputBaseDir </> "queries"
      createDirectoryIfMissing True queriesDir
      let queryFile = queriesDir </> (baseName ++ ".txt")
      TL.writeFile queryFile (TL.pack (show query))

      -- 証明木を保存（Normal / Neural）
      let proofBaseDir = outputBaseDir </> "proofTrees"
          normalDir = proofBaseDir </> "normal"
          neuralDir = proofBaseDir </> "neural"
      writeProofTrees normalDir baseName normalTrees
      writeProofTrees neuralDir baseName neuralTrees
      
      return $ Just ProofSearchEvalResult
        { pseJsemId        = jspJsemId problem
        , pseNormalTime    = normalTime
        , pseNeuralTime    = neuralTime
        , pseNormalSuccess = normalSuccess
        , pseNeuralSuccess = neuralSuccess
        }

-- ============================================
-- レポート出力関連の関数
-- ============================================

-- | 評価結果のサマリーを表示
printEvalSummary :: [ProofSearchEvalResult] -> IO ()
printEvalSummary results = do
  putStrLn ""
  putStrLn "============================================"
  putStrLn "=== PROOF SEARCH EVALUATION SUMMARY ==="
  putStrLn "============================================"
  
  let totalTests = length results
      normalSuccessCount = length $ filter pseNormalSuccess results
      neuralSuccessCount = length $ filter pseNeuralSuccess results
  
  putStrLn $ "Total tests: " ++ show totalTests
  putStrLn ""
  
  putStrLn "--- Success Rate ---"
  putStrLn $ "Normal Prover:     " ++ show normalSuccessCount ++ "/" ++ show totalTests
  printf "                   %.1f%%\n" (100.0 * fromIntegral normalSuccessCount / fromIntegral totalTests :: Double)
  putStrLn $ "NeuralWani Prover: " ++ show neuralSuccessCount ++ "/" ++ show totalTests
  printf "                   %.1f%%\n" (100.0 * fromIntegral neuralSuccessCount / fromIntegral totalTests :: Double)
  putStrLn ""
  
  -- 両方成功したものの平均時間
  let bothSuccess = filter (\r -> pseNormalSuccess r && pseNeuralSuccess r) results
  if null bothSuccess
    then putStrLn "No tests where both provers succeeded."
    else do
      let avgNormalTime = sum (map pseNormalTime bothSuccess) / fromIntegral (length bothSuccess)
          avgNeuralTime = sum (map pseNeuralTime bothSuccess) / fromIntegral (length bothSuccess)
          speedup = realToFrac avgNormalTime / realToFrac avgNeuralTime :: Double
      
      putStrLn $ "--- Average Time (both succeeded: " ++ show (length bothSuccess) ++ " tests) ---"
      putStrLn $ "Normal Prover:     " ++ TL.unpack (formatTimeNominal avgNormalTime)
      putStrLn $ "NeuralWani Prover: " ++ TL.unpack (formatTimeNominal avgNeuralTime)
      printf "Speedup: %.2fx\n" speedup
  
  putStrLn ""
  
  -- NeuralWaniのみ成功したもの
  let neuralOnlySuccess = filter (\r -> not (pseNormalSuccess r) && pseNeuralSuccess r) results
  putStrLn $ "NeuralWani only success: " ++ show (length neuralOnlySuccess)
  
  -- NormalProverのみ成功したもの
  let normalOnlySuccess = filter (\r -> pseNormalSuccess r && not (pseNeuralSuccess r)) results
  putStrLn $ "Normal only success: " ++ show (length normalOnlySuccess)

-- | 評価結果をファイルに保存
saveProofSearchReport :: FilePath -> ProverConfig -> [ProofSearchEvalResult] -> IO ()
saveProofSearchReport outputDir config results = do
  let reportFile = outputDir </> "proof-search-eval-report.txt"
      
  let totalTests = length results
      normalSuccessCount = length $ filter pseNormalSuccess results
      neuralSuccessCount = length $ filter pseNeuralSuccess results
      bothSuccess = filter (\r -> pseNormalSuccess r && pseNeuralSuccess r) results
      
  let reportLines =
        [ "=== Proof Search Evaluation Report ==="
        , ""
        , "Configuration:"
        , "  maxDepth: " ++ show (cfgMaxDepth config)
        , "  maxTime: " ++ show (cfgMaxTime config)
        , ""
        , "Results:"
        , "  Total tests: " ++ show totalTests
        , "  Normal Prover success: " ++ show normalSuccessCount ++ "/" ++ show totalTests
        , "  NeuralWani Prover success: " ++ show neuralSuccessCount ++ "/" ++ show totalTests
        , ""
        ] ++
        (if null bothSuccess
        then ["  No tests where both provers succeeded."]
        else
          let avgNormalTime = sum (map pseNormalTime bothSuccess) / fromIntegral (length bothSuccess)
              avgNeuralTime = sum (map pseNeuralTime bothSuccess) / fromIntegral (length bothSuccess)
              speedup = realToFrac avgNormalTime / realToFrac avgNeuralTime :: Double
              speedupStr = "  Speedup: " ++ show (fromIntegral (round (speedup * 100)) / 100 :: Double) ++ "x"
          in [ "Average Time (both succeeded: " ++ show (length bothSuccess) ++ " tests):"
             , "  Normal Prover: " ++ TL.unpack (formatTimeNominal avgNormalTime)
             , "  NeuralWani Prover: " ++ TL.unpack (formatTimeNominal avgNeuralTime)
             , speedupStr
             ])
      report = unlines reportLines
  
  writeFile reportFile report
  putStrLn $ "Report saved to: " ++ reportFile

-- ============================================
-- TeX レポート生成（JSeM評価用）
-- ============================================

-- | TeXの特殊文字をエスケープ（Lazy Text版）
escapeTeX :: TL.Text -> TL.Text
escapeTeX = TL.concatMap escapeChar
  where
    escapeChar '_' = "\\_"
    escapeChar '#' = "\\#"
    escapeChar '%' = "\\%"
    escapeChar '&' = "\\&"
    escapeChar '$' = "\\$"
    escapeChar '{' = "\\{"
    escapeChar '}' = "\\}"
    escapeChar '^' = "\\^{}"
    escapeChar '~' = "\\~{}"
    escapeChar c   = TL.singleton c

-- | 短い時間フォーマット（Lazy Text）
formatTimeShort :: NominalDiffTime -> TL.Text
formatTimeShort t = TL.pack $ printf "%.3fs" (realToFrac t :: Double)

-- | サマリーTeXの生成（JSeM評価用）
generateSummaryTexJSeM :: [ProofSearchEvalResult] -> TL.Text
generateSummaryTexJSeM results =
  let totalTests = length results
      normalSuccessCount = length $ filter pseNormalSuccess results
      neuralSuccessCount = length $ filter pseNeuralSuccess results
      bothSuccess = filter (\r -> pseNormalSuccess r && pseNeuralSuccess r) results
      avgNormalAll = if totalTests == 0 then 0 else sum (map pseNormalTime results) / fromIntegral totalTests
      avgNeuralAll = if totalTests == 0 then 0 else sum (map pseNeuralTime results) / fromIntegral totalTests
      avgNormalBoth = if null bothSuccess then 0 else sum (map pseNormalTime bothSuccess) / fromIntegral (length bothSuccess)
      avgNeuralBoth = if null bothSuccess then 0 else sum (map pseNeuralTime bothSuccess) / fromIntegral (length bothSuccess)
      avgSpeedupBoth :: Maybe Double
      avgSpeedupBoth = if null bothSuccess then Nothing else Just $ avgToDouble avgNormalBoth / avgToDouble avgNeuralBoth
      avgToDouble x = realToFrac x :: Double
      speedupStr = maybe "N/A" (TL.pack . printf "%.2fx") avgSpeedupBoth
  in TL.unlines
    [ "\\begin{tabular}{ll}"
    , "\\toprule"
    , "\\textbf{Metric} & \\textbf{Value} \\\\"
    , "\\midrule"
    , "Total tests & " <> TL.pack (show totalTests) <> " \\\\"
    , "Normal success & " <> TL.pack (show normalSuccessCount) <> "/" <> TL.pack (show totalTests) <> " \\\\"
    , "Neural success & " <> TL.pack (show neuralSuccessCount) <> "/" <> TL.pack (show totalTests) <> " \\\\"
    , "\\midrule"
    , "Avg. Normal time (all) & " <> formatTimeNominal avgNormalAll <> " \\\\"
    , "Avg. Neural time (all) & " <> formatTimeNominal avgNeuralAll <> " \\\\"
    , "Avg. Normal time (both ok) & " <> formatTimeNominal avgNormalBoth <> " \\\\"
    , "Avg. Neural time (both ok) & " <> formatTimeNominal avgNeuralBoth <> " \\\\"
    , "Speedup (Normal/Neural; both ok avg) & " <> speedupStr <> " \\\\"
    , "\\bottomrule"
    , "\\end{tabular}"
    ]

-- | 詳細結果テーブルの生成（JSeM評価用）
generateResultsTableJSeM :: [ProofSearchEvalResult] -> TL.Text
generateResultsTableJSeM results = TL.unlines $
  [ "\\begin{longtable}{lccccc}"
  , "\\toprule"
  , "\\textbf{JSeM ID} & \\textbf{Normal Time} & \\textbf{Normal OK} & \\textbf{Neural Time} & \\textbf{Neural OK} & \\textbf{Speedup} \\\\"
  , "\\midrule"
  , "\\endhead"
  ] ++ map row results ++
  [ "\\bottomrule"
  , "\\end{longtable}"
  ]
  where
    b2mark True  = "\\checkmark"
    b2mark False = "$\\times$"
    row r = TL.concat
      [ escapeTeX (TL.pack (pseJsemId r)), " & "
      , formatTimeShort (pseNormalTime r), " & "
      , TL.pack (b2mark (pseNormalSuccess r)), " & "
      , formatTimeShort (pseNeuralTime r), " & "
      , TL.pack (b2mark (pseNeuralSuccess r)), " & "
      , TL.pack (printf "%.2fx" (speedup r))
      , " \\\\"
      ]
      where
        speedup x =
          let nt = realToFrac (pseNeuralTime x) :: Double
              tt = realToFrac (pseNormalTime x) :: Double
          in if nt > 0 then tt / nt else 0

-- | TeX本文の生成（JSeM評価用）
generateTexContentJSeM :: ProverConfig -> String -> FilePath -> [ProofSearchEvalResult] -> TL.Text
generateTexContentJSeM config sessionId modelDir results = TL.unlines
  [ "\\documentclass[a4paper,10pt]{article}"
  , "\\usepackage[utf8]{inputenc}"
  , "\\usepackage{booktabs}"
  , "\\usepackage{longtable}"
  , "\\usepackage{geometry}"
  , "\\usepackage{xcolor}"
  , "\\usepackage{colortbl}"
  , "\\geometry{margin=1.5cm}"
  , ""
  , "\\title{JSeM Proof Search Evaluation Report}"
  , "\\author{jsem-train-eval}"
  , "\\date{\\today}"
  , ""
  , "\\begin{document}"
  , "\\maketitle"
  , ""
  , "\\section{Configuration}"
  , "\\begin{itemize}"
  , "\\item maxDepth: " <> TL.pack (show (cfgMaxDepth config))
  , "\\item maxTime: " <> TL.pack (show (cfgMaxTime config)) <> " ms"
  , "\\item Session ID: \\texttt{" <> escapeTeX (TL.pack sessionId) <> "}"
  , "\\item Output Directory: \\texttt{" <> escapeTeX (TL.pack modelDir) <> "}"
  , "\\end{itemize}"
  , ""
  , "\\section{Summary}"
  , generateSummaryTexJSeM results
  , ""
  , "\\section{Detailed Results}"
  , generateResultsTableJSeM results
  , ""
  , "\\end{document}"
  ]

-- | TeXレポートを書き出し
writeTexReportJSeM :: FilePath -> ProverConfig -> String -> [ProofSearchEvalResult] -> IO ()
writeTexReportJSeM outputDir config sessionId results = do
  let texFilename = outputDir </> ("proof-search-eval-report_" ++ sessionId ++ ".tex")
  TL.writeFile texFilename (generateTexContentJSeM config sessionId outputDir results)
  putStrLn $ "TeX report written to: " ++ texFilename

-- ============================================
-- メイン関数
-- ============================================

main :: IO ()
main = do
  args <- getArgs
  
  -- コマンドライン引数のパース
  -- Usage: jsem-train-eval-exe jsemDataPath biDirectional embDim hiddenSize layers bias lr batchSize epochs maxDepth maxTime
  let (jsemDataPath, bi, emb, h, l, bias, lr, steps, iter, maxDepth, maxTime) = case args of
        [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] ->
          ( a0                    -- JSeMProblemDataファイルパス
          , read a1 :: Bool       -- 双方向LSTM
          , read a2 :: Int        -- 埋め込み次元
          , read a3 :: Int        -- 隠れ層サイズ
          , read a4 :: Int        -- LSTM層数
          , read a5 :: Bool       -- バイアス
          , read a6 :: Float      -- 学習率
          , read a7 :: Int        -- バッチサイズ
          , read a8 :: Int        -- エポック数
          , read a9 :: Int        -- maxDepth
          , read a10 :: Int       -- maxTime
          )
        _ -> error $ unlines
          [ "Usage: jsem-train-eval-exe jsemDataPath biDirectional embDim hiddenSize layers bias lr batchSize epochs maxDepth maxTime"
          , ""
          , "Example: jsem-train-eval-exe jsemProblemData.bin False 256 256 1 False 5.0e-4 32 10 9 6000"
          , ""
          , "Arguments:"
          , "  jsemDataPath  : String - Path to JSeMProblemData binary file (created by collectTypeCheckTrees-exe)"
          , "  biDirectional : Bool   - Use bidirectional LSTM"
          , "  embDim        : Int    - Embedding dimension"
          , "  hiddenSize    : Int    - Hidden layer size"
          , "  layers        : Int    - Number of LSTM layers"
          , "  bias          : Bool   - Use bias"
          , "  lr            : Float  - Learning rate"
          , "  batchSize     : Int    - Batch size"
          , "  epochs        : Int    - Number of epochs"
          , "  maxDepth      : Int    - Max proof search depth"
          , "  maxTime       : Int    - Max proof search time (ms)"
          ]
  
  putStrLn "=== JSeM Train & Evaluate ==="
  putStrLn ""
  
  -- ============================================
  -- Phase 1: JSeMProblemDataの読み込み
  -- ============================================
  putStrLn "=== Phase 1: Loading JSeMProblemData ==="
  putStrLn $ "Loading from: " ++ jsemDataPath
  
  -- ディレクトリかファイルかを判定
  isDir <- doesDirectoryExist jsemDataPath
  if isDir
    then putStrLn "Detected directory: loading per-file data..."
    else putStrLn "Detected file: loading all-in-one data..."
  
  allProblems <- loadJSeMProblemsFromFile jsemDataPath
  
  putStrLn $ "Loaded " ++ show (length allProblems) ++ " JSeM problems"
  
  -- (Judgment, Rule)ペアを全て抽出
  let allJudgmentRules = concatMap jspJudgmentRules allProblems
  putStrLn $ "Total judgment-rule pairs: " ++ show (length allJudgmentRules)
  
  -- 推論問題を持つ問題のみ抽出
  let problemsWithQuery = filter (not . null . jspInferenceQuery) allProblems
  putStrLn $ "Problems with inference query: " ++ show (length problemsWithQuery)
  
  -- ============================================
  -- Phase 2: データの前処理と分割
  -- ============================================
  putStrLn ""
  putStrLn "=== Phase 2: Preprocessing and Splitting Data ==="
  
  let delimiterToken = Unused
      isIncludeF = False
      isOnlyBackwardRules = True
  
  -- フィルタリング
  let backwardDataset = if isOnlyBackwardRules
                then filter (\(_, rule) -> elem rule backwardRules) allJudgmentRules
                else allJudgmentRules
      filteredDataset = if isIncludeF
                then backwardDataset
                else filter (\(_, rule) -> rule `notElem` formationRules) backwardDataset
      -- (Judgment, RuleLabel) のペアに変換
      dataset = mapMaybe (\(judgment, dttRule) -> 
                  case dttruleToRuleLabel dttRule of
                    Just ruleLabel -> Just (judgment, ruleLabel)
                    Nothing -> Nothing) filteredDataset
      wordList = concatMap (getConstantSymbolsFromJudgment . fst) dataset
      frequentWords = getFrequentConstantSymbols wordList
      wordMap = buildWordMap frequentWords
      -- トークン列に変換
      constructorData = map (\(judgment, _) -> splitJudgment judgment wordMap delimiterToken) dataset
      ruleList = map snd dataset
  
  putStrLn $ "Filtered to " ++ show (length dataset) ++ " pairs (backward rules only)"
  
  -- 規則の出現回数をカウントして表示
  let countedRules = countRule ruleList
  putStrLn $ "Rule distribution: " ++ show countedRules
  
  -- JSeM問題単位で分割（評価用）
  (trainProblems, validProblems, testProblems) <- splitJSeMProblems problemsWithQuery
  putStrLn $ "Train problems: " ++ show (length trainProblems)
  putStrLn $ "Valid problems: " ++ show (length validProblems)
  putStrLn $ "Test problems: " ++ show (length testProblems)
  
  -- 学習データ（Token, RuleLabel）を分割
  splitedData <- splitByLabel (zip constructorData ruleList)
  (trainData, validData, testData) <- smoothData splitedData (Just 2000)
  
  putStrLn $ "Training data (judgment-rule pairs): " ++ show (length trainData)
  putStrLn $ "Validation data (judgment-rule pairs): " ++ show (length validData)
  putStrLn $ "Test data (judgment-rule pairs): " ++ show (length testData)
  
  -- ============================================
  -- Phase 3: モデルの学習
  -- ============================================
  putStrLn ""
  putStrLn "=== Phase 3: Training Model ==="
  
  let device = Device CUDA 0
      biDirectional = bi
      embDim = emb
      numOfLayers = l
      hiddenSize = h
      hasBias = bias
      vocabSize = length allTokens
      projSize = Nothing
      numOfRules = length (enumFrom minBound :: [BR.RuleLabel])
      hyperParams = HypParams device biDirectional embDim hasBias projSize vocabSize numOfLayers hiddenSize numOfRules
      learningRate = toDevice device (asTensor (lr :: Float))
      numberOfBatch = steps
  
  putStrLn $ "HyperParams: " ++ show hyperParams
  putStrLn $ "Learning rate: " ++ show lr
  putStrLn $ "Batch size: " ++ show numberOfBatch
  putStrLn $ "Epochs: " ++ show iter
  
  startTime <- Time.getCurrentTime
  putStrLn $ "Training started at: " ++ show startTime
  
  (trainedModel, lossesPair, frequentWords') <- trainModel device hyperParams trainData validData biDirectional iter numberOfBatch learningRate frequentWords
  
  endTime <- Time.getCurrentTime
  let trainingDuration = Time.diffUTCTime endTime startTime
  putStrLn $ "Training finished at: " ++ show endTime
  putStrLn $ "Total training time: " ++ show trainingDuration
  
  -- ============================================
  -- Phase 4: モデルの保存
  -- ============================================
  putStrLn ""
  putStrLn "=== Phase 4: Saving Model ==="
  
  currentTime <- getZonedTime
  let timeString = Time.formatTime Time.defaultTimeLocale "%Y-%m-%d_%H-%M-%S" (zonedTimeToLocalTime currentTime)
      folderName = "jsem_bi" ++ show biDirectional ++ "_s" ++ show numberOfBatch ++ 
                   "_lr" ++ show (asValue learningRate :: Float) ++ "_i" ++ show embDim ++ 
                   "_h" ++ show hiddenSize ++ "_layer" ++ show numOfLayers
      newFolderPath = "jsemResults" </> folderName </> timeString
  
  createDirectoryIfMissing True newFolderPath
  
  let modelFileName = newFolderPath </> "seq-class.model"
      frequentWordsFileName = newFolderPath </> "frequentWords.bin"
      graphFileName = newFolderPath </> "graph-seq-class.png"
      (losses, validLosses) = unzip lossesPair
      learningCurveTitle = "JSeM: bi=" ++ show biDirectional ++ " h=" ++ show hiddenSize
  
  saveParams trainedModel modelFileName
  B.writeFile frequentWordsFileName (encode frequentWords')
  drawLearningCurve graphFileName learningCurveTitle [("training", reverse losses), ("validation", reverse validLosses)]
  
  putStrLn $ "Model saved to: " ++ modelFileName
  putStrLn $ "FrequentWords saved to: " ++ frequentWordsFileName
  putStrLn $ "Learning curve saved to: " ++ graphFileName

  -- 以降の成果物保存場所の案内
  putStrLn $ "Proof trees will be saved under: " ++ (newFolderPath </> "proofTrees")
  putStrLn $ "Queries will be saved under:     " ++ (newFolderPath </> "queries")
  
  -- テストデータに対する予測評価（分類精度）
  evalResult <- evaluateModel device trainedModel testData biDirectional
  saveEvaluationReport newFolderPath evalResult allLabels
  putStrLn $ "Classification Accuracy: " ++ show (erAccuracy evalResult)
  
  -- ============================================
  -- Phase 5: 証明探索による速度評価
  -- ============================================
  putStrLn ""
  putStrLn "=== Phase 5: Proof Search Speed Evaluation ==="
  
  let proverConfig = ProverConfig
        { cfgMaxDepth = maxDepth
        , cfgMaxTime = maxTime
        }
  
  putStrLn $ "Prover config: maxDepth=" ++ show maxDepth ++ ", maxTime=" ++ show maxTime
  
  -- 保存したモデルをロードしてNeuralWani関数を構築
  putStrLn "Loading saved model for NeuralWani..."
  emptyModel <- sample hyperParams
  loadedModel <- loadParams emptyModel modelFileName
  frequentWordsEither <- decode <$> B.readFile frequentWordsFileName
  loadedFrequentWords <- case frequentWordsEither of
    Left err -> error $ "Failed to decode frequentWords: " ++ show err
    Right ws -> return ws
  let loadedWordMap = buildWordMap loadedFrequentWords
      neuralWaniFunc = buildNeuralWani device loadedModel loadedWordMap biDirectional delimiterToken
  putStrLn "Model loaded successfully."
  
  -- テスト問題に対して証明探索を実行（クエリと証明木も保存）
  let maxTestCases = 50  -- 最大テストケース数
      testCases = take maxTestCases testProblems
  
  putStrLn $ "Running " ++ show (length testCases) ++ " test cases..."
  putStrLn ""
  
  evalResults <- forM (zip [1..] testCases) $ \(idx :: Int, problem) -> do
    putStr $ "Test " ++ show idx ++ " [" ++ jspJsemId problem ++ "]... "
    result <- try $ evaluateOneProblem proverConfig neuralWaniFunc newFolderPath idx problem
    case result of
      Right (Just r) -> do
        putStrLn $ "Normal: " ++ TL.unpack (formatTimeNominal (pseNormalTime r)) ++ 
                   " (" ++ (if pseNormalSuccess r then "OK" else "FAIL") ++ ")" ++
                   ", Neural: " ++ TL.unpack (formatTimeNominal (pseNeuralTime r)) ++
                   " (" ++ (if pseNeuralSuccess r then "OK" else "FAIL") ++ ")"
        return $ Just r
      Right Nothing -> do
        putStrLn "SKIP (no inference query)"
        return Nothing
      Left (e :: SomeException) -> do
        putStrLn $ "ERROR: " ++ show e
        return Nothing
  
  let successfulResults = catMaybes evalResults
  
  -- サマリーを表示
  printEvalSummary successfulResults
  
  -- レポートをファイルに保存
  saveProofSearchReport newFolderPath proverConfig successfulResults

  -- TeXレポートを出力（evaluate/Main.hs を参考に構成）
  let sessionId = "D" ++ show (cfgMaxDepth proverConfig) ++ "T" ++ show (cfgMaxTime proverConfig) ++ "_" ++ timeString
  writeTexReportJSeM newFolderPath proverConfig sessionId successfulResults
  
  putStrLn ""
  putStrLn "=== Done ==="
  putStrLn $ "All results saved to: " ++ newFolderPath

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | JSeM XMLから問題を読み込み、型チェック証明木と推論問題を抽出して保存するプログラム
--
-- 保存されるデータ:
-- - JSeMProblemData: JSeM ID、(Judgment, Rule)ペア、推論問題（ProofSearchQuery）
--
-- 使用方法:
--   collectTypeCheckTrees-exe jsemDir outputPath
--
-- 例:
--   collectTypeCheckTrees-exe ../JSeM/data/v1.0 jsemProblemData.bin

module Main (main) where

import Control.Monad (forM, forM_)
import System.FilePath ((</>), takeDirectory)
import System.Directory (createDirectoryIfMissing)
import Data.List (isSuffixOf)
import qualified Data.Text as StrictT     --text
import qualified Data.Text.IO as TextIO   --text
import qualified Data.Text.Lazy as TL     --text
import qualified Data.Text.Lazy.IO as TL  --text
import qualified Data.ByteString as B     --bytestring
import Data.Store (Store, encode, decode)
import qualified GHC.Generics as G
import System.Environment (getArgs)
import qualified System.IO as S           --base
import qualified ListT

import qualified DTS.QueryTypes as QT
import qualified DTS.DTTdeBruijn as DTT
import qualified Interface.Tree as I
import Data.Maybe (catMaybes)

-- JSeM関連のインポート
import qualified JSeM as J
import qualified JSeM.XML as J

-- パーサー関連のインポート
import qualified Parser.ChartParser as CP
import Parser.LangOptions (defaultJpOptions)
import qualified DTS.NaturalLanguageInference as NLI

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

-- | JSeM XMLファイルのリスト
jsemFileNames :: [String]
jsemFileNames = 
  [ "Adjectives"
  , "CompoundAdjective"
  , "GeneralizedQuantifier"
  -- , "Question"
  -- , "Adverb"
  -- , "CompoundVerb"
  -- , "Modality"
  , "TemporalReference"
  , "Attitudes"
  -- , "Conditional"
  , "NP"
  -- , "Toritate"
  -- , "AuxiliaryVerb"
  -- , "Conjunction"
  -- , "NewAdjective"
  , "Verbs"
  -- , "CaseParticle"
  -- , "Coordination"
  , "NominalAnaphora"
  ]

-- ============================================
-- JSeM問題の読み込みと処理
-- ============================================

-- | JSeM問題を読み込み、型チェック証明木と推論問題を抽出し、各ファイルごとに即座に保存
loadAndSaveJSeMProblems :: FilePath -> FilePath -> CP.ParseSetting -> QT.Prover -> IO [(String, [JSeMProblemData])]
loadAndSaveJSeMProblems jsemDir outputDir parseSetting prover = do
  createDirectoryIfMissing True outputDir
  forM jsemFileNames $ \fileName -> do
    let filePath = jsemDir </> fileName ++ ".xml"
    putStrLn $ "Loading: " ++ filePath
    contents <- TL.readFile filePath
    parsedJSeM <- J.xml2jsemData $ TL.toStrict contents
    
    results <- forM parsedJSeM $ \j -> do
      let jsemId = StrictT.unpack $ J.jsem_id j
      S.putStr $ "[JSeM-ID " ++ jsemId ++ "] "
      mapM_ TextIO.putStr $ J.premises j
      S.putStr " ==> "
      TextIO.putStrLn $ J.hypothesis j
      
      let sentences = reverse $ (TL.fromStrict $ J.hypothesis j) : (map TL.fromStrict $ J.premises j)
          parseResult = NLI.parseWithTypeCheck parseSetting prover [("dummy", DTT.Entity)] [] sentences
      
      -- 型チェック証明木を取得
      typeCheckDiagrams <- ListT.toList $ trawlTypeCheckDiagrams parseResult
      let judgmentRules = concatMap extractJudgmentRules typeCheckDiagrams
      
      -- 推論問題を取得
      inferenceQuery <- getInferenceQuery parseResult
      
      return JSeMProblemData
        { jspJsemId = jsemId
        , jspJudgmentRules = judgmentRules
        , jspInferenceQuery = inferenceQuery
        }
    
    -- 処理完了後、即座に保存
    let outputPath = outputDir </> fileName ++ ".bin"
        fileData = JSeMFileData
          { jfdFileName = fileName
          , jfdProblems = results
          }
    B.writeFile outputPath (encode fileData)
    putStrLn $ "  Saved: " ++ outputPath ++ " (" ++ show (length results) ++ " problems)"
    
    return (fileName, results)

-- | ParseResultから型チェック証明木を抽出
trawlTypeCheckDiagrams :: NLI.ParseResult -> ListT.ListT IO QT.DTTProofDiagram
trawlTypeCheckDiagrams (NLI.SentenceAndParseTrees _ parseTreeAndFelicityChecks) = do
  (NLI.ParseTreeAndFelicityChecks _ _ _ felicityCheckAndMores) <- parseTreeAndFelicityChecks 
  (typeCheckDiagram, parseResult) <- felicityCheckAndMores
  ListT.cons typeCheckDiagram $ trawlTypeCheckDiagrams parseResult
trawlTypeCheckDiagrams (NLI.InferenceResults _ _) = ListT.fromFoldable []
trawlTypeCheckDiagrams NLI.NoSentence = ListT.fromFoldable []

-- | ParseResultから推論問題を取得
getInferenceQuery :: NLI.ParseResult -> IO (Maybe DTT.ProofSearchQuery)
getInferenceQuery (NLI.SentenceAndParseTrees _ parseTreeAndFelicityChecks) = do
  maybeUncons <- ListT.uncons parseTreeAndFelicityChecks
  case maybeUncons of
    Nothing -> return Nothing
    Just (NLI.ParseTreeAndFelicityChecks _ _ _ felicityCheckAndMores, _) -> do
      maybeUncons2 <- ListT.uncons felicityCheckAndMores
      case maybeUncons2 of
        Nothing -> return Nothing
        Just ((_, parseResult), _) -> getInferenceQuery parseResult
getInferenceQuery (NLI.InferenceResults (NLI.QueryAndDiagrams query _) _) = return $ Just query
getInferenceQuery NLI.NoSentence = return Nothing

-- | 証明木から(Judgment, DTTrule)ペアを抽出
extractJudgmentRules :: I.Tree QT.DTTrule DTT.Judgment -> [(DTT.Judgment, QT.DTTrule)]
extractJudgmentRules tree = processTree [] tree
  where
    processTree pairs t = 
      let newPair = (I.node t, I.ruleName t)
          updatedPairs = pairs ++ [newPair]
          ds = I.daughters t
      in if null ds
         then updatedPairs
         else foldl processTree updatedPairs ds

-- | JSeMProblemDataをファイルに保存（統合版）
saveJSeMProblems :: FilePath -> [JSeMProblemData] -> IO ()
saveJSeMProblems path problems = B.writeFile path (encode problems)

-- | JSeMファイルごとにデータを保存
saveJSeMProblemsPerFile :: FilePath -> [(String, [JSeMProblemData])] -> IO ()
saveJSeMProblemsPerFile outputDir problemsPerFile = do
  createDirectoryIfMissing True outputDir
  forM_ problemsPerFile $ \(fileName, problems) -> do
    let filePath = outputDir </> fileName ++ ".bin"
        fileData = JSeMFileData
          { jfdFileName = fileName
          , jfdProblems = problems
          }
    B.writeFile filePath (encode fileData)
    putStrLn $ "  " ++ fileName ++ ".bin (" ++ show (length problems) ++ " problems)"

-- | JSeMFileDataをファイルから読み込み
loadJSeMFileData :: FilePath -> IO JSeMFileData
loadJSeMFileData path = do
  bytes <- B.readFile path
  case decode bytes of
    Left err -> error $ "Failed to decode JSeMFileData from " ++ path ++ ": " ++ show err
    Right fileData -> return fileData

-- | 指定したJSeMファイルのデータを読み込み
loadJSeMProblemsFromFile :: FilePath -> String -> IO [JSeMProblemData]
loadJSeMProblemsFromFile outputDir fileName = do
  let filePath = outputDir </> fileName ++ ".bin"
  fileData <- loadJSeMFileData filePath
  return $ jfdProblems fileData

-- | 全てのJSeMファイルのデータを読み込み
loadAllJSeMProblems :: FilePath -> IO [(String, [JSeMProblemData])]
loadAllJSeMProblems outputDir = do
  forM jsemFileNames $ \fileName -> do
    let filePath = outputDir </> fileName ++ ".bin"
    fileData <- loadJSeMFileData filePath
    return (jfdFileName fileData, jfdProblems fileData)

-- ============================================
-- メイン関数
-- ============================================

main :: IO ()
main = do
  args <- getArgs
  
  let (jsemDir, outputPath) = case args of
        [a1, a2] -> (a1, a2)
        _ -> error $ unlines
          [ "Usage: collectTypeCheckTrees-exe jsemDir outputPath"
          , ""
          , "Example: collectTypeCheckTrees-exe ../JSeM/data/v1.0 jsemProblemData"
          , ""
          , "Arguments:"
          , "  jsemDir    : String - Path to JSeM XML directory"
          , "  outputPath : String - Output directory for per-file data, or .bin file for all-in-one"
          , ""
          , "Note: If outputPath ends with .bin, saves all data in one file."
          , "      Otherwise, creates a directory and saves each JSeM file separately."
          ]
  
  putStrLn "=== Collect TypeCheck Trees from JSeM ==="
  putStrLn ""
  putStrLn $ "JSeM directory: " ++ jsemDir
  putStrLn $ "Output path: " ++ outputPath
  putStrLn ""
  
  -- パーサー設定
  langOptions <- defaultJpOptions
  let beamW = 32
      nParse = 1
      nTypeCheck = 1
      nProof = 1
      parseSetting = CP.ParseSetting langOptions beamW nParse nTypeCheck nProof True Nothing False False
      prover = NLI.getProver NLI.Wani $ QT.defaultProofSearchSetting { QT.maxDepth = Just 4, QT.maxTime = Nothing, QT.logicSystem = Just QT.Classical }
  
  -- JSeM問題を読み込み（各ファイル処理後に即座に保存）
  putStrLn "=== Loading and Saving JSeM Problems ==="
  
  -- .binで終わる場合は統合版モード、それ以外はファイルごとモード
  let isUnifiedMode = ".bin" `isSuffixOf` outputPath
  
  if isUnifiedMode
    then do
      -- 統合版モード: 全て読み込んでから一括保存
      putStrLn "Mode: Unified file (all-in-one)"
      problemsPerFile <- forM jsemFileNames $ \fileName -> do
        let filePath = jsemDir </> fileName ++ ".xml"
        putStrLn $ "Loading: " ++ filePath
        contents <- TL.readFile filePath
        parsedJSeM <- J.xml2jsemData $ TL.toStrict contents
        
        results <- forM parsedJSeM $ \j -> do
          let jsemId = StrictT.unpack $ J.jsem_id j
          S.putStr $ "[JSeM-ID " ++ jsemId ++ "] "
          mapM_ TextIO.putStr $ J.premises j
          S.putStr " ==> "
          TextIO.putStrLn $ J.hypothesis j
          
          let sentences = reverse $ (TL.fromStrict $ J.hypothesis j) : (map TL.fromStrict $ J.premises j)
              parseResult = NLI.parseWithTypeCheck parseSetting prover [("dummy", DTT.Entity)] [] sentences
          
          typeCheckDiagrams <- ListT.toList $ trawlTypeCheckDiagrams parseResult
          let judgmentRules = concatMap extractJudgmentRules typeCheckDiagrams
          
          inferenceQuery <- getInferenceQuery parseResult
          
          return JSeMProblemData
            { jspJsemId = jsemId
            , jspJudgmentRules = judgmentRules
            , jspInferenceQuery = inferenceQuery
            }
        
        return (fileName, results)
      
      let allProblems = concatMap snd problemsPerFile
      saveJSeMProblems outputPath allProblems
      putStrLn $ "All data saved to: " ++ outputPath
      
      -- サマリー
      putStrLn ""
      putStrLn "=== Summary ==="
      putStrLn $ "Total JSeM problems: " ++ show (length allProblems)
      let allJudgmentRules = concatMap jspJudgmentRules allProblems
      putStrLn $ "Total judgment-rule pairs: " ++ show (length allJudgmentRules)
      let problemsWithQuery = filter (not . null . jspInferenceQuery) allProblems
      putStrLn $ "Problems with inference query: " ++ show (length problemsWithQuery)
    else do
      -- ファイルごとモード: 各ファイル処理後に即座に保存
      putStrLn $ "Mode: Per-file (directory: " ++ outputPath ++ ")"
      problemsPerFile <- loadAndSaveJSeMProblems jsemDir outputPath parseSetting prover
      
      let allProblems = concatMap snd problemsPerFile
      
      -- 統合版も保存（互換性のため）
      putStrLn ""
      putStrLn "=== Creating combined file ==="
      let combinedPath = outputPath </> "all.bin"
      saveJSeMProblems combinedPath allProblems
      putStrLn $ "Combined data saved to: " ++ combinedPath
      
      -- サマリー
      putStrLn ""
      putStrLn "=== Summary ==="
      putStrLn $ "Total JSeM files: " ++ show (length problemsPerFile)
      forM_ problemsPerFile $ \(fileName, problems) -> do
        putStrLn $ "  " ++ fileName ++ ": " ++ show (length problems) ++ " problems"
      putStrLn $ "Total JSeM problems: " ++ show (length allProblems)
      let allJudgmentRules = concatMap jspJudgmentRules allProblems
      putStrLn $ "Total judgment-rule pairs: " ++ show (length allJudgmentRules)
      let problemsWithQuery = filter (not . null . jspInferenceQuery) allProblems
      putStrLn $ "Problems with inference query: " ++ show (length problemsWithQuery)
  
  putStrLn ""
  putStrLn "=== Done ==="




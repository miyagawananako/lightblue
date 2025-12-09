{-# OPTIONS -Wall #-}
{-# LANGUAGE OverloadedStrings, RecordWildCards #-}

import Options.Applicative hiding (style) --optparse-applicative
import Control.Applicative (optional)     --base
import Control.Monad (forM, foldM)               --base
import ListT (ListT(..),toList,fromFoldable)                     --list-t
import qualified Data.Text.Lazy as T      --text
import qualified Data.Text.Lazy.IO as T   --text
import qualified Data.Text as StrictT     --text
import qualified Data.Text.IO as StrictT  --text
import Data.Ratio ((%))                   --base
import qualified Data.Char as C           --base
import qualified Data.List as L           --base
import qualified Data.Fixed as F          --base
import qualified System.IO as S           --base
import qualified System.Environment as E -- base
import qualified Data.Map as M            --container
import qualified Data.Time as Time        --time
import qualified Parser.ChartParser as CP
import qualified Parser.PartialParsing as CP
import qualified Parser.Language.Japanese.Lexicon as LEX
import qualified Parser.Language.Japanese.MyLexicon as LEX
import qualified Parser.Language.Japanese.Juman.CallJuman as Juman
import qualified Parser.Language.Japanese.Filter.KNPFilter as Filter
import qualified Parser.Language.Japanese.Filter.KWJAFilter as Filter
import Parser.LangOptions (defaultJpOptions)
import qualified Interface as I
import qualified Interface.Text as I
import qualified JSeM as J
import qualified JSeM.XML as J
import qualified DTS.UDTTdeBruijn as UDTT
import qualified DTS.DTTdeBruijn as DTT
import DTS.TypeChecker (typeInfer,nullProver)
import qualified DTS.QueryTypes as QT
import qualified DTS.NaturalLanguageInference as NLI
import qualified JSeM as JSeM                         --jsem
import qualified Data.ByteString as B --bytestring
import Data.Store (encode)
import Interface.Tree as I
import qualified DTS.Prover.Wani.Prove as Wani
import qualified DTS.Prover.Wani.Arrowterm as A

main :: IO()
main = do
    contents <- T.readFile "../JSeM/data/v1.0/Verbs.xml"
    langOptions <- defaultJpOptions
    let style = I.TEXT
        beamW = 32
        nParse = 1
        nTypeCheck = 1
        nProof = 1
        noInference = False
        noTypeCheck = False
        nSample = 10
        verbose = False
        maxDepth = Just 6
        maxTime = Nothing
        handle = S.stdout
        parseSetting = CP.ParseSetting langOptions beamW nParse nTypeCheck nProof True Nothing noInference verbose
        proofSearchSetting = QT.defaultProofSearchSetting { QT.maxDepth = maxDepth, QT.maxTime = maxTime, QT.logicSystem = Just QT.Classical }
        prover = NLI.getProver NLI.Wani proofSearchSetting
        -- 指定されたJSeM IDのリスト
        targetIds = ["696", "699", "700", "702", "703", "704", "705", "706", "709", "711", "720", "722", "724", "725", "726", "727", "728"]
    parsedJSeM <- J.xml2jsemData $ T.toStrict contents
    -- 指定されたIDのみをフィルタリング
    let filteredJSeM = filter (\j -> StrictT.unpack (J.jsem_id j) `elem` targetIds) parsedJSeM
    parseResults <- forM filteredJSeM $ \j -> do
        let title = "JSeM-ID " ++ (StrictT.unpack $ J.jsem_id j)
        S.putStr $ "[" ++ title ++ "] "
        mapM_ StrictT.putStr $ J.premises j
        S.putStr " ==> "
        StrictT.putStrLn $ J.hypothesis j
        let sentences = reverse $ (T.fromStrict $ J.hypothesis j):(map T.fromStrict $ J.premises j)
        return $ toList $ trawlParseResultWithArrowTree proofSearchSetting $ NLI.parseWithTypeCheck parseSetting prover [("dummy",DTT.Entity)] [] sentences
    arrowTrees <- mconcat parseResults
    mapM_ (T.putStrLn . I.toText . A.aTreeTojTree') $ take nSample arrowTrees
    proofSearchResults <- mapM makePairFromArrowTree arrowTrees
    B.writeFile ("../../wani/neuralWani/data/JSeM_ProofSearchTrees/ArrowTerm/Verbs"++ (show $ length proofSearchResults) ++ "_" ++ (show $ length (concat proofSearchResults))) (encode proofSearchResults)

{-- Trawling functions using prove'WithArrowTree --}

-- | prove'WithArrowTree を使って Arrow Tree を取得する trawl 関数
trawlParseResultWithArrowTree :: QT.ProofSearchSetting -> NLI.ParseResult -> ListT IO (I.Tree A.Arrowrule A.AJudgment)
trawlParseResultWithArrowTree settings (NLI.SentenceAndParseTrees _ parseTreeAndFelicityChecks) = do
  (NLI.ParseTreeAndFelicityChecks _ _ _ felicityCheckAndMores) <- parseTreeAndFelicityChecks 
  (_, parseResult) <- felicityCheckAndMores
  trawlParseResultWithArrowTree settings parseResult
trawlParseResultWithArrowTree settings (NLI.InferenceResults (NLI.QueryAndDiagrams psqPos _) (NLI.QueryAndDiagrams psqNeg _)) =
  -- prove'WithArrowTree を使って Arrow Tree を直接取得
  let resultPos = Wani.prove'WithArrowTree settings psqPos
      resultNeg = Wani.prove'WithArrowTree settings psqNeg
  in mappend resultPos resultNeg
trawlParseResultWithArrowTree _ NLI.NoSentence = fromFoldable []

{-- Conversion functions using a2dtJudgment --}

-- | Arrow Tree から (DTT.Judgment, QT.DTTrule) のペアリストを作成
-- | a2dtJudgment を使って AJudgment を DTT.Judgment に変換する
makePairFromArrowTree :: I.Tree A.Arrowrule A.AJudgment -> IO [(DTT.Judgment, QT.DTTrule)]
makePairFromArrowTree tree = processTree [] tree
  where
    processTree pairs t = do
      -- a2dtJudgment を使って AJudgment を DTT.Judgment に変換
      let newPair = (A.a2dtJudgment (I.node t), I.ruleName t)
      let updatedPairs = pairs ++ [newPair]
      if null (I.daughters t)
        then return updatedPairs
        else foldM processTree updatedPairs (I.daughters t)

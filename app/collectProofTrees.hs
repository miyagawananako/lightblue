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
        prover = NLI.getProver NLI.Wani $ QT.ProofSearchSetting maxDepth maxTime (Just QT.Classical)
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
        return $ toList $ trawlParseResult $ NLI.parseWithTypeCheck parseSetting prover [("dummy",DTT.Entity)] [] sentences
    proofDiagrams <- mconcat parseResults
    mapM_ (T.putStrLn . I.toText) $ take nSample proofDiagrams
    proofSearchResults <- getProofSearchResult proofDiagrams
    B.writeFile ("../../wani/neuralWani/data/JSeM_ProofSearchTrees/Verbs"++ (show $ length proofSearchResults) ++ "_" ++ (show $ length (concat proofSearchResults))) (encode proofSearchResults)

{-- Trawling functions --}

trawlParseResult :: NLI.ParseResult -> ListT IO QT.DTTProofDiagram
trawlParseResult (NLI.SentenceAndParseTrees _ parseTreeAndFelicityChecks) = do
  (NLI.ParseTreeAndFelicityChecks _ _ _ felicityCheckAndMores) <- parseTreeAndFelicityChecks 
  (_, parseResult) <- felicityCheckAndMores
  trawlParseResult parseResult
trawlParseResult (NLI.InferenceResults (NLI.QueryAndDiagrams _ resultPos) (NLI.QueryAndDiagrams _ resultNeg)) = mappend resultPos resultNeg
trawlParseResult NLI.NoSentence = fromFoldable []

getProofSearchResult :: [I.Tree QT.DTTrule DTT.Judgment] -> IO [[(DTT.Judgment, QT.DTTrule)]]
getProofSearchResult ts = do
    results <- forM ts makePair
    return results

makePair :: I.Tree QT.DTTrule DTT.Judgment -> IO [(DTT.Judgment, QT.DTTrule)]
makePair resultList = do
    processTree [] resultList
    where
        processTree pairs tree = do
            let daughters = I.daughters tree
            let newPair = (I.node tree, I.ruleName tree)
            let updatedPairs = pairs ++ [newPair]
            if null daughters
                then return updatedPairs
                else foldM processTree updatedPairs daughters
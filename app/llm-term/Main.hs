{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
-- | Builds Wani's proof trees from problems and proof terms a language model wrote.
module Main (main) where

import Control.DeepSeq (rnf)
import Control.Exception (evaluate, try, SomeException)
import Control.Monad (forM, forM_)
import qualified Data.Aeson as Aeson
import Data.Aeson ((.=))
import qualified Data.Aeson.KeyMap as KeyMap
import qualified Data.ByteString.Lazy.Char8 as BLC
import qualified Data.List as List
import qualified Data.List.Split as List
import qualified Data.Map.Strict as Map
import Data.Time.Clock (getCurrentTime, diffUTCTime, NominalDiffTime)
import qualified Data.Text.Lazy as TL
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.FilePath ((</>))
import System.Mem (performMajorGC)
import System.Timeout (timeout)
import Text.Printf (printf)
import qualified ListT
import qualified Interface.Tree as I
import qualified Interface.Text as IText
import qualified DTS.QueryTypes as QT
import qualified DTS.DTTdeBruijn as DTT
import qualified DTS.UDTTdeBruijn as UDTT
import qualified DTS.TypeChecker as TC
import qualified DTS.Prover.Wani.BackwardRules as BR
import qualified DTS.Prover.Wani.Prove as Prove
import qualified LlmTerm
import DttJson ()

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--llm-term-selftest"] -> LlmTerm.llmTermSelfTest
    ("--llm-build":rest) -> llmBuildMain rest
    _ -> error "Usage: llmTerm --llm-term-selftest | --llm-build [--sequential] problems.jsonl outDir"

-- ============================================
-- --llm-build: training data from problems and proof terms a language model wrote
-- ============================================

llmBuildMain :: [String] -> IO ()
llmBuildMain ("--sequential":args) = llmBuild False args
llmBuildMain args = llmBuild True args

-- | The first argument is `QT.concurrent` for both the plain search and the build.
llmBuild :: Bool -> [String] -> IO ()
llmBuild concurrent args = case args of
  [problemsFile, outDir] -> do
    createDirectoryIfMissing True outDir
    -- Each line is read twice: as a problem, and as the object accepted.jsonl extends.
    rawLines <- filter (not . BLC.null) . BLC.lines <$> BLC.readFile problemsFile
    outcomes <- forM (zip [1 :: Int ..] rawLines) $ \(idx, raw) ->
      case (,) <$> Aeson.eitherDecode raw <*> Aeson.eitherDecode raw of
        Left err -> do
          putStrLn $ printf "[%d] not read: %s" idx err
          return (printf "%d\t-\t-\tnot read\t%s" idx (oneLine err), Nothing)
        Right (problem, object) -> do
          (row, built) <- llmBuildOne concurrent idx problem
          return (row, fmap ((,) object) built)
    writeFile (outDir </> "results.tsv") $ unlines $
      List.intercalate "\t" ["idx", "name", "logic", "stage", "detail", "search", "searchTime", "trees", "buildTime", "typeCheck", "pairs", "depth9"]
      : map fst outcomes
    BLC.writeFile (outDir </> "accepted.jsonl") $ BLC.unlines
      [ Aeson.encode (Aeson.Object (KeyMap.union (builtFields b) object)) | (_, Just (object, b)) <- outcomes ]
    let rules = concatMap (map snd . builtPairs . snd) [b | (_, Just b) <- outcomes]
        stageCount s = length [() | (row, _) <- outcomes, (List.splitOn "\t" row !! 3) == s]
        labels = Map.fromListWith (+) [ (show l, 1 :: Int) | r <- rules, Just l <- [BR.dttruleToRuleLabel r] ]
    putStrLn ""
    putStrLn $ "Problems:        " ++ show (length outcomes)
    forM_ ["not read", "not converted", "no tree", "tree"] $ \s ->
      putStrLn $ printf "  %-14s %d" (s ++ ":") (stageCount s)
    putStrLn $ "Accepted:        " ++ (outDir </> "accepted.jsonl")
    putStrLn $ "Pairs:           " ++ show (length rules)
    putStrLn $ "Rule labels:     " ++ show (Map.toList labels)
    putStrLn $ "Plain search:    " ++ if concurrent then "concurrent" else "sequential"
  _ -> error "Usage: llmTerm --llm-build [--sequential] problems.jsonl outDir"
  where
    oneLine = map (\c -> if c `elem` ("\t\n\r" :: String) then ' ' else c)

-- | A problem whose term Wani built a tree from.
data Built = Built
  { builtSearch     :: String
  , builtSearchTime :: Maybe Double
  , builtTrees      :: Int
  , builtQuery      :: DTT.ProofSearchQuery
  , builtPairs      :: [(DTT.Judgment, QT.DTTrule)]  -- ^ of the first tree
  , builtDepth9     :: String
  }

builtFields :: Built -> Aeson.Object
builtFields b = KeyMap.fromList
  [ "search" .= builtSearch b
  , "searchTime" .= builtSearchTime b
  , "trees" .= builtTrees b
  , "pairs" .= length (builtPairs b)
  , "ruleLabels" .= Map.fromListWith (+) [ (show l, 1 :: Int) | (_, r) <- builtPairs b, Just l <- [BR.dttruleToRuleLabel r] ]
  , "query" .= builtQuery b
  , "judgmentRules" .= builtPairs b
  , "depth9" .= builtDepth9 b
  ]

-- | One problem: convert it, record whether plain Wani proves it on its own, and build
-- Wani's tree from the term.
llmBuildOne :: Bool -> Int -> LlmTerm.LlmProblem -> IO (String, Maybe Built)
llmBuildOne concurrent idx problem = do
  let name = LlmTerm.lpName problem
      row stage detail rest = List.intercalate "\t" ([show idx, name, LlmTerm.lpLogic problem, stage, oneLine detail] ++ rest)
  putStr $ printf "[%d] %s: " idx name
  let settingFor el = QT.defaultProofSearchSetting { QT.maxDepth = Just 9, QT.maxTime = Just 30000, QT.logicSystem = Just (LlmTerm.elLogic el), QT.concurrent = concurrent }
  converted <- either (return . Left) (\el -> LlmTerm.fillEquations (settingFor el) el)
                 (LlmTerm.elaborateProblem problem)
  case converted of
    Left err -> do
      putStrLn $ "not converted: " ++ err
      return (row "not converted" err ["-", "-", "-", "-", "-", "-", "-"], Nothing)
    Right el -> do
      let query = LlmTerm.elQuery el
          term = LlmTerm.elTerm el
          searchSetting = settingFor el
          buildSetting = searchSetting { QT.maxDepth = Just 15 }
      searched <- try $ timeout (120 * 1000000) (runProveWithTree searchSetting query)
      let (search, searchSeconds) = case searched of
            Left (_ :: SomeException) -> ("error", Nothing)
            Right Nothing -> ("timeout", Nothing)
            Right (Just ([], t)) -> ("not proved", Just (realToFrac t :: Double))
            Right (Just (_, t)) -> ("proved", Just (realToFrac t))
          searchTime = maybe "-" (printf "%.3f") searchSeconds :: String
      start <- getCurrentTime
      built <- try $ timeout (60 * 1000000) $ do
        ts <- Prove.proveWithTerm buildSetting query term
        evaluate (length ts) >> return ts
      end <- getCurrentTime
      typeChecked <- typeCheckProof query term
      let buildTime = printf "%.3f" (realToFrac (diffUTCTime end start) :: Double) :: String
          termText = TL.unpack (IText.toText term)
      case built of
        Right (Just ts@(tree : _)) -> do
          -- Plain search stops at depth 9, so a tree beyond it is out of its reach.
          built9 <- try $ timeout (60 * 1000000) $ do
            ts9 <- Prove.proveWithTerm buildSetting { QT.maxDepth = Just 9 } query term
            evaluate (length ts9)
          let pairs = treePairs tree
              -- Not yes/no, which read as JSeM's answers (the hypothesis or its negation is proved).
              depth9 = case built9 of
                Left (_ :: SomeException) -> "error"
                Right Nothing -> "timeout"
                Right (Just 0) -> "exceeds"
                Right (Just _) -> "fits"
          putStrLn $ printf "tree (%d), %d pairs, depth 9: %s; plain Wani %s" (length ts) (length pairs) depth9 search
          return ( row "tree" termText [search, searchTime, show (length ts), buildTime, typeChecked, show (length pairs), depth9]
                 , Just (Built search searchSeconds (length ts) query pairs depth9) )
        other -> do
          let detail = case other of
                Left (e :: SomeException) -> "error: " ++ takeWhile (/= '\n') (show e)
                Right Nothing -> "timeout"
                _ -> "no tree"
          putStrLn $ printf "%s; plain Wani %s" detail search
          return (row "no tree" (detail ++ ": " ++ termText) [search, searchTime, "0", buildTime, typeChecked, "0", "-"], Nothing)
  where
    oneLine = map (\c -> if c `elem` ("\t\n\r" :: String) then ' ' else c)

-- | Pre-order, the same order as proofNodePairs on the NeuralWani line.
treePairs :: I.Tree QT.DTTrule DTT.Judgment -> [(DTT.Judgment, QT.DTTrule)]
treePairs t = (I.node t, I.ruleName t) : concatMap treePairs (I.daughters t)

runProveWithTree :: QT.ProofSearchSetting -> DTT.ProofSearchQuery
                 -> IO ([I.Tree QT.DTTrule DTT.Judgment], NominalDiffTime)
runProveWithTree setting query@(DTT.ProofSearchQuery sig ctx typ) = do
  -- Keep evaluating the query and collecting garbage out of the measured time.
  evaluate $ rnf (sig, ctx, typ)
  performMajorGC
  startTime <- getCurrentTime
  maybeTree <- ListT.head (Prove.prove' setting query)
  endTime <- getCurrentTime
  return (maybe [] (: []) maybeTree, diffUTCTime endTime startTime)

-- | The type checker throws its failure messages away (list-t's fail), so
-- only the outcome is reported.
typeCheckProof :: DTT.ProofSearchQuery -> DTT.Preterm -> IO String
typeCheckProof (DTT.ProofSearchQuery sig ctx goal) term = do
  let query = UDTT.toUDTTJudgment (DTT.Judgment sig ctx term goal)
      checker = TC.typeCheck (TC.nullProver QT.defaultProofSearchSetting) False
  r <- try $ timeout (60 * 1000000) $ ListT.head (checker query)
  return $ case r of
    Left (e :: SomeException) -> "error: " ++ map (\c -> if c `elem` ("\t\n\r" :: String) then ' ' else c) (show e)
    Right Nothing             -> "timeout"
    Right (Just Nothing)      -> "rejected"
    Right (Just (Just _))     -> "accepted"

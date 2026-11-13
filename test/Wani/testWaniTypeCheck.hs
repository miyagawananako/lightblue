{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad (forM, unless)
import System.Exit (exitFailure)
import System.Timeout (timeout)
import qualified ListT
import qualified DTS.DTTdeBruijn as D
import qualified DTS.UDTTdeBruijn as U
import qualified DTS.QueryTypes as QT
import DTS.Prover.Wani.Prove (prove')
import DTS.TypeChecker (typeCheck, nullProver)
import qualified Interface.Tree as I

-- | Checks that every proof term Wani finds is accepted by the type checker.
-- The problems stay in the intuitionistic fragment without EFQ or disjunction
-- elimination, since the type checker rejects the terms for those rules.
main :: IO ()
main = do
  results <- forM problems $ \(name, query) -> do
    result <- timeout timeLimit $ checkProblem query
    let verdict = case result of
          Nothing -> Left "timeout"
          Just v -> v
    putStrLn $ either (\e -> "NG\t" ++ name ++ "\t" ++ e) (\t -> "ok\t" ++ name ++ "\t" ++ t) verdict
    return $ either (const False) (const True) verdict
  unless (and results) exitFailure

timeLimit :: Int
timeLimit = 60 * 1000000

setting :: QT.ProofSearchSetting
setting = QT.defaultProofSearchSetting { QT.logicSystem = Nothing, QT.enableNegativeOracle = False }

checkProblem :: D.ProofSearchQuery -> IO (Either String String)
checkProblem query = do
  trees <- ListT.toList $ prove' setting query
  if null trees
    then return $ Left "no proof found"
    else do
      verdicts <- forM trees $ \tree -> do
        let judgment = I.node tree
        accepted <- fmap not $ ListT.null $
          typeCheck (nullProver QT.defaultProofSearchSetting) False (U.toUDTTJudgment judgment)
        return (accepted, show (D.trm judgment))
      return $ case [t | (False, t) <- verdicts] of
        [] -> Right $ unwords (map snd verdicts)
        rejected -> Left $ "rejected: " ++ unwords rejected

neg :: D.Preterm -> D.Preterm
neg a = D.Pi a D.Bot

-- | Contexts list the innermost assumption first.
problems :: [(String, D.ProofSearchQuery)]
problems =
  [ ( "d:¬(¬p2∧¬¬p1), h1:p1 ⊢ ¬¬p2"
    , D.ProofSearchQuery (sig ["p2", "p1"])
        [D.Con "p1", neg (D.Sigma (neg (D.Con "p2")) (neg (neg (D.Con "p1"))))]
        (neg (neg (D.Con "p2"))) )
  , ( "f:(q→p∧q)→r ⊢ p→r"
    , D.ProofSearchQuery (sig ["r", "q", "p"])
        [D.Pi (D.Pi (D.Con "q") (D.Sigma (D.Con "p") (D.Con "q"))) (D.Con "r")]
        (D.Pi (D.Con "p") (D.Con "r")) )
  , ( "f:(q→s→p∧(q∧s))→r ⊢ p→r"
    , D.ProofSearchQuery (sig ["s", "r", "q", "p"])
        [D.Pi (D.Pi (D.Con "q") (D.Pi (D.Con "s") (D.Sigma (D.Con "p") (D.Sigma (D.Con "q") (D.Con "s"))))) (D.Con "r")]
        (D.Pi (D.Con "p") (D.Con "r")) )
  , ( "f:(q→q)→p→r ⊢ s→p→r"
    , D.ProofSearchQuery (sig ["s", "r", "q", "p"])
        [D.Pi (D.Pi (D.Con "q") (D.Con "q")) (D.Pi (D.Con "p") (D.Con "r"))]
        (D.Pi (D.Con "s") (D.Pi (D.Con "p") (D.Con "r"))) )
  , ( "g:p→q, f:q→r ⊢ p→r"
    , D.ProofSearchQuery (sig ["r", "q", "p"])
        [D.Pi (D.Con "q") (D.Con "r"), D.Pi (D.Con "p") (D.Con "q")]
        (D.Pi (D.Con "p") (D.Con "r")) )
  , ( "f:(q→p∧q)→r ⊢ p→(r∧(q→q))"
    , D.ProofSearchQuery (sig ["r", "q", "p"])
        [D.Pi (D.Pi (D.Con "q") (D.Sigma (D.Con "p") (D.Con "q"))) (D.Con "r")]
        (D.Pi (D.Con "p") (D.Sigma (D.Con "r") (D.Pi (D.Con "q") (D.Con "q")))) )
  ]
  where sig names = [(n, D.Type) | n <- names]

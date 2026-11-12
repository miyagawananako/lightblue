{-# OPTIONS_GHC -Wno-orphans #-}
-- | JSON for the (Judgment, rule) pairs handed to the NeuralWani line, which builds with
-- another resolver and so cannot read this side's Store encoding. The same file sits on
-- both sides; the instances are generic, so both sides agree while the types do.
module DttJson () where

import qualified Data.Aeson as Aeson
import qualified DTS.DTTdeBruijn as DTT
import qualified DTS.QueryTypes as QT

instance Aeson.ToJSON DTT.Selector
instance Aeson.FromJSON DTT.Selector
instance Aeson.ToJSON DTT.Preterm
instance Aeson.FromJSON DTT.Preterm
instance Aeson.ToJSON DTT.Judgment
instance Aeson.FromJSON DTT.Judgment
instance Aeson.ToJSON DTT.ProofSearchQuery
instance Aeson.FromJSON DTT.ProofSearchQuery
instance Aeson.ToJSON QT.DTTrule
instance Aeson.FromJSON QT.DTTrule

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Semantics.State where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Lazy as BL
import Data.Aeson
import GHC.Generics (Generic)
import Syntax.Syntax (Var)

data State = State {
    vars    :: Map Var Int
  , arrays  :: Map Var (Map Int Int)
  } deriving (Eq, Show)

emptyState :: State
emptyState = State Map.empty Map.empty

lookupVar :: Var -> State -> Int
lookupVar x st = Map.findWithDefault 0 x (vars st)

updateVar :: Var -> Int -> State -> State
updateVar x val st = st { vars = Map.insert x val (vars st) }

lookupArr :: Var -> Int -> State -> Int
lookupArr arrName idx st = 
  case Map.lookup arrName (arrays st) of
    Nothing   -> 0
    Just arr  -> Map.findWithDefault 0 idx arr

updateArr :: Var -> Int -> Int -> State -> State
updateArr arrName idx val st = 
  let currentArr  = Map.findWithDefault Map.empty arrName (arrays st)
      newArr      = Map.insert idx val currentArr
  in st { arrays  = Map.insert arrName newArr (arrays st) }

data CostModel = CostModel {
    costNum :: Int
  , costVar :: Int
  , costArr :: Int
  , costAdd :: Int
  , costSub :: Int
  , costMul :: Int
  , costDiv :: Int
  , costExp :: Int
  , costTrue :: Int
  , costFalse :: Int
  , costLe  :: Int
  , costGe  :: Int
  , costLt  :: Int
  , costGt  :: Int
  , costAnd :: Int
  , costOr  :: Int
  , costEq  :: Int
  , costNe  :: Int
  , costNeg :: Int
  , costAssV :: Int
  , costAssA :: Int
  , costSkip :: Int
  } deriving (Eq, Show, Generic)

unitModel :: CostModel
unitModel = CostModel {
    costNum = 1
  , costVar = 1
  , costArr = 1
  , costAdd = 1
  , costSub = 1
  , costMul = 1
  , costDiv = 1
  , costExp = 1
  , costTrue = 1
  , costFalse = 1
  , costLe  = 1
  , costGe  = 1
  , costLt  = 1
  , costGt  = 1
  , costAnd = 1
  , costOr  = 1
  , costEq  = 1
  , costNe  = 1
  , costNeg = 1
  , costAssV = 1
  , costAssA = 1
  , costSkip = 1
  }

instance FromJSON CostModel where
  parseJSON = withObject "CostModel" $ \v -> CostModel
    <$> v .:? "costNum"   .!= 1
    <*> v .:? "costVar"   .!= 1
    <*> v .:? "costArr"   .!= 1
    <*> v .:? "costAdd"   .!= 1
    <*> v .:? "costSub"   .!= 1
    <*> v .:? "costMul"   .!= 1
    <*> v .:? "costDiv"   .!= 1
    <*> v .:? "costExp"   .!= 1
    <*> v .:? "costTrue"  .!= 1
    <*> v .:? "costFalse" .!= 1
    <*> v .:? "costLe"    .!= 1
    <*> v .:? "costGe"    .!= 1
    <*> v .:? "costLt"    .!= 1
    <*> v .:? "costGt"    .!= 1
    <*> v .:? "costAnd"   .!= 1
    <*> v .:? "costOr"    .!= 1
    <*> v .:? "costEq"    .!= 1
    <*> v .:? "costNe"    .!= 1
    <*> v .:? "costNeg"   .!= 1
    <*> v .:? "costAssV"  .!= 1
    <*> v .:? "costAssA"  .!= 1
    <*> v .:? "costSkip"  .!= 1

instance ToJSON CostModel

loadCostModel :: FilePath -> IO (Either String CostModel)
loadCostModel path = do
  bytes <- BL.readFile path
  case eitherDecode bytes of
    Left err -> pure (Left $ "Error reading CostModel JSON: " ++ err)
    Right cm ->
      if any (< 0) (allCosts cm)
        then pure (Left "Error: operation costs cannot be negative.")
        else pure (Right cm)
  where
    allCosts :: CostModel -> [Int]
    allCosts c = [ 
        costNum   c
      , costVar   c
      , costArr   c
      , costAdd   c
      , costSub   c
      , costMul   c
      , costDiv   c
      , costExp   c
      , costTrue  c
      , costFalse c
      , costLe    c
      , costGe    c
      , costLt    c
      , costGt    c
      , costAnd   c
      , costOr    c
      , costEq    c
      , costNe    c
      , costNeg   c
      , costAssV  c
      , costAssA  c
      , costSkip  c
      ]
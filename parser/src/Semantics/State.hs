module Semantics.State where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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
  } deriving (Eq, Show)

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
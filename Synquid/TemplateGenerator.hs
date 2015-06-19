-- | Filling in the holes in program templates
module Synquid.TemplateGenerator where

import Synquid.Logic
import Synquid.Program
import Synquid.Util

import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Applicative
import Control.Monad
import Control.Monad.Stream

-- | Parameters of template generation
data TemplGenParams = TemplGenParams {
  maxDepth :: Int
}

-- | 'exapansions' @params leafShapes templ@ : all expansions of holes in @templ@
-- that only use leaves of @leafShapes@ generated using @params@
exapansions :: TemplGenParams -> Set SType -> Template -> Stream Template
exapansions params leafShapes (Program templ s) = flip Program s <$> let go = exapansions params leafShapes in case templ of
  PSymbol () -> return $ PSymbol ()
  PApp tFun tArg -> liftM2 PApp (go tFun) (go tArg)
  PFun x tBody -> liftM (PFun x) (go tBody)
  PIf () tThen tElse -> liftM2 (PIf ()) (go tThen) (go tElse)
  PMatch tScr tCases -> liftM2 PMatch (go tScr) (mapM expandCase tCases)
  PFix f tBody -> liftM (PFix f) (go tBody)
  PHole -> content <$> appTemplates leafShapes s (maxDepth params)
  where
    expandCase (Case consName argNames tExpr) = liftM (Case consName argNames) (exapansions params leafShapes tExpr)

-- | 'appTemplates' @leafShapes s depth@ : all templates of type @s@ made up of only symbols of shapes @leafShapes@ and applications up to depth @depth@. 
appTemplates :: Set SType -> SType -> Int -> Stream Template
appTemplates leafShapes s depth = if depth == 0 then mzero else flip Program s <$> symbols `mplus` applications
  where
    symbols = do
      guard $ Set.member s leafShapes
      return $ PSymbol ()
      
    applications = do
      sArg <- scalarTypes      
      let sFun = sArg |->| s
      guard $ not $ Set.null $ Set.filter (isRhs sFun) leafShapes 
      arg <- appTemplates leafShapes sArg (depth - 1)
      fun <- appTemplates leafShapes sFun (depth - 1)
      return $ PApp fun arg
      
    isRhs t (ScalarT _ _) = False
    isRhs t t'@(FunctionT _ tArg tRes) = t == t' || isRhs t tRes

-- | All scalar types    
scalarTypes :: Stream SType
scalarTypes = msum $ map return [int_, list_]


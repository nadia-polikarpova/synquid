{-# LANGUAGE TemplateHaskell #-}

-- | Executable programs
module Synquid.Program where

import Synquid.Logic
import Synquid.Util

import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Lens
  
-- | Base types  
data BaseType = BoolT | IntT
  deriving (Eq, Ord)

-- | Type skeletons parametrized by refinements  
data TypeSkeleton r =
  ScalarT BaseType r |
  FunctionT Id (TypeSkeleton r) (TypeSkeleton r)
  deriving (Eq, Ord)
  
-- | Unrefined typed  
type SType = TypeSkeleton ()  

-- | Refinement types  
type RType = TypeSkeleton Formula

-- | Forget refinements
shape :: RType -> SType  
shape (ScalarT base _) = ScalarT base ()
shape (FunctionT _ tArg tFun) = FunctionT dontCare (shape tArg) (shape tFun)

refine :: SType -> RType
refine (ScalarT base _) = ScalarT base ftrue
refine (FunctionT _ tArg tFun) = FunctionT dontCare (refine tArg) (refine tFun) -- ToDo: do we care???
  
-- | 'unifyVarsWith' @t' t@: @t@ with value variables replaced by the corresponding ones from @t'@
-- (the types must have the same shape)
unifyVarsWith :: RType -> RType -> RType
unifyVarsWith t' t = unifyVarsWith' Map.empty t' t
  where
    unifyVarsWith' m (ScalarT _ _) (ScalarT base fml) = ScalarT base (substitute m fml)
    unifyVarsWith' m (FunctionT x tArg' tFun') (FunctionT y tArg tFun) = FunctionT x (unifyVarsWith' m tArg' tArg) (unifyVarsWith' (Map.insert y (Var x) m) tFun' tFun)
    
renameVar :: Id -> Id -> RType -> RType    
renameVar old new (ScalarT base fml) = ScalarT base (substitute (Map.singleton old (Var new)) fml)
renameVar old new (FunctionT x tArg tRes) = FunctionT x (renameVar old new tArg) (renameVar old new tRes)
      
unknownsOfType :: RType -> Set Formula
unknownsOfType (ScalarT _ fml) = unknownsOf fml
unknownsOfType (FunctionT _ arg res) = unknownsOfType arg `Set.union` unknownsOfType res

-- | 'typeApplySolution' @sol t@: replace all unknowns in @t@ with their valuations in @sol@
typeApplySolution :: Solution -> RType -> RType
typeApplySolution sol (ScalarT base fml) = ScalarT base $ applySolution sol fml
typeApplySolution sol (FunctionT x arg fun) = FunctionT x (typeApplySolution sol arg) (typeApplySolution sol fun)

-- | Typing environment
data Environment = Environment {
  _symbols :: Map Formula RType,                -- ^ Variables and constants (with their refinement types)
  _symbolsOfShape :: Map SType (Set Formula),   -- ^ Variables and constants indexed by their simple type
  _assumptions :: Set Formula,                  -- ^ Positive unknown assumptions
  _negAssumptions :: Set Formula                -- ^ Negative unknown assumptions
}

makeLenses ''Environment  

-- | Environment with no symbols or assumptions
emptyEnv = Environment Map.empty Map.empty Set.empty Set.empty

-- | 'addSymbol' @sym t env@ : add type binding @sym@ :: @t@ to @env@
addSymbol :: Formula -> RType -> Environment -> Environment
addSymbol sym t = (symbols %~ Map.insert sym t) . (symbolsOfShape %~ Map.insertWith (Set.union) (shape t) (Set.singleton sym))

-- | 'varRefinement' @v x@ : refinement of a scalar variable
varRefinement x = valueVar |=| Var x

-- | 'varFromRefinement' @v fml@ : if @fml@ is a variable refinement, return the variable
varFromRefinement (Binary Eq v (Var x))
  | v == valueVar = Just $ Var x
varFromRefinement _ = Nothing
                  
-- | 'symbolsByShape' @s env@ : symbols of simple type @s@ in @env@ 
symbolsByShape :: SType -> Environment -> Map Formula RType
symbolsByShape s env = restrictDomain (Map.findWithDefault Set.empty s (env ^. symbolsOfShape)) (env ^. symbols)

-- | 'addAssumption' @f env@ : @env@ with extra assumption @f@
addAssumption :: Formula -> Environment -> Environment
addAssumption f = assumptions %~ Set.insert f

-- | 'addNegAssumption' @f env@ : @env@ with extra assumption not @f@
addNegAssumption :: Formula -> Environment -> Environment
addNegAssumption f = negAssumptions %~ Set.insert f

-- | 'restrict' @t env@ : @env@ with only those symbols whose simple type matches the shape of @t@, and variables renamed accordingly
restrict :: RType -> Environment -> Environment
restrict t env = env {_symbols = Map.map (unifyVarsWith t) $ symbolsByShape (shape t) env}
    
-- | Positive and negative formulas encoded in an environment    
embedding :: Environment -> (Set Formula, Set Formula)    
embedding env = ((env ^. assumptions) `Set.union` (Map.foldlWithKey (\fmls s t -> fmls `Set.union` embedBinding s t) Set.empty $ env ^. symbols), env ^.negAssumptions)
  where
    embedBinding _ (ScalarT _ (BoolLit True)) = Set.empty -- Ignore trivial types
    embedBinding (Var x) (ScalarT _ (Unknown _ u)) = Set.singleton $ Unknown x u -- Pending substitution
    embedBinding (Var x) (ScalarT _ fml) = Set.singleton $ substitute (Map.singleton valueVarName (Var x)) fml -- In-place substitution
    embedBinding _ _ = Set.empty
    
-- | Program skeletons parametrized by information stored in symbols and conditionals
data Program v s c =
  PSymbol s |
  PApp (Program v s c) (Program v s c) |
  PFun v (Program v s c) |
  PIf c (Program v s c) (Program v s c) |
  PFix v (Program v s c)
    
-- | Program templates (skeleton + unrefined types of symbols)
type Template = Program SType SType ()

-- | Fully defined programs 
type SimpleProgram = Program Id Formula Formula

-- | Programs where symbols are represented by their refinement type, which might contain unknowns
type LiquidProgram = Program Id (Environment, RType) Formula

-- | Simple type of a program template
sTypeOf :: Template -> SType
sTypeOf (PSymbol t) = t
sTypeOf (PApp fun _) = let (FunctionT _ _ t) = sTypeOf fun in t
sTypeOf (PFun t p) = FunctionT dontCare t (sTypeOf p)
sTypeOf (PIf _ p _) = sTypeOf p
sTypeOf (PFix t _) = t

int = ScalarT IntT
int_ = int ()
(|->|) = FunctionT dontCare
sym = PSymbol
choice = PIf ()
(|$|) = PApp
(|.|) = PFun
fix_ = PFix 

infixr 5 |->|
infixr 5 |$|
infixr 4 |.|
          
-- | Typing constraints
data Constraint = Subtype Environment RType RType
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
  | WellFormedSymbol Environment RType
  
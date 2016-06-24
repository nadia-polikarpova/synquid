{-# LANGUAGE ExistentialQuantification, FlexibleInstances, UndecidableInstances #-}

module Synquid.Codegen where

import qualified Data.Map as Map
import Data.Map (assocs,elems,union,empty,(!))
import qualified Data.Set as Set
import Data.Set ((\\))

import Control.Lens ((^.))
import Control.Monad

import Safe

import System.IO

import Language.Haskell.Exts.Syntax hiding (Case, PApp)
import qualified Language.Haskell.Exts.Syntax as Hs
import Language.Haskell.Exts.Pretty

import Synquid.Util
import Synquid.Type
import Synquid.Program hiding (DataDecl)
import Synquid.Logic hiding (Var)
import Synquid.Tokens
import qualified Synquid.Pretty


(|>) x y = y x
infixl 0 |>
(|>>) x y = map y x
infixl 0 |>>

type HsDecl = Decl
type HsType = Type
type HsQualType = Type
type HsExp = Exp

{- Some container classes -}

data HaskellElement = forall s. Pretty s => HE s

class AsHaskell a where
  toHs :: Environment -> a -> HaskellElement

class AsHaskellDecl a where
  toHsDecl :: Environment -> a -> HsDecl

class AsHaskellType a where
  toHsType :: Environment -> a -> HsType
  toHsQualType :: Environment -> a -> HsQualType
  toHsQualType env t = {- HsQualType [] $ -} toHsType env t

class AsHaskellExp a where
  toHsExp :: Environment -> a -> HsExp

data AsHaskellDeclElement =  {- to create heterogenous lists of AsHaskellDecl -}
  forall s. AsHaskellDecl s => AHDE s

{- Helper functions for the implementation -}

unknownLoc = SrcLoc { srcFilename="", srcLine=0, srcColumn=0 }

argTypes (TyFun argType resultType) = argType : argTypes resultType
argTypes typ = []

{- for now, all type parameters get these type classes by default -}
defaultTypeClasses = map tc ["Eq", "Ord"]
  where tc = UnQual . Ident

defaultImports = [ImportDecl {
    importLoc = unknownLoc,
    importModule = ModuleName "Prelude",
    importQualified = False,
    importSrc = False,
    importSafe = False,
    importPkg = Nothing,
    importAs = Nothing,
    importSpecs = Just (False, ids ++ syms)}]
  where
    ids = map (IAbs NoNamespace . Ident) ["Eq", "Ord", "Int", "Bool"] ++
          map (IVar . Ident) ["undefined"]
    syms = map (IVar . Symbol) ["<=", "==", ">=", "<", ">", "/=", "+", "-"]

qualifyByDefault tArg typ = typ {- (HsQualType ctx typ) =
  HsQualType (ctx ++ map qual defaultTypeClasses) typ
  where qual cls = (cls, [HsTyVar $ HsIdent tArg]) -}



constructorNames env = concatMap (^. constructors) $ env ^. datatypes

nonConstructorConsts env =
  let ctors = Set.fromList $ constructorNames env
      consts = env ^. constants
      symbs = allSymbols env
  in map (\c -> (c, symbs ! c)) $ Set.toList (consts \\ ctors)

{- AsHaskell* instances -}

instance AsHaskell (Id, DatatypeDef) where
  toHs env nameDef = HE $ toHsDecl env nameDef

instance AsHaskell (Id, SchemaSkeleton r) where
  toHs env nameType = HE $ toHsDecl env nameType

instance AsHaskell (Program r) where
  toHs env p = HE $ toHsExp env p

instance AsHaskell (BareProgram r) where
  toHs env p = HE $ toHsExp env p

instance AsHaskell (Goal, Program r) where
  toHs env goalProg = HE $ toHsDecl env goalProg

instance AsHaskellDecl (Id, DatatypeDef) where
  toHsDecl env (name,def) =
    DataDecl unknownLoc         -- source location
             DataType           -- 'data' or 'newtype'
               []                 -- context (type class reqs for parameters)
               (Ident name)     -- datatype name
               params             -- type parameter names
               ctors              -- constructor declarations
               typeClss           -- deriving
    where
      params = def ^. typeParams |>> UnkindedVar . Ident
      ctors = def ^. constructors |>>
              \x -> QualConDecl unknownLoc [] [] (ConDecl (Ident x) (ctorArgs x))
      ctorArgs name = toHsType env (allSymbols env ! name)
                      |> argTypes
      typeClss = if null ctors then [] else defaultTypeClasses |>> (\x -> (x, []))

instance AsHaskellDecl (Goal, Program r) where
  toHsDecl _ (Goal name env _ _ _ _, p) = PatBind unknownLoc
    (PVar $ Ident name)                -- lhs (pattern)
    (UnGuardedRhs $ toHsExp env p)     -- rhs (expression)
    Nothing                            -- bindings??

instance AsHaskellDecl Goal where
  toHsDecl _ (Goal name env spec _ _ _) = TypeSig unknownLoc
    [Ident name]
    (toHsQualType env spec)

instance AsHaskellDecl (Id, SchemaSkeleton r) where
  toHsDecl env (name, typ) = TypeSig unknownLoc
    [Ident name]
    (toHsQualType env typ)

instance AsHaskellDecl Id where
  toHsDecl env name = PatBind unknownLoc
    (PVar $ Ident name)
    (UnGuardedRhs $ Var $ UnQual $ Ident "undefined")
    Nothing

instance AsHaskellDecl AsHaskellDeclElement where
  toHsDecl env (AHDE e) = toHsDecl env e

instance AsHaskellType (SchemaSkeleton r) where
  toHsType env (ForallT tArg typ) = toHsType env typ
  toHsType env (ForallP pArg typ) = toHsType env typ
  toHsType env (Monotype skel) = toHsType env skel
  toHsQualType env (ForallT tArg typ) =
    qualifyByDefault tArg $ toHsQualType env typ
  toHsQualType env typ = {- HsQualType [] $ -} toHsType env typ

instance AsHaskellType (TypeSkeleton r) where
  toHsType env (ScalarT base _) = toHsType env base
  toHsType env (FunctionT _ argType resultType) =
    TyFun (toHsType env argType) (toHsType env resultType)
  toHsType env AnyT = TyCon $ UnQual $ Ident "Any"

instance AsHaskellType (BaseType r) where
  toHsType env BoolT = TyCon $ UnQual $ Ident "Bool"
  toHsType env IntT = TyCon $ UnQual $ Ident "Int"
  toHsType env (DatatypeT name tArgs pArgs) =
    foldl TyApp typeCtor $ map (toHsType env) tArgs
    where
      typeCtor = TyCon $ UnQual $ Ident name
  toHsType env (TypeVarT _ name) = TyVar $ Ident name

instance AsHaskellExp (Program r) where
  toHsExp env (Program term _) = toHsExp env term

instance AsHaskellExp (BareProgram r) where
  toHsExp env (PSymbol sym) = Var $ UnQual $ Ident sym
  toHsExp env (PApp fun arg) =
    case infixate fun arg of
      Just (l, op, r) -> Paren $ InfixApp (toHsExp env l) (QVarOp (UnQual (Symbol op))) (toHsExp env r)
      Nothing -> Paren $ App (toHsExp env fun) (toHsExp env arg)
    where
      infixate (Program (PApp (Program (PSymbol op) _) l) _) r
       | isBinOp op = Just (l, op, r)
      infixate _ _  = Nothing
      isBinOp x | x `elem` elems binOpTokens = True
      isBinOp _ = False
  toHsExp env (PFun arg body) = Paren $ Lambda unknownLoc [pvar] (toHsExp env body)
    where pvar = PVar $ Ident arg
  toHsExp env (PIf cond then_ else_) =
    If (toHsExp env cond) (toHsExp env then_) (toHsExp env else_)
  toHsExp env (PMatch switch cases) =
    Hs.Case (toHsExp env switch) (map alt cases)
    where alt (Case ctor argNames expr) =
            Alt unknownLoc
              (Hs.PApp (UnQual $ Ident ctor)       -- pattern
                $ map (PVar . Ident) argNames)
              (UnGuardedRhs $ toHsExp env expr)   -- body
              Nothing                                    -- ??
  toHsExp env (PFix _ p) = toHsExp env p
  toHsExp env (PLet name value body) =
    Let (BDecls [PatBind unknownLoc
                 (PVar $ Ident name)                           -- binder name
                 (UnGuardedRhs $ toHsExp env value) Nothing])  -- rhs
                 (toHsExp env body)                            -- in (expr)
  toHsExp env other = Var $ UnQual $ Ident "??"

{- A module contains data declarations and functions -}
toHsModule :: String -> [(Goal, RProgram)] -> Module
toHsModule name goalProgs =
  -- TODO Currently grabs environment from the first goal.
  --   Merge environments from all goals?
  let decls = inspectGP goalProgs
      sigs =  goalProgs |>> AHDE . fst
      funcs = goalProgs |>> AHDE
   in Module unknownLoc
         (ModuleName name)                            -- module name
         []                                           -- module pragmas
         Nothing                                      -- warning text
         Nothing                                      -- exports
         (defaultImports ++ userImports)              -- imports
         (decls ++ sigs ++ funcs |>> toHsDecl env)    -- body (declarations)
  where
    env = goalProgs |>> gEnvironment . fst |> headDef emptyEnv
    inspectGP l = assocs (env ^. datatypes) |> filter (not . isSkipped . fst) |>> AHDE
               -- ++ (nonConstructorConsts env |>> AHDE)
               -- ++ (nonConstructorConsts env |>> AHDE . fst)

{-- TODO these should definitely not be hard-coded --}

isSkipped ident = ident `elem` ["String", "Tagged", "PaperId", "User", "World"]

userImports = [ImportDecl {
    importLoc = unknownLoc,
    importModule = ModuleName "ConferenceImpl",
    importQualified = False,
    importSrc = True,
    importSafe = False,
    importPkg = Nothing,
    importAs = Nothing,
    importSpecs = Nothing}]

{- Pretty printing and inspection   -}
{- (these are useful for debugging) -}

prettyPrintHE (HE a) = prettyPrint a

prettify :: AsHaskell a => Environment -> a -> String
prettify env = prettyPrintHE . toHs env

inspectDatatypes :: Environment -> IO ()
inspectDatatypes env =
  forM_ (assocs $ env ^. datatypes) $ putStrLn . prettify env

inspectConstants :: Environment -> IO ()
inspectConstants env =
  forM_ (nonConstructorConsts env) $ putStrLn . prettify env

inspectSolution :: Goal -> Program r -> IO ()
inspectSolution goal p = --do
  let env = gEnvironment goal
    in putStrLn $ prettify env (goal, p)

inspectSolutions :: [(Goal, Program r)] -> IO ()
inspectSolutions goalProgs = do
  unless (null goalProgs) $ inspectDatatypes (gEnvironment $ fst $ head goalProgs)
  forM_ goalProgs $ uncurry inspectSolution

{-
 - Module entry point; translate everything and write result to file
 -  filePath: output filename; '-' for standard output
 -  moduleName: identifier to name the new module
 -  goalProgs: a list of (goal, synthesized program)
 -}
extractModule filePath moduleName goalProgs =
    let out = if filePath == "-" then putStr else writeFileLn filePath
        writeFileLn f s = do h <- openFile f WriteMode ; hPutStrLn h s ; hClose h
        env = gEnvironment $ fst $ head goalProgs
    in do
      inspectDatatypes env
      inspectConstants env
      out $ prettyPrint $ toHsModule moduleName goalProgs

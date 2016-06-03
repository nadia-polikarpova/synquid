{-# LANGUAGE ExistentialQuantification, FlexibleInstances #-}

module Synquid.Codegen where

import Data.Map (assocs,elems,union,empty,(!))

import Control.Lens ((^.))
import Control.Monad

import System.IO

import Language.Haskell.Syntax
import Language.Haskell.Pretty

import Synquid.Program
import Synquid.Logic
import Synquid.Tokens


(|>) x y = y x
infixl 0 |>
(|>>) x y = map y x
infixl 0 |>>


{- Some container classes -}

data HaskellElement = forall s. Pretty s => HE s

class AsHaskell a where
  toHs :: Environment -> a -> HaskellElement

class AsHaskellDecl a where
  toHsDecl :: Environment -> a -> HsDecl

class AsHaskellType a where
  toHsType :: Environment -> a -> HsType
  toHsQualType :: Environment -> a -> HsQualType
  toHsQualType env t = HsQualType [] $ toHsType env t

class AsHaskellExp a where
  toHsExp :: Environment -> a -> HsExp


{- Helper functions for the implementation -}

unknownLoc = SrcLoc { srcFilename="", srcLine=0, srcColumn=0 }

argTypes (HsTyFun argType resultType) = argType : argTypes resultType
argTypes typ = []

{- for now, all type parameters get these type classes by default -}
defaultTypeClasses = map tc ["Eq", "Ord"]
  where tc = UnQual . HsIdent

defaultImports = [HsImportDecl {
    importLoc = unknownLoc,
    importModule = Module "Prelude",
    importQualified = False,
    importAs = Nothing,
    importSpecs = Just (False, ids ++ syms)}]
  where
    ids = map (HsIAbs . HsIdent) ["Eq", "Ord", "Int", "Bool"]
    syms = map (HsIVar . HsSymbol) ["<=", "==", ">=", "<", ">", "/=", "+", "-"]

qualifyByDefault tArg (HsQualType ctx typ) =
  HsQualType (ctx ++ map qual defaultTypeClasses) typ
  where qual cls = (cls, [HsTyVar $ HsIdent tArg])



symbolTable env = foldl union empty $ elems $ env ^. symbols

constructorNames env = concatMap (^. constructors) $ elems $ env ^. datatypes


{- AsHaskell* instances -}

instance AsHaskell (Id, DatatypeDef) where
  toHs env nameDef = HE $ toHsDecl env nameDef

instance AsHaskell (Program r) where
  toHs env p = HE $ toHsExp env p

instance AsHaskell (BareProgram r) where
  toHs env p = HE $ toHsExp env p

instance AsHaskell (Goal, Program r) where
  toHs env goalProg = HE $ toHsDecl env goalProg

instance AsHaskellDecl (Id, DatatypeDef) where
  toHsDecl env (name,def) =
    HsDataDecl unknownLoc         -- source location
               []                 -- context (type class reqs for parameters)
               (HsIdent name)     -- datatype name
               params             -- type parameter names
               ctors              -- constructor declarations
               defaultTypeClasses -- deriving
    where
      params = def ^. typeParams |>> HsIdent
      ctors = def ^. constructors |>>
              \x -> HsConDecl unknownLoc (HsIdent x) (ctorArgs x)
      ctorArgs name = toHsType env (symbolTable env ! name)
                      |> argTypes |>> HsUnBangedTy

instance AsHaskellDecl (Goal, Program r) where
  toHsDecl _ (Goal name env _ _ _, p) = HsPatBind unknownLoc
    (HsPVar $ HsIdent name)            -- lhs (pattern)
    (HsUnGuardedRhs $ toHsExp env p)   -- rhs (expression)
    []                                 -- declarations??

instance AsHaskellDecl Goal where
  toHsDecl _ (Goal name env spec _ _) = HsTypeSig unknownLoc
    [HsIdent name]
    (toHsQualType env spec)

instance AsHaskellType (SchemaSkeleton r) where
  toHsType env (ForallT tArg typ) = toHsType env typ
  toHsType env (ForallP pArg typ) = toHsType env typ
  toHsType env (Monotype skel) = toHsType env skel
  toHsQualType env (ForallT tArg typ) =
    qualifyByDefault tArg $ toHsQualType env typ
  toHsQualType env typ = HsQualType [] $ toHsType env typ

instance AsHaskellType (TypeSkeleton r) where
  toHsType env (ScalarT base _) = toHsType env base
  toHsType env (FunctionT _ argType resultType) =
    HsTyFun (toHsType env argType) (toHsType env resultType)
  toHsType env AnyT = HsTyCon $ UnQual $ HsIdent "Any"

instance AsHaskellType (BaseType r) where
  toHsType env BoolT = HsTyCon $ UnQual $ HsIdent "Bool"
  toHsType env IntT = HsTyCon $ UnQual $ HsIdent "Int"
  toHsType env (DatatypeT name tArgs pArgs) =
    foldl HsTyApp typeCtor $ map (toHsType env) tArgs
    where
      typeCtor = HsTyCon $ UnQual $ HsIdent name
  toHsType env (TypeVarT name) = HsTyVar $ HsIdent name

instance AsHaskellExp (Program r) where
  toHsExp env (Program term _) = toHsExp env term

instance AsHaskellExp (BareProgram r) where
  toHsExp env (PSymbol sym) = HsVar $ UnQual $ HsIdent sym
  toHsExp env (PApp fun arg) =
    case infixate fun arg of
      Just (l, op, r) -> HsParen $ HsInfixApp (toHsExp env l) (HsQVarOp (UnQual (HsSymbol op))) (toHsExp env r)
      Nothing -> HsParen $ HsApp (toHsExp env fun) (toHsExp env arg)
    where
      infixate (Program (PApp (Program (PSymbol op) _) l) _) r
       | isBinOp op = Just (l, op, r)
      infixate _ _  = Nothing
      isBinOp x | x `elem` elems binOpTokens = True
      isBinOp _ = False
  toHsExp env (PFun arg body) = HsLambda unknownLoc [pvar] (toHsExp env body)
    where pvar = HsPVar $ HsIdent arg
  toHsExp env (PIf cond then_ else_) =
    HsIf (toHsExp env cond) (toHsExp env then_) (toHsExp env else_)
  toHsExp env (PMatch switch cases) =
    HsCase (toHsExp env switch) (map alt cases)
    where alt (Case ctor argNames expr) =
            HsAlt unknownLoc
              (HsPApp (UnQual $ HsIdent ctor)       -- pattern
                $ map (HsPVar . HsIdent) argNames)
              (HsUnGuardedAlt $ toHsExp env expr)   -- body
              []                                    -- ??
  toHsExp env (PFix _ p) = toHsExp env p
  toHsExp env (PLet name value body) =
    HsLet [HsPatBind unknownLoc
              (HsPVar $ HsIdent name)                   -- binder name
              (HsUnGuardedRhs $ toHsExp env value) []]  -- rhs
              (toHsExp env body)                        -- in
  toHsExp env other = HsVar $ UnQual $ HsIdent "??"

{- A module contains data declarations and functions -}
toHsModule :: String -> [(Goal, RProgram)] -> HsModule
toHsModule name goalProgs =
  -- TODO Currently grabs environment from the first goal.
  --   Merge environments from all goals?
  let datas = if null goalProgs then [] else inspectGP goalProgs
      sigs = map (\(goal, prog) -> toHsDecl env goal) goalProgs
      funcs = map (toHsDecl env) goalProgs
   in HsModule unknownLoc (Module name) Nothing defaultImports (datas ++ sigs ++ funcs)
  where
    env = gEnvironment $ fst $ head goalProgs
    inspectGP l = map (toHsDecl env) $ assocs $ env ^. datatypes


{- Pretty printing and output formatting -}

prettyPrintHE (HE a) = prettyPrint a

prettify :: AsHaskell a => Environment -> a -> String
prettify env = prettyPrintHE . toHs env

codegenDatatypes :: Environment -> IO ()
codegenDatatypes env =
  forM_ (assocs $ env ^. datatypes) $ putStrLn . prettify env

codegenSolution :: Goal -> Program r -> IO ()
codegenSolution goal p = --do
  let env = gEnvironment goal
    in putStrLn $ prettify env (goal, p)

codegenSolutions :: [(Goal, Program r)] -> IO ()
codegenSolutions goalProgs = do
  unless (null goalProgs) $ codegenDatatypes (gEnvironment $ fst $ head goalProgs)
  forM_ goalProgs $ uncurry codegenSolution

{-
 - Module entry point; translate everything and write result to file
 -  filePath: output filename; '-' for standard output
 -  moduleName: identifier to name the new module
 -  goalProgs: a list of (goal, synthesized program)
 -}
extractModule filePath moduleName goalProgs =
    let out = if filePath == "-" then putStr else writeFileLn filePath
        writeFileLn f s = do h <- openFile f WriteMode ; hPutStrLn h s ; hClose h
    in
      out $ prettyPrint $ toHsModule moduleName goalProgs

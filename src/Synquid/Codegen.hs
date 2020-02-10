{-# LANGUAGE ExistentialQuantification, FlexibleInstances, UndecidableInstances #-}

module Synquid.Codegen where

import Data.Char
import qualified Data.Map as Map
import Data.Map (assocs,keys,elems,union,empty,findWithDefault,filterWithKey,(!))
import qualified Data.Set as Set
import Data.Set ((\\))

import Control.Lens ((^.), over)
import Control.Monad

import Safe

import System.IO

import Language.Haskell.Exts.Syntax hiding (Case, PApp, DataDecl)
import qualified Language.Haskell.Exts.Syntax as Hs
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.SrcLoc

import Synquid.Util
import Synquid.Type
import Synquid.Program
import Synquid.Logic hiding (Var)
import Synquid.Tokens
import Synquid.Error
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
  toHsDecl :: Environment -> a -> HsDecl SrcLoc

class AsHaskellType a where
  toHsType :: Environment -> a -> HsType SrcLoc
  toHsQualType :: Environment -> a -> HsQualType SrcLoc
  toHsQualType = toHsType   -- ^ overridden when type qualifiers are possible

class AsHaskellExp a where
  toHsExp :: Environment -> a -> HsExp SrcLoc

data AsHaskellDeclElement =  {- to create heterogenous lists of AsHaskellDecl -}
  forall s. AsHaskellDecl s => AHDE s

{- Helper functions for the implementation -}

unknownLoc = SrcLoc { srcFilename="", srcLine=0, srcColumn=0 }

argTypes (TyFun unknownLoc argType resultType) = argType : argTypes resultType
argTypes typ = []

{- for now, all type parameters get these type classes by default -}
defaultTypeClasses = map tc ["Eq", "Ord"]
  where tc = UnQual unknownLoc . Ident unknownLoc

defaultImports = [ImportDecl {
    importAnn = unknownLoc,
    importModule = ModuleName unknownLoc "Prelude",
    importQualified = False,
    importSrc = False,
    importSafe = False,
    importPkg = Nothing,
    importAs = Nothing,
    importSpecs = Just $ ImportSpecList unknownLoc False (ids ++ syms)}]
  where
    ids :: [ImportSpec SrcLoc]
    ids = map (IAbs unknownLoc (NoNamespace unknownLoc) . Ident unknownLoc) ["Eq", "Ord", "Int", "Bool"] ++
          map (IVar unknownLoc . Ident unknownLoc) ["undefined"]
    syms :: [ImportSpec SrcLoc]
    syms = map (IVar unknownLoc . Symbol unknownLoc) ["<=", "==", ">=", "<", ">", "/=", "&&", "||", "+", "-"]

qualifyByDefault tArg = TyForall unknownLoc Nothing (Just $ CxTuple unknownLoc (map qual defaultTypeClasses))
  where qual cls = ClassA unknownLoc cls [TyVar unknownLoc $ Ident unknownLoc tArg]

ensureLower s = case s of
  c:cs | isLower c -> s
  _                -> "v" ++ s

vIdent env name
  | name `elem` constructorNames env = Ident unknownLoc name
  | otherwise = Ident unknownLoc $ ensureLower name

constructorNames env = concatMap (^. constructors) $ env ^. datatypes

nonConstructorConsts env =
  let ctors = Set.fromList $ constructorNames env
      consts = env ^. constants
      symbs = allSymbols env
  in map (\c -> (c, symbs ! c)) $ Set.toList (consts \\ ctors)

symbolRenames = Map.fromList [("!=", "/=")]

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
    Hs.DataDecl unknownLoc            -- source location
                (DataType unknownLoc) -- 'data' or 'newtype'
                Nothing               -- context (type class reqs for parameters)
                dhead                 -- name and parameters
                ctors                 -- constructor declarations
                typeClss              -- deriving
    where
      params = def ^. typeParams |>> UnkindedVar unknownLoc . Ident unknownLoc      
      dhead = foldl (DHApp unknownLoc) (DHead unknownLoc (Ident unknownLoc name)) params
      ctors = def ^. constructors |>>
              \x -> QualConDecl unknownLoc Nothing Nothing (ConDecl unknownLoc (Ident unknownLoc x) (ctorArgs x))
      ctorArgs name = toHsType env (allSymbols env ! name)
                      |> argTypes
      paramTyVars = def ^. typeParams |>> TyVar unknownLoc . Ident unknownLoc
      tyCon = TyCon unknownLoc $ UnQual unknownLoc $ Ident unknownLoc name
      instHead x = IHApp unknownLoc (IHCon unknownLoc x) (TyParen unknownLoc (foldl (TyApp unknownLoc) tyCon paramTyVars))
      rule x = IRule unknownLoc Nothing Nothing (instHead x)
      typeClss = if null ctors 
                   then [] 
                   else defaultTypeClasses |>> \x -> Deriving unknownLoc Nothing [rule x] -- (\x -> (x, []))

instance AsHaskellDecl (Goal, Program r) where
  toHsDecl _ (Goal name env _ _ _ _, p) = PatBind unknownLoc
    (PVar unknownLoc $ vIdent env name)           -- lhs (pattern)
    (UnGuardedRhs unknownLoc $ toHsExp env p)     -- rhs (expression)
    Nothing                                       -- bindings??

instance AsHaskellDecl Goal where
  toHsDecl _ (Goal name env spec _ _ _) = TypeSig unknownLoc
    [Ident unknownLoc name]
    (toHsQualType env spec)

instance AsHaskellDecl (Id, SchemaSkeleton r) where
  toHsDecl env (name, typ) = TypeSig unknownLoc
    [Ident unknownLoc name]
    (toHsQualType env typ)

instance AsHaskellDecl Id where
  toHsDecl env name = PatBind unknownLoc
    (PVar unknownLoc $ vIdent env name)
    (UnGuardedRhs unknownLoc $ Var unknownLoc $ UnQual unknownLoc $ Ident unknownLoc "undefined")
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
    TyFun unknownLoc (toHsType env argType) (toHsType env resultType)
  toHsType env AnyT = TyCon unknownLoc $ UnQual unknownLoc $ Ident unknownLoc "Any"

instance AsHaskellType (BaseType r) where
  toHsType env BoolT = TyCon unknownLoc $ UnQual unknownLoc $ Ident unknownLoc "Bool"
  toHsType env IntT = TyCon unknownLoc $ UnQual unknownLoc $ Ident unknownLoc "Int"
  toHsType env (DatatypeT name tArgs pArgs) =
    foldl (TyApp unknownLoc) typeCtor $ map (toHsType env) tArgs
    where
      typeCtor = TyCon unknownLoc $ UnQual unknownLoc $ Ident unknownLoc name
  toHsType env (TypeVarT _ name) = TyVar unknownLoc $ Ident unknownLoc name

instance AsHaskellExp (Program r) where
  toHsExp env (Program term _) = toHsExp env term

instance AsHaskellExp (BareProgram r) where
  toHsExp env (PSymbol sym) | Just n <- readMay sym = Lit unknownLoc $ Int unknownLoc n (show n)
                            | otherwise = Var unknownLoc $ UnQual unknownLoc $ vIdent env sym
  toHsExp env (PApp fun arg) =
    case infixate fun arg of
      Just (l, op, r) -> Paren unknownLoc $ InfixApp unknownLoc (toHsExp env l) (QVarOp unknownLoc (UnQual unknownLoc (Symbol unknownLoc op))) (toHsExp env r)
      Nothing -> Paren unknownLoc $ App unknownLoc (toHsExp env fun) (toHsExp env arg)
    where
      infixate (Program (PApp (Program (PSymbol op) _) l) _) r
       | isBinOp op = Just (l, ren op, r)
      infixate _ _  = Nothing
      isBinOp = (`elem` elems binOpTokens)
      ren op = findWithDefault op op symbolRenames
  toHsExp env (PFun arg body) = Paren unknownLoc $ Lambda unknownLoc [pvar] (toHsExp env body)
    where pvar = PVar unknownLoc $ vIdent env arg
  toHsExp env (PIf cond then_ else_) =
    If unknownLoc (toHsExp env cond) (toHsExp env then_) (toHsExp env else_)
  toHsExp env (PMatch switch cases) =
    Hs.Case unknownLoc (toHsExp env switch) (map alt cases)
    where alt (Case ctor argNames expr) =
            Alt unknownLoc
              (Hs.PApp unknownLoc (UnQual unknownLoc $ Ident unknownLoc ctor) -- pattern
                $ map (PVar unknownLoc . vIdent env) argNames)
              (UnGuardedRhs unknownLoc $ toHsExp env expr)         -- body
              Nothing                                              -- ??
  toHsExp env (PFix _ p) = toHsExp env p
  toHsExp env (PLet name value body) =
    Let unknownLoc (BDecls unknownLoc [PatBind unknownLoc
                 (PVar unknownLoc $ vIdent env name)           -- binder name
                 (UnGuardedRhs unknownLoc $ toHsExp env value) Nothing])  -- rhs
                 (toHsExp env body)                            -- in (expr)
  toHsExp env other = Var unknownLoc $ UnQual unknownLoc $ Symbol unknownLoc "??"

{- A module contains data declarations and functions -}
toHsModule :: String -> Environment -> [(Goal, RProgram)] -> Module SrcLoc

toHsModule name env goalProgs =
  -- TODO Currently grabs environment from the first goal.
  --   Merge environments from all goals?
  let decls = inspectGP goalProgs
      sigs =  goalProgs |>> AHDE . fst
      funcs = goalProgs |>> AHDE
      modHead = ModuleHead unknownLoc (ModuleName unknownLoc name) Nothing Nothing
   in Module unknownLoc
         (Just modHead)                               -- module header
         []                                           -- module pragmas
         (defaultImports ++ hardcodedImports)         -- imports
         (decls ++ sigs ++ funcs |>> toHsDecl env)    -- body (declarations)
  where
    inspectGP l = assocs (env ^. datatypes) |> filter (not . isSkipped . fst) |>> AHDE
               -- ++ (nonConstructorConsts env |>> AHDE)
               -- ++ (nonConstructorConsts env |>> AHDE . fst)

addImports imports (Module loc modHead prag imp decl) =
    Module loc modHead prag (imp ++ userImports) decl
  where
    userImports = map (\m -> importTmpl { importModule = ModuleName loc m }) imports

importTmpl = ImportDecl {
    importAnn = unknownLoc,
    importModule = ModuleName unknownLoc "?",
    importQualified = False,
    importSrc = False,
    importSafe = False,
    importPkg = Nothing,
    importAs = Nothing,
    importSpecs = Nothing }

filterOutDeps deps env =
  let isDeclOf name Pos {node = (DataDecl name' _ _ _)} = (name == name')
      isDeclOf _ _ = False
      inDeps k = any (isDeclOf k) $ concat $ elems deps
  in over datatypes (filterWithKey (\k _ -> not $ inDeps k)) env

{-- TODO these should definitely not be hard-coded --}

isSkipped ident = ident `elem` ["String", "Tagged", "PaperId", "User", "World", "Token"]

hardcodedImports = [importTmpl {
    importModule = ModuleName unknownLoc  "ConferenceImpl",
    importSrc = True}]

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
 -  deps: additional module dependencies (map of module name -> [decls])
 -}
extractModule filePath moduleName goalProgs deps =
    let out = if filePath == "-" then putStr else writeFileLn filePath
        writeFileLn f s = do h <- openFile f WriteMode ; hPutStrLn h s ; hClose h
        env = goalProgs |>> gEnvironment . fst |> headDef emptyEnv
                |> filterOutDeps deps
    in do
      inspectDatatypes env
      inspectConstants env
      out $ prettyPrint $ addImports (keys deps) $ toHsModule moduleName env goalProgs

{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | This module provides utilities for creating backends. Regular users do not
-- need to use this module.
module Database.Persist.TH
    ( persist
    , persistFile
    , mkPersist
    , share2
    , mkSave
    , mkDeleteCascade
    , derivePersistField
    , mkMigrate
    ) where

import Database.Persist.Base
import Database.Persist.GenericSql (Migration, SqlPersist, migrate)
import Database.Persist.Quasi (parse)
import Database.Persist.Util (deprecate, nullable)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Data.Char (toLower, toUpper)
import Data.List (nub, partition)
import Data.Maybe (mapMaybe, catMaybes)
import Web.Routes.Quasi (SinglePiece)
import Data.Int (Int64)
import Control.Monad (forM, liftM)
import Control.Monad.IO.Peel (MonadPeelIO)
import qualified System.IO as SIO

type ToClause = (Name, String, Type) -> Clause
-- | Converts a quasi-quoted syntax into a list of entity definitions, to be
-- used as input to the template haskell generation code (mkPersist).
persist :: QuasiQuoter
persist = QuasiQuoter
    { quoteExp = lift . parse
    }

persistFile :: FilePath -> Q Exp
persistFile fp = do
    h <- qRunIO $ SIO.openFile fp SIO.ReadMode
    qRunIO $ SIO.hSetEncoding h SIO.utf8_bom
    s <- qRunIO $ SIO.hGetContents h
    lift $ parse s

-- | Create data types and appropriate 'PersistEntity' instances for the given
-- 'EntityDef's. Works well with the persist quasi-quoter.
mkPersist :: [EntityDef] -> Q [Dec]
mkPersist = fmap concat . mapM mkEntity

recName :: String -> String -> String
recName dt f = lowerFirst dt ++ upperFirst f

lowerFirst :: String -> String
lowerFirst (x:xs) = toLower x : xs
lowerFirst [] = []

upperFirst :: String -> String
upperFirst (x:xs) = toUpper x : xs
upperFirst [] = []

dataTypeDec :: EntityDef -> Dec
dataTypeDec t =
    let name = eName t
        cols = map (mkCol $ entityName t) $ entityColumns t
     in DataD [] name [] [RecC name cols] $ map mkName $ entityDerives t
  where
    mkCol x (n, ty, as) =
        (mkName $ recName x n, NotStrict, pairToType (ty, nullable as))

keyTypeDec :: String -> Name -> EntityDef -> Dec
keyTypeDec constr typ t =
    NewtypeInstD [] ''Key [ConT $ eName t]
                (NormalC (mkName constr) [(NotStrict, ConT typ)])
                [''Show, ''Read, ''Num, ''Integral, ''Enum, ''Eq, ''Ord,
                 ''Real, ''PersistField, ''SinglePiece]

filterTypeDec :: EntityDef -> Dec
filterTypeDec t =
    DataInstD [] ''Filter [ConT $ eName t]
            (map mkFilter filts)
            (if null filts then [] else [''Show, ''Read, ''Eq])
  where
    filts = entityFilters t

data FilterD = FilterD { fName :: Name
                       , ffName :: String
                       , fType :: Type
                       , sfType :: String
                       , fEntityType :: Type
                       , fFilter :: PersistFilter
                       }
entityFilters :: EntityDef -> [FilterD]
entityFilters t = mapMaybe go' . concatMap go . entityColumns $ t
  where
    go (n, ty, fs) = map (\f -> (n, ty, nullable fs, f)) fs
    go' (n, ty, nu, sf) =
        case readMay sf of
            Nothing -> Nothing
            Just f ->
              let constr = mkName $ entityName t ++ upperFirst n ++ showFilter f
                  ty' = pairToType (ty, nu && isNullableFilter f)
                  ty'' = if isFilterList f then ListT `AppT` ty' else ty'
              in Just $ FilterD constr n ty'' ty (ConT $ eName t) f

isNullableFilter :: PersistFilter -> Bool
isNullableFilter Eq = True
isNullableFilter Ne = True
isNullableFilter In = True
isNullableFilter NotIn = True
isNullableFilter Lt = False
isNullableFilter Le = False
isNullableFilter Gt = False
isNullableFilter Ge = False
isNullableFilter Foreign = True

showFilter :: PersistFilter -> String
showFilter Foreign = ""
showFilter f = show f

readMay :: Read a => String -> Maybe a
readMay s =
    case reads s of
        (x, _):_ -> Just x
        [] -> Nothing

isFilterList :: PersistFilter -> Bool
isFilterList In = True
isFilterList NotIn = True
isFilterList _ = False

mkFilter :: FilterD -> Con
mkFilter FilterD {fName=constr, sfType=sty, fFilter=Foreign} =
    NormalC constr [(NotStrict, ConT ''Filter `AppT` ty)]
      where ty = unIdType sty
mkFilter FilterD {fName=constr, fType=ty} =
    NormalC constr [(NotStrict, ty)]

updateTypeDec :: EntityDef -> Dec
updateTypeDec t =
    DataInstD [] ''Update [ConT $ eName t]
        (map mkUpdate tu)
        (if null tu then [] else [''Show, ''Read, ''Eq])
  where
    tu = entityUpdates t

entityUpdates :: EntityDef -> [(Name, String, Type, Bool, PersistUpdate)]
entityUpdates t = mapMaybe go' . concatMap go . entityColumns $ t
  where
    go (n, ty, us) = 
      map (\u -> (n, ty, nullable us, u)) us
    go' (n, ty, isNull', "update") =
        deprecate "'update' is deprecated; please use 'Update'"
            $ go' (n, ty, isNull', "Update")
    go' (n, ty, isNull', u) =
        case readMay u of
            Nothing -> Nothing
            Just u' -> Just ( updateConName n u'
                            , n
                            , pairToType (ty, isNull')
                            , isNull'
                            , u'
                            )
    updateConName constr u = mkName $ concat
                                [ entityName t
                                , upperFirst constr
                                , case u of
                                  Update -> ""
                                  _ -> show u
                                ]

mkUpdate :: (Name, String, Type, Bool, PersistUpdate) -> Con
mkUpdate (constr, _, ty, _, _) =
    NormalC constr [(NotStrict, ty)]

orderTypeDec :: EntityDef -> Q Dec
orderTypeDec t = do
    let ords = entityOrders t
    return $ DataInstD [] ''Order [ConT $ eName t]
            (map mkOrder ords)
            (if null ords then [] else [''Show, ''Read, ''Eq])

data OrderD = OrderD { oName :: Name
                     , ooName :: String
                     , oEntityType :: Type
                     , oOrder :: PersistOrder
                     }
entityOrders :: EntityDef -> [OrderD]
entityOrders t = concat . map go . entityColumns $ t
  where
    go (n, _, os) = catMaybes $ map (go' n) os
    go' n o =
      case reads o of
        (y, _):_ -> Just $
          OrderD (mkName $ entityName t ++ upperFirst n ++ o)
                     n
                     (ConT $ eName t)
                     y
        _ -> Nothing

mkOrder :: OrderD -> Con
mkOrder OrderD {oName=constr} = NormalC constr []

uniqueTypeDec :: EntityDef -> Dec
uniqueTypeDec t =
    DataInstD [] ''Unique [ConT $ eName t]
            (map (mkUnique t) $ entityUniques t)
            (if null (entityUniques t) then [] else [''Show, ''Read, ''Eq])

mkUnique :: EntityDef -> (String, [String]) -> Con
mkUnique t (constr, fields) =
    NormalC (mkName constr) types
  where
    types = map (go . flip lookup3 (entityColumns t)) fields
    go (_, True) = error "Error: cannot have nullables in unique"
    go x = (NotStrict, pairToType x)
    lookup3 s [] =
        error $ "Column not found: " ++ s ++ " in unique " ++ constr
    lookup3 x ((x', y, z):rest)
        | x == x' = (y, nullable z)
        | otherwise = lookup3 x rest

pairToType :: (String, Bool) -> Type
pairToType (s, False) = ConT $ mkName s
pairToType (s, True) = ConT (mkName "Maybe") `AppT` ConT (mkName s)

degen :: [Clause] -> [Clause]
degen [] =
    let err = VarE (mkName "error") `AppE` LitE (StringL
                "Degenerate case, should never happen")
     in [Clause [WildP] (NormalB err) []]
degen x = x

mkFunc :: Name -> [Clause] -> Dec
mkFunc func clauses = FunD func $ degen $ nub clauses

mkToPersistFields :: [(Name, Int)] -> Q Dec
mkToPersistFields pairs = do
    clauses <- mapM go pairs
    return $ mkFunc (mkName "toPersistFields") clauses
  where
    go :: (Name, Int) -> Q Clause
    go (constr, fields) = do
        xs <- sequence $ replicate fields $ newName "x"
        let pat = ConP constr $ map VarP xs
        sp <- [|SomePersistField|]
        let bod = ListE $ map (AppE sp . VarE) xs
        return $ Clause [pat] (NormalB bod) []

mkToFieldNames :: [(String, [String])] -> Dec
mkToFieldNames pairs =
        mkFunc (mkName "persistUniqueToFieldNames") $ map go pairs
  where
    go (constr, names) =
        Clause [RecP (mkName constr) []]
               (NormalB $ ListE $ map (LitE . StringL) names)
               []

mkUpdateToUpdate = 
  mkToUpdate (mkName "persistUpdateToUpdate") . map go . entityUpdates
    where go (constr, _, _, _, u) = (constr, u)

mkToUpdate :: Name -> [(Name, PersistUpdate)] -> Q Dec
mkToUpdate func pairs = do
    pairs' <- mapM go pairs
    return $ mkFunc func pairs'
  where
    go (constr, pu) = do
        pu' <- lift pu
        return $ Clause [RecP constr []] (NormalB pu') []

mkUniqueToValues :: [(String, [String])] -> Q Dec
mkUniqueToValues pairs = do
    pairs' <- mapM go pairs
    return $ mkFunc (mkName "persistUniqueToValues") pairs'
  where
    go :: (String, [String]) -> Q Clause
    go (constr, names) = do
        xs <- mapM (const $ newName "x") names
        let pat = ConP (mkName constr) $ map VarP xs
        tpv <- [|toPersistValue|]
        let bod = ListE $ map (AppE tpv . VarE) xs
        return $ Clause [pat] (NormalB bod) []


mkFilterToField, mkFilterToFieldName, mkFilterToFilter, mkFilterToValue,
 mkFilterToJoins,
 mkUpdateToFieldName, mkUpdateToUpdate, mkUpdateToValue,
 mkOrderToField, mkOrderToFieldName, mkOrderToOrder
 :: EntityDef -> Q Dec

mkFilterToFieldName = mkFilterTo (mkName "persistFilterToFieldName") mkToFieldNameClause

mkUpdateToFieldName =
  mkUpdateTo (mkName "persistUpdateToFieldName") mkToFieldNameClause

mkOrderToFieldName = mkOrderTo (mkName "persistOrderToFieldName") mkToFieldNameClause

mkToFieldNameClause :: ToClause
mkToFieldNameClause (constr, name, _) =
  Clause [RecP constr []] (NormalB $ LitE $ StringL name) []


mkFilterToField = mkFilterTo (mkName "persistFilterToField") mkToFieldClause

mkOrderToField = mkOrderTo (mkName "persistOrderToField") mkToFieldClause

mkToFieldClause :: ToClause
mkToFieldClause (constr, name, table) =
  Clause [RecP constr []] (NormalB $ TupE [table', name']) []
    where table' = VarE (mkName "entityDef") `AppE` (VarE (mkName "undefined") `SigE` table)
          name' = LitE $ StringL name


mkFilterToValue = 
  mkFilterTo' (mkName "persistFilterToValue") (return . mkToFiltValueClause)

mkToFiltValueClause :: FilterD -> Clause
mkToFiltValueClause FilterD {fName=constr, fFilter=flt} =
  Clause [ConP constr [xP]]
         (NormalB $ body `AppE` xE)
         []
    where isList = isFilterList flt
          body = if isList then right else left
          left = InfixE (Just l) dot (Just tpv)
          right = InfixE (Just r) dot (Just (m `AppE` tpv))
          tpv = v "toPersistValue"
          dot = v "."
          m = v "map"
          l = ConE (mkName "Left")
          r = ConE (mkName "Right")
          v = VarE . mkName


mkFilterToJoins t = mapM go filters >>= return . mkFunc func
  where func = mkName "persistFilterToJoins"
        go = mkFilterToJoinsClause func
        filters = entityFilters t

mkFilterToJoinsClause :: Name -> FilterD -> Q Clause
mkFilterToJoinsClause func FilterD {fName=constr, ffName=name, sfType=joinedType, fEntityType=thisType, fFilter=Foreign} = do
  spe <- [|SomePersistEntity|]
  let body = InfixE (Just tuple) (ConE (mkName ":")) (Just call)
      tuple = TupE [ TupE [ spe `AppE` dummy thisType
                          , LitE $ StringL name]
                   , TupE [ spe `AppE` dummy (unIdType joinedType)
                          , LitE $ StringL "id"]]
      call = VarE func `AppE` xE
      dummy table = VarE (mkName "undefined") `SigE` table
  return $ 
    Clause [ConP constr [xP]]
           (NormalB $ body)
           []
mkFilterToJoinsClause _ FilterD {} =
  return $ Clause [WildP] (NormalB $ ListE []) []


mkFilterTo' 
  :: Name
  -> (FilterD -> Q Clause)
  -> EntityDef
  -> Q Dec
mkFilterTo' func clause t = do
  let filters = entityFilters t
      (ff, nf) = partition isForeign filters
      fc = map (mkForeignClause func) ff
  nc <- mapM clause nf
  let clauses = (fc ++ nc)
  return $ mkFunc func clauses
    where isForeign FilterD {fFilter=Foreign} = True
          isForeign _ = False
          

mkFilterTo :: Name -> ToClause -> EntityDef -> Q Dec
mkFilterTo name clause t = mkFilterTo' name clause' t
  where clause' FilterD {fName=constr, ffName=f, fEntityType=t} = 
          return $ clause (constr, f, t)


mkForeignClause :: Name -> FilterD -> Clause
mkForeignClause func FilterD {fName=constr} = 
  Clause [ConP constr [xP]] (NormalB $ VarE func `AppE` xE) []

mkUpdateTo :: Name -> ToClause -> EntityDef -> Q Dec
mkUpdateTo func clause = return . mkFunc func . map (clause . go) . entityUpdates
  where go (constr, name, _, _, _) = (constr, name, undefined)

mkOrderTo :: Name -> ToClause -> EntityDef -> Q Dec
mkOrderTo func clause = return . mkFunc func . map (clause . go) . entityOrders
  where go OrderD {oName=constr, ooName=name, oEntityType=t} = (constr, name, t)

mkFilterToFilter = mkFilterTo' (mkName "persistFilterToFilter") mkToFilterClause

mkToFilterClause :: FilterD -> Q Clause
mkToFilterClause FilterD {fName=constr, fFilter=f} = do
  f' <- lift f
  return $ Clause 
    [RecP constr []]
    (NormalB f')
    []
{-    go' (constr, _, False) =
        [Clause [RecP (mkName constr) []]
            (NormalB $ ConE $ mkName "False") []]
    go' (constr, _, True) =
        [ Clause [ConP (mkName constr) [ConP (mkName "Nothing") []]]
            (NormalB $ ConE $ mkName "True") []
        , Clause [ConP (mkName constr) [WildP]]
            (NormalB $ ConE $ mkName "False") []
        ] 
-}

mkOrderToOrder = mkToOrder (mkName "persistOrderToOrder") . map go . entityOrders
  where go OrderD {oName=constr, oOrder=o} = (constr, o)

mkToOrder :: Name -> [(Name, PersistOrder)] -> Q Dec
mkToOrder func ps = mapM go ps >>= return . mkFunc func
  where
    go (constr, val) = do
      val' <- lift val
      return $ Clause [RecP constr []] (NormalB val') []

mkUpdateToValue = return . mkToValue func . entityUpdateNames
  where func = mkName "persistUpdateToValue"
        entityUpdateNames = map (\(constr, _, _, _, _)-> constr) . entityUpdates

mkToValue :: Name -> [Name] -> Dec
mkToValue func = mkFunc func . map go
  where
    go constr =
         Clause [ConP constr [xP]]
                (NormalB $ VarE (mkName "toPersistValue") `AppE` xE)
                []

mkHalfDefined :: Name -> Int -> Dec
mkHalfDefined constr count' =
        FunD (mkName "halfDefined")
            [Clause [] (NormalB
            $ foldl AppE (ConE constr)
                    (replicate count' $ VarE $ mkName "undefined")) []]

apE :: Either x (y -> z) -> Either x y -> Either x z
apE (Left x) _ = Left x
apE _ (Left x) = Left x
apE (Right f) (Right y) = Right $ f y

mkFromPersistValues :: EntityDef -> Q [Clause]
mkFromPersistValues t = do
    nothing <- [|Left "Invalid fromPersistValues input"|]
    let cons = ConE $ eName t
    xs <- mapM (const $ newName "x") $ entityColumns t
    fs <- [|fromPersistValue|]
    let xs' = map (AppE fs . VarE) xs
    let pat = ListP $ map VarP xs
    ap' <- [|apE|]
    just <- [|Right|]
    let cons' = just `AppE` cons
    return
        [ Clause [pat] (NormalB $ foldl (go ap') cons' xs') []
        , Clause [WildP] (NormalB nothing) []
        ]
  where
    go ap' x y = InfixE (Just x) ap' (Just y)

mkEntity :: EntityDef -> Q [Dec]
mkEntity t = do
    t' <- lift t
    let name = eName t
    let clazz = ConT ''PersistEntity `AppT` ConT name
    ftfl <- mkFilterToFilter t
    tpf <- mkToPersistFields [(name, length $ entityColumns t)]
    fpv <- mkFromPersistValues t
    fromIntegral' <- [|fromIntegral|]
    uqtv <- mkUniqueToValues $ entityUniques t
    show' <- [|show|]
    otd <- orderTypeDec t
    puk <- mkUniqueKeys t
    otf <- mkOrderToField t
    otn <- mkOrderToFieldName t
    oto <- mkOrderToOrder t
    utf <- mkUpdateToFieldName t
    utv <- mkUpdateToValue t
    putu <- mkUpdateToUpdate t
    ftn <- mkFilterToFieldName t
    ftv <- mkFilterToValue t
    ftf <- mkFilterToField t
    ftn <- mkFilterToFieldName t
    ftv <- mkFilterToValue t
    ftj <- mkFilterToJoins t
    return
      [ dataTypeDec t
      , TySynD (mkName $ entityName t ++ "Id") [] $
            ConT ''Key `AppT` ConT name
      , InstanceD [] clazz $
        [ keyTypeDec (entityName t ++ "Id") ''Int64 t
        , filterTypeDec t
        , updateTypeDec t
        , otd
        , uniqueTypeDec t
        , FunD (mkName "entityDef") [Clause [WildP] (NormalB t') []]
        , ftfl
        , tpf
        , FunD (mkName "fromPersistValues") fpv
        , mkHalfDefined name $ length $ entityColumns t
        , FunD (mkName "toPersistKey") [Clause [] (NormalB fromIntegral') []]
        , FunD (mkName "fromPersistKey") [Clause [] (NormalB fromIntegral') []]
        , FunD (mkName "showPersistKey") [Clause [] (NormalB show') []]
        , otf
        , otn
        , oto
        , utf
        , utv
        , putu
        , ftf
        , ftn
        , ftv
        , ftj
        , mkToFieldNames $ entityUniques t
        , uqtv
        , puk
        ]
        ]

share :: [[EntityDef] -> Q [Dec]] -> [EntityDef] -> Q [Dec]
share fs x = fmap concat $ mapM ($ x) fs

share2 :: ([EntityDef] -> Q [Dec])
       -> ([EntityDef] -> Q [Dec])
       -> [EntityDef]
       -> Q [Dec]
share2 f g x = do
    y <- f x
    z <- g x
    return $ y ++ z

mkSave :: String -> [EntityDef] -> Q [Dec]
mkSave name' defs' = do
    let name = mkName name'
    defs <- lift defs'
    return [ SigD name $ ListT `AppT` ConT ''EntityDef
           , FunD name [Clause [] (NormalB defs) []]
           ]

data Dep = Dep
    { depTarget :: String
    , depSourceTable :: String
    , depSourceField :: String
    , depSourceNull :: Bool
    }

mkDeleteCascade :: [EntityDef] -> Q [Dec]
mkDeleteCascade defs = do
    let deps = concatMap getDeps defs
    mapM (go deps) defs
  where
    getDeps :: EntityDef -> [Dep]
    getDeps def =
        concatMap getDeps' $ entityColumns def
      where
        getDeps' (name, typ, attribs) =
            let isNull = nullable attribs
                l = length typ
                (f, b) = splitAt (l - 2) typ
             in if b == "Id"
                    then return Dep
                            { depTarget = f
                            , depSourceTable = entityName def
                            , depSourceField = name
                            , depSourceNull = isNull
                            }
                    else []
    go :: [Dep] -> EntityDef -> Q Dec
    go allDeps EntityDef{entityName = name} = do
        let deps = filter (\x -> depTarget x == name) allDeps
        key <- newName "key"
        del <- [|delete|]
        dcw <- [|deleteCascadeWhere|]
        just <- [|Just|]
        let mkStmt dep = NoBindS
                $ dcw `AppE`
                  ListE
                    [ ConE (mkName filtName) `AppE` val (depSourceNull dep)
                    ]
              where
                filtName =
                    depSourceTable dep ++ upperFirst (depSourceField dep)
                      ++ "Eq"
                val False = VarE key
                val True = just `AppE` VarE key



        let stmts = map mkStmt deps ++ [NoBindS $ del `AppE` VarE key]
        return $
            InstanceD
            []
            (ConT ''DeleteCascade `AppT` ConT (mkName name))
            [ FunD (mkName "deleteCascade")
                [Clause [VarP key] (NormalB $ DoE stmts) []]
            ]

mkUniqueKeys :: EntityDef -> Q Dec
mkUniqueKeys def = do
    c <- clause
    return $ FunD (mkName "persistUniqueKeys") [c]
  where
    clause = do
        xs <- forM (entityColumns def) $ \(x, _, _) -> do
            x' <- newName $ '_' : x
            return (x, x')
        let pcs = map (go xs) $ entityUniques def
        let pat = ConP (mkName $ entityName def) $ map (VarP . snd) xs
        return $ Clause [pat] (NormalB $ ListE pcs) []
    go xs (name, cols) =
        foldl (go' xs) (ConE (mkName name)) cols
    go' xs front col =
        let Just col' = lookup col xs
         in front `AppE` VarE col'

-- | Automatically creates a valid 'PersistField' instance for any datatype
-- that has valid 'Show' and 'Read' instances. Can be very convenient for
-- 'Enum' types.
derivePersistField :: String -> Q [Dec]
derivePersistField s = do
    ss <- [|SqlString|]
    tpv <- [|PersistString . show|]
    fpv <- [|\dt v ->
                case fromPersistValue v of
                    Left e -> Left e
                    Right s' ->
                        case reads s' of
                            (x, _):_ -> Right x
                            [] -> Left $ "Invalid " ++ dt ++ ": " ++ s'|]
    return
        [ InstanceD [] (ConT ''PersistField `AppT` ConT (mkName s))
            [ FunD (mkName "sqlType")
                [ Clause [WildP] (NormalB ss) []
                ]
            , FunD (mkName "toPersistValue")
                [ Clause [] (NormalB tpv) []
                ]
            , FunD (mkName "fromPersistValue")
                [ Clause [] (NormalB $ fpv `AppE` LitE (StringL s)) []
                ]
            ]
        ]

-- | Creates a single function to perform all migrations for the entities
-- defined here. One thing to be aware of is dependencies: if you have entities
-- with foreign references, make sure to place those definitions after the
-- entities they reference.
mkMigrate :: String -> [EntityDef] -> Q [Dec]
mkMigrate fun defs = do
    body' <- body
    return
        [ SigD (mkName fun) typ
        , FunD (mkName fun) [Clause [] (NormalB body') []]
        ]
  where
    typ = ForallT [PlainTV $ mkName "m"]
            [ ClassP ''MonadPeelIO [VarT $ mkName "m"]
            ]
            $ ConT ''Migration `AppT` (ConT ''SqlPersist `AppT` VarT (mkName "m"))
    body :: Q Exp
    body =
        case defs of
            [] -> [|return ()|]
            _ -> DoE `fmap` mapM toStmt defs
    toStmt :: EntityDef -> Q Stmt
    toStmt ed = do
        let n = entityName ed
        u <- [|undefined|]
        m <- [|migrate|]
        let u' = SigE u $ ConT $ mkName n
        return $ NoBindS $ m `AppE` u'

instance Lift EntityDef where
    lift (EntityDef a b c d e) = do
        x <- [|EntityDef|]
        a' <- lift a
        b' <- lift b
        c' <- lift c
        d' <- lift d
        e' <- lift e
        return $ x `AppE` a' `AppE` b' `AppE` c' `AppE` d' `AppE` e'

instance Lift PersistFilter where
    lift Eq = [|Eq|]
    lift Ne = [|Ne|]
    lift Gt = [|Gt|]
    lift Lt = [|Lt|]
    lift Ge = [|Ge|]
    lift Le = [|Le|]
    lift In = [|In|]
    lift NotIn = [|NotIn|]
    lift Foreign = [|Foreign|]

instance Lift PersistOrder where
    lift Asc = [|Asc|]
    lift Desc = [|Desc|]

instance Lift PersistUpdate where
    lift Update = [|Update|]
    lift Add = [|Add|]
    lift Subtract = [|Subtract|]
    lift Multiply = [|Multiply|]
    lift Divide = [|Divide|]

eName :: EntityDef -> Name
eName = mkName . entityName

xP :: Pat
xP = VarP (mkName "x")
xE :: Exp
xE = VarE (mkName "x")

unIdType :: String -> Type
unIdType s = ConT (mkName . reverse . drop 2 . reverse $ s)

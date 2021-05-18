module TH.Conversion where

import Conversion
import Language.Haskell.TH
import Language.Haskell.TH.Syntax as TH
import Data.List as L


someFunc :: IO ()
someFunc = putStrLn "someFunc"

mkConversionBy
  :: (String -> String)
  -- ^ to find corresponding constructor. Use `id` usually
  -> (String -> String -> String)
  -- ^ to find corresponding field for constructor. Use `const id` usually
  -> Name -> Name -> DecsQ
mkConversionBy fCons fFld from to = do
  TyConI tFrom <- reify from
  TyConI tTo <- reify to
  case (tFrom, tTo) of
    (DataD _ _ _ _ csFrom _, DataD _ _ _ _ csTo _) -> mkInstance csFrom csTo
    (DataD _ _ _ _ csFrom _, NewtypeD _ _ _ _ cTo _) -> mkInstance csFrom [cTo]
    (NewtypeD _ _ _ _ cFrom _, DataD _ _ _ _ csTo _) -> mkInstance [cFrom] csTo
    (NewtypeD _ _ _ _ cFrom _, NewtypeD _ _ _ _ cTo _) -> mkInstance [cFrom] [cTo]
    _ -> fail "mkConversionBy expects names of data or newtype in its params"
  where
    mkInstance csFrom csTo = do
      (VarE convertName) <- [|convert|]
      inst <- instanceD (pure []) [t|Conversion $(conT from) $(conT to)|]
        [ funD convertName
        $ zipWith (\cFrom -> mkConvClauseBy (fFld $ conToStr cFrom) cFrom) csFrom
        $ sortSndBy (fCons . conToStr) csFrom ((\c -> (conToStr c, c)) <$> csTo)
        ]
      pure [inst]

mkConvClauseBy :: (String -> String) -> Con -> Con -> ClauseQ
mkConvClauseBy fFld from to = [|convert|] >>= mkClauseQ
  where
    mkClauseQ convertE = case (from, to) of
      (NormalC cFrom btsFrom, NormalC cTo _) ->
        clauseByOrder cFrom cTo $ () <$ btsFrom
      (NormalC cFrom btsFrom, RecC cTo _) ->
        clauseByOrder cFrom cTo $ () <$ btsFrom
      (RecC cFrom vbtsFrom, NormalC cTo _) ->
        clauseByOrder cFrom cTo $ () <$ vbtsFrom
      (RecC cFrom vbtsFrom, RecC cTo vbtsTo) ->
        clauseByName cFrom cTo (getStr <$> vbtsFrom) (getStr <$> vbtsTo)
      _ -> fail "mkConvExpBy works only for regular constructors (NormalC, RecC)"
      where
        getStr (a,_,_) = nameToStr a
        clauseByOrder cFrom cTo units = do
          names <- traverse (\_ -> newName "x") units
          pure $ mkClause cFrom cTo names names
        clauseByName cFrom cTo namesFrom namesTo = do
          names <- traverse (\_ -> newName "x") namesFrom
          pure $ mkClause cFrom cTo names
            $ sortSndBy fFld namesFrom $ zip namesTo names
        mkClause cFrom cTo namesFrom namesTo =
          Clause [ConP cFrom $ VarP <$> namesFrom]
            (NormalB $ foldl'
              (\f v -> AppE f $ AppE convertE $ VarE v) (ConE cTo) namesTo)
            []

nameToStr :: Name -> String
nameToStr (Name (OccName s) _) = s

conToStr :: Con -> String
conToStr = \case
  NormalC n _ -> nameToStr n
  RecC n _ -> nameToStr n
  _ -> error "conToStr works only for regular constructors (NormalC, RecC)"

sortSndBy :: (Eq b, Show a) => (a -> b) -> [a] -> [(b, c)] -> [c]
sortSndBy f as bcs = foldr step [] as
  where
    step a cs = case find ((== f a) . fst) bcs of
      Just (_, c) -> c : cs
      Nothing -> error
        $ "not found corresponding value for " <> show a <> " in sortSndBy"

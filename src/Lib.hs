{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lib where

import Data.Maybe
import Control.Monad
import Data.Foldable
import Data.List
import Data.Set (Set)
import Control.Applicative
import Data.Hashable
import Data.Hashable.Lifted
import GHC.Generics (Generic,Generic1)
import Data.HashSet (HashSet)
import Data.Typeable (Typeable)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Classes
import Data.Monoid
import qualified Data.HashSet as HashSet
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Text.PrettyPrint.Annotated as P

data Exp a = ExpInt Int | ExpNeg a | ExpAdd a a
  deriving (Functor,Show)

cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . fmap (cata f) . unFix

data Ctx = Pos | Neg

invertCtx :: Ctx -> Ctx
invertCtx x = case x of
  Pos -> Neg
  Neg -> Pos

newtype FromTo a b = FromTo { apFromTo :: a -> b }
  deriving (Functor)

myExp :: Fix Exp
myExp = Fix $ ExpNeg $ Fix $ ExpAdd
  (Fix $ ExpInt 6)
  (Fix $ ExpNeg $ Fix $ ExpInt 4)

topDownNegationSimplify :: Fix Exp -> Fix Exp
topDownNegationSimplify = flip apFromTo Pos . simp

simp :: Fix Exp -> FromTo Ctx (Fix Exp)
simp = cata simplifyNegation2

simplifyNegation2 :: Exp (FromTo Ctx (Fix Exp)) -> FromTo Ctx (Fix Exp)
simplifyNegation2 x = case x of
  ExpInt i -> FromTo $ \ctx -> case ctx of
    Pos -> Fix $ ExpInt i
    Neg -> Fix $ ExpNeg (Fix $ ExpInt i)
  ExpNeg (FromTo f) -> FromTo $ f . invertCtx
  ExpAdd (FromTo f) (FromTo g) -> FromTo $ \c -> Fix $ ExpAdd (f c) (g c)

-- simplifyNegation :: Exp (Fix Exp) -> FromTo Ctx (Fix Exp)
-- simplifyNegation x = case x of
--   ExpInt i -> FromTo $ \ctx -> case ctx of
--     Pos -> Fix $ ExpInt i
--     Neg -> Fix $ ExpNeg (Fix $ ExpInt i)
--   ExpNeg e -> FromTo $ \ctx -> case ctx of
--     Pos -> Fix $ ExpNeg e
--     Neg -> e
--   ExpAdd a b -> FromTo $ \ctx -> case ctx of
--     Pos -> Fix $ ExpAdd a b
--     Neg -> Fix $ ExpAdd (Fix $ ExpNeg a) (Fix $ ExpNeg b)


data Value = ValueInt Int | ValueString String
  deriving (Eq,Ord,Show,Generic)

instance Hashable Value

data Atom = AtomInt | AtomString

newtype Column = Column { getColumn :: String }
  deriving (Eq,Ord,Show,Hashable)

newtype Fix f = Fix { unFix :: f (Fix f) }

deriving instance (Show (f (Fix f))) => Show (Fix f)
deriving instance (Eq (f (Fix f))) => Eq (Fix f)
deriving instance (Ord (f (Fix f))) => Ord (Fix f)

instance Hashable1 f => Hashable (Fix f) where
  hashWithSalt = let go s (Fix f) = liftHashWithSalt go s f in go

newtype Table = Table { getTable :: [(Column,[Value])] }
  deriving (Show,Eq,Hashable,Ord)

instance Hashable a => Hashable (Set a) where
  hashWithSalt = hashUsing Set.toList

data Base
  = BaseTable String Table
  | BaseHeaders (Set Column)
  | BaseZeroOne
  deriving (Eq,Show,Generic,Ord)

instance Hashable Base

data Pair a = Pair a a
  deriving (Functor,Eq,Ord,Show,Read,Foldable)

instance Eq1 Pair where
  liftEq f (Pair a b) (Pair c d) = f a c && f b d

data RelationF f a
  = RelationBinary BinaryOperation (f a)
  | RelationBase Base
  deriving (Show,Functor,Generic1,Generic)

instance (Eq1 f, Eq a) => Eq (RelationF f a) where (==) = eq1
instance (Ord1 f, Ord a) => Ord (RelationF f a) where compare = compare1

instance Eq1 f => Eq1 (RelationF f) where
  liftEq f (RelationBase a) (RelationBase b) = a == b
  liftEq _ (RelationBinary _ _) (RelationBase _) = False
  liftEq _ (RelationBase _) (RelationBinary _ _) = False
  liftEq f (RelationBinary opA a) (RelationBinary opB b) = opA == opB && liftEq f a b

instance Ord1 f => Ord1 (RelationF f) where
  liftCompare f (RelationBase a) (RelationBase b) = compare a b
  liftCompare _ (RelationBinary _ _) (RelationBase _) = GT
  liftCompare _ (RelationBase _) (RelationBinary _ _) = LT
  liftCompare f (RelationBinary opA a) (RelationBinary opB b) = compare opA opB <> liftCompare f a b

instance Hashable1 f => Hashable1 (RelationF f)

instance (Hashable1 f, Hashable a) => Hashable (RelationF f a) where
  hashWithSalt = hashWithSalt1

type Relation = RelationF Pair
type RelationAssociated = RelationF []

data BinaryOperation
  = NaturalJoin
  | InnerUnion
  deriving (Show,Eq,Generic,Ord)

instance Hashable BinaryOperation

data With a f b = With
  { withFirst :: a
  , withSecond :: (f b)
  } deriving (Functor,Eq)

data Size = SizeZero | SizeOther
  deriving (Eq)

baseCardinality :: Base -> Size
baseCardinality x = case x of
  BaseTable _ _ -> SizeOther
  BaseHeaders _ -> SizeZero
  BaseZeroOne -> SizeOther

relationCardinality :: Relation a -> Size
relationCardinality x = case x of
  RelationBinary _ _ -> SizeOther
  RelationBase b -> baseCardinality b

data Annotation = Annotation
  { annotationColumns :: Set Column
  , annotationHash :: Int
  }


--------------
-- Identities involving zeroes:
-- H00 & A = H(A)
-- H01 & A = A
-- H0X & A = H(A) -- headers without body
--
-- These ones are sort of worthless:
-- H0X | A = H0X- | A -- projection, we can reduce the headers in H0X
-- H00 | A = ... -- either H01 or H00, basically tests if cardinality(A) = 0
-- H01 | A = H01

applyZeroIdentities :: Fix (With (Set Column) Relation) -> Fix (With (Set Column) Relation)
applyZeroIdentities = cata applyZeroIdentitiesX

applyIdempotenceIdentities :: Fix Relation -> Fix (With Int Relation)
applyIdempotenceIdentities = cata applyIdempotenceIdentitiesX


-- This can be applied bottom-up. It is simple to write.
applyZeroIdentitiesX :: With (Set Column) Relation (Fix (With (Set Column) Relation)) -> Fix (With (Set Column) Relation)
applyZeroIdentitiesX original@(With ann x) = case x of
  RelationBase _ -> Fix original
  RelationBinary op (Pair a b) -> case op of
    NaturalJoin -> fromMaybe (Fix original)
      $ naturalJoinLeftIdentities a b <|> naturalJoinLeftIdentities b a
    InnerUnion -> Fix original -- fix this

-- drewmorphX :: (With a f (Fix (With a f)) -> Fix (With a f)) -> f (Fix (With a f)) -> Fix (With a f)

applyAbsorptionIdentities :: Fix (RelationF []) -> Fix (Compose Hashed (RelationF []))
applyAbsorptionIdentities = cata applyAbsorptionIdentitiesX

applyAbsorptionIdentitiesX ::
     RelationF [] (Fix (Compose Hashed (RelationF [])))
  -> Fix (Compose Hashed (RelationF []))
applyAbsorptionIdentitiesX x = case x of
  RelationBase _ -> Fix $ Compose $ hashed x
  RelationBinary op xs -> Fix $ Compose $ hashed
    $ RelationBinary op $ filter (\x -> not $ any (\y -> isAbsorbed op y x) xs) xs

-- The second relation is the one that would be absorbed.
isAbsorbed :: BinaryOperation
  -> Fix (Compose Hashed (RelationF []))
  -> Fix (Compose Hashed (RelationF []))
  -> Bool
isAbsorbed op a (Fix (Compose b)) = case unhashed b of
  RelationBase _ -> False
  RelationBinary opInner bs -> (op /= opInner) && (any (== a) bs)

-- The second relation set is the one that would be eliminated.
-- isAbsorbedHelp :: Hashed a -> [Hashed a] -> Bool
-- isAbsorbedHelp opHigh a opLow b = (Fix (Compose a)) ->

applyIdempotenceIdentitiesX :: Relation (Fix (With Int Relation)) -> Fix (With Int Relation)
applyIdempotenceIdentitiesX x = case x of
  RelationBase _ -> xWithHash
  RelationBinary _ (Pair (Fix (With hashA a)) (Fix (With hashB b))) -> if hashA == hashB && a == b
    then Fix (With hashA a)
    else xWithHash
  where
  xWithHash = Fix (With (determineHashX mySalt (fmap (withFirst . unFix) x)) x)

applyIdempotenceIdentitiesList :: Fix (RelationF []) -> Fix (Compose Hashed (RelationF []))
applyIdempotenceIdentitiesList = cata applyIdempotenceIdentitiesListX

applyIdempotenceIdentitiesListX ::
     RelationF [] (Fix (Compose Hashed (RelationF [])))
  -> Fix (Compose Hashed (RelationF []))
applyIdempotenceIdentitiesListX x = case x of
  RelationBase _ -> Fix $ Compose $ hashed x
  RelationBinary op xs -> Fix $ Compose $ hashed $ RelationBinary op
    $ List.sortBy (\(Fix (Compose a)) (Fix (Compose b)) -> fastHashedCompare a b)
    $ HashSet.toList $ HashSet.fromList xs

fastHashedCompare :: Ord a => Hashed a -> Hashed a -> Ordering
fastHashedCompare a b = compare (hash a) (hash b) <> compare (unhashed a) (unhashed b)

naturalJoinLeftIdentities :: Fix (With (Set Column) Relation) -> Fix (With (Set Column) Relation) -> Maybe (Fix (With (Set Column) Relation))
naturalJoinLeftIdentities a@(Fix (With colsA relA)) b@(Fix (With colsB relB)) = case relA of
  RelationBinary _ _ -> Nothing
  RelationBase base -> case base of
    BaseZeroOne -> Just b
    BaseHeaders _colsA ->
      let newCols = Set.union colsA colsB
       in Just $ Fix (With newCols $ RelationBase $ BaseHeaders newCols)
    BaseTable _ _ -> Nothing

associateOperations :: (Foldable f, Functor f) => Fix (RelationF f) -> Fix (RelationF [])
associateOperations = cata associateOperationsX

-- This can be used with either Pair or [] as f
associateOperationsX :: Foldable f => RelationF f (Fix (RelationF [])) -> Fix (RelationF [])
associateOperationsX x = case x of
  RelationBase t -> Fix (RelationBase t)
  RelationBinary op xs -> Fix (RelationBinary op (foldMap (expandAssociation op) xs))

expandAssociation :: BinaryOperation -> Fix (RelationF []) -> [Fix (RelationF [])]
expandAssociation target (Fix x) = case x of
  RelationBase _ -> [Fix x]
  RelationBinary found xs -> if found == target then xs else [Fix x]

annotateRelationX :: Relation (Fix (With Annotation Relation)) -> Fix (With Annotation Relation)
annotateRelationX x = error "write me"
  -- RelationBase base -> case base of
  --   BaseZeroOne -> Fix (With (Annotation Set.empty 0) x)
  --   BaseHeaders cols -> Fix (With (Annotation cols 1) x)
  --   BaseTable _ t -> Fix (With (Annotation $ Set.fromList $ columns t) x)
  -- RelationBinary op (Fix (With (Annotation colsA) _)) (Fix (With (Annotation colsB) _)) -> case op of
  --   NaturalJoin -> Fix (With (Annotation $ Set.union colsA colsB) x)
  --   InnerUnion -> Fix (With (Annotation $ Set.intersection colsA colsB) x)

determineHeaders :: Fix Relation -> Fix (With (Set Column) Relation)
determineHeaders = liftAnnotate determineHeadersX

determineHash :: Int -> Fix Relation -> Fix (With Int Relation)
determineHash s = liftAnnotate (determineHashX s)

determineHeadersX :: Relation (Set Column) -> Set Column
determineHeadersX x = case x of
  RelationBase base -> case base of
    BaseZeroOne -> Set.empty
    BaseHeaders cols -> cols
    BaseTable _ t -> Set.fromList $ columns t
  RelationBinary op (Pair colsA colsB) -> case op of
    NaturalJoin -> Set.union colsA colsB
    InnerUnion -> Set.intersection colsA colsB

determineHashX :: Int -> Relation Int -> Int
determineHashX s x = case x of
  RelationBase base -> case base of
    BaseZeroOne -> s `hashWithSalt` (0 :: Int)
    BaseHeaders cols -> s `hashWithSalt` (1 :: Int) `hashFoldableWithSalt` cols
    BaseTable name t -> s `hashWithSalt` (2 :: Int) `hashWithSalt` name `hashWithSalt` t
  RelationBinary op (Pair hashA hashB) -> case op of
    NaturalJoin -> s `hashWithSalt` (3 :: Int) `hashWithSalt` hashA `hashWithSalt` hashB
    InnerUnion -> s `hashWithSalt` (4 :: Int) `hashWithSalt` hashA `hashWithSalt` hashB

attr :: Fix (With a f) -> a
attr (Fix (With a _)) = a

annotate :: Functor f => (f a -> a) -> Fix f -> Fix (With a f)
annotate f = cata alg where
  -- alg :: f (Fix (With a f)) -> Fix (With a f)
  alg v = Fix (With (f (fmap attr v)) v)

liftAnnotate :: Functor f => (f a -> a) -> Fix f -> Fix (With a f)
liftAnnotate f v =
  let res = fmap (liftAnnotate f) . unFix $ v
      ann = f $ fmap (withFirst . unFix) res
   in Fix (With ann res)

-- drewmorph :: Functor f => (f (a,Fix f) -> (a,Fix f)) -> Fix f -> Fix (With a f)
-- drewmorph f = cata (drewmorphX f)

-- drewmorphX :: (With a f (Fix (With a f)) -> Fix (With a f)) -> f (Fix (With a f)) -> Fix (With a f)
-- drewmorphX f x = Fix $ fmap (f . unFix) x

-- attempt :: Functor f => (f a -> a) -> f (a,b) -> (a,b)
-- attempt f v = f (fmap fst v)

-- cata :: Functor f => (f a -> a) -> Fix f -> a
-- cata f = f . fmap (cata f) . unFix

-- cataHashSet :: (HashSet a -> a) -> Fix HashSet

annotateRelation :: Fix Relation -> Fix (With Annotation Relation)
annotateRelation = cata annotateRelationX

dropAnnotations :: Fix (With a Relation) -> Fix Relation
dropAnnotations = cata (\(With _ r) -> Fix r)

dropHashed :: Functor f => Fix (Compose Hashed f) -> Fix f
dropHashed = Fix . altMap dropHashed . unFix

altMap :: Functor f => (a -> b) -> Compose Hashed f a -> f b
altMap f (Compose h) = fmap f (unhashed h)

companyRelation :: Table
companyRelation = Table
  [ (Column "company_id", map ValueInt [1,2])
  , (Column "company_name", map ValueString ["Coca Cola","Sprite"])
  ]

employmentRelation :: Table
employmentRelation = Table
  [ (Column "company_id", map ValueInt [1,2,2])
  , (Column "person_id", map ValueInt [2,3,3])
  ]

personRelation :: Table
personRelation = Table
  [ (Column "person_id", map ValueInt [1,2,3,4])
  , (Column "name", map ValueString ["drew","luke","jake","josh"])
  , (Column "age", map ValueInt [25,23,21,19])
  ]

petRelation :: Table
petRelation = Table
  [ (Column "person_id", map ValueInt [2,2,2,3,3])
  , (Column "dog_name", map ValueString ["Fluff","Scruff","Spike","Scar","Mane"])
  ]

project :: [String] -> Fix Relation -> Fix Relation
project cols r = Fix $ RelationBinary InnerUnion $ Pair r
  (Fix $ RelationBase $ BaseHeaders (Set.fromList (map Column cols)))

h00 :: Fix Relation
h00 = Fix $ RelationBase $ BaseHeaders Set.empty

h01 :: Fix Relation
h01 = Fix $ RelationBase $ BaseZeroOne

optimizeRelation :: Fix Relation -> Fix (RelationF [])
optimizeRelation = id
  . dropHashed . applyAbsorptionIdentities
  . dropHashed . applyIdempotenceIdentitiesList
  . associateOperations
  . dropAnnotations . applyIdempotenceIdentities
  . dropAnnotations . applyZeroIdentities . determineHeaders

mySalt :: Int
mySalt = 24623463

runRelationX :: Relation Table -> Table
runRelationX x = case x of
  RelationBase b -> case b of
    BaseTable _ t -> t
    BaseZeroOne -> Table [] -- this is not currently correctly representable by Table
    BaseHeaders cols -> Table $ map (\c -> (c,[])) $ Set.toList cols
  RelationBinary b (Pair n m) -> case b of
    NaturalJoin -> joinTables n m
    InnerUnion -> unionTables n m

runRelation :: Fix Relation -> Table
runRelation = cata runRelationX

printRelation :: (Foldable f, Functor f) => Fix (RelationF f) -> IO ()
printRelation = putStrLn . P.render . prettyPrintRelation

prettyPrintRelation :: (Foldable f, Functor f) => Fix (RelationF f) -> P.Doc a
prettyPrintRelation = cata prettyPrintRelationX

prettyPrintRelationX :: Foldable f => RelationF f (P.Doc a) -> P.Doc a
prettyPrintRelationX x = case x of
  RelationBase b -> case b of
    BaseTable name _ -> P.text name
    BaseHeaders cols -> P.text $ ("headers: " ++) $ List.intercalate ", " $ map getColumn $ Set.toList cols
    BaseZeroOne -> P.text "H01"
  RelationBinary op xs ->
    (P.$$) (P.text $ opToString op) (P.nest 2 $ P.vcat $ toList xs) -- (P.nest 2 (a P.$$ b))

opToString :: BinaryOperation -> String
opToString x = case x of
  NaturalJoin -> "Natural Join"
  InnerUnion -> "Inner Union"

table :: String -> Table -> Fix Relation
table str = Fix . RelationBase . BaseTable str

person, pet, employment, company :: Fix Relation
person = table "person" personRelation
pet = table "pet" petRelation
employment = table "employment" employmentRelation
company = table "company" companyRelation

petsAtCompany :: Fix Relation
petsAtCompany =
  -- innerUnion pet $ naturalJoin pet $ naturalJoin person $ naturalJoin company $ naturalJoin h00 employment
  innerUnion pet $ naturalJoin pet $ naturalJoin person $ naturalJoin company $ naturalJoin employment employment

petsDoubled :: Fix Relation
petsDoubled =
  innerUnion pet $ naturalJoin pet $
    let e = naturalJoin person $ naturalJoin company employment
     in naturalJoin e (naturalJoin e person)


-- colsRelation :: Fix Relation -> Set Column
-- colsRelation

-- colsRelationX :: Relation (Set Column) -> Set Column
-- colsRelationX x = case x of


naturalJoin :: Fix Relation -> Fix Relation -> Fix Relation
naturalJoin a b = Fix $ RelationBinary NaturalJoin $ Pair a b

innerUnion :: Fix Relation -> Fix Relation -> Fix Relation
innerUnion a b = Fix $ RelationBinary InnerUnion $ Pair a b

joinTables :: Table -> Table -> Table
joinTables xs ys = uninjectColumns (Set.toList $ Set.union (Set.fromList $ columns xs) (Set.fromList $ columns ys)) $ do
  xvals <- injectColumns xs
  yvals <- injectColumns ys
  guard $ flip all xvals $ \(col,xval) -> case lookup col yvals of
    Nothing -> True
    Just yval -> xval == yval
  return $ xvals ++ yvals

unionTables :: Table -> Table -> Table
unionTables xs ys = uninjectColumns commonCols
  (nub $ map (filter $ \(c,v) -> elem c commonCols) $ injectColumns xs ++ injectColumns ys)
  where
  commonCols = Set.toList $ Set.intersection (Set.fromList $ columns xs) (Set.fromList $ columns ys)

-- xsSorted = List.sortBy (compare `on` fst) xs
-- ysSorted = List.sortBy (compare `on` fst) ys
-- commonColumns = map fst $ List.filter (\(c,_) -> isJust $ List.lookup c ysSorted) xsSorted
-- xsCommon = map snd $ List.filter (\(c,_) -> isJust $ List.lookup c ysSorted) xsSorted
-- ysCommon = map snd $ List.filter (\(c,_) -> isJust $ List.lookup c xsSorted) ysSorted
-- xsSet = Set.fromList (List.transpose xsCommon)
-- ysSet = Set.fromList (List.transpose ysCommon)
-- xsMatch = filter (Set.member . lookupMany commonColumns) xsSorted
-- ysMatch = filter (Set.member . lookupMany commonColumns) ysSorted

hashFoldableWithSalt :: (Foldable f, Hashable a) => Int -> f a -> Int
hashFoldableWithSalt s = foldl' hashWithSalt s

columns :: Table -> [Column]
columns (Table xs) = map fst xs

injectColumns :: Table -> [[(Column,Value)]]
injectColumns (Table xs) = transpose $ map (\(col,vals) -> map (\val -> (col,val)) vals) xs

-- this is partial
uninjectColumns :: [Column] -> [[(Column,Value)]] -> Table
uninjectColumns cols rows = go cols (Table []) where
  go [] t = t
  go (col:cnext) (Table res) = go cnext (Table $ (col, map (fromJust . lookup col) rows) : res)

lookupMany :: Eq a => [a] -> [(a,b)] -> [b]
lookupMany [] xs = []
lookupMany (a : as) xs = fromJust (lookup a xs) : lookupMany as xs


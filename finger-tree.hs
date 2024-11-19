{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}

import Data.Binary.Get (isEmpty)
import Data.Sequence ()
import Prelude hiding (Monoid, length, splitAt)

type Digit a = [a]

class Monoid v where
  (#) :: v
  (<+>) :: v -> v -> v

class (Monoid v) => Measured a v where
  measure :: a -> v

data Node v a = Node2 v a a | Node3 v a a a

node2 :: (Measured a v) => a -> a -> Node v a
node2 a b = Node2 (measure a <+> measure b) a b

node3 :: (Measured a v) => a -> a -> a -> Node v a
node3 a b c = Node3 (measure a <+> measure b <+> measure c) a b c

instance (Monoid v) => Measured (Node v a) v where
  measure (Node2 v _ _) = v
  measure (Node3 v _ _ _) = v

instance (Measured a v) => Measured (Digit a) v where
  measure xs = reducel (\v x -> v <+> measure x) (#) xs

instance (Measured a v) => Measured (FingerTree v a) v where
  measure Empty = (#)
  measure (Single x) = measure x
  measure (Deep v _ _ _) = v

data FingerTree v a
  = Empty
  | Single a
  | Deep v (Digit a) (FingerTree v (Node v a)) (Digit a)

deep :: (Measured a v) => Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deep pr m sf = Deep (measure pr <+> measure m <+> measure sf) pr m sf

infixr 5 <|

(<|) :: (Measured a v) => a -> FingerTree v a -> FingerTree v a
a <| Empty = Single a
a <| Single b = deep [a] Empty [b]
a <| Deep _ [b, c, d, e] m sf = deep [a, b] (node3 c d e <| m) sf
a <| Deep _ pr m sf = deep ([a] ++ pr) m sf

infixl 5 |>

(|>) :: (Measured a v) => FingerTree v a -> a -> FingerTree v a
Empty |> a = Single a
Single a |> b = deep [a] Empty [b]
Deep _ pr m [a, b, c, d] |> e = deep pr (m |> node3 a b c) [d, e]
Deep _ pr m sf |> a = deep pr m (sf ++ [a])

-- reduce

class Reduce f where
  reducer :: (a -> b -> b) -> f a -> b -> b
  reducel :: (b -> a -> b) -> b -> f a -> b

instance Reduce [] where
  reducer f xs z = foldr f z xs
  reducel f z xs = foldl f z xs

instance Reduce (Node v) where
  reducer f (Node2 v a b) z = f a (f b z)
  reducer f (Node3 v a b c) z = f a (f b (f c z))
  reducel f z (Node2 v a b) = f (f z a) b
  reducel f z (Node3 v a b c) = f (f (f z a) b) c

instance Reduce (FingerTree v) where
  reducer f Empty z = z
  reducer f (Single x) z = f x z
  reducer f (Deep _ pr m sf) z = f1 pr (f2 m (f1 sf z))
    where
      f1 = reducer f
      f2 = reducer (reducer f)
  reducel f z Empty = z
  reducel f z (Single x) = f z x
  reducel f z (Deep _ pr m sf) = f1 (f2 (f1 z pr) m) sf
    where
      f1 = reducel f
      f2 = reducel (reducel f)

toList :: (Reduce f) => f a -> [a]
toList s = reducer (:) s []

toTree :: (Reduce f, Measured a v) => f a -> FingerTree v a
toTree s = reducer (<|) s Empty

-- lift |> and <|

infixr 5 <<|

(<<|) :: (Reduce f, Measured a v) => f a -> FingerTree v a -> FingerTree v a
(<<|) = reducer (<|)

infixl 5 |>>

(|>>) :: (Reduce f, Measured a v) => FingerTree v a -> f a -> FingerTree v a
(|>>) = reducel (|>)

-- view from left
data ViewL s a = NilL | ConsL a (s a)

viewL :: (Measured a v) => FingerTree v a -> ViewL (FingerTree v) a
viewL Empty = NilL
viewL (Single x) = ConsL x Empty
viewL (Deep _ (p : pf) m sf) = ConsL p (deepL pf m sf)

deepL :: (Measured a v) => [a] -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deepL [] m sf = case viewL m of
  NilL -> toTree sf
  ConsL a m' -> deep (toList a) m' sf
deepL pr m sf = deep pr m sf

-- view from right
data ViewR s a = NilR | ConsR (s a) a

viewR :: (Measured a v) => FingerTree v a -> ViewR (FingerTree v) a
viewR Empty = NilR
viewR (Single x) = ConsR Empty x
viewR (Deep _ pr m sf) = ConsR (deepR pr m (init sf)) (last sf)

deepR :: (Measured a v) => Digit a -> FingerTree v (Node v a) -> [a] -> FingerTree v a
deepR pr m [] = case viewR m of
  NilR -> toTree pr
  ConsR m' a -> deep pr m' (toList a)
deepR pr m sf = deep pr m sf

isEmpty :: (Measured a v) => FingerTree v a -> Bool
isEmpty x = case viewL x of
  NilL -> True
  ConsL _ _ -> False

headL :: (Measured a v) => FingerTree v a -> a
headL x = case viewL x of
  ConsL a _ -> a

tailL :: (Measured a v) => FingerTree v a -> FingerTree v a
tailL x = case viewL x of
  ConsL _ s -> s

headR :: (Measured a v) => FingerTree v a -> a
headR x = case viewR x of
  ConsR _ a -> a

tailR :: (Measured a v) => FingerTree v a -> FingerTree v a
tailR x = case viewR x of
  ConsR s _ -> s

-- concat two trees

app3 :: (Measured a v) => FingerTree v a -> [a] -> FingerTree v a -> FingerTree v a
app3 Empty ts xs = ts <<| xs
app3 xs ts Empty = xs |>> ts
app3 (Single x) ts xs = x <| ts <<| xs
app3 xs ts (Single x) = xs |>> ts |> x
app3 (Deep _ pr1 m1 sf1) ts (Deep _ pr2 m2 sf2) =
  deep pr1 (app3 m1 (nodes (sf1 ++ ts ++ pr2)) m2) sf2

nodes :: (Measured a v) => [a] -> [Node v a]
nodes [a, b] = [node2 a b]
nodes [a, b, c] = [node3 a b c]
nodes [a, b, c, d] = [node2 a b, node2 c d]
nodes (a : b : c : xs) = node3 a b c : nodes xs

(|><|) :: (Measured a v) => FingerTree v a -> FingerTree v a -> FingerTree v a
t1 |><| t2 = app3 t1 [] t2

-- split
data Split f a = Split (f a) a (f a)

splitDigit :: (Measured a v) => (v -> Bool) -> v -> Digit a -> Split [] a
splitDigit p i [a] = Split [] a []
splitDigit p i (a : as)
  | p i' = Split [] a as
  | otherwise = let Split l x r = splitDigit p i' as in Split (a : l) x r
  where
    i' = i <+> measure a

-- valid only for non-empty tree
splitTree :: (Measured a v) => (v -> Bool) -> v -> FingerTree v a -> Split (FingerTree v) a
splitTree p i (Single x) = Split Empty x Empty
splitTree p i (Deep _ pr m sf)
  | p vpr =
      let Split l x r = splitDigit p i pr
       in Split (toTree l) x (deepL r m sf)
  | p vm =
      let Split ml xs mr = splitTree p vpr m
          Split l x r = splitDigit p (vpr <+> measure ml) (toList xs)
       in Split (deepR pr ml l) x (deepL r mr sf)
  | otherwise =
      let Split l x r = splitDigit p vm sf
       in Split (deepR pr m l) x (toTree r)
  where
    vpr = i <+> measure pr
    vm = vpr <+> measure m

split :: (Measured a v) => (v -> Bool) -> FingerTree v a -> (FingerTree v a, FingerTree v a)
split p Empty = (Empty, Empty)
split p xs
  | p (measure xs) = (l, x <| r)
  | otherwise = (xs, Empty)
  where
    Split l x r = splitTree p (#) xs

takeUntil :: (Measured a v) => (v -> Bool) -> FingerTree v a -> FingerTree v a
takeUntil p = fst . split p

dropUntil :: (Measured a v) => (v -> Bool) -> FingerTree v a -> FingerTree v a
dropUntil p = snd . split p

lookupTree :: (Measured a v) => (v -> Bool) -> v -> FingerTree v a -> (v, a)
lookupTree p i t = (i <+> measure l, x)
  where
    Split l x r = splitTree p i t

-- random access

newtype Size = Size {getSize :: Int} deriving (Eq, Ord, Show)

-- N as a monoid
instance Monoid Size where
  (#) = Size 0
  Size x <+> Size y = Size (x + y)

newtype Elem a = Elem {getElem :: a} deriving (Eq, Ord)

newtype Seq a = Seq (FingerTree Size (Elem a))

instance (Show a) => Show (Elem a) where
  show (Elem x) = show x

instance (Show a) => Show (Seq a) where
  show (Seq xs) = show (toList xs)

instance (Measured (Elem a) Size) where
  measure (Elem _) = Size 1

length :: Seq a -> Int
length (Seq xs) = getSize (measure xs)

splitAt :: Int -> Seq a -> (Seq a, Seq a)
splitAt i (Seq xs) = (Seq l, Seq r)
  where
    (l, r) = split (Size i <) xs

(!) :: Seq a -> Int -> a
Seq xs ! i = getElem x
  where
    Split _ x _ = splitTree (Size i <) (#) xs

-- max-heap

-- max as a monoid, -inf as identity
data Prio a = MInfty | Prio a deriving (Eq, Ord, Show)

instance (Ord a) => Monoid (Prio a) where
  (#) = MInfty
  MInfty <+> x = x
  x <+> MInfty = x
  Prio x <+> Prio y = Prio (max x y)

newtype PQueue a = PQueue (FingerTree (Prio a) (Elem a))

instance (Ord a) => Measured (Elem a) (Prio a) where
  measure (Elem x) = Prio x

extractMax :: (Ord a) => PQueue a -> (a, PQueue a)
extractMax (PQueue xs) = (x, PQueue (l |><| r))
  where
    Split l (Elem x) r = splitTree (measure xs <=) (#) xs

-- ordered sequence
data Key a = NoKey | Key a deriving (Eq, Ord)

instance Monoid (Key a) where
  (#) = NoKey
  k <+> NoKey = k
  _ <+> k = k

newtype OrdSeq a = OrdSeq (FingerTree (Key a) (Elem a))

instance (Show a) => Show (OrdSeq a) where
  show (OrdSeq xs) = show (toList xs)

instance Measured (Elem a) (Key a) where
  measure (Elem x) = Key x

partition :: (Ord a) => a -> OrdSeq a -> (OrdSeq a, OrdSeq a)
partition k (OrdSeq xs) = (OrdSeq l, OrdSeq r)
  where
    (l, r) = split (>= Key k) xs

insert :: (Ord a) => a -> OrdSeq a -> OrdSeq a
insert k (OrdSeq xs) = OrdSeq ((l |> Elem k) |><| r)
  where
    (l, r) = split (>= Key k) xs

deleteAll :: (Ord a) => a -> OrdSeq a -> OrdSeq a
deleteAll x (OrdSeq xs) = OrdSeq (l1 |><| r2)
  where
    (l1, r1) = split (>= Key x) xs
    (l2, r2) = split (> Key x) r1

merge :: (Ord a) => OrdSeq a -> OrdSeq a -> OrdSeq a
merge (OrdSeq xs) (OrdSeq ys) = OrdSeq (merge' xs ys)
  where
    merge' xs ys = case viewL ys of
      NilL -> xs
      ConsL y ys' -> l |><| (y <| merge' ys' r)
        where
          (l, r) = split (> measure y) xs

-- test OrdSeq

testOrdSeq :: IO ()
testOrdSeq = do
  let xs = OrdSeq $ toTree [Elem 1, Elem 2, Elem 3, Elem 4, Elem 6]
  print xs
  let (l, r) = partition 3 xs
  print l
  print r
  let xs2 = insert 5 xs
  let xs3 = insert 5 xs2
  print xs3
  let xs4 = deleteAll 3 xs3
  print xs4
  let xs5 = deleteAll 5 xs4
  print xs5
  let xs6 = deleteAll 2 xs5
  print xs6
  let xs7 = deleteAll 1 xs6
  print xs7
  let xs8 = deleteAll 6 xs7
  print xs8
  let xs9 = deleteAll 4 xs8
  print xs9
  let ys = OrdSeq $ toTree [Elem 1, Elem 1, Elem 4, Elem 5, Elem 14]
  print $ merge xs ys

testSeq :: IO ()
testSeq = do
  let xs = Seq $ toTree [Elem 1, Elem 2, Elem 3, Elem 4, Elem 5]
  print $ length xs
  print (xs ! 2)
  let (l, r) = splitAt 2 xs
  print l
  print r
  print 1

main :: IO ()
main = do
  testOrdSeq

-- testSeq

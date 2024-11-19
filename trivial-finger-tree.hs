-- lift binary function to a reduce function
class Reduce f where
    reducer :: (a -> b -> b) -> f a -> b -> b
    reducel :: (b -> a -> b) -> b -> f a -> b

instance Reduce [] where
    reducer f xs z = foldr f z xs
    reducel f z xs = foldl f z xs

toList :: (Reduce f) => f a -> [a]
toList s = reducer (:) s []

-- 2-3 tree
data Tree a = Zero a | Succ (Tree (Node a))

data Node a = Node2 a a | Node3 a a a

data FingerTree a
    = Empty
    | Single a
    | Deep (Digit a) (FingerTree (Node a)) (Digit a)

type Digit = []

instance Reduce Node where
    reducer f (Node2 a b) z = f a (f b z)
    reducer f (Node3 a b c) z = f a (f b (f c z))
    reducel f z (Node2 a b) = f (f z a) b
    reducel f z (Node3 a b c) = f (f (f z a) b) c

instance Reduce FingerTree where
    reducer f Empty z = z
    reducer f (Single x) z = f x z
    reducer f (Deep pr m sf) z = f1 pr (f2 m (f1 sf z))
        where
        f1 = reducer f
        f2 = reducer (reducer f)
    reducel f z Empty = z
    reducel f z (Single x) = f z x
    reducel f z (Deep pr m sf) = f1 (f2 (f1 z pr) m) sf
        where
        f1 = reducel f
        f2 = reducel (reducel f)

infixr 5 <|

(<|) :: a -> FingerTree a -> FingerTree a
a <| Empty = Single a
a <| Single b = Deep [a] Empty [b]
a <| Deep [b, c, d, e] m sf = Deep [a, b] (Node3 c d e <| m) sf
a <| Deep pr m sf = Deep ([a] ++ pr) m sf

infixl 5 |>

(|>) :: FingerTree a -> a -> FingerTree a
Empty |> a = Single a
Single a |> b = Deep [a] Empty [b]
Deep pr m [a, b, c, d] |> e = Deep pr (m |> Node3 a b c) [d, e]
Deep pr m sf |> a = Deep pr m (sf ++ [a])

-- lift |> and <|
infixr 5 <<|

(<<|) :: (Reduce f) => f a -> FingerTree a -> FingerTree a
(<<|) = reducer (<|)

infixl 5 |>>

(|>>) :: (Reduce f) => FingerTree a -> f a -> FingerTree a
(|>>) = reducel (|>)

toTree :: (Reduce f) => f a -> FingerTree a
toTree s = s <<| Empty

-- view from left
data ViewL s a = NilL | ConsL a (s a)

viewL :: FingerTree a -> ViewL FingerTree a
viewL Empty = NilL
viewL (Single x) = ConsL x Empty
viewL (Deep pr m sf) = ConsL (head pr) (deepL (tail pr) m sf)

deepL :: [a] -> FingerTree (Node a) -> Digit a -> FingerTree a
deepL [] m sf = case viewL m of
    NilL -> toTree sf
    ConsL a m' -> Deep (toList a) m' sf
deepL pr m sf = Deep pr m sf

isEmpty :: FingerTree a -> Bool
isEmpty x = case viewL x of
    NilL -> True
    ConsL _ _ -> False

headL :: FingerTree a -> a
headL x = case viewL x of
    NilL -> error "empty"
    ConsL a _ -> a

tailL :: FingerTree a -> FingerTree a
tailL x = case viewL x of
    NilL -> error "empty"
    ConsL _ s -> s

-- view from right
data ViewR s a = NilR | ConsR (s a) a

viewR :: FingerTree a -> ViewR FingerTree a
viewR Empty = NilR
viewR (Single x) = ConsR Empty x
viewR (Deep pr m sf) = ConsR (deepR pr m (tail sf)) (last sf)

deepR :: Digit a -> FingerTree (Node a) -> [a] -> FingerTree a
deepR pr m [] = case viewR m of
    NilR -> toTree pr
    ConsR m' a -> Deep pr m' (toList a)
deepR pr m sf = Deep pr m sf

headR :: FingerTree a -> a
headR x = case viewR x of
    NilR -> error "empty"
    ConsR _ a -> a

tailR :: FingerTree a -> FingerTree a
tailR x = case viewR x of
    NilR -> error "empty"
    ConsR s _ -> s

-- build middle tree from two trees
app3 :: FingerTree a -> [a] -> FingerTree a -> FingerTree a
app3 Empty ts xs = ts <<| xs
app3 xs ts Empty = xs |>> ts
app3 (Single x) ts xs = x <| (ts <<| xs)
app3 xs ts (Single x) = (xs |>> ts) |> x
app3 (Deep pr1 m1 sf1) ts (Deep pr2 m2 sf2) =
    Deep pr1 (app3 m1 (nodes (sf1 ++ ts ++ pr2)) m2) sf2

nodes :: [a] -> [Node a]
nodes [a, b] = [Node2 a b]
nodes [a, b, c] = [Node3 a b c]
nodes [a, b, c, d] = [Node2 a b, Node2 c d]
nodes (a : b : c : xs) = Node3 a b c : nodes xs

-- concat two trees
(|><|) :: FingerTree a -> FingerTree a -> FingerTree a
xs |><| ys = app3 xs [] ys

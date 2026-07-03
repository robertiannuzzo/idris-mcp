module Data.List.IxMonad

import Data.List.Quantifiers

import Proofs

import Syntax.PreorderReasoning
import Data.Iso

%hide All.splitAt

%unbound_implicits off


-- lemma about bimap
bimapFst : {0 a, a', b, b' : Type} ->
           (x : Pair a b) -> (f : a -> a') -> (g : b -> b') ->
           fst (bimap f g x) === f (fst x)
bimapFst (x, y) f g = Refl

-- lemma about bimap
bimapSnd : {0 a, a', b, b' : Type} ->
           (x : Pair a b) -> (f : a -> a') -> (g : b -> b') ->
           snd (bimap f g x) === g (snd x)
bimapSnd (x, y) f g = Refl

parameters {0 a : Type}
 -- Joining two lists
 listJoin : List (List a) -> List a
 listJoin [] = []
 listJoin (x :: xs) = x ++ listJoin xs

 mayCons : Maybe a -> Maybe (List a) -> Maybe (List a)
 mayCons Nothing xs = Nothing
 mayCons (Just x) (xs) = map (x ::) xs

 distrib : List (Maybe a) -> Maybe (List a)
 distrib [] = Just []
 distrib (x :: xs) = mayCons x (distrib xs)

 parameters {0 p : a -> Type}
  -- If we have an `All` predicate from two lists, we can split them appart into two predicates
  splitAll : {0 ys : List a} -> (xs : List a) -> All p (xs ++ ys) -> (All p xs, All p ys)
  splitAll [] pxs = ([], pxs)
  splitAll (_ :: xs) (px :: pxs) = mapFst (px ::) (splitAll xs pxs)

  -- If we have evidence that all the elements of a nested list hold the predicate, then we can
  -- reconstruct the nesting
  unJoin : (xs : List (List a)) -> All p (listJoin xs) -> All (All p) xs
  unJoin [] x = []
  unJoin (y :: xs) x = let
      ss : (All p y, All p (listJoin xs))
      ss = splitAll y x
      in fst ss :: unJoin xs (snd ss)

  -- If we have evidence that all the nested elements of a list hold a predicate
  -- then we can flatten the nested predicates
  reJoin : (xs : List (List a)) -> All (All p) xs -> All p (listJoin xs)
  reJoin [] x = []
  reJoin (x :: xs) (y :: ys) = y ++ reJoin xs ys

  -- View to compute the split of a concatenated list of predicates
  data SplitView :
    (x : List a) ->
    (xs : List (List a)) ->
    (ys : All p (x ++ listJoin xs)) -> Type where

    SplitList : (x : List a) -> (xs : List (List a)) ->
                (y : All p x) -> (ys : All p (listJoin xs)) ->
                SplitView x xs (y ++ ys)

  -- lemma about split
  splitPrefix : (x, xs : List a) ->
                (y : All p x) ->
                (ys : All p xs) ->
                fst (splitAll x {ys = xs} (y ++ ys)) = y
  splitPrefix [] xs [] ys = Refl
  splitPrefix (x :: xs) ws (y :: ys) zs =
    let rec = splitPrefix xs ws ys zs
    in trans (bimapFst (splitAll xs (ys ++ zs)) (y ::) id) (cong (y ::) rec)

  -- lemma about split
  splitPostfix : (x, xs : List a) ->
                (y : All p x) ->
                (ys : All p xs) ->
                snd (splitAll x {ys = xs} (y ++ ys)) = ys
  splitPostfix [] xs [] ys = Refl
  splitPostfix (x :: zs) xs (y :: z) ys = trans (bimapSnd {}) (splitPostfix zs xs z ys)

  -- lemma about split
  splitConcat :
     (x, xs : List a) ->
     (ys : All p (x ++ xs)) ->
     (fst (splitAll {ys = xs} x ys) ++ snd (splitAll {ys = xs} x ys)) === ys
  splitConcat [] xs ys = Refl
  splitConcat (x :: xs) zs (y :: ys)
    = let rec = splitConcat xs zs ys
      in Calc $
      |~ fst (bimap (\arg => y :: arg) id (splitAll xs ys)) ++ snd (bimap (y ::) id (splitAll xs ys))
      ~~ (y :: fst (splitAll xs ys)) ++ snd (bimap (y ::) id (splitAll xs ys))
          ...(congDep (++ snd (bimap (y ::) id (splitAll xs ys))) (bimapFst (splitAll xs ys) (y ::) Prelude.id))
      ~~ (y :: fst (splitAll xs ys)) ++ snd (splitAll xs ys) ...(cong ((y :: fst (splitAll xs ys)) ++) (bimapSnd (splitAll xs ys) (y::) Prelude.id))
      ~= (y :: fst (splitAll xs ys) ++ snd (splitAll xs ys))
      ~~ (y :: ys) ...(cong (y::) rec)

  -- computing the view
  splitView : (x : List a) -> (xs : List (List a)) -> (ys : All p (x ++ listJoin xs)) ->
              SplitView x xs ys
  splitView x xs ys = let
    gg = SplitList x xs (fst $ splitAll x ys) (snd $ splitAll x ys)
    in replace {p = SplitView x xs} (splitConcat {}) gg

  -- undoing a join and redoing it is like doing nothing
  unrejoin : (xs : List (List a)) -> (ys : All p (listJoin xs)) ->
             reJoin xs (unJoin xs ys) === ys
  unrejoin [] [] = Refl
  unrejoin (x :: xs) ys with (splitView x xs ys) proof pp
    unrejoin (x :: xs) (y ++ ys) | (SplitList x xs y ys)
      = cong2Dep All.(++) (splitPrefix {})
      $ let ff = unrejoin xs ys
            qq = (cong (reJoin xs . unJoin xs) (splitPostfix x (listJoin xs) y ys))
      in trans qq ff

  -- redoing a join and undoing it is like doing nothing
  reunjoin : (xs : List (List a)) -> (ys : All (All p) xs) ->
             unJoin xs (reJoin xs ys) === ys
  reunjoin [] [] = Refl
  reunjoin (x :: xs) (y :: ys)
    = cong2Dep (::) (splitPrefix {}) (trans (cong (unJoin xs) (splitPostfix {})) (reunjoin xs ys))

  joinAllIso : (xs : List (List a)) -> All p (listJoin xs) ≅ All (All p) xs
  joinAllIso xs = MkIso
    (unJoin xs)
    (reJoin xs)
    (reunjoin xs)
    (unrejoin xs)

  pureIso : (x : a) -> All p [x] ≅ p x
  pureIso x = MkIso
      head
      (\y => [y])
      (\y => Refl)
      (\([y]) => Refl)


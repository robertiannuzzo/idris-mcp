module Data.Container.ListMaybe


import Data.Container
import Data.Container.Descriptions.List
import Data.Container.Maybe.Functor
import Data.Container.Maybe.Monad
import Data.Container.List.Functor
import Data.Container.List.Monad
import Data.Container.Distrib
import Data.Container.Morphism
import Data.Distributive
import Data.List
import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation

-- lemmas about list and maybe
maybeJustEq : {0 x, y : a} -> Prelude.Just x === Prelude.Just y -> x === y
maybeJustEq Refl = Refl

listConsEq : {0 x : a} -> {0 xs : List a} -> x :: xs === y :: ys -> (x === y, xs === ys)
listConsEq Refl = (Refl, Refl)

mapEmpty : {0 xs : List a} -> xs === [] -> map f xs === []
mapEmpty Refl = Refl

mapCons : {0 xs, ys : List a} -> {0 f : a -> b} ->
          xs === (y :: ys) -> map f xs === f y :: map f ys
mapCons Refl = Refl

-- list and maybe distribute

listMaybeDist : List (Maybe a) -> Maybe (List a)
listMaybeDist [] = Just []
listMaybeDist (x :: xs) = (::) <$> x <*> listMaybeDist xs

distribEmpty : {ll : List (Maybe a)} -> Just [] = listMaybeDist ll -> ll === []
distribEmpty {ll = []} prf = Refl
distribEmpty {ll = Nothing :: xs} Refl impossible
distribEmpty {ll = Just x :: xs} prf with (listMaybeDist xs)
  distribEmpty {ll = Just x :: xs} Refl | Nothing impossible
  distribEmpty {ll = Just x :: xs} prf | (Just y) = let xx = maybeJustEq prf in absurd xx

distribCons : {ll : List (Maybe a)} ->
              (p : Just (y :: ys) = listMaybeDist ll) ->
              ll === (Just y :: map Just ys)
distribCons {ll = []} Refl impossible
distribCons {ll = Types.Nothing :: xs} Refl impossible
distribCons {ll = Just x :: xs} {ys} p with (listMaybeDist xs) proof px
  distribCons {ll = Just x :: xs} {ys} Refl | Types.Nothing impossible
  distribCons {ll = Just x :: xs} {ys} p | (Just [])
    = let x1 = distribEmpty (sym px)
          py = (listConsEq (maybeJustEq p))
          pq = sym $ mapEmpty (snd py)
      in cong2 (::)
          (sym $ cong Just (fst py))
          (trans x1 pq)
  distribCons {ll = Just x :: xs} {ys}  pp | (Just (z1 :: z2))
    = let recc = distribCons (sym px)
          m1 = maybeJustEq pp
          (c1, c2) = listConsEq m1
          cx = mapCons c2
      in cong2 (::) (cong Just (sym c1)) (trans recc (sym cx))

distribJust : {ys : List a} -> Just ys = listMaybeDist (map Just ys)
distribJust {ys = []} = Refl
distribJust {ys = (x :: xs)} with (distribJust {ys = xs})
  distribJust {ys = (x :: xs)} | prf = rewrite sym prf in Refl

bwd : {0 a : Container} ->
      (xs : Maybe (List a.request)) ->
      (ys : List (Maybe a.request)) ->
      (xs === listMaybeDist ys) ->
      Any (All a.response) xs ->
      All (Any a.response) ys
bwd Nothing _ p x = absurd x
bwd (Just []) ll p (Aye x) = replace {p = All (Any a.response)} (sym $ distribEmpty p) []
bwd (Just (y :: ys)) ll p (Aye x) with (distribCons p)
  bwd (Just (y :: ys)) ll p (Aye (x1 :: x2)) | px
    = rewrite__impl (All (Any a.response)) px
      (Aye x1 :: (assert_total $ ListMaybe.bwd (Just ys) (map Just ys) (distribJust {ys}) (Aye x2)))

distribListMaybe :
    All.List (Any.Maybe a) =%> Any.Maybe (All.List a)
distribListMaybe = listMaybeDist <! \xs, ys => ListMaybe.bwd (listMaybeDist xs) xs Refl ys


{-
ListMaybeContDistrib : ContDistrib ?MaybeMonad Any.MaybeMonad
ListMaybeContDistrib = MkDistribProofCont
  ?dist
  ?natu
  ?pant1
  ?patn2
  ?tri1
  ?tri2

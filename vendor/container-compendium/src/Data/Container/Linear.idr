module Data.Container.Linear

import Data.Distributive

import Data.Container
import Data.Container.Extension
import Data.Container.ForallSeq
import Data.Container.Sequence
import Data.Container.Descriptions.Maybe
import Data.Container.Descriptions.List

import Data.Category
import Data.Category.Functor
import Data.Category.Monad
import Data.Category.NaturalTransformation
import Data.Category.Endofunctor

import Data.ListMaybe
import Data.List.Quantifiers
import Data.List
import Data.Maybe
import Data.Sigma
import Control.Function

import Data.Iso
import Data.Distributive
import Data.Maybe
import Data.Maybe.Any
import Data.List
import Data.List.Quantifiers as QL
import Data.List.Monad
import Data.Sigma

import Data.Category
import Data.Category.Action
import Data.Category.Bifunctor
import Data.Category.Functor
import Data.Category.Monad
import Data.Category.MonadAction
import Data.Category.Monoid
import Data.Category.NaturalTransformation

import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Cartesian.ForallSeq.Bifunctor
import Data.Container.Cartesian.ForallSeq.Monoidal
import Data.Container.Cartesian.Category
import Data.Container.Definition
import Data.Container.Descriptions.Maybe
import Data.Container.Descriptions.List
import Data.Container.Extension
import Data.Container.ForallSeq
import Data.Container.ForallSeq.Action
import Data.Container.Morphism
import Data.Container.Sequence
import Data.Container.Monad
import Data.Container.Morphism.Eq
import Data.Container.Maybe.Monad
import Data.Container.List.Monad

private prefix 0 @@

private infixr 1 =@>
record (=@>) (a, b : Container) where
  constructor (@@)
  k : (x : a.req) -> Σ (y : b.req) | b.res y -> a.res x


distribExistsAll : {0 a : Type} -> {0 q : a -> Type} ->
    (xs : List (Maybe a)) ->
    Maybe.Any.Any (All q) (distribListMaybe xs) -> All (Maybe.Any.Any q) xs
distribExistsAll [] x = []
distribExistsAll (Nothing :: xs) x = absurd x
distribExistsAll ((Just y) :: ys) x with (distribListMaybe ys) proof p
  distribExistsAll ((Just y) :: ys) x | Nothing = absurd x
  distribExistsAll ((Just y) :: ys) (Aye (x :: xs)) | (Just z) = Aye x :: distribExistsAll {q} ys (rewrite p in Aye xs)


SigPiDistribute :
    {0 b : Type} -> {0 a : b -> Type} -> {0 f : (bv : b) -> a bv -> Type} ->
    (s : Σ (y : b) | (x : a y) -> f y x) -> (x : a s.π1) -> Σ (z : b) | Σ (prf : s.π1 === z) | f z (replace {p = a} prf x)
SigPiDistribute g x = g.π1 ## (Refl ## g.π2 x )

distribCont : All.List (Any.Maybe a) =@> Any.Maybe (All.List a)
distribCont = @@ \x => distribListMaybe x ## distribExistsAll x

distributive : {0 a, b, c : Container} ->
               a ▶ (b ▷ c) =%> (a ▶ b) ▷ (a ▶ c)
distributive = (\x => MkEx (v <- (MkEx (v <- x.ex1) |(ex1 (x.ex2 v)))) |
                           (MkEx (w <- x.ex1) | (x.ex2 w).ex2 (v w))) <!
               (\x, y, z => y.π1 z ## y.π2 z)

%unbound_implicits off

parameters {0 l, m: Container} {a : Container}
  {monad : Monad' Set (exFunctor m)}
  {lonad : Monad' Set (exFunctor l)}
  (distrib : SetDistrib lonad monad)
  (distribBwd :
      (xs : Ex l (Ex m (a .request))) ->
      Σ (m.response ((distrib.dist.component (a.request) xs).ex1))
        (\x => (val : l.response (((distrib.dist.component (a.request) xs).ex2 x).ex1)) -> a.response (((distrib.dist.component (a.request) xs).ex2 x).ex2 val)) ->
      (val : l.response (xs.ex1)) -> Σ (m.response ((xs.ex2 val).ex1)) (\y => a.response ((xs.ex2 val).ex2 y))
  )


  generalDistrib : (l ▶ (m ▷ a)) =@> (m ▷ (l ▶ a))
  generalDistrib = @@ \xs =>  distrib.dist.component ? xs ## distribBwd xs

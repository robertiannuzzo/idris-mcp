module Data.Container.Maybe.Monad

import Data.Category.Action
import Data.Category.Bifunctor
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Monad
import Data.Category.Monoid
import Data.Category.MonadAction

import Data.Container
import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Sequence.Monoidal as Cart
import Data.Container.ForallSeq.Action
import Data.Container.Morphism
import Data.Container.Maybe.Functor
import Data.Container.Maybe.Monoid
import Data.Container.Product
import Data.Container.Sequence.Bifunctor
import Data.Container.Sequence.Monoidal

import Data.Sigma
import Data.Product
import Data.Maybe.Any
import Data.Maybe.Monad

import Proofs.Void
import Proofs.Extensionality
import Proofs.Congruence
import Proofs.Sigma
import Proofs.Unit

%hide Data.Category.(|>)
%hide Prelude.Ops.infixl.(*>)
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
unit : (a : Container) -> a =%> Any.Maybe a
unit _ = Just <! (\x, y => y.unwrap)
%unbound_implicits off
MaybeAnyIsNatural : {0 a, b : Container} ->
                    (m : a =%> b) ->
                    m |%> unit b <%≡%> unit a |%> mapHom Any.MaybeF a b m
MaybeAnyIsNatural (fwd <! bwd) = MkDepLensEq
    (\arg => Refl)
    (\arg, wrg => Refl)
unitNT : Functor.idF Cont =>> Any.MaybeF
unitNT = MkNT
    unit
    (\_, _, arg => depLensEqToEq (MaybeAnyIsNatural arg))
public export
mult : (x : Container) -> Any.Maybe (Any.Maybe x) =%> Any.Maybe x
mult container = joinMaybe <! anyJoin
JoinIsNatural : {0 a, b : Container} ->
    (m : a =%> b) ->
    mapHom Any.MaybeF (Any.Maybe a) (Any.Maybe b) (mapHom Any.MaybeF a b m) |%> mult b
    <%≡%> mult a |%> mapHom Any.MaybeF a b m
JoinIsNatural m = MkDepLensEq
    (\case Nothing => Refl ; (Just _) => Refl)
    (\case Nothing => \x => absurd x
           (Just x) => \_ => Refl)

joinCommutes : (0 x, y : Container) -> (m : x =%> y) ->
  let 0 top : Any.Maybe (Any.Maybe x) =%> Any.Maybe x
      top = mult x

      0 bot : Any.Maybe (Any.Maybe y) =%> Any.Maybe y
      bot = mult y

      0 left : Any.Maybe (Any.Maybe x) =%> Any.Maybe (Any.Maybe y)
      left = mapHom (Any.MaybeF ⨾⨾ Any.MaybeF) x y m

      0 right : Any.Maybe x =%> Any.Maybe y
      right = mapHom Any.MaybeF x y m

  in top |%> right <%≡%> left |%> bot
joinCommutes x y m = MkDepLensEq
    (\case Nothing => Refl
           (Just z) => Refl)
    (\case Nothing => \y => absurd y
           (Just z) => \_ => Refl)
joinNT : (Any.MaybeF ⨾⨾ Any.MaybeF) =>> Any.MaybeF
joinNT = MkNT
  mult
  (\a, b, m => depLensEqToEq (joinCommutes a b m))
MaybeAnyMonad : Monad Cont Any.MaybeF
MaybeAnyMonad = MkMonad
  { unit = unitNT
  , mult = joinNT
  , square = \c => depLensEqToEq (monadSquare c)
  , identityLeft = \c => depLensEqToEq $ MkDepLensEq (\_ => Refl) (\_, _ => Refl)
  , identityRight = \c => depLensEqToEq $ MkDepLensEq
      (\case Nothing => Refl
             (Just x) => Refl)
      (\case Nothing => \x => absurd x
             (Just x) => \(Aye y) => Refl)
  }
  where
    monadSquare : (x : Container) ->
                  (Any.mapMaybe (mult x) |%> mult x)
                  <%≡%>
                  (mult (Any.Maybe x) |%> mult x)
    monadSquare x = MkDepLensEq
        (\case Nothing => Refl
               (Just y) => Refl)
        (\case Nothing => \y => absurd y
               (Just y) => \_ => Refl)
MaybeMonoidAction : Action Cont Cont SequenceMonoidal
MaybeMonoidAction = monoidalSelfAction SequenceMonoidal
namespace Any
  public export
  MaybeMonad : Monad Cont MaybeSeq
  MaybeMonad =
    MonadFromLaxAction ? ? Cont Cont SequenceMonoidal
      (relax MaybeMonoidAction) Cont.MaybeMonoidCompose
namespace All
  MaybeMonad : Monad Cont MaybeAllSeq
  MaybeMonad =
    MonadFromLaxAction Container Container ContCart Cont
      Cart.SequenceMonoidal
      ForallLaxAction
      Cart.MaybeMonoidCompose

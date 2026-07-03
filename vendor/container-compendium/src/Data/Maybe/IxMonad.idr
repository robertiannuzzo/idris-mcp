module Data.Maybe.IxMonad

import Data.Maybe.Any
import Data.Iso

import Proofs

import Syntax.PreorderReasoning

%unbound_implicits off
%hide Prelude.Interfaces.Bool.Monoid.Any
%hide Prelude.Interfaces.Bool.Lazy.Monoid.Any
%hide Prelude.Bool.Lazy.Semigroup.Any
%hide Prelude.Bool.Semigroup.Any

parameters {0 a : Type}
 -- Joining two Maybe
 maybeJoin : Maybe (Maybe a) -> Maybe a
 maybeJoin (Just x) = x
 maybeJoin Nothing = Nothing

 parameters {0 p : a -> Type}
  -- if we have a nested maybe, and that either of them holds predicate p
  --  then the nested predicate holds
  unJoin : (xs : Maybe (Maybe a)) -> Any p (maybeJoin xs) -> Any (Any p) xs
  unJoin Nothing x = absurd x
  unJoin (Just y) x = Aye x

  -- if we have a nested predicate then we can flatten it
  reJoin : (xs : Maybe (Maybe a)) -> Any (Any p) xs -> Any p (maybeJoin xs)
  reJoin Nothing x = absurd x
  reJoin (Just y) (Aye x) = x

  -- undoing a join and redoing it is like doing nothing
  unrejoin : (xs : Maybe (Maybe a)) -> (ys : Any p (maybeJoin xs)) ->
             reJoin xs (unJoin xs ys) === ys
  unrejoin Nothing ys = absurd ys
  unrejoin (Just x) ys = Refl

  -- redoing a join and undoing it is like doing nothing
  reunjoin : (xs : Maybe (Maybe a)) -> (ys : Any (Any p) xs) ->
             unJoin xs (reJoin xs ys) === ys
  reunjoin Nothing ys = absurd ys
  reunjoin (Just x) (Aye y) = Refl

  mapJoinAnyIso : (xs : Maybe (Maybe a)) -> Any p (maybeJoin xs) ≅ Any (Any p) xs
  mapJoinAnyIso xs = MkIso
    (unJoin xs)
    (reJoin xs)
    (reunjoin xs)
    (unrejoin xs)

  rePure : (xs : a) -> Any p (pure xs) -> p xs
  rePure xs (Aye x) = x

  unPure : (xs : a) -> p xs -> Any p (pure xs)
  unPure xs x = Aye x

  pureIso : (xs : a) -> p xs ≅ Any p (pure xs)
  pureIso xs = MkIso
      (unPure xs)
      (rePure xs)
      (\(Aye x) => Refl)
      (\x => Refl)


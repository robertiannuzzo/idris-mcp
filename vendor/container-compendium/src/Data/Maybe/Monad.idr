module Data.Maybe.Monad

import Data.Category
import Data.Category.Functor
import Data.Category.Endofunctor
import Data.Category.Monad
import Data.Category.NaturalTransformation

public export
maybeFunctorCompose :
    {0 a, b, c : Type} ->
    (f : b -> c) -> (g : a -> b) -> (x : Maybe a) ->
    map f (map g x) === map (f . g) x
maybeFunctorCompose f g Nothing = Refl
maybeFunctorCompose f g (Just x) = Refl

public export
maybeFunctorId : (xs : Maybe a) -> map Prelude.id xs === xs
maybeFunctorId Nothing = Refl
maybeFunctorId (Just x) = Refl
public export
MaybeIsFunctor : Endo Set
MaybeIsFunctor = MkFunctor
  Maybe
  (\_, _ => map)
  (\_ => funExt maybeFunctorId)
  (\a, b, c, f, g => sym $ funExt $ maybeFunctorCompose g f)
public export
joinMaybe : Maybe (Maybe a) -> Maybe a
joinMaybe Nothing = Nothing
joinMaybe (Just a) = a
%unbound_implicits off
export
joinMaybeMap :
    {0 a : Type} ->
    (x : Maybe (Maybe (Maybe a))) ->
    joinMaybe (map joinMaybe x) ≡ joinMaybe (joinMaybe {a = Maybe a}  x)
joinMaybeMap Nothing = Refl
joinMaybeMap (Just x) = Refl
export
joinMapId : {0 a : Type} ->
            (x : Maybe a) -> joinMaybe (map Just x) ≡ x
joinMapId Nothing = Refl
joinMapId (Just x) = Refl
%unbound_implicits on
public export
MaybeIsMonad : Monad Set MaybeIsFunctor
MaybeIsMonad = MkMonad
  (MkNT
    (\_ => Just)
    (\_, _, m => Refl))
  (MkNT
    (\_ => joinMaybe)
    (\a, b, m => funExt $ \case Nothing => Refl
                                (Just x) => Refl)
    )
  (\_ => funExt joinMaybeMap)
  (\_ => Refl)
  (\_ => funExt joinMapId)

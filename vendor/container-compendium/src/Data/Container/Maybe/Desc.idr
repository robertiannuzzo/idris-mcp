module Data.Container.Maybe.Desc

import Data.Container.Coproduct
import Data.Container.Definition
import Data.Container.ForallSeq.Definition
import Data.Container.Morphism
import Data.Container.Morphism.Eq
import Data.Product
import Data.Sigma
import Data.Iso
import Data.Iso.Generic
import Data.Maybe
import Data.Maybe.Any as Maybe.Quantifier
import Proofs

%default total

-- strict version of boolean operations
public export
and : Bool -> Bool -> Bool
and True x = x
and False _ = False

export
andR : {x : Bool} -> and x True === x
andR {x = False} = Refl
andR {x = True} = Refl

export
andAssoc : {x, y, z : Bool} -> (x `and` y) `and` z = x `and` (y `and` z)
andAssoc {x} = ?andAssoc_rhs

public export
or : Bool -> Bool -> Bool
or False x = x
or True _ = True
public export
data IsTrue : Bool -> Type where
  TT : IsTrue True
public export
Uninhabited (IsTrue False) where
  uninhabited _ impossible

export
fromTruth : IsTrue x -> x === True
fromTruth TT = Refl

export
allTruths : (x, y : _) -> IsTrue x -> IsTrue y -> x === y
allTruths False _ TT _ impossible
allTruths True False _ TT impossible
allTruths True True z w = Refl

public export
isTrueUniq : (x : IsTrue True) -> TT === x
isTrueUniq TT = Refl
public export
MaybeCont : Container
MaybeCont = (isJust : Bool) !> IsTrue isJust
public export
Maybe : Type -> Type
Maybe = Ex MaybeCont
public export
Just : (x : a) -> Desc.Maybe a
Just x = MkEx True (\_ => x)

public export
Nothing : Desc.Maybe a
Nothing = MkEx False absurd
fromDesc : Desc.Maybe a -> Prelude.Maybe a
fromDesc (MkEx False p) = Nothing
fromDesc (MkEx True p) = Just (p TT)

toDesc : Prelude.Maybe a -> Desc.Maybe a
toDesc Nothing = Nothing
toDesc (Just x) = Just x

toFromEq : {0 a : Type} -> (x : Prelude.Maybe a) -> fromDesc (toDesc x) === x
toFromEq Nothing = Refl
toFromEq (Just x) = Refl

0 fromToEq : {0 a : Type} -> (x : Desc.Maybe a) -> toDesc (fromDesc x) === x
fromToEq (MkEx True p) = cong (MkEx True) (funExt $ \TT => Refl)
fromToEq (MkEx False p) = cong (MkEx False) (allUninhabited _ _)

public export
MaybeIso : Desc.Maybe a ≅ Prelude.Maybe a
MaybeIso = MkIso fromDesc toDesc toFromEq fromToEq
public export
MaybeCont' : Container
MaybeCont' = One + I

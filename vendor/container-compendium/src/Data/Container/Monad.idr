module Data.Container.Monad

import Data.Category
import Data.Category.Monad
import Data.Category.Functor
import Data.Category.Endofunctor
import Data.Category.Bifunctor
import Data.Category.NaturalTransformation
import Data.List.Monad

import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Descriptions.List
import Data.Container.Morphism
import Data.Container.Morphism.Eq
import Data.Container.Maybe.Definition
import Data.Container.Maybe.Desc
import Data.Container.Maybe.Functor
import Data.Container.List.Desc
import Data.Container.List.Functor
import Data.Container.Descriptions.Maybe

import Proofs.Congruence
import Proofs.Extensionality

import Data.Fin
import Data.Integral
import Data.Maybe.Monad
import Data.List.Monad

import Syntax.PreorderReasoning.Generic

%default total

%hide Prelude.Ops.infixl.(*>)
NotFunctor : Type -> Type
NotFunctor a = Bool

notMap : {a, b : Type} -> (a -> b) -> NotFunctor a -> NotFunctor b
notMap f True = False
notMap f False = True

failing "Mismatch between: False and True."
  idFunctor : {a : Type} -> (v : NotFunctor a) -> Monad.notMap {b = a} (\x => x) v === v
  idFunctor False = Refl
  idFunctor True = Refl
public export
record ContainerMonad (func : Endo Cont) where
  constructor MkContainerMonad

  pure : (a : Container) -> a =%> func.mapObj a

  join : (0 a : Container) -> func.mapObj (func.mapObj a) =%> func.mapObj a

  0 assoc : forall a.
          let 0 top : func.mapObj (func.mapObj (func.mapObj a)) =%> func.mapObj (func.mapObj a)
              top = join (func.mapObj a)
              0 left : func.mapObj (func.mapObj (func.mapObj a)) =%> func.mapObj (func.mapObj a)
              left = func.mapHom _ _ (join a)
          in join (func.mapObj a) |%> join a <%≡%> left |%> join a

  0 id1 : (a : Container) ->
          pure {a = func.mapObj a} |%> join a <%≡%> identity {a = func.mapObj a}

  0 id2 : (a : Container) ->
          func.mapHom _ _ (pure {a = a}) |%> join a <%≡%> identity {a = func.mapObj a}
  0 pureNatural : (0 x, y : Container) -> (m : x =%> y) ->
                  pure {a = x} |%> func.mapHom x y m <%≡%> m |%> pure {a = y}

  0 joinNatural : (0 x, y : Container) -> (m : x =%> y) ->
                  join x |%> func.mapHom x y m <%≡%> func.mapHom _ _ (func.mapHom x y m) |%> join y
ContainerMonadToMonad : {f : Endo Cont} -> ContainerMonad f -> Monad Cont f
ContainerMonadToMonad mon = MkMonad
    { unit = mkNTEta
    , mult = mkNTMu
    , square = \vx => sym $ depLensEqToEq mon.assoc
    , identityLeft = \vx => depLensEqToEq $ mon.id1 vx
    , identityRight = \vx => depLensEqToEq $ mon.id2 vx
    }
  where
    mkNTEta : idF Cont =>> f
    mkNTEta = MkNT
      (mon.pure)
      (\x, y, m => depLensEqToEq $ mon.pureNatural x y m)

    mkNTMu : f ⨾⨾ f =>> f
    mkNTMu = MkNT
        (\v => mon.join v)
        (\x, y, m => depLensEqToEq $ mon.joinNatural x y m)
public export
record ContainerComonad (func : Endo Cont) where
  constructor MkContainerComonad
  counit : (a : Container) -> func.mapObj a =%> a
  comult : (a : Container) -> func.mapObj a =%> func.mapObj (func.mapObj a)
  0 assoc : (a : Container) ->
          let 0 top : func.mapObj (func.mapObj a) =%> func.mapObj (func.mapObj (func.mapObj a))
              top = comult (func.mapObj a)
              0 left : func.mapObj (func.mapObj a) =%> func.mapObj (func.mapObj (func.mapObj a))
              left = func.mapHom _ _ (comult a)
          in comult a |%> left <%≡%> comult a |%> comult (func.mapObj a)
  0 id1 : (a : Container) ->
             comult a |%> counit (func.mapObj a) <%≡%> identity {a = func.mapObj a}
  0 id2 : (a : Container) ->
             comult a |%> func.mapHom _ _ (counit a) <%≡%> identity {a = func.mapObj a}
-- containerComonadToMonadOp
MLF : Endo Cont
MLF = All.ListF ⨾⨾ Any.MaybeF
{-

unitML : (a : Container) -> a =%> Any.Maybe (All.List a)
unitML a = ?Hole1

unitMLPrf : (0 x, y : Container) -> (m : x =%> y) ->
      let 0 top : x =%> Any.Maybe (All.List x)
          top = unitML x

          0 bot : y =%> Any.Maybe (All.List y)
          bot = unitML y

          0 left : x =%> y
          left = m

          0 right : Any.Maybe (All.List x) =%> Any.Maybe (All.List y)
          -- right = (MLF).mapHom _ _ m

          0 comp1 : x =%> Any.Maybe (All.List y)
          comp1 = top ⨾ right

          0 comp2 : x =%> Any.Maybe (All.List y)
          comp2 = left ⨾ bot

      in comp1 === comp2
unitMLPrf x y m = ?hole2

joinMLFwd' : {x : Container} ->
            Maybe (List (Maybe (List x.req))) ->
            Maybe (List x.req)
joinMLFwd' x = joinMaybe $ map (map joinList . distribListMaybe) x

joinMLFwd : {x : Container} ->
            Maybe (List (Maybe (List x.req))) ->
            Maybe (List x.req)

joinML : (a : Container) -> Any.Maybe (All.List (Any.Maybe (All.List a))) =%> Any.Maybe (All.List a)
joinML a = ?joinmlimpl

joinMLPrf : (0 x, y : Container) -> (m : x =%> y) ->
      let MLFF : Container -> Container
          MLFF a = (MLF *> MLF).mapObj a
          0 top : MLFF x =%> Any.Maybe (All.List x)
          top = joinML x

          0 bot : MLFF y =%> Any.Maybe (All.List y)
          bot = joinML y

          0 left : MLFF x =%> MLFF y
          left = (MLF *> MLF).mapHom _ _ m

          0 right : Any.Maybe (All.List x) =%> Any.Maybe (All.List y)
          right = (MLF).mapHom _ _ m

          0 comp1 : MLFF x =%> Any.Maybe (All.List y)
          comp1 = top ⨾ right

          0 comp2 : MLFF x =%> Any.Maybe (All.List y)
          comp2 = left ⨾ bot

      in comp1 === comp2
joinMLPrf x y m = ?joinMLPrf_rhs

MLUnit : Functor.idF Cont =>> MLF
MLUnit = MkNT
  unitML
  unitMLPrf

MLMult : (MLF *> MLF) =>> MLF
MLMult = MkNT
    joinML
    joinMLPrf

MaybeListMonad : Monad Cont
MaybeListMonad = MkMonad
    MLF
    MLUnit
    MLMult

public export
record ContainerMonad (func : Functor Cont Cont) where
  constructor MkContainerMonad
  pure : (a : Container) -> a =%> func.mapObj a
  join : (a : Container) -> func.mapObj (func.mapObj a) =%> func.mapObj a
  0 assoc : forall a.
          let 0 top : func.mapObj (func.mapObj (func.mapObj a)) =%> func.mapObj (func.mapObj a)
              top = join (func.mapObj a)
              0 left : func.mapObj (func.mapObj (func.mapObj a)) =%> func.mapObj (func.mapObj a)
              left = func.mapObj' _ _ (join a)
          in join (func.mapObj a) |> join a `DepLensEq` left |> join a

  0 idl : (a : Container) ->
          pure (func.mapObj a) |> join a `DepLensEq` identity {a = func.mapObj a}
  0 idr : (a : Container) ->
          func.mapObj' _ _ (pure a) |> (join a) `DepLensEq` identity {a = func.mapObj a}

public export
ContMonadToMonad : (func : Functor Cont Cont) -> ContainerMonad func -> Monad Cont
ContMonadToMonad func@(MkFunctor mo mm ci cc) m = MkMonad
    func
    pureNT
    (MkNT m.join (\x, y, f => ?Add ))
    ?ContMonadToMonad_rhs
    ?ddkjnvn
    ?qeqee
    where
      pureNTSq : (x, y : Container) -> (f : x =%> y) -> m.pure x |> func.mapObj' _ _ f `DepLensEq` f |> m.pure y
      pureNTSq x y mor@(MkMorphism f f') = CalcWith {leq = DepLensEq} $
                                     |~ m.pure x |> func.mapObj' x y mor
                                     ~~ mor |> m.pure y ...(?huhu)

      pureNT : idF Cont =>> func
      pureNT = MkNT m.pure
          (\x, y, f => depLensEqToEq (pureNTSq x y f))

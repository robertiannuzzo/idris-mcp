module Data.Container.Fix

import Data.Container.Category
import Data.Category.Monoid
import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Category.Monad
import Data.Product

import Syntax.PreorderReasoning

%hide Prelude.Functor
%default covering
ContMon : Type
ContMon = Monoidal {o = Container} Cont
data Fw : (mon : ContMon) -> (0 _ : Container) -> Type
data Bw : (mon : ContMon) -> (0 c : Container) -> Fw mon c -> Type
Free : {auto mon : ContMon} -> Container -> Container
Free c = (x : Fw mon c) !> Bw mon c x
public export
data Fw : (mon : ContMon) -> (0 _ : Container) -> Type where
  Done : mon.i.request -> Fw mon c
  More : {mon : ContMon} -> ((c ⊗ Free c) @{Cont}).request -> Fw mon c

public export
data Bw : (mon : ContMon) -> (0 c : Container) -> Fw mon c -> Type where
  U : {x : mon.i.request} -> mon.i.response x -> Bw mon c (Done x)
  M : {mon : ContMon} -> {0 c : Container} ->
      {0 ix : ((c ⊗ Free c) @{Cont}).request} ->
              ((c ⊗ Free c) @{Cont}).response ix ->
      Bw mon c (More ix)
parameters (mon : ContMon)
  freeHom : {x, y : Container} -> x =%> y -> Free {mon} x =%> Free {mon} y

  mapFw : {x, y : Container} -> (f : x =%> y) -> Fw mon x -> Fw mon y
  mapFw f (Done z) = Done z
  mapFw f (More z) = More ((mon.mult.mapHom (x && Free {mon} x) (y && Free {mon} y) (f && freeHom f)).fwd z)

  mapBwd : {x, y : Container} ->
    (fm : x =%> y) ->
    (fw : Fw mon x) -> Bw mon y (mapFw fm fw) -> Bw mon x fw
  mapBwd fm (Done w) (U z) = U z
  mapBwd fm (More w) (M z) = M ((mon.mult.mapHom (x && Free {mon} x) (y && Free {mon} y) (fm && freeHom fm)).bwd w z)

  freeHom fm = mapFw fm <! mapBwd fm

  0 freePresId : (v : Container) -> freeHom (identity v) = identity (Free v)

  fwPresId : (v: Container) -> (w : Fw mon v) -> mapFw (identity v) w === w
  fwPresId v (Done x) = Refl
  fwPresId v (More x) =
      cong More $ Calc $
      |~ (mon.mult.mapHom
           (v && Free v)
           (v && Free v)
           (identity v && freeHom (identity v))).fwd x
      ~~ (mon.mult.mapHom
           (v && Free v)
           (v && Free v)
           (identity v && (identity (Free v)))).fwd x
           ...(cong (\xx => (mon.mult.mapHom (v && Free v) (v && Free v) (identity v && xx)).fwd x) (freePresId v))
      ~~ (identity (mon.mult.mapObj (v && Free v))).fwd x
          ...(cong (\xx => xx.fwd x) (mon.mult.presId (v && Free v)))
      ~~ x
      ...(Refl)

  0 bwPresId : (v : Container) ->
    (w : Fw mon v) -> (y : Bw mon v (mapFw (identity v) w)) ->
        mapBwd (identity v) w y === transport (Bw mon v) (fwPresId v w) y
  bwPresId v (Done x) (U y) = applyRefl' ? ?
  bwPresId v (More x) (M y) = let
      ff = freePresId v
      mh = mon.mult.presId (v && Free v)
      rr = applyTransport' (Bw mon v) (M y)
      pr : ((mon.mult.mapHom
            (v && Free v)
            (v && Free v)
            (identity v && freeHom (identity v))).bwd x) ~=~
           ((mon.mult.mapHom
            (v && Free v)
            (v && Free v)
            (identity v && (identity (Free v)))).bwd x)
      pr = rewrite freePresId v in Refl
--       prY : ((mon.mult.mapHom
--             (v && Free v)
--             (v && Free v)
--             (identity v && freeHom (identity v))).bwd x y)
--             ===
--             ((identity (mon.mult.mapObj (v && Free v))).bwd x
--             $ transport (\xx => (mon.mult.mapObj (v && Free v)).response xx)
--                          ?hwll y)
      in Calc $
      |~ mapBwd (identity v) (More x) (M y)
      ~~ M ((mon.mult.mapHom
            (v && Free v)
            (v && Free v)
            (identity v && freeHom (identity v))).bwd x y)
         ...(Refl)
      ~~ M ((mon.mult.mapHom
            (v && Free v)
            (v && Free v)
            (identity v && (identity (Free v)))).bwd x
              (transport (\xx => (mon.mult.mapObj (v && Free v)).response
                  ((mon.mult.mapHom (v && Free v) (v && Free v)
                    (identity v && xx)).fwd x)
                 ) (freePresId v) y))
            ...(?hbei)
      ~~ M ((identity (mon.mult.mapObj (v && Free v))).bwd x
              (transport ((mon.mult.mapObj (v && Free v)).response)
                         (?arg) y))
         ...(?hwllo2)
      ~~ replace {p = Bw mon v} (fwPresId v (More x)) (M y)

         ...(?oooo)
      ~~ transport (Bw mon v) (fwPresId v (More x)) (M y)
         ...(applyTransport' (Bw mon v) (M y))

  freePresId v = depLensEqToEq $ MkDepLensEq
      (fwPresId v)
      (\vx, vy => bwPresId v vx vy `trans` applyTransport (Bw mon v) ?)

  0 freePresComp : (a, b, c : Container) ->
    (f : a =%> b) -> (g : b =%> c) ->
    freeHom (f |%> g) = freeHom f |%> freeHom g
  freePresComp a b c f g = ?freePresComp_rhs

{-
  FreeIsFunctor : Endo Cont
  FreeIsFunctor = MkFunctor
      (Free {mon})
      (\_, _ => freeHom)
      freePresId
      freePresComp
FreeIsMonad : (mon : ContMon) -> Monad Cont (FreeIsFunctor mon)
FreeIsMonad mon = MkMonad
    ?FreeIsMonad_rhsu
    ?FreeIsMonad_rhsm
    ?FreeIsMonad_rhse1
    ?FreeIsMonad_rhser1
    ?FreeIsMonad_rhser2

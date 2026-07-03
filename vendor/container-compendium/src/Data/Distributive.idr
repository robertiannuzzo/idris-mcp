module Data.Distributive

import Data.Maybe
import Data.List
import public Data.List.Monad
import public Data.Maybe.Monad
import Data.Category
import Data.Category.Endofunctor
import Data.Category.Monad
import Data.Category.NaturalTransformation

import Data.Container.Descriptions.Maybe

import Pipeline.Equality
import Control.Order
import Control.Relation

import Syntax.PreorderReasoning.Generic

%unbound_implicits off
public export
record SetDistrib
  {lendo, mendo : Endo Set} (l : Monad Set lendo) (m : Monad Set mendo) where
  constructor MkDistribProof
  -- the natural transofmration
  dist : mendo ⨾⨾ lendo =>> lendo ⨾⨾ mendo
  --              l . M
  -- L . M . M ──────────> M L M
  --     │                   │
  --     │                   │ M . l
  --     │                   v
  --     │ L . µ         M . M . L
  --     │                   │
  --     │                   │ µ . L
  --     V                   v
  --   L . M ────────────> M . L
  --               l
  0 penta1 : (0 a : Type) -> let
    -- top right corner
    0 top : lendo.mapObj (mendo.mapObj (mendo.mapObj a)) -> mendo.mapObj (lendo.mapObj (mendo.mapObj a))
    top = dist.component (mendo.mapObj a)
    0 topRight : mendo.mapObj (lendo.mapObj (mendo.mapObj a)) -> mendo.mapObj (mendo.mapObj (lendo.mapObj a))
    topRight = mendo.mapHom ? ? (dist.component a)
    0 botRight : mendo.mapObj (mendo.mapObj (lendo.mapObj a)) -> mendo.mapObj (lendo.mapObj a)
    botRight = m.mult.component (lendo.mapObj a)

    -- bottom left corner
    0 left : lendo.mapObj (mendo.mapObj (mendo.mapObj a)) -> lendo.mapObj (mendo.mapObj a)
    left = lendo.mapHom ? ? (m.mult.component a)
    0 bottom : lendo.mapObj (mendo.mapObj a) -> mendo.mapObj (lendo.mapObj a)
    bottom = dist.component a
    in (x : lendo.mapObj (mendo.mapObj (mendo.mapObj a))) ->
       botRight (topRight (top x)) === bottom (left x)

  --              L . l
  -- L . L . M ──────────> L M L
  --     │                   │
  --     │                   │ L . l
  --     │                   v
  --     │ µ . M         M . L . L
  --     │                   │
  --     │                   │ M . µ
  --     V                   v
  --   L . M ────────────> M . L
  --               l
  0 penta2 : (0 a : Type) -> let
      -- top-right corner
      0 top : lendo.mapObj (lendo.mapObj (mendo.mapObj a)) -> lendo.mapObj (mendo.mapObj (lendo.mapObj a))
      top = lendo.mapHom ? ? (dist.component a)
      0 topRight : lendo.mapObj (mendo.mapObj (lendo.mapObj a)) -> mendo.mapObj (lendo.mapObj (lendo.mapObj a))
      topRight = dist.component (lendo.mapObj a)
      0 botRight : mendo.mapObj (lendo.mapObj (lendo.mapObj a)) -> mendo.mapObj (lendo.mapObj a)
      botRight = mendo.mapHom ? ? (l.mult.component a)

      -- bot-left corner
      0 left : lendo.mapObj (lendo.mapObj (mendo.mapObj a)) -> lendo.mapObj (mendo.mapObj a)
      left = l.mult.component (mendo.mapObj a)
      0 bottom : lendo.mapObj (mendo.mapObj a) -> mendo.mapObj (lendo.mapObj a)
      bottom = dist.component a
      in (x : lendo.mapObj (lendo.mapObj (mendo.mapObj a))) ->
         botRight (topRight (top x)) === bottom (left x)

  --         η_M
  --    List ────────> Maybe . List
  --      │               ^
  --      │ L . η         │
  --      │               │
  --      V             l │
  -- List . Maybe ────────┘
  tri1 : (0 a : Type) -> let
      0 top : lendo.mapObj a -> mendo.mapObj (lendo.mapObj a)
      top = m.unit.component (lendo.mapObj a)
      0 left : lendo.mapObj a -> lendo.mapObj (mendo.mapObj a)
      left = lendo.mapHom ? ? (m.unit.component a)
      in (x : lendo.mapObj a) ->
         top x === dist.component a (left x)

  --           M . η
  --    Maybe ──────> Maybe . List
  --      │               ^
  --      │ η_L           │
  --      │               │
  --      V             δ │
  -- List . Maybe ────────┘
  tri2 : (0 a : Type) -> let
      0 top : mendo.mapObj a -> mendo.mapObj (lendo.mapObj a)
      top = mendo.mapHom ? ? (l.unit.component a)
      0 left : mendo.mapObj a -> lendo.mapObj (mendo.mapObj a)
      left = l.unit.component (mendo.mapObj a)
      in (x : mendo.mapObj a) ->
         top x === dist.component a (left x)

CompositeMonad : {lendo, mendo : Endo Set} -> {l : Monad Set lendo} -> {m : Monad Set mendo} ->
                 SetDistrib l m -> Monad Set (lendo ⨾⨾ mendo)
CompositeMonad distrib =
  let u2 : idF Set =>> idF Set ⨾⨾ idF Set
      u2 = funcIdLNT' {f = idF Set}

      uu : idF Set =>> lendo ⨾⨾ mendo
      uu = u2 ⨾⨾⨾ l.unit -⨾- m.unit

      mm : (lendo ⨾⨾ mendo) ⨾⨾ (lendo ⨾⨾ mendo) =>> lendo ⨾⨾ mendo
      mm = CalcWith {dom = Endo Set} {leq = (=>>)}$
           |~ (lendo ⨾⨾ mendo) ⨾⨾ (lendo ⨾⨾ mendo)
           <~ lendo ⨾⨾ (mendo ⨾⨾ (lendo ⨾⨾ mendo)) ...(funcCompAssocNTL lendo mendo (lendo ⨾⨾ mendo))
           <~ lendo ⨾⨾ ((mendo ⨾⨾ lendo) ⨾⨾ mendo) ...(lendo ⨾- funcCompAssocNTR mendo lendo mendo)
           <~ lendo ⨾⨾ ((lendo ⨾⨾ mendo) ⨾⨾ mendo) ...(lendo ⨾- (distrib.dist -⨾ mendo))
           <~ lendo ⨾⨾ (lendo ⨾⨾ (mendo ⨾⨾ mendo)) ...(lendo ⨾- funcCompAssocNTL lendo mendo mendo)
           <~ lendo ⨾⨾ (lendo ⨾⨾ mendo)            ...(lendo ⨾- (lendo ⨾- m.mult))
           <~ (lendo ⨾⨾ lendo) ⨾⨾ mendo            ...(funcCompAssocNTR lendo lendo mendo)
           <~ lendo ⨾⨾ mendo                       ...(l.mult -⨾ mendo)
  in MkMonad
  uu
  mm
  ?law1
  ?law2
  ?law3

public export
distribute :
    {lendo, mendo : Endo Set} ->  {l : Monad Set lendo} -> {m : Monad Set mendo} ->
    (s : SetDistrib l m) => {a : Type} -> lendo.mapObj (mendo.mapObj a) -> mendo.mapObj (lendo.mapObj a)
distribute x = s.dist.component a x


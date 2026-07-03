module Data.Container.Distrib

import Control.Function

import Data.Iso
import Data.Distributive
import Data.Maybe
import Data.List
import Data.List.Quantifiers as QL
import Data.List.Monad
import Data.Sigma

import Data.Category
import Data.Category.Action
import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Category.Functor
import Data.Category.Functor.Category
import Data.Category.Functor.Exponential
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
import Data.Container.ForallSeq.Definition
import Data.Container.ForallSeq.Action
import Data.Container.Morphism
import Data.Container.Sequence.Definition
import Data.Container.Monad
import Data.Container.Morphism.Eq
import Data.Container.Maybe.Monad
import Data.Container.List.Functor
import Data.Container.List.Monad


import Proofs.Sigma
import Proofs.Extensionality
import Proofs.Congruence
import Proofs.Void
import Proofs.UIP
import Proofs.List
import Proofs.Maybe
import Proofs.Relation

import Syntax.PreorderReasoning

%hide Prelude.Ops.infixl.(|>)
%default total
%unbound_implicits off

public export
record ContDistrib {l, m : Endo Cont} (lonad : Monad Cont l) (monad : Monad Cont m) where
  constructor MkDistribProofCont
  -- component of the natural transofmration
  dist : (0 a : Container) -> l.mapObj (m.mapObj a) =%> m.mapObj (l.mapObj a)
  -- naturality square
  l_nt : {0 a, b : Container} ->
         (f : a =%> b) ->
         ((l.mapHom (m.mapObj a)  (m.mapObj b) (m.mapHom a b f))
           |%> dist {a = b})
         <%≡%> (dist a |%> m.mapHom (l.mapObj a) (l.mapObj b) (l.mapHom a b f))

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
  0 penta1 : (0 a : Container) -> let
    -- top right corner
    0 top : l.mapObj (m.mapObj (m.mapObj a)) =%> m.mapObj (l.mapObj (m.mapObj a))
    top = dist (m.mapObj a)
    0 topRight : m.mapObj (l.mapObj (m.mapObj a)) =%> m.mapObj (m.mapObj (l.mapObj a))
    topRight = m.mapHom ? ? (dist a)
    0 botRight : m.mapObj (m.mapObj (l.mapObj a)) =%> m.mapObj (l.mapObj a)
    botRight = monad.mult.component (l.mapObj a)

    0 top_right : l.mapObj (m.mapObj (m.mapObj a)) =%> m.mapObj (l.mapObj a)
    top_right = top |%> topRight |%> botRight

    -- bottom left corner
    0 left : l.mapObj (m.mapObj (m.mapObj a)) =%> l.mapObj (m.mapObj a)
    left = l.mapHom ? ? (monad.mult.component a)
    0 bottom : l.mapObj (m.mapObj a) =%> m.mapObj (l.mapObj a)
    bottom = dist a

    0 bottom_left : l.mapObj (m.mapObj (m.mapObj a)) =%> m.mapObj (l.mapObj a)
    bottom_left = left |%> bottom
    in
    top_right <%≡%> bottom_left
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
  penta2 : (0 a : Container) -> let
      -- top-right corner
      0 top : l.mapObj (l.mapObj (m.mapObj a)) =%> l.mapObj (m.mapObj (l.mapObj a))
      top = l.mapHom ? ? (dist a)
      0 topRight : l.mapObj (m.mapObj (l.mapObj a)) =%> m.mapObj (l.mapObj (l.mapObj a))
      topRight = dist (l.mapObj a)
      0 botRight : m.mapObj (l.mapObj (l.mapObj a)) =%> m.mapObj (l.mapObj a)
      botRight = m.mapHom ? ? (lonad.mult.component a)

      -- bot-left corner
      0 left : l.mapObj (l.mapObj (m.mapObj a)) =%> l.mapObj (m.mapObj a)
      left = lonad.mult.component (m.mapObj a)
      0 bottom : l.mapObj (m.mapObj a) =%> m.mapObj (l.mapObj a)
      bottom = dist a
      in
        (top |%> topRight |%> botRight) <%≡%> left |%> bottom

  --         η_M
  --    List ────────> Maybe . List
  --      │               ^
  --      │ L . η         │
  --      │               │
  --      V             l │
  -- List . Maybe ────────┘
  tri1 : (0 a : Container) -> let
      0 top : l.mapObj a =%> m.mapObj (l.mapObj a)
      top = monad.unit.component (l.mapObj a)
      0 left : l.mapObj a =%> l.mapObj (m.mapObj a)
      left = l.mapHom ? ? (monad.unit.component a)
      in  top <%≡%> left |%> dist a

  --           M . η
  --    Maybe ──────> Maybe . List
  --      │               ^
  --      │ η_L           │
  --      │               │
  --      V             l │
  -- List . Maybe ────────┘
  tri2 : (0 a : Container) -> let
      0 top : m.mapObj a =%> m.mapObj (l.mapObj a)
      top = m.mapHom ? ? (lonad.unit.component a)
      0 left : m.mapObj a =%> l.mapObj (m.mapObj a)
      left = lonad.unit.component (m.mapObj a)
      in top <%≡%> left |%> dist a


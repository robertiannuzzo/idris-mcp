module Data.Container.Sequence.Definition

import Data.Container.Definition
import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Extension.Definition
import Data.Container.Morphism.Definition
import Data.Container.Morphism.Eq

import Data.Sigma
import Data.Iso

import Proofs

import Data.Category.Bifunctor

public export
(▷) : Container -> Container -> Container
(▷) a b =
  (x : Ex a b.request) !>
  (Σ (a.response x.ex1) (b.response . x.ex2))

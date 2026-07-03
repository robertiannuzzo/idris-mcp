module Data.Category.Monad

import Data.Category
import Data.Category.NaturalTransformation
import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Category.Monoid
import Control.Relation

import Syntax.PreorderReasoning

%hide Prelude.Ops.infixl.(*>)
%hide Prelude.Monad
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
public export
record Monad (c : Category o) (endo : Endo c) where
  constructor MkMonad
  unit : idF c =>> endo
  mult : (endo ⨾⨾ endo) =>> endo
  0 square : (x : o) -> let
      0 top : endo.mapObj (endo.mapObj (endo.mapObj x)) ~> endo.mapObj (endo.mapObj x)
      top = endo.mapHom _ _ (mult.component x)
      0 bot, right : endo.mapObj (endo.mapObj x) ~> endo.mapObj x
      right = mult.component x
      bot = mult.component x
      0 left : endo.mapObj (endo.mapObj (endo.mapObj x)) ~> endo.mapObj (endo.mapObj x)
      left = mult.component (endo.mapObj x)
      0 arm2, arm1 : endo.mapObj (endo.mapObj (endo.mapObj x)) ~> endo.mapObj x
      arm1 = (top |> right) {cat = c}
      arm2 = left |> bot
      in arm1 === arm2
  0 identityLeft : (x : o) -> let
      0 compose : endo.mapObj x ~> endo.mapObj x
      compose = (unit.component (endo.mapObj x) |> mult.component x) {cat = c}
      0 straight : endo.mapObj x ~> endo.mapObj x
      straight = c.id (endo.mapObj x)
      in compose === straight

  0 identityRight : (x : o) -> let
      0 compose : endo.mapObj x ~> endo.mapObj x
      compose = (endo.mapHom _ _ (unit.component x) |> mult.component x) {cat = c}
      0 straight : endo.mapObj x ~> endo.mapObj x
      straight = c.id (endo.mapObj x)
      in compose === straight
public export
record Comonad (c : Category o) (endo : Endo c) where
  constructor MkCoMonad
  extract : endo =>> idF c
  duplicate : endo =>> endo ⨾⨾ endo

  idL : let
         0 ηT : (endo ⨾⨾ endo) =>> endo
         ηT = (extract -⨾ endo) ⨾⨾⨾ funcIdRNT
         in (duplicate ⨾⨾⨾ ηT) `NTEq` identity {f = endo}
  idR : let
         0 Tη : endo ⨾⨾ endo =>> endo
         Tη = (endo ⨾- extract) ⨾⨾⨾ funcIdLNT
         in (duplicate ⨾⨾⨾ Tη) `NTEq` identity {f = endo}
  comp : let
         0 whiskL : endo ⨾⨾ endo =>> endo ⨾⨾ (endo ⨾⨾ endo)
         whiskL = (endo ⨾- duplicate) {a = c, b = c, c = c, g = endo , h = endo ⨾⨾ endo}
         0 whiskR : endo ⨾⨾ endo =>> endo ⨾⨾ (endo ⨾⨾ endo)
         whiskR = (duplicate -⨾ endo) ⨾⨾⨾ funcCompAssocNTL _ _ _
         in whiskL `NTEq` whiskR

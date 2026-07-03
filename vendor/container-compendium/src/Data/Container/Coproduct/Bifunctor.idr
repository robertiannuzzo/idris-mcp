module Data.Container.Coproduct.Bifunctor

import public Data.Coproduct

import Data.Category.Bifunctor
import Data.Container.Category
import Data.Container.Coproduct.Definition
import Data.Container.Closed.Definition
import Data.Container.Closed.Eq
import Data.Container.Definition
import Data.Container.Morphism.Definition
import Data.Container.Morphism.Conversion
import Data.Category.Preorder
import Data.Category.Functor
import Data.Category.Iso
import public Data.Category.Notation

import Data.Iso
import Data.Iso.Category

import Syntax.PreorderReasoning

import Proofs
public export
(~+~) : a =%> a' -> b =%> b' -> (a + b) =%> (a' + b')
(~+~) x y =
  (bimap x.fwd y.fwd) <!
  (dchoice (\xy => x.bwd xy)
           (\xy => y.bwd xy)
           {c = \xa => (a' + b').response (bimap x.fwd y.fwd xa) ->
                       choice (a .response) (b .response) xa}
  )
public export
CoprodContBifunctor : Bifunctor Cont Cont Cont
CoprodContBifunctor = MkFunctor
  (Product.uncurry (+))
  (\_, _, m => m.π1 ~+~ m.π2)
  -- proofs in appendix
  (\(x1 && x2) => depLensEqToEq $ MkDepLensEq bifunctorId'
      (\case (+> v) => \_ => Refl
             (<+ v) => \_ => Refl
      )
  )
  (\a, b, c, (f1 && f2), (g1 && g2) => depLensEqToEq $ MkDepLensEq
      (bimapCompose)
      (\case (<+ x) => \_ => Refl
             (+> x) => \_ => Refl))
public export
dia : a + a =%> a
dia = dia <! dchoice (\_ => id) (\_ => id)
public export
dia3 : a + a + a =%> a
dia3 = dia ~+~ identity a |%> dia
public export
inr : b =%> a + b
inr = (+>) <! (\x => id)
public export
inl : a =%> a + b
inl = (<+) <! (\x => id)
coprod : a =%> c -> b =%> c -> a + b =%> c
coprod f g = f ~+~ g |%> dia
diaSame : (f : a -> c) ->
          (g : b -> c) ->
          (h : a + b -> c) ->
          (f = h . (<+)) ->
          (g = h . (+>)) ->
          (v : a + b) ->
          dia (bimap f g v) = h v
diaSame f g h prf1 prf2 (<+ x) = app prf1 x
diaSame f g h prf1 prf2 (+> x) = app prf2 x

prfClosed :
   (f : a =%> c) ->
   (g : b =%> c) ->
   (h : a + b =%> c) ->
   (p : (Bifunctor.inl {a, b} |%> h) `DepLensEqTr` f) ->
   (q : (Bifunctor.inr {a, b} |%> h) `DepLensEqTr` g) ->
   coprod f g `DepLensEqTr` h
prfClosed f g h p q = MkDepLensEqTr
    (diaSame f.fwd g.fwd h.fwd (funExt $ \vx => sym $ p.eqFwd vx)
                               (funExt $ \vy => sym $ q.eqFwd vy))
    (\case (<+ x) => \y =>
                        let
                          gg = sym $ p.eqBwd x (transport c.response (sym $ p.eqFwd x) y)
                          in Calc $
                          |~ f.bwd x y
                          ~~ f.bwd x (transport c.response (sym (p.eqFwd x) `trans` p.eqFwd x) y)
                              ..<(cong (f.bwd x) (applyTransport ? ?))
                          ~~ f.bwd x (transport c.response (p.eqFwd x) (transport c.response (sym (p.eqFwd x)) y))
                              ..<(congDep (f.bwd x) $ transportCompose c.response y)
                          ~~ h.bwd (<+ x) (transport c.response (sym (p.eqFwd x)) y)
                              ...(gg)
                          ~~ h.bwd (<+ x)
                                   (transport c.response (app (funExt (\vx => sym (p.eqFwd vx))) x) y)
                            ...(cong (h.bwd (<+ x)) $ transpUIP c.response y)
           (+> x) => \y => let
                              qq = sym $ q.eqBwd x (transport c.response (sym $ q.eqFwd x) y)
                            in Calc $
                            |~ g.bwd x y
                            ~~ g.bwd x (transport c.response (sym (q .eqFwd x) `trans` q.eqFwd x) y)
                               ..<(cong (g.bwd x) (applyTransport ? ?))
                            ~~ g.bwd x (transport (c .response) (q .eqFwd x) (transport (c .response) (sym (q .eqFwd x)) y))
                               ..<(cong (g.bwd x) (transportCompose c.response y))
                            ~~ h.bwd ((+>) x) (transport (c .response) (sym (q .eqFwd x)) y)
                               ...(qq)
                            ~~ h.bwd ((+>) x) (transport (c .response) (app (funExt (\vy => sym (q .eqFwd vy))) x) y)
                               ...(cong (h.bwd (+> x)) (transpUIP ? ?))
          )
contCoprod : HasProduct (Cont .op)
contCoprod = MkProd
    (+)
    inl
    inr
    (coprod)
    (\n, m => depLensEqToEq $ MkDepLensEq (\_ => Refl) (\_, _ => Refl))
    (\n, m => depLensEqToEq $ MkDepLensEq (\_ => Refl) (\_, _ => Refl))
    (\f, g, p, a, b =>
      depLensEqTrToEq (prfClosed f g p (rewrite sym a in reflexive)
                                       (rewrite sym b in reflexive))
    )

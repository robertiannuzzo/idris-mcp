module Data.Container.ForallSeq.Bifunctor

import Data.Container.Definition
import Data.Container.Category
import Data.Container.ForallSeq.Definition
import Data.Container.Morphism
import Data.Container.Morphism.Eq
import Data.Container.Cartesian
import Data.Container.Cartesian.Category

import Data.Category.Bifunctor

import Data.Iso
import Proofs

import Syntax.PreorderReasoning

%unbound_implicits off
public export
bimapCompBwd :
    {0 a, a', b, b' : Container} ->
    (m1 : a =#> a') -> (m2 : b =%> b') ->
    (x : Ex a b.req) ->
    ((val : a'.res (m1.cfwd x.ex1)) -> b'.res (m2.fwd (x.ex2 ((m1.cbwd x.ex1).to val)))) ->
    (val : a.res x.ex1) ->
    b.res (x.ex2 val)
bimapCompBwd m1 m2 x y z =
  m2.bwd (x.ex2 z) (replace
      {p = b'.res . m2.fwd . x.ex2}
      ((m1.cbwd x.ex1).toFrom z)
      (y ((m1.cbwd x.ex1).from z))
      )
public export
(~▶~) :
    {0 a, a', b, b' : Container} ->
    (a =#> a') -> (b =%> b') ->
    a ▶ b =%> a' ▶ b'
(~▶~) m1 m2 =
    (exBimap (toLens a a' m1) m2.fwd) <!
    (bimapCompBwd m1 m2)
public export
contFunctor :
    {0 a, x, y: Container} ->
    (x =%> y) ->
    a ▶ x =%> a ▶ y
contFunctor = (identity a ~▶~)
public export
0 bimapIdentity :
   (a, b : Container) ->
   (vx : Ex a b.req) ->
   (vy : (val : a.res vx.ex1) -> b.res (vx.ex2 val)) ->
   bimapCompBwd (identity a) (identity b) vx vy ≡ vy
bimapIdentity a b (MkEx x1 x2) vy = funExtDep $ \vx => Refl
%ambiguity_depth 5
public export
0 bimapCompose :
    {0 a, a', b, b', c, c' : Container} ->
    (f : a =#> b) -> (f' : a' =%> b') ->
    (g : b =#> c) -> (g' : b' =%> c') ->
    (x : Ex a (a' .req)) ->
    (y : (val : c.res (g.cfwd (f.cfwd x.ex1))) ->
        c'.res (g'.fwd (f'.fwd (x.ex2 ((f.cbwd x.ex1).to ((g.cbwd (f.cfwd x.ex1)).to val)))))) ->
    (z : a .res x.ex1) ->
    bimapCompBwd (f |#> g) (f' |%> g') x y z ===
    bimapCompBwd f f' x (bimapCompBwd g g' (exBimap (toLens _ _ f) f'.fwd x) y) z
bimapCompose
    (MkCartDepLens f1 f2)
    (f1' <! f2')
    (MkCartDepLens g1 g2)
    (g1' <! g2')
    (MkEx x1 x2) y z = rewrite (f2 x1).toFrom z in Refl
public export
0 preservesComposition :
    {0 a, a', b, b', c, c' : Container} ->
    (f : a =#> b) -> (f' : a' =%> b') ->
    (g : b =#> c) -> (g' : b' =%> c') ->
    ((f |#> g) ~▶~ (f' |%> g')) ≡
    (f ~▶~ f') |%> (g ~▶~ g')
preservesComposition f f' g g' = depLensEqToEq $ MkDepLensEq
    (\x => exEqToEqRw $ MkExEqRw (cartFwdEq f g x)
        (\y => cong (g'.fwd . f'.fwd . x.ex2) (cartBwdEq f g x y)))
    (\x : Ex a a'.req =>
     \y : ((val : c.res (g.cfwd (f.cfwd x.ex1))) ->
          c'.res (g'.fwd (f'.fwd (x.ex2 ((f.cbwd x.ex1).to ((g.cbwd (f.cfwd x.ex1)).to val))))))
          => funExtDep $ \z =>
           Calc $
            |~ bwd ((f |#> g) ~▶~ (f' |%> g')) x y z
            ~= bimapCompBwd (f |#> g) (f' |%> g') x y z
            ~~ bimapCompBwd f f' x (bimapCompBwd g g' (exBimap (toLens _ _ f) f'.fwd x) y) z
               ...(bimapCompose f f' g g' x y z)
            ~= (f ~▶~ f').bwd x ((g ~▶~ g').bwd (exBimap (toLens _ _ f) f'.fwd x) y) z
            ~= (f ~▶~ f').bwd x ((g ~▶~ g').bwd ((f ~▶~ f').fwd x) y) z
            ~= ((f ~▶~ f').bwd x . (g ~▶~ g').bwd ((f ~▶~ f').fwd x)) y z
            ~= (\z => (f ~▶~ f').bwd z . (g ~▶~ g').bwd ((f ~▶~ f').fwd z)) x y z
            ~= bwd ((f ~▶~ f') |%> (g ~▶~ g')) x y z
    )
public export
ForallSeqBifunctor : Bifunctor ContCart Cont Cont
ForallSeqBifunctor = MkFunctor
  (uncurry (▶))
  (\x, y, m => m.π1 ~▶~ m.π2)
  (\x => depLensEqToEq $ MkDepLensEq
      (\vx => exEqToEq $ MkExEq Refl (\_ => cong vx.ex2 (applyRefl' ? ?)))
      (\vx, vy => bimapIdentity x.π1 x.π2 vx vy))
  (\a, b, c, f, g => preservesComposition _ _ _ _)

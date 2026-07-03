module Data.Container.Extension.Properties

import Data.Coproduct

import Data.Container.Definition
import Data.Container.Category
import Data.Container.Coproduct
import Data.Container.Product
import Data.Container.Sequence.Definition
import Data.Container.Extension.Definition
import Data.Container.Morphism.Definition

import Data.Category.Bifunctor
import public Data.Category.Functor.Exponential
import Data.Category.NaturalTransformation
import Data.Category.Set
import public Data.Category.Functor.Category

import Proofs
import Syntax.PreorderReasoning

%hide Prelude.Ops.infixl.(*>)
%hide Prelude.(*>)
public export
record ExEq {a : Container} {b : Type} (c1, c2 : Ex a b) where
  constructor MkExEq
  pex1 : c1.ex1 ≡ c2.ex1
  pex2 : (v : a.res c1.ex1) ->
         let 0 b1, b2 : b
             b1 = c1.ex2 v
             b2 = c2.ex2 (transport a.res (pex1) v)
          in b1 ≡ b2

public export
0 exEqToEq : {0 c1, c2 : Ex a b} -> ExEq c1 c2 -> c1 ≡ c2
exEqToEq {c1 = c1@(MkEx _ x2)} {c2 = c2@(MkEx _ y2)} (MkExEq Refl y) =
  cong2Dep MkEx Refl (funExt $ \vy => trans (y vy) (cong y2 (applyRefl ? ?)))

public export
record ExEqRw {a : Container} {b : Type} (c1, c2 : Ex a b) where
  constructor MkExEqRw
  pex1 : c1.ex1 ≡ c2.ex1
  pex2 : (v : a.res c1.ex1) ->
         let 0 b1, b2 : b
             b1 = c1.ex2 v
             b2 = c2.ex2 (rewrite__impl a.res (sym pex1) v)
          in b1 ≡ b2

export
0 exEqToEqRw : {0 c1, c2 : Ex a b} -> ExEqRw c1 c2 -> c1 ≡ c2
exEqToEqRw {c1 = c1@(MkEx _ _)} {c2 = c2@(MkEx _ _)} (MkExEqRw Refl y) = cong2Dep MkEx Refl (funExt y)
public export
exBimap : a =%> a' -> (b -> b') -> Ex a b -> Ex a' b'
exBimap f g x = MkEx (y <- f.fwd x.ex1) | g (x.ex2 (f.bwd x.ex1 y))
public export
ExBifunctor : Bifunctor Cont Set Set
ExBifunctor = MkFunctor
    (uncurry Ex)
    (\x, y, m => exBimap m.π1 m.π2)
    (\v => funExt $ \z => exEqToEq $ MkExEq Refl (\_ => cong z.ex2 (sym $ applyRefl ? ?)))
    (\x, y, (z1 && z2), (f1 && f2), (g1 && g2) => funExt $ \z =>
        exEqToEq $ MkExEq Refl (\_ => cong (g2 . f2 . z.ex2 . f1.bwd z.ex1 . g1.bwd (f1.fwd z.ex1))
                                    $ sym $ applyRefl ? ?))
public export
ExFunctor : Cont ->> (FunctorCat Set Set)
ExFunctor = uncurryFunctor ExBifunctor
public export
exFunctor : Container -> Set ->> Set
exFunctor c = (ExFunctor .mapObj c)
export
inj1 : MkEx v1 v2 ≡ MkEx v1' v2' -> v1 ≡ v1'
inj1 Refl = Refl

export
inj2 : {0 c : Container} -> {0 t : Type} ->
       {0 v1 : c.req} -> {0 v2 : c.res v1 -> t} ->
       {0 v2' : c.res v1 -> t} ->
       (v : MkEx {cont = c} v1 v2 ≡ MkEx {cont = c} v1 v2') -> v2 ≡ v2'
inj2 Refl = Refl

export
exUniq : (x : Ex a b) -> MkEx x.ex1 x.ex2 = x
exUniq (MkEx ex1 ex2) = Refl

public export
ExProj1 :
   (x : Container) ->
   (y : Type) ->
   (v2 : Ex x y) ->
   (v2.ex1 ≡ v2.ex1)
ExProj1 x y v2 = Refl
public export
exFunc :
    {0 a, b : Type} -> {0 c : Container} ->
    (a -> b) -> Ex c a -> Ex c b
exFunc f x = MkEx x.ex1 (f . x.ex2)

||| F is a functor indeed
export
{0 c : Container} -> Functor (Ex c) where
  map f x = exFunc f x

export
exMap : {0 a, a' : Container} -> {0 b : Type} ->
        (f : a.req -> a'.req) ->
        ((x : a.req) -> a'.res (f x) -> a.res x) ->
        Ex a b -> Ex a' b
exMap fwd bwd y = MkEx (z <- fwd y.ex1) | y.ex2 (bwd y.ex1 z)

public export
exMap' : a =%> a' -> Ex a b -> Ex a' b
exMap' x y = MkEx (z <- x.fwd y.ex1) | y.ex2 (x.bwd y.ex1 z)
public export
record ExEqIx {a : Container} {b : Type} (c1, c2 : Ex a b) where
  constructor MkExEqIx
  pex1 : c1.ex1 ≡ c2.ex1
  pex2 : (v : a.res c1.ex1) ->
         let 0 b1, b2 : b
             b1 = c1.ex2 v
             b2 = c2.ex2 (transport a.res (pex1) v)
          in b1 ≡ b2

export
exEqIxToEq : ExEqIx a b -> a ≡ b
exEqIxToEq {a = MkEx _ e2} {b = MkEx _ x2} (MkExEqIx Refl pex2)
  = cong (MkEx _)
    (funExt $ \vx => trans (pex2 vx)
        (cong x2 (applyRefl ? ?))
    )

public export
0 exEta : MkEx (recd.ex1) (\x => recd.ex2 x) = recd
exEta {recd = MkEx r1 r2} = Refl

public export
0 exP1 : MkEx a b === c -> a === c.ex1
exP1 {c = (MkEx ex1 ex2)} Refl = Refl

0 exP2 : {cont : Container} ->
         {c : Ex cont x} ->
         {0 a : cont.req} ->
         {0 b : cont.res a -> x} ->
         (p : MkEx a b === c) -> (v : cont.res a) -> b v === c.ex2 (transport cont.res (exP1 p) v)
exP2 Refl x = cong b (applyRefl' cont.res x)
lensFromExMap : {a, b : Container} ->
   ((v : Type) -> Ex a v -> Ex b v) ->
   a =%> b
lensFromExMap f = (\xv => (f (a.response xv) (MkEx xv id)).ex1) <!
                  (\xv => (f (a.response xv) (MkEx xv id)).ex2)
ExIsFullAndFaithFull : FullyFaithful ExFunctor
ExIsFullAndFaithFull = MkFullFaithful
    (\nt => lensFromExMap nt.component)
    (\x => depLensEqToEq $ MkDepLensEq (\_ => Refl) (\_, _ => Refl))
    (\x, y, (MkNT xc xs) => ntEqToEq $ MkNTEq $ \vx =>
        funExt $ \(MkEx vy vz) => exEqToEq $
        let gg = app (xs vx vx id) (MkEx vy vz)
            qq = app (xs (? .response vy) vx vz) (MkEx vy (\x => x))
            pp = sym $ exP1 gg
            ss = exP1 qq
        in MkExEq
        (trans ss pp)
        (\vy =>
          let vy' = rewrite__impl y.response (sym ss) vy
              pq = exP2 gg vy'
              sq = exP2 qq vy
          in trans sq (cong2Dep (.ex2) Refl (transpUIP ? ?))
        )
    )
public export
exCoprod : Ex (a + b) c -> Ex a c + Ex b c
exCoprod (MkEx (<+ x) ex2) = <+ MkEx x ex2
exCoprod (MkEx (+> x) ex2) = +> MkEx x ex2
public export
exCompose : Ex (a ▷ b) c -> Ex a (Ex b c)
exCompose x = MkEx x.ex1.ex1 (\vx => MkEx (x.ex1.ex2 vx) (x.ex2 . (vx ##)))
public export
exProduct : Ex (a * b) c -> Ex a c * Ex b c
exProduct xx = MkEx xx.ex1.π1 (xx.ex2 . (<+)) && MkEx xx.ex1.π2 (xx.ex2 . (+>))

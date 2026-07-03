module Data.Container.Product

import Data.Container.Definition
import Data.Container.Category

import Data.Category.Product
import Data.Category.Bifunctor
import Data.Category.Notation
import Data.Category.Monoid
import Data.Category.NaturalTransformation

import Data.Coproduct
import Data.Product

import Proofs


public export
(*) : (c1, c2 : Container) -> Container
(*) c1 c2 = (x : c1.req * c2.req) !> c1.res x.π1 + c2.res x.π2
public export
(~*~) : a =%> a' -> b =%> b' -> a * b =%> a' * b'
(~*~) m1 m2 =
    (bimap m1.fwd m2.fwd) <!
    (\x => bimap (m1.bwd x.π1) (m2.bwd x.π2))
public export
ProductBifunctor : Bifunctor Cont Cont Cont
ProductBifunctor = MkFunctor
    (uncurry (*))
    (\_, _ => uncurry (~*~))
    (\(x && y) => depLensEqToEq $ MkDepLensEq
        (\z => projIdentity z)
        (\z => bifunctorId')
    )
    (\(x1 && x2), (y1 && y2), (z1 && z2), (m1 && m2), (n1 && n2) =>
      depLensEqToEq $ MkDepLensEq
        (\(vx && vy) => Refl)
        (\(vz && vy), vz => bimapCompose vz)
    )
proj1 : {0 c1, c2 : Container} -> (c1 * c2) =%> c1
proj1 = π1 <! (\x => (<+))

proj2 : {0 c1, c2 : Container} -> (c1 * c2) =%> c2
proj2 = π2 <! (\x => (+>))
contProd : c =%> a -> c =%> b -> c =%> a * b
contProd x y = (\v => x.fwd v && y.fwd v) <!
               (\v => choice (x.bwd v) (y.bwd v))
mkMorphismInjL : a <! b = c <! d -> a = c
mkMorphismInjL Refl = Refl

mkMorphismInjR : a <! b = a <! d -> b = d
mkMorphismInjR Refl = Refl

mkMorphismPrf : {x : Type} -> {x' : x -> Type} ->
                {y : Type} -> {y' : y -> Type} ->
                {w : Type} -> {w' : w -> Type} ->
                {z : Type} -> {z' : z -> Type} ->
                {a : x -> y} -> {c : (v : x) -> y' (a v) -> x' v} ->
                {b : w -> z} -> {d : (v : w) -> z' (b v) -> w' v} ->
                a ~=~ b -> c ~=~ d ->
                the ((!>) x x' =%> (!>) y y') (a <! c) ~=~ the ((!>) w w' =%> (!>) z z') (b <! d)

mkMorphismInj : {a, b : Container} ->
                {f1 : a.req -> b.req} -> {b1 : (v : a.req) -> b.res (f1 v) -> a.res v} ->
                {f2 : a.req -> b.req} -> {b2 : (v : a.req) -> b.res (f2 v) -> a.res v} ->
                the (a =%> b) (f1 <! b1) ===
                the (a =%> b) (f2 <! b2) ->
                (prf : f1 === f2 ** (rewrite sym prf in b1) === b2)
mkMorphismInj Refl = (Refl ** Refl)
0 contProdUniq : {0 a, b, c : Container} ->
               (f1 : c =%> a) ->
               (f2 : c =%> b) ->
               (p : c =%> a * b) ->
               p |%> proj1 {c1 = a, c2 = b} = f1 -> p |%> proj2 {c1 = a, c2 = b} = f2 -> contProd {a} {b} {c} f1 f2 = p
-- Proof in appendix
contProdUniq
  (g1 <! s1) (g2 <! s2)  (fwd <! bwd)
  prf1 prf2 =
  let p1 : (\x => (fwd x).π1) === g1
      p1 = mkMorphismInjL prf1
      p1' : (x : c.req) -> (fwd x).π1 === g1 x
      p1' x = rewrite sym p1 in Refl
      p2 : (\x => (fwd x).π2) === g2
      p2 = mkMorphismInjL prf2
      p2' : (x : c.req) -> (fwd x).π2 = g2 x
      p2' x = rewrite sym p2 in Refl
      p3 :  (x : c.req) -> (fwd x).π1 && (fwd x).π2 = (fwd x)
      p3 v = projIdentity (fwd v)
      0 p4 : (\x => (fwd x).π1 && (fwd x).π2) === fwd
      p4 = funExt p3
      sprf1 : (\z, x => bwd z ((<+) (rewrite (p1' z) in x))) === s1
      sprf1 = let (Refl ** v) =  (mkMorphismInj prf1) in v
      sprf2 : (\z, x => bwd z ((+>) (rewrite p2' z in x))) === s2
      sprf2 = let (Refl ** v) =  (mkMorphismInj prf2) in v

  in rewrite sym p1
  in rewrite sym p2
  in rewrite p4
  in cong (fwd <!) $
      funExt2Dep {b = \x => a .res ((fwd x).π1) + b .res ((fwd x).π2)} {c = c.res} $ \x, y =>
          case y of
               (+> v) => rewrite sym sprf2 in Refl
               (<+ v) => rewrite sym sprf1 in Refl
ContProd : HasProduct Cont
ContProd = MkProd
  (*)
  proj1
  proj2
  contProd
  (\(m1 <! m1'), m2 => Refl)
  (\m1, (m2 <! m2') => Refl)
  contProdUniq
public export
assoc1 : a * (b * c) =%> (a * b) * c
assoc1 = Product.assocR <! (\x => Coproduct.assocR)


public export
alpha1 : let f1, f2 : (Cont × (Cont × Cont)) ->>  Cont
             f1 = ((idF Cont) `pair` ProductBifunctor) ⨾⨾ ProductBifunctor
             f2 = assocR {a = Cont, b = Cont, c = Cont} ⨾⨾ ((ProductBifunctor `pair` idF Cont) ⨾⨾ ProductBifunctor)
         in f1 =>> f2
alpha1 = MkNT (\_ => assoc1)
  (\(x1 && (x2 && x3)), (y1 && (y2 && y3)), (m1 && (m2 && m3)) =>
      depLensEqToEq $ MkDepLensEq (\(w1 && (q && w2)) => Refl)
          (\(w1 && (q && w2)) =>
              \case (<+ <+ x) => Refl
                    (<+ +> x) => Refl
                    (+> x) => Refl
          )
  )

public export
assoc2 : (a * b) * c =%> a * (b * c)
assoc2 = Product.assocL <! (\x => Coproduct.assocL)


public export
alpha2 : let f1, f2 : (Cont × (Cont × Cont)) ->> Cont
             f1 = ((idF Cont) `pair` ProductBifunctor) ⨾⨾ ProductBifunctor
             f2 = assocR {a = Cont, b = Cont, c = Cont} ⨾⨾ ((ProductBifunctor `pair` idF Cont) ⨾⨾ ProductBifunctor)
         in f2 =>> f1
alpha2 = MkNT
    (\_ => assoc2)
    (\(x1 && (x2 && x3)), (y1 && (y2 && y3)), (m1 && (m2 && m3)) =>
        depLensEqToEq $ MkDepLensEq (\((w1 && q) && w2) => Refl)
            (\((w1 && q) && w2) =>
                \case (<+ x) => Refl
                      (+> +> x) => Refl
                      (+> <+x) => Refl
            )
    )

public export
alpha : let f1, f2 : (Cont × (Cont × Cont)) ->> Cont
            f1 = ((idF Cont) `pair` ProductBifunctor) ⨾⨾ ProductBifunctor
            f2 = assocR {a = Cont, b = Cont, c = Cont} ⨾⨾ ((ProductBifunctor `pair` idF Cont) ⨾⨾ ProductBifunctor)
        in f1 =~= f2
alpha = MkNaturalIsomorphism
    alpha1
    alpha2
    (\v => depLensEqToEq $ MkDepLensEq (\(a && (b && c)) => Refl) (\x, y => assocLRL y))
    (\v => depLensEqToEq $ MkDepLensEq (\((a && b) && c) => Refl) (\x, y => assocRLR y))

public export
unitL : One * a =%> a
unitL = π2 <! (\_ => (+>))

public export
leftUnitor1 :
    let 0 leftAppliedMult : Cont ->> Cont
        leftAppliedMult = applyL {a = Cont, b = Cont, c = Cont} One ProductBifunctor
    in leftAppliedMult =>> idF Cont
leftUnitor1 = MkNT
  (\_ => unitL)
  (\x, y, m => Refl)


public export
unitL' : a =%> One * a
unitL' = (() &&) <! (\x => getRight)

public export
leftUnitor2 :
    let 0 leftAppliedMult : Cont ->> Cont
        leftAppliedMult = applyL {a = Cont, b = Cont, c = Cont} One ProductBifunctor
    in idF Cont =>> leftAppliedMult
leftUnitor2 = MkNT
  (\_ => unitL')
  (\x, y, m => depLensEqToEq $ MkDepLensEq
      (\_ => Refl)
      (\_ => \case (<+ x) => absurd x
                   (+> x) => Refl))

public export
leftUnitor :
    let 0 leftAppliedMult : Cont ->> Cont
        leftAppliedMult = applyL {a = Cont, b = Cont, c = Cont} One ProductBifunctor
    in leftAppliedMult =~= idF Cont
leftUnitor = MkNaturalIsomorphism
  leftUnitor1
  leftUnitor2
  (\v => depLensEqToEq $ MkDepLensEq
      (\(() && a) => Refl)
      (\x => \case (<+ y) => void y
                   (+> y) => Refl
      )
  )
  (\v => Refl)

public export
unitR : a * One =%> a
unitR = π1 <! (\_ => (<+))


public export
unitR' : a =%> a * One
unitR' = (&& ()) <! (\_ => getLeft)

public export
rightUnitor1 :
    let 0 rightAppliedMult : Cont ->> Cont
        rightAppliedMult = applyR {a = Cont, b = Cont, c = Cont} One ProductBifunctor
    in rightAppliedMult =>> idF Cont
rightUnitor1 = MkNT
  (\_ => unitR)
  (\x, y, m => Refl)

public export
rightUnitor2 :
    let 0 rightAppliedMult : Cont ->> Cont
        rightAppliedMult = applyR {a = Cont, b = Cont, c = Cont} One ProductBifunctor
    in idF Cont =>> rightAppliedMult
rightUnitor2 = MkNT
  (\_ => unitR')
  (\x, y, m => depLensEqToEq $ MkDepLensEq
      (\_ => Refl)
      (\_ => \case (<+ z) => Refl
                   (+> z) => void z)
  )

-- apply unit to the right
public export
rightUnitor :
    let 0 rightAppliedMult : Cont ->> Cont
        rightAppliedMult = applyR {a = Cont, b = Cont, c = Cont} One ProductBifunctor
    in rightAppliedMult =~= idF Cont
rightUnitor = MkNaturalIsomorphism
  rightUnitor1
  rightUnitor2
  (\v => depLensEqToEq $ MkDepLensEq
      (\(a && ()) => Refl)
      (\y => \case (<+ x) => Refl
                   (+> x) => void x))
  (\v => Refl)
public export
CartesianMonoidal : Monoidal Cont
CartesianMonoidal = MkMonoidal
    ProductBifunctor
    One
    alpha
    leftUnitor
    rightUnitor

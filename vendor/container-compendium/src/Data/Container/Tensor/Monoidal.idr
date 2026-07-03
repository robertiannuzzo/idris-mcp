module Data.Container.Tensor.Monoidal

import Data.Category.Functor
import Data.Category.Bifunctor
import Data.Category.Product
import Data.Category.ProductCat
import Data.Category.Monoid
import Data.Category.NaturalTransformation

import Data.Container.Category
import Data.Container.Extension.Definition
import Data.Container.Extension.Properties
import Data.Container.Tensor.Definition
import Data.Container.Tensor.Bifunctor

public export
unitL : I ⊗ a =%> a
unitL = π2 <! (\_ => (() &&))

public export
unitR : a ⊗ I =%> a
unitR = π1 <! (\_ => (&&()))
public export
TensorMonoidal : Monoidal Cont
TensorMonoidal = MkMonoidal
    TensorBifunctor
    I
    alpha
    leftUnit
    rightUnit
  where
  alpha : let f1, f2 : (Cont × (Cont × Cont)) ->> Cont
              f1 = ((idF Cont) `pair` TensorBifunctor) ⨾⨾ TensorBifunctor
              f2 = assocR {a = Cont, b = Cont, c = Cont}
                   ⨾⨾ ((TensorBifunctor `pair` idF Cont) ⨾⨾ TensorBifunctor)
          in f1 =~= f2
  alpha = MkNaturalIsomorphism
        (MkNT
            (\v => assocR <! (\x, y => assocL y))
            (\a, b, m => Refl))
        (MkNT
            (\v => assocL <! (\x, y => assocR y))
            (\_,_,_ => Refl))
        (\v => cong2Dep
                 (<!)
                 (funExt $ \(a && (b && c)) => Refl)
                 (funExtDep $ \v => funExt $ \(g1 && (g2 && g3)) => Refl))
        (\v => cong2Dep
                 (<!)
                 (funExt $ \((x1 && x2) && x3) => Refl)
                 (funExtDep $ \v => funExt $ \((x1 && x2) && x3) => Refl))
  leftUnit : (Bifunctor.unitL ⨾⨾
             (Const I Cont `pair` idF Cont) ⨾⨾
              TensorBifunctor)
              =~= idF Cont
  leftUnit = MkNaturalIsomorphism
        (MkNT
          (\_ => unitL)
          (\_,_,_ => Refl))
        (MkNT
          (\_ =>
            (MkUnit &&) <! (\_ => π2))
          (\_,_,_ => Refl))
        (\c => cong2Dep
          (<!)
          (funExt $ \(() && a) => Refl)
          (funExtDep $ \x => funExt $ \(() && b) => Refl))
        (\_ => Refl)
  rightUnit : (Bifunctor.unitR ⨾⨾
              (idF Cont `pair` Const I Cont) ⨾⨾
               TensorBifunctor)
               =~= idF Cont
  rightUnit = MkNaturalIsomorphism
      (MkNT
        (\v => unitR)
        (\a, b, m => Refl))
      (MkNT
        (\v => (&& ()) <! (\_ => π1))
        (\_,_,_ => Refl))
      (\v => cong2Dep
        (<!)
        (funExt $ \(x1 && ()) => Refl)
        (funExtDep $ \v => funExt $ \(w && ()) => Refl))
      (\_ => Refl)
export %hint
ApplicativeFromMonoid :
  (m : MonoidObject {o = Container, cat = Cont} TensorMonoidal) => Applicative (Ex m.obj)
ApplicativeFromMonoid {m }
  = MkApplicative
    (\x => MkEx (m.η.fwd ()) (const x))
    (\(MkEx lf1 lf2), (MkEx lx1 lx2) =>
         MkEx (m.mult.fwd (lf1 && lx1))
           (\z => let ff = m.mult.bwd (lf1 && lx1) z
                  in lf2 ff.π1 (lx2 ff.π2)))

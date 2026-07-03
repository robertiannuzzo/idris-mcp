module Data.Container.Cartesian.Tensor.Monoidal


import Data.Product
import Data.Category
import Data.Category.Bifunctor as Bi
import Data.Category.Endofunctor
import Data.Category.Monoid
import Data.Category.Product
import Data.Category.NaturalTransformation
import Data.Iso

import Data.Container
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Tensor.Definition
import Data.Container.Cartesian.Tensor.Bifunctor

import Proofs.Product

%default total

%unbound_implicits off
-- associator (a * (b * c)) -> ((a * b) * c)
public export
assoc1 : (0 a, b, c : Container) ->
         a ⊗ (b ⊗ c) =#> (a ⊗ b) ⊗ c
assoc1 a b c = MkCartDepLens
  assocR
  (\_ => symIso assocIso)

public export
alpha1 : let f1, f2 : (ContCart × (ContCart × ContCart)) ->> ContCart
             f1 = ((idF ContCart) `pair` TensorBifunctorCart) ⨾⨾ TensorBifunctorCart
             f2 = Bi.assocR {a = ContCart, b = ContCart, c = ContCart}
                 ⨾⨾ ((Bi.pair TensorBifunctorCart (idF ContCart)) ⨾⨾ TensorBifunctorCart)
         in f1 =>> f2
alpha1 = MkNT
  (\(x && (y && z)) => assoc1 x y z)
  (\(x1 && (x2 && x3)), (y1 && (y2 && y3)), (m1 && (m2 && m3)) =>
     cartEqToEq $ MkCartDepLensEq
         (\_ => Refl)
         (\(z1 && (z2 && z3)) => MkIsoEq (\_ => Refl) (\_ => Refl))
  )

-- associator ((a * b) * c) -> (a * (b * c))
public export
assoc2 : (0 a, b, c : Container) ->
         (a ⊗ b) ⊗ c =#> a ⊗ (b ⊗ c)
assoc2 a b c
    = MkCartDepLens assocL (\_ => assocIso)

public export
alpha2 : let f1, f2 : (ContCart × (ContCart × ContCart)) ->> ContCart
             f1 = ((idF ContCart) `pair` TensorBifunctorCart) ⨾⨾ TensorBifunctorCart
             f2 = Bi.assocR {a = ContCart, b = ContCart, c = ContCart}
                 ⨾⨾ ((Bi.pair TensorBifunctorCart (idF ContCart)) ⨾⨾ TensorBifunctorCart)
         in f2 =>> f1
alpha2 = MkNT
  (\(x && (y && z)) => assoc2 x y z)
  (\(x1 && (x2 && x3)), (y1 && (y2 && y3)), (m1 && (m2 && m3)) =>
    cartEqToEq $ MkCartDepLensEq
        (\_ => Refl)
        (\((z1 && z2) && z3) => MkIsoEq (\_ => Refl) (\_ => Refl))
  )

public export
alpha : let f1, f2 : (ContCart × (ContCart × ContCart)) ->> ContCart
            f1 = ((idF ContCart) `pair` TensorBifunctorCart) ⨾⨾ TensorBifunctorCart
            f2 = Bi.assocR {a = ContCart, b = ContCart, c = ContCart}
                ⨾⨾ ((Bi.pair TensorBifunctorCart (idF ContCart)) ⨾⨾ TensorBifunctorCart)
        in f1 =~= f2
alpha = MkNaturalIsomorphism
    alpha1
    alpha2
    (\(x1 && (x2 && x3)) => cartEqToEq $ MkCartDepLensEq
        (\(y1 && (y2 && y3)) => Refl)
        (\(y1 && (y2 && y3)) => MkIsoEq
            (\(z1 && (z2 && z3)) => Refl)
            (\(z1 && (z2 && z3)) => Refl)
        )
    )
    (\(x1 && (x2 && x3)) => cartEqToEq $ MkCartDepLensEq
        (\((y1 && y2) && y3) => Refl)
        (\((y1 && y2) && y3) => MkIsoEq
            (\((z1 && z2) && z3) => Refl)
            (\((z1 && z2) && z3) => Refl)
        )
    )

-- Left unitor (I * a) -> a

public export
unitL : (0 a : Container) -> I ⊗ a =#> a
unitL a = MkCartDepLens π2 (\_ => symIso leftUnitIso)

public export
pureL : (0 a : Container) -> a =#> I ⊗ a
pureL a = MkCartDepLens (() &&) (\_ => leftUnitIso)

public export
leftUnitor :
    let leftAppliedMult : Endo ContCart
        leftAppliedMult = applyL {a = ContCart, b = ContCart, c = ContCart} I TensorBifunctorCart
    in leftAppliedMult =~= idF ContCart
leftUnitor = MkNaturalIsomorphism
    (MkNT
        (\x => unitL x)
        (\x, y, m => cartEqToEq $ MkCartDepLensEq
            (\_ => Refl) (\(() && w) => MkIsoEq (\_ => Refl) (\_ => Refl))
        )
    )
    (MkNT
        (\x => pureL x)
        (\x, y, m => cartEqToEq $ MkCartDepLensEq
            (\_ => Refl)
            (\w => MkIsoEq (\(() && q) => Refl) (\_ => Refl))
        )
    )
    (\x => cartEqToEq $ MkCartDepLensEq
        (\(() && a) => Refl)
        (\x => MkIsoEq (\(() && w) => Refl) (\(() && w) => Refl) )
    )
    (\x => cartEqToEq $ MkCartDepLensEq
        (\_ => Refl)
        (\_ => reflIsoEq)
    )
-- right unitor (a * I) -> a

public export
unitR : (0 a : Container) -> a ⊗ I =#> a
unitR a = MkCartDepLens π1 (\_ => symIso rightUnitIso)

public export
pureR : (0 a : Container) -> a =#> a ⊗ I
pureR a = MkCartDepLens (&& ()) (\_ => rightUnitIso)

-- apply unit to the right
public export
rightUnitor :
    let rightAppliedMult : Endo ContCart
        rightAppliedMult = applyR {a = ContCart, b = ContCart} I TensorBifunctorCart
    in rightAppliedMult =~= idF ContCart
rightUnitor = MkNaturalIsomorphism
    (MkNT
        (\x => unitR x)
        (\x, y, m => cartEqToEq $ MkCartDepLensEq
            (\_ => Refl)
            (\_ => MkIsoEq (\_ => Refl) (\_ => Refl) )
        )
    )
    (MkNT
        (\x => pureR x)
        (\x, y, m => cartEqToEq $ MkCartDepLensEq
            (\_ => Refl)
            (\_ => MkIsoEq (\_ => Refl) (\_ => Refl) )
        )
    )
    (\x => cartEqToEq $ MkCartDepLensEq
        (\(a && ()) => Refl)
        (\(a && ()) => MkIsoEq (\(b && ()) => Refl) (\(b && ()) => Refl))
    )
    (\x => cartEqToEq $ MkCartDepLensEq
        (\_ => Refl)
        (\_ => MkIsoEq (\_ => Refl) (\_ => Refl))
    )
public export
ContCartMonoidal : Monoidal ContCart
ContCartMonoidal = MkMonoidal
    TensorBifunctorCart
    I
    alpha
    leftUnitor
    rightUnitor

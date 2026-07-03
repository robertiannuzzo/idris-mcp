module Data.Container.Cartesian.Tensor.Product

import Data.Container.Definition
import Data.Iso
import Data.DPair
import Data.Sigma
import Data.Product

record CommutativeMonoid where
  constructor MkCMon
  a : Type
  empty : a
  plus : a -> a -> a
  sym : (x, y : a) -> plus x y === plus y x

(*) : CommutativeMonoid -> CommutativeMonoid -> CommutativeMonoid
(*) m1 m2 = MkCMon (m1.a * m2.a) (m1.empty && m2.empty) (\x, y => m1.plus x.π1 y.π1 && m2.plus x.π2 y.π2)
    (\x, y => let gg = m1.sym x.π1 y.π1 in cong2 (&&) gg (m2.sym x.π2 y.π2))

-- commutative monoid homomorphism
-- record CMonHom (c1, c2 : CommutativeMonoid) where
--   constructor MkCMonHom
--   mapCarrier : c1.a -> c2.a
--   presEmpty : mapCarrier c1.empty === c2.empty
--   presPlus : {x, y : c1.a} -> c2.plus (mapCarrier x) (mapCarrier y) === mapCarrier (c1.plus x y)

record EContainer where
  constructor (!>)
  shape : Type
  pos : shape -> CommutativeMonoid

(=&>) : EContainer -> EContainer -> Type
(=&>) c1 c2 = (x : c1.shape) -> Σ (y : c2.shape) | (c2.pos y) .a -> (c1.pos x).a

(=#>) : EContainer -> EContainer -> Type
(=#>) c1 c2 = (x : c1.shape) -> Σ (y : c2.shape) | (c2.pos y).a ≅ (c1.pos x).a

(⊗) : EContainer -> EContainer -> EContainer
(⊗) x y = (base : x.shape * y.shape) !> (x.pos base.π1 * y.pos base.π2)

fst : {a, b : _} -> a ⊗ b =#> a
fst (x1 && x2) = x1 ## MkIso
    (\y => y && (b.pos x2).empty )
    π1
    (\(x1' && x2') => cong2 (&&) Refl ?cc) -- impossible
    (\_ => Refl)


module Data.Container.Closed.List.Monoid

import Data.Container.Closed
import Data.Container.Closed.Category
import Data.Container.Closed.Tensor.Bifunctor
import Data.Container.Closed.Tensor.Monoidal
import Data.Container.List.Desc
import Data.Container.Tensor.Definition

import Data.Category.Monoid

import Data.Fin
import Data.Coproduct

public export
neutral : I =&> ListCont
neutral = !! \x => 1 ## const ()

public export
splitFinPlus : (m, n : Nat) ->  Fin (m + n) -> Fin m + Fin n
splitFinPlus 0 n z = +> z
splitFinPlus (S k) n FZ = <+ FZ
splitFinPlus (S k) n (FS x) = mapFst FS (splitFinPlus k n x)

public export
splitFin : (m, n : Nat) ->  Fin (m * n) -> Fin m * Fin n
splitFin 0 n x = absurd x
splitFin (S k) n x =
  case splitFinPlus ? ? x of
      <+ n' => FZ && n'
      +> m => mapFst FS (splitFin ? ? m)

public export
mult : ListCont ⊗ ListCont =&> ListCont
mult = !! \x => x.π1 * x.π2 ## splitFin ? ?

left : let 0 η_id_μ, λ : I ⊗ ListCont =&> ListCont
           0 topMorphism : I ⊗ ListCont =&> ListCont ⊗ ListCont
           topMorphism = neutral ~⊗~ Cont .id ListCont
           η_id_μ = topMorphism |&> mult
           λ = TensorMonoidal .leftUnitor.nat.component ListCont
        in η_id_μ === λ
left = ?left_rhs

right : let 0 id_η_μ, ρ : ListCont ⊗ I =&> ListCont
            0 topMorphism : ListCont ⊗ I  =&> ListCont ⊗ ListCont
            topMorphism = Cont .id ListCont ~⊗~ neutral
            id_η_μ = topMorphism |&> mult
            ρ  = TensorMonoidal .rightUnitor.nat.component ListCont
         in id_η_μ === ρ

assoc : let
            0 botLeft : (ListCont ⊗ ListCont) ⊗ ListCont =&> ListCont
            botLeft = mult ~⊗~ Cont .id ListCont |&> mult
            0 assoc : ((ListCont ⊗ ListCont) ⊗ ListCont) =&> ListCont ⊗ (ListCont ⊗ ListCont)
            assoc = TensorMonoidal .alpha.tan.component (ListCont && (ListCont && ListCont))
            0 topRight : ((ListCont ⊗ ListCont) ⊗ ListCont) =&> ListCont
            topRight = assoc |&> Cont .id ListCont ~⊗~ mult |&> mult
        in botLeft === topRight

ListMonoidTensor :
    MonoidObject {o = Container} {cat = Cont} TensorMonoidal
ListMonoidTensor = MkMonObj
    ListCont
    neutral
    mult
    left
    right
    assoc


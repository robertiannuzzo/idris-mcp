module Data.Container.General.Tensor

import Data.Category.Monoid

import Data.Container.General
import Data.Container.Tensor.Definition
import Data.Container.Definition

import Data.Product

%hide Prelude.(|>)
%hide Prelude.(*)

record CartesianBimap (cat : Category Type) where
  bimap : {0 a, a', b, b' : Type} -> a ~> a' -> b ~> b' -> a * b ~> a' * b'
  bimapId : {0 a, b : Type} ->
            bimap {a, a' = a, b, b' = b} (cat.id a) (cat.id b) === cat.id (a * b)
  bimapComp : {0 a, b, c : Type} ->
              {0 a', b', c' : Type} ->
              {0 f : a ~> b} ->
              {0 g : b ~> c} ->
              {0 f' : a' ~> b'} ->
              {0 g' : b' ~> c'} ->
              bimap {a, b = a', a' = c, b' = c'}
              ((f |> g) {a, b, c}) ((f' |> g'){a = a', b = b', c = c'})
                ≡ (bimap {a = a, a' = b, b = a', b' = b'} f f'
                |> bimap {a = b, a' = c, b = b', b' = c'} g g')
                    {a = a * a', b = b * b' , c = c * c'}

parameters (cat : Category Type) (cart : CartesianBimap cat)

  Poly : Category Container
  Poly = GeneralDLensCat cat

  private infixl 0 =^>
  public export
  (=^>) : Container -> Container -> Type
  (=^>) a b = GeneralDLens cat a b

  tensorBimap : {a, b, a', b' : _} -> a =^> a' -> b =^> b' -> a ⊗ b =^> a' ⊗ b'
  tensorBimap (!~ g) (!~ f) = !~ \x => ((g x.π1).π1 && (f x.π2).π1)
                              ## cart.bimap (g x.π1).π2 (f x.π2).π2

  0
  presId :
    (v : Container * Container) ->
      tensorBimap
        (generalIdentity cat {c = v.π1})
        (generalIdentity cat {c = v.π2})
      = (generalIdentity cat {c = v.π1 ⊗ v.π2})
  presId v = gdeqToEq $ MkGDLEq $ \(x1 && x2) =>
             MkSigEqS (cong Σ.(.π1) $ let gfg = cart.bimapId in ?ad) ?presId_rhs

  tensorBifunctor : Bifunctor Poly Poly Poly
  tensorBifunctor = MkFunctor
    (uncurry (⊗))
    (\a, b, f => tensorBimap f.π1 f.π2)
    presId
    ?tensorBifunctor_rhs3


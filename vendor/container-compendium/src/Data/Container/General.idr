module Data.Container.General

import Data.Category
import Data.Container
import Data.Category.Set
import Data.Category.Iso
import Data.Category.Functor
import Proofs.Transport
import Proofs.Sigma

%hide Prelude.Ops.infixl.(|>)
%hide Prelude.(|>)


export prefix 0 !~
record GeneralDLens (bwd : Category Type) (c1, c2 : Container) where
  constructor (!~)
  fn : (x : c1.request) -> Σ (y : c2.request) | (c1.response x) ~> c2.response y

record GeneralDLensEq (a, b : GeneralDLens cat c1 c2) where
  constructor MkGDLEq
  eq : (x : c1.request) -> SigEqS (a.fn x) (b.fn x)

public export
0 gdeqToEq : GeneralDLensEq a b -> a === b
gdeqToEq {a = !~ a} {b = !~ b} (MkGDLEq eq) = cong (!~) $ funExtDep $ \z => sigEqToEqS (eq z)

export infixl 0 =^>
parameters (cat : Category Type)

  public export
  (=^>) : Container -> Container -> Type
  (=^>) a b = GeneralDLens cat a b

  public export
  generalComposition : {a, b, c : Container} -> a =^> b -> b =^> c -> a =^> c
  generalComposition x y = !~ \z =>
                           let xx : ?
                               xx = x.fn z
                               yy : ?
                               yy = y.fn xx.π1
                           in yy.π1 ## (xx.π2 |> yy.π2)

  public export
  generalIdentity : {c : Container} -> c =^> c
  generalIdentity = !~ \x => x ## cat.id (c.response x)

  public export
  GeneralDLensCat : Category Container
  GeneralDLensCat = MkCategory
    (=^>)
    (\_ => generalIdentity)
    generalComposition
    (\a, b, f => gdeqToEq $ MkGDLEq $ \z => MkSigEqS Refl (trans (cat.idRight {}) (sym $ applyRefl ? ?)))
    (\a, b, f => gdeqToEq $ MkGDLEq $ \z => MkSigEqS Refl (trans (cat.idLeft {}) (sym $ applyRefl ? ?)))
    (\a, b, c, d, f, g, h =>
        gdeqToEq $ MkGDLEq $ \z => MkSigEqS Refl (trans (cat.compAssoc {}) (sym $ applyRefl {})))

Chart, DLens, CartLens : (a, b : Container) -> Type
Chart = GeneralDLens Set
DLens = GeneralDLens (Set .op)
CartLens = GeneralDLens IsoCat


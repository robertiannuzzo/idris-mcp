module Data.Category.Design
import Control.Relation

import Data.Product
import Proofs

%unbound_implicits off
typebind
record Σ0 (a : Type) (0 b : a -> Type) where
  constructor (##)
  π1 : a
  π2 : b π1

namespace Ok
  private
  record Cat (obj : Type) where
    constructor MkC
    mor : Rel obj
  --   iden : forall x. mor x x
  --   idl : {0 x, y : obj} -> {0 f : mor x y} -> comp f iden === f
  --   idr : {0 x, y : obj} -> {0 f : mor x y} -> comp iden f === f
  --   ass : {0 x, y, z, w : obj} ->
  --         {0 f : mor x y} -> {0 g : mor y z} -> {0 h : mor z w} ->
  --         comp (comp f g) h === comp f (comp g h)

  private
  (~>) : forall o. (c : Cat o) => Rel o
  (~>) = c.mor

  private infixr 1 ~>

  record Func {0 o1, o2 : Type} (c : Cat o1) (d : Cat o2) where
    constructor MkF
    mapO : o1 -> o2
    mapH : {0 x, y : o1} -> x ~> y -> mapO x ~> mapO y

  %hide (~>)
  %hide Cat

namespace Fail
 failing "Multiple solutions found"
  private
  record Cat where
    constructor MkC
    obj : Type
    mor : Rel obj

  (~>) : (c : Cat ) => Rel c.obj
  (~>) = c.mor

  private infixr 1 ~>

  record Func (c : Cat ) (d : Cat) where
    constructor MkF
    mapO : c.obj -> d.obj
    mapH : {0 x, y : c.obj} -> x ~> y -> mapO x ~> mapO y

namespace Index
 failing "Can't bind implicit"
  record Cat (obj : Type) (mor : Rel obj) where
    [search mor]
    constructor MkC
    iden : forall x. mor x x
    comp : forall x, y, z. (f : mor x y) -> (g : mor y z) -> mor x z
    idl : {0 x, y : obj} -> {0 f : mor x y} -> comp f iden === f
    idr : {0 x, y : obj} -> {0 f : mor x y} -> comp iden f === f
    ass : {0 x, y, z, w : obj} ->
          {0 f : mor x y} -> {0 g : mor y z} -> {0 h : mor z w} ->
          comp (comp f g) h === comp f (comp g h)

  private 0
  (~>) : forall o, m. (c : Cat o m) => Rel o
  (~>) = m

  private infixr 1 ~>

  record Func {0 o1, o2 : Type} {m1 : Rel o1} {m2 : Rel o2} (c : Cat o1 m1) (d : Cat o2 m2) where
    constructor MkF
    mapO : o1 -> o2
    mapH : {0 x, y : o1} -> x ~> y -> mapO x ~> mapO y
  %hide Cat
  %hide Func

namespace Homs
 failing "Multiple solutions"
  record Cat where
    constructor MkCat
    obj : Type
    hom : Type
    dom : hom -> obj
    cod : hom -> obj
    iden : Σ (m : hom) | dom m ≡ cod m
    comp : (f : hom) -> (g : hom) -> Σ (fg : hom) | (cod f ≡ dom g)
                                                  * (dom fg ≡ dom f)
                                                  * (cod fg ≡ cod g)

  (~>) : (c : Cat) => Rel c.obj
  (~>) x y = Σ (h : c.hom) | (c.dom h ≡ x) * (c.cod h ≡ y)

  (|>) : (c : Cat) => {0 x, y, z : c.obj} -> x ~> y -> y ~> z -> x ~> z
  (|>) f g = let cx ## ((cy1 && cy2) && cy3) = c.comp f.π1 g.π1
              in cx ## (trans cy2 f.π2.π1 && trans cy3 g.π2.π2 )

  record Func (c, d : Cat) where
    constructor MkF
    mapO : c.obj -> d.obj
    mapH : {0 x, y : c.obj} -> x ~> y -> mapO x ~> mapO y
  %hide Cat
  %hide Func

%hide Sigma.Σ
%hide Sigma.(##)
namespace HomIndex
  record Cat (0 obj : Type) where
    constructor MkCat
    hom : obj -> Type
    cod : (0 x : obj) -> hom x -> obj
    iden : (0 x : obj) -> Σ0 (m : hom x) | cod x m ≡ x
    comp : (0 x : obj) ->
           (f : hom x) -> -- x ~> y
           (g : hom (cod x f)) -> -- y ~> z
           Σ0 (fg : hom x) | cod x fg ≡ cod (cod x f) g

  (~>) : forall o. (c : Cat o) => Rel o
  (~>) x y = Σ0 (h : c.hom x) | c.cod x h ≡ y

  Id : forall o . (c : Cat o) => (0 x : o) -> Σ0 (m : c.hom x) | c.cod x m ≡ x
  Id = c.iden

  (|>) : forall o. (c : Cat o) => {0 x, y, z : o} -> x ~> y -> y ~> z -> x ~> z
  (|>) f g = let cx ## cy = c.comp x f.π1 ?hdu
              in cx ## ?adad


  record Func {o, p : Type} (c : Cat o) (d : Cat p) where
    constructor MkF
    mapO : o -> p
    mapH : {0 x, y : o} -> x ~> y -> mapO x ~> mapO y

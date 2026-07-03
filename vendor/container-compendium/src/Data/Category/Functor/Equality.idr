module Data.Category.Functor.Equality

-- import Data.Category.Functor
--
-- import Proofs

import Control.Relation

%unbound_implicits off

-- record FunctorEq {o1, o2 : Type}
--   {c : Category o1} {d : Category o2} (f1 , f2 : c ->> d) where
--   constructor MkFuncEq
--   objRel : Rel o2
--   morRel : (x1, x2, y1, y2 : o2) -> objRel x1 x2 -> objRel y1 y2 ->
--            (x1 ~> y1) -> x2 ~> y2 -> Type
--   sameMapObj : (x : o1) -> f1.mapObj x `objRel` f2.mapObj x
--   sameMapHom : (x, y : o1) -> (m : x ~> y) ->
--                morRel (f1.mapObj x) (f1.mapObj y)
--                  (f1.mapHom x y m) (f2.mapHom x y m)
--
-- namespace Ok
--   record Cat (obj : Type) where
--     constructor MkC
--     mor : Rel obj
--   --   iden : forall x. mor x x
--   --   idl : {0 x, y : obj} -> {0 f : mor x y} -> comp f iden === f
--   --   idr : {0 x, y : obj} -> {0 f : mor x y} -> comp iden f === f
--   --   ass : {0 x, y, z, w : obj} ->
--   --         {0 f : mor x y} -> {0 g : mor y z} -> {0 h : mor z w} ->
--   --         comp (comp f g) h === comp f (comp g h)
--
--   private
--   (~>) : (c : Cat o) => Rel o
--   (~>) = c.mor
--
--   private infixr 1 ~>
--
--   record Func (c : Cat o1) (d : Cat o2) where
--     constructor MkF
--     mapO : o1 -> o2
--     mapH : {0 x, y : o1} -> x ~> y -> mapO x ~> mapO y

namespace Fail
 failing "Multiple solutions found"
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


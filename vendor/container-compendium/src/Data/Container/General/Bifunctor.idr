module Data.Container.General.Bifunctor

import Data.Container.General
import Data.Category
import Data.Category.Functor
import Data.Category.Bifunctor
import Data.Container.Definition

parameters (cat : Category Type)

  public export
  (=^>) : Container -> Container -> Type
  (=^>) a b = GeneralDLens cat a b

  public export
  gid : {c : Container} -> c =^> c
  gid = !~ \x => x ## cat.id (c.response x)

  public export
  Lens : Category Container
  Lens = GeneralDLensCat cat

  bifunctor : (F : cat ->> cat2) ->
              (bi : Bifunctor Lens Lens Lens ) ->
              Bifunctor (GeneralDLensCat cat2)(GeneralDLensCat cat2)(GeneralDLensCat cat2)
  bifunctor (MkFunctor fo fm fid fcomp) (MkFunctor bio bim bipid bipcomp) = ?bifunctor_rhs




module Data.Container.Closed.List.Functor

import Data.Container.Closed
import Data.Container.Closed.Category
import Data.Container.Closed.Eq
import Data.Container.Definition
import Data.Container.Sequence.Definition
import Data.Container.List.Desc
import Data.Container.List.Functor
import Data.Container.Extension

import Data.List.Quantifiers

import Data.Category.Functor

import Data.Sigma
import Data.Fin

import Proofs.Transport

%hide Data.Container.List.Functor.Forany

namespace Any
  public export
  mapList : a =&> b -> Any.List a =&> Any.List b

  public export
  ListF : Cont ->> Cont
  ListF = MkFunctor Any.List (\_, _ => mapList) ?bb ?cc

public export
Forany : Container -> Container
Forany = (ListCont ▷)

public export
toAny : Any.List a =&> Forany a
toAny = !! \x => listToTyList x ## toAnyBwd x

public export covering
fromAny : Forany a =&> Any.List a
fromAny = !! \x => tyListToList x ## fromAnyBwd x

-- toFromAnyBwd :
--   {0 a : Container} ->
--   (xs : TyList a.request) ->
--   (x : Σ (ls : Fin ((listToTyList (tyListToList xs)) .ex1)) |
--          (a .response ((listToTyList (tyListToList xs)) .ex2 ls))) ->
--   fromAnyBwd {a} xs (toAnyBwd {a} (tyListToList {x = a.request} xs) x) === x
covering 0
toFromAny : {0 a : Container} ->
            ClosedEq (fromAny {a} |&> toAny {a})
                     (identity (Forany a))
                     SigEq'
toFromAny = MkClsEq $
    \x => MkSigEq'
        (fromTo x)
        (funExt $ ?adoo)


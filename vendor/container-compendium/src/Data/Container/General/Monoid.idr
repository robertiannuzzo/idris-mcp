module Data.Container.General.Monoid

import Data.Category.Monoid
import Data.Category.Bifunctor

import Data.Container.Definition
import Data.Container.Category
import Data.Container.General


parameters (cat : Category Type)
  fromBifunctor : Bendo Set -> (Bendo cat) -> Bendo Cont
  fromBifunctor fwCat bwCat
    = MkFunctor (\x => (y : fwCat.mapObj (x.π1.request && x.π2.request))
                    !> bwCat.mapObj (x.π1.response ?aa && x.π2.response ?qw)
                ) ?bb ?cc ?aiuo

  {-


  GeneralLensMonoidal :
    Bendo (GeneralDLensCat cat) ->
    (neutral : Container) ->
    Monoidal (GeneralDLensCat cat)
  GeneralLensMonoidal mult i =
    MkMonoidal
      mult
      i
      ?ad
      ?ioqw
      ?GeneralLensMonoidal_rhs


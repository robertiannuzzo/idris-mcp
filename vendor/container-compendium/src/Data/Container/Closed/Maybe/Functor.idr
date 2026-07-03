module Data.Container.Closed.Maybe.Functor

import Data.Container.Closed
import Data.Container.Closed.Category
import Data.Container.Closed.Eq
import Data.Container.Definition
import Data.Container.Maybe.Definition

import Data.Category.Endofunctor
import Data.Category.Functor

import Data.Maybe.Monad

import Data.Maybe.Any
import Data.Maybe.All

namespace Any

  public export
  mapMaybe : a =&> b -> Any.Maybe a =&> Any.Maybe b
  mapMaybe m = !! \case Nothing => Nothing ## absurd
                        (Just x) => let xx = m.fn x in Just xx.π1 ## (\v => Aye (xx.π2 v.unwrap))

  export
  unit : Any.Maybe One =&> One
  unit = !! \case Nothing => () ## absurd
                  (Just x) => () ## absurd

  public export
  MaybeF : Endo Cont
  MaybeF = MkFunctor Any.Maybe (\a, b, m => Any.mapMaybe m)
      (\x => clsEqToEq SigEq' sigEqToEq' $ MkClsEq $
                \case Nothing => MkSigEq' Refl (funExt $ \xx => absurd xx)
                      (Just y) => MkSigEq' Refl (funExt $ \(Aye xx) => Refl)
      )
      (\x, y, z, f, g => clsEqToEq SigEq' sigEqToEq' $ MkClsEq $
                        \case Nothing => MkSigEq' Refl (funExt $ \xx => absurd xx)
                              (Just w) => MkSigEq' Refl (funExt $ \(Aye xx) => Refl)
      )

namespace All

  public export
  mapMaybe : a =&> b -> All.Maybe a =&> All.Maybe b
  mapMaybe m = !! \case Nothing => Nothing ## \_ => Nay
                        (Just x) => let xx = m.fn x in Just xx.π1 ## (\v => Yay (xx.π2 v.unwrap))

  export
  unitI : All.Maybe I =&> I
  unitI = !! \case Nothing => () ## \_ => Nay
                   (Just x) => () ## \_ => Yay ()

  export
  unit : All.Maybe One =&> One
  unit = !! \case Nothing => () ## absurd
                  (Just x) => () ## absurd

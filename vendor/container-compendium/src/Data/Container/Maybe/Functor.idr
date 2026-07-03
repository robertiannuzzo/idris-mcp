module Data.Container.Maybe.Functor

import public Data.Container.Category

import Data.Iso
import Data.Iso.Generic
import public Data.Maybe.Any
import public Data.Maybe.All
import Data.Maybe.Monad
import Data.MaybeCoprod
import public Data.Category.Bifunctor
import public Data.Category.Endofunctor

import public Data.Container.Sequence.Definition
import public Data.Container.Coproduct.Definition
import public Data.Container.Coproduct.Bifunctor
import public Data.Container.Cartesian.Category
import public Data.Container.Extension.Definition
import public Data.Container.ForallSeq.Bifunctor
import public Data.Container.Sequence.Bifunctor as Cont
import Data.Container.Maybe.Desc
import public Data.Container.Maybe.Definition
import public Data.Container.Morphism.Eq

import Control.Order
import Syntax.PreorderReasoning.Generic
namespace Any

  public export
  mapMaybe : a =%> b -> Any.Maybe a =%> Any.Maybe b
  mapMaybe x = map x.fwd <! (\y, z => anyFunctorMap x.fwd x.bwd y z)

  public export
  MaybeF : Endo Cont
  MaybeF = MkFunctor Any.Maybe (\_, _ => Any.mapMaybe)
  -- proofs in appendix
      (\x => depLensEqToEq $ MkDepLensEq
          maybeFunctorId
          (\case Nothing => (\case (Aye _) impossible)
                 (Just y) => \(Aye z) => Refl)
      )
      (\x, y, z, f, g => depLensEqToEq $ MkDepLensEq
          (\w => sym $ maybeFunctorCompose g.fwd f.fwd w)
          (\case Nothing => \case (Aye _) impossible
                 (Just x) => \(Aye w) => Refl
          )
      )
MaybeCoprod : Endo Cont
MaybeCoprod = applyL {a = Cont, b = Cont} One CoprodContBifunctor
AnyCoprodIso : ContIso (Any.Maybe x) (MaybeCoprod .mapObj x)
AnyCoprodIso = MkGenIso toCoprod fromCoprod toFrom fromTo
  where
    toCoprod : {0 x : Container} -> Any.Maybe x =%> MaybeCoprod .mapObj x
    toCoprod = maybeToCoprod <! (\case Nothing => absurd
                                       (Just y) => Aye)

    fromCoprod : {0 x : Container} -> MaybeCoprod .mapObj x =%> Any.Maybe x
    fromCoprod = coprodToMaybe <! (\case (<+ y) => absurd
                                         (+> y) => .unwrap)

    toFrom : {x : Container} ->
             (toCoprod {x} |%> fromCoprod {x}) <%≡%> identity (Any.Maybe x)
    toFrom = MkDepLensEq
        (\case Nothing => Refl
               (Just y) => Refl)
        (\case Nothing => \yx => absurd yx
               (Just y) => \(Aye z) => Refl)

    fromTo : {x : Container} ->
             (fromCoprod {x} |%> toCoprod {x}) <%≡%> identity (MaybeCoprod .mapObj x)
    fromTo = MkDepLensEq
        (\case (<+ ()) => Refl
               (+> x) => Refl)
        (\case (<+ ()) => \y => absurd y
               (+> x) => \_ => Refl)
public export
MaybeSeq : Endo Cont
MaybeSeq = applyL {a = Cont, b = Cont} MaybeCont Cont.SequenceBifunctor
namespace All
  public export
  mapMaybe : a =%> b -> All.Maybe a =%> All.Maybe b
  mapMaybe x = map x.fwd <! (\y, z => allFunctorMap x.fwd x.bwd y z)

  public export
  MaybeF : Endo Cont
  MaybeF = MkFunctor All.Maybe (\_, _ => All.mapMaybe)
    (\xx => depLensEqTrToEq
        $ MkDepLensEqTr maybeFunctorId allFunctorMapId
    )
    (\a, b, c, f, g => depLensEqTrToEq
        $ MkDepLensEqTr
            (\xx => sym (maybeFunctorCompose g.fwd f.fwd xx))
            (allFunctorMapCompose f.fwd f.bwd g.fwd g.bwd)
    )
  public export
  MaybeAllSeq : Endo Cont
  MaybeAllSeq = applyL {a = ContCart, b = Cont} MaybeCont ForallSeqBifunctor
  MaybeCoprod : Endo Cont
  MaybeCoprod = applyL {a = Cont, b = Cont} I CoprodContBifunctor

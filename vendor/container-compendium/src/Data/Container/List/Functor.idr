module Data.Container.List.Functor

import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Container.Category
import Data.Container.Morphism.Definition
import Data.Container.Cartesian.Category
import Data.Container.Extension
import Data.Container.ForallSeq.Definition
import Data.Container.ForallSeq.Bifunctor
import Data.Container.List.Desc
import Data.Container.Sequence.Definition
import Data.Container.Sequence.Bifunctor
import Data.Container.Tensor.Definition
import Data.Container.Product
import Data.Container.Coproduct

import Data.List.Quantifiers
import Data.List.Monad
import Data.Iso
import Data.Fin
namespace Any
  public export
  List : Container -> Container
  List c = (ls : List c.request) !> Any c.response ls
  public export
  mapList : a =%> b -> List a =%> List b

  public export
  ListF : Cont ->> Cont
  ListF = MkFunctor Any.List (\_, _ => mapList) ?bb ?cc

  match : List a =%> One + (a * List a)
  match =
      matchFwd <! matchBwd
      where
        matchFwd : List a.msg -> () + (a.msg * List a.msg)
        matchFwd [] = <+ ()
        matchFwd (x :: xs) = +> (x && xs)

        matchBwd :
          (xs : List (a .request)) -> (One + (a * List a)).res (matchFwd xs) -> Any (a .response) xs
        matchBwd [] x = absurd x
        matchBwd (y :: xs) (<+ x) = Here x
        matchBwd (y :: xs) (+> x) = There x

  export
  reduce : (a * b =%> b) ->
           One =%> b ->
           Any.List a =%> b
  reduce m initial =
    let handleRec : a * List a =%> b
        handleRec = identity a ~*~ (assert_total $ reduce m initial) |%> m
    in match |%>
      (initial
      ~+~
      handleRec |%> dia)
public export
Forany : Container -> Container
Forany = (ListCont ▷)
ForanyListIso : (c : Container) -> ContIso (Forany c) (Any.List c)
public export
ForanyFunctor : Endo Cont
ForanyFunctor = applyBifunctor {a = Cont, b = Cont} ListCont SequenceBifunctor
namespace All
  public export
  List : Container -> Container
  List c = (ls : List c.request) !> All c.response ls
  public export
  mapList : a =%> b -> All.List a =%> All.List b
  mapList lens = map lens.fwd <! composeMap
    where
      composeMap : (xs : List a.request) ->
                   All b.response (map lens.fwd xs) ->
                   All a.response xs
      composeMap [] ys = []
      composeMap (x :: xs) (y :: ys) = lens.bwd x y :: composeMap xs ys

  export
  elimI : All.List I =%> I
  elimI = const () <! elimBwd
    where
     elimBwd : (x : List ()) -> () -> All (\x => ()) x
     elimBwd [] y = []
     elimBwd (x :: xs) y = () :: elimBwd xs y

  public export
  ListF : Cont ->> Cont
  ListF = MkFunctor All.List ?ww ?ee ?rr
public export
Forall : Container -> Container
Forall = (ListCont ▶)
public export
ForallFunctor : Endo Cont
ForallFunctor = applyL {a = ContCart, b = Cont} ListCont ForallSeqBifunctor

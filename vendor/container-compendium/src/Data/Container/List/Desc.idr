module Data.Container.List.Desc

import Data.Container.Definition
import Data.Container.Extension

import Data.Fin
import Data.Iso
import Data.List.Quantifiers

import Proofs
import Proofs.Transport

import Syntax.PreorderReasoning

elimFin : a -> (Fin n -> a) -> (f : Fin (S n)) -> a
elimFin x g FZ = x
elimFin x g (FS y) = g y

elimFinF : (f : Fin (S n) -> a) ->
           (x : Fin (S n)) ->
           elimFin (f FZ) (f . FS) x = f x
elimFinF f FZ = Refl
elimFinF f (FS x) = Refl

elimFinP :
  (base : a) ->
  (ind1 : Fin n -> a) ->
  (ind2 : Fin m -> a) ->
  (prf : n === m) ->
  (xx : Fin (S n)) ->
  elimFin
     base
     ind1
     xx
  ===
  elimFin
     base
     ind2
     (transport Fin (cong S prf) xx)
elimFinP base ind1 ind2 prf xx = ?elimFinP_rhs
public export
ListCont : Container
ListCont = (len : Nat) !> Fin len
public export
TyList : Type -> Type
TyList = Ex ListCont
public export
Nil : TyList a
Nil = MkEx Z absurd

public export
Cons : a -> TyList a -> TyList a
Cons x ls = MkEx (S ls.ex1) (elimFin x ls.ex2)
public export covering
tyListToList : TyList x -> List x
tyListToList (MkEx Z y) = []
tyListToList (MkEx (S n) y) = y FZ :: (tyListToList (MkEx n (y . FS)))

public export
listToTyList : List x -> TyList x
listToTyList [] = Nil
listToTyList (y :: xs) = Cons y (listToTyList xs)

public export covering
toFrom : {0 a : Type} -> (x : List a) -> tyListToList (listToTyList x) = x
toFrom [] = Refl
toFrom (x :: xs) = cong (x ::) (cong tyListToList exEta `trans` toFrom xs)


public export covering
0 fromTo : (v : TyList x) -> listToTyList (tyListToList v) = v
fromTo (MkEx Z f) = cong2Dep' MkEx Refl (allUninhabited _ _)
fromTo (MkEx (S n) f) = let
    pat = (fromTo (MkEx n (f . FS)))
  in exEqToEq $ MkExEq
      (cong S $ sym $ exP1 $ sym pat)
      (\xx => Calc $
           |~ elimFin
                 (f FZ)
                 ((listToTyList (tyListToList (MkEx n (f . FS)))).ex2)
                 xx
           ~~ elimFin
                 (f FZ)
                 ((MkEx {cont = ListCont} n (f . FS)).ex2)
                 (transport Fin (cong S (sym (exP1 (sym pat)))) xx)
              ...(rewrite pat in cong (elimFin (f FZ) (f . FS)) (sym $ applyTransport ? ?))
           ~~ elimFin
                 (f FZ)
                 (f . FS)
                 (transport Fin (cong S (sym (exP1 (sym pat)))) xx)
              ...(Refl)
           ~~ f (transport Fin (cong S (sym (exP1 (sym pat)))) xx)
              ...(elimFinF f ?)
      )

public export covering
tyListIso : TyList x ≅ List x
tyListIso = MkIso
  tyListToList
  listToTyList
  toFrom
  fromTo
public export
fromAnyBwd :
    {0 a : Container} ->
    (x : Ex ListCont a.request) ->
    Any a.response (tyListToList x) ->
    Σ (Fin x.ex1) (a.response . x.ex2)
fromAnyBwd (MkEx 0 ex2) y = absurd y
fromAnyBwd (MkEx (S k) ex2) (Here x) = FZ ## x
fromAnyBwd (MkEx (S k) ex2) (There x) =
  let rest : ?
      rest = fromAnyBwd (MkEx k (ex2 . FS)) x
  in FS rest.π1 ## rest.π2

public export
toAnyBwd :
  {0 a : Container} ->
  (x : List a.request) ->
  Σ (Fin (listToTyList x).ex1)
    (a.response . (listToTyList x).ex2) ->
  Any a.response x
toAnyBwd [] y = absurd y.π1
toAnyBwd (x :: xs) (FZ ## p2) = Here p2
toAnyBwd (x :: xs) (FS p1 ## p2) =
  There (toAnyBwd xs (p1 ## p2))

covering
export 0
toFromBwd : {0 a : Container} ->
            {x : TyList  a.request} ->
            (y : Σ (Fin (listToTyList (tyListToList x)).ex1)
                   (a.response . (listToTyList (tyListToList x)).ex2) ) ->
            fromAnyBwd {a} x (toAnyBwd {a} (tyListToList {x = a.request} x) y)
            === (transport (\nx => Σ (Fin nx.ex1) (a.response . nx.ex2)) (fromTo x) y)
toFromBwd {x = MkEx 0 ex2} y = absurd y.π1
toFromBwd {x = (MkEx (S k) ex2)} (FZ ## y2) =
  let
    pp = applyTransport {x = MkEx (S k) ex2} (\nx : TyList a.request => Σ (Fin nx.ex1) (a.response . nx.ex2)) ((FZ ## y2) {a = Fin (S k), b = a.response . ex2})
                {prf = ?aui}
  in
  sigEqToEqS $ MkSigEqS
    (Calc $
      |~ FZ
      ~= ((Fin.FZ ## y2) {b = a.response . ex2}).π1
      ~~ (transport (\nx => Σ (Fin (nx .ex1)) (a .response . nx .ex2)) (fromTo (MkEx (S k) ex2)) (FZ ## y2)) .π1
        ...(congDep {a = FZ ## y2, b = (transport (\nx => Σ (Fin (nx .ex1)) (a .response . nx .ex2)) (fromTo (MkEx (S k) ex2)) (FZ ## y2))} (.π1)
                   ?adi)
    -- (trans (sym $ sigP1 {b = a.response . ex2} FZ y2) (?ad))
    )
    (Calc $
      |~ (fromAnyBwd (MkEx (S k) ex2) (toAnyBwd (tyListToList (MkEx (S k) ex2)) (FZ ## y2))) .π2
      ~~ y2
      ...(Refl)
      ~~ ((Fin.FZ ## y2) {b = a.response . ex2}).π2
      ...(?huiw)
      ~~ replace {p = (a .response . (MkEx {cont = ListCont} (S k) ex2) .ex2)} ? ((transport (\nx => Σ (Fin (nx .ex1)) (a .response . nx .ex2)) (fromTo (MkEx (S k) ex2)) (FZ ## y2)) .π2)
      ...(?huiw2)
      ~~ transport (a .response . (MkEx {cont = ListCont} (S k) ex2) .ex2) ? ((transport (\nx => Σ (Fin (nx .ex1)) (a .response . nx .ex2)) (fromTo (MkEx (S k) ex2)) (FZ ## y2)) .π2)
      ..<(?adi2)
    )
toFromBwd {x = (MkEx (S k) ex2)} (FS y1 ## y2) = ?owi

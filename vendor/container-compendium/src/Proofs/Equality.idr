module Proofs.Equality

import Control.Relation
import Control.Order
import Data.Ops
import Proofs.Transport

export infix 0 ≡≡

public export
data (≡≡) : {0 a : Type} -> {0 p : a -> Type} ->
            {0 i, j : a} -> p i -> p j -> Type where
  IRefl : {0 i, j : a} -> {0 v : p i} -> (0 prf : i === j) ->
         (≡≡) {i} {j} v (replace {p} prf v)
public export 0
getEq :
    {0 a : Type} -> {0 p : a -> Type} -> {0 i, j : a} ->
    {0 x : p i} -> {0 y : p j} ->
    (ieq : (x ≡≡ y) {p})  -> i === j
getEq (IRefl prf) = prf

export
iCong :
    {0 a : Type} -> {0 p : a -> Type} ->
    {0 x, y : a} ->
    (f : (x : a) -> p x)
    -> x === y -> (f x ≡≡ f y) {p}
iCong _ Refl = IRefl Refl

%unbound_implicits off
export
iTrans : {0 a : Type} -> {0 p : a -> Type} -> {0 i, j, k : a} ->
         {0 x : p i} -> {0 y : p j} -> {0 z : p k} ->
         (x ≡≡ y) {p} -> (y ≡≡ z) {p} -> (x ≡≡ z) {p}
iTrans (IRefl prf) (IRefl prf1) = IRefl (trans prf prf1)

export
iSym : {0 a : Type} -> {0 p : a -> Type} -> {0 i, j : a} ->
       {0 x : p i} -> {0 y : p j} ->
       (x ≡≡ y) {p}  -> (y ≡≡ x) {p}
iSym (IRefl p) = IRefl (sym p)

export
refl : {0 a : Type} -> {0 p : a -> Type} -> {0 i : a} ->
       {0 x : p i} ->
       (x ≡≡ x) {p}
refl = IRefl Refl

export
iEqToEq' :
    {0 a : Type} -> {0 p : a -> Type} -> {0 i, j : a} ->
    {0 x : p i} -> {0 y : p j} ->
    (ieq : (x ≡≡ y) {p})  -> x === (transport p (sym $ getEq ieq) y)
iEqToEq' (IRefl Refl) = applyRefl' ? ?

export
iEqToEq :
    {0 a : Type} -> {0 p : a -> Type} -> {0 i, j : a} ->
    {0 x : p i} -> {0 y : p j} ->
    (ieq : (x ≡≡ y) {p})  -> x === (replace {p} (sym $ getEq ieq) y)
iEqToEq (IRefl prf) = Refl

export
eqToIxEq : {0 a : Type} -> {0 p : a -> Type} ->
           {i : a} ->
           {x, y : p i} -> x === y -> (x ≡≡ y) {p}
eqToIxEq Refl = IRefl Refl

public export
(≡) : {a : Type} -> (e1, e2 : a) -> Type
(≡) = (===)

export
IxUIP : {0 a, b : Type} -> (p1, p2 : a ≡ b) -> (p1 ≡≡ p2) {p = Prelude.id}
IxUIP Refl Refl = IRefl Refl
private infixl 0 ≡≡≡
public export
data (≡≡≡) : {0 a, b : Type} -> {p : a -> Type} -> {q : b -> Type} ->
             {0 i : a} -> {0 j : b} -> (0 v1 : p i) -> (0 v2 : q j) -> Type where
  IRefl' : {0 a, b : Type} -> {0 p : a -> Type} -> {0 q : b -> Type} ->
           {0 i : a} -> {0 j : b} -> {0 v1 : p i} -> {0 v2 : q j} ->
           (0 prf : i ~=~ j) -> (0 prf2 : v1 ~=~ v2) ->
           (≡≡≡) {p, q, i, j} v1 v2

export
0 megaEqToEq : {0 a, b : Type} -> {p : a -> Type} -> {q : b -> Type} ->
             {0 i : a} -> {0 j : b} -> {0 v1 : p i} -> {0 v2 : q j} ->
             (v1 ≡≡≡ v2) {p, q} -> v1 ~=~ v2
megaEqToEq (IRefl' Refl prf2) = prf2



public export
IEq : {a : Type} -> {b : a -> Type} -> {x, y : a} -> x ≡ y -> b x ->  b y -> Type
IEq Refl x y = x ≡ y

public export
IxCong : {a : Type} -> {b : a -> Type} -> (f : (x : a) -> b x) -> {x, y : a} ->
         (p : x ≡ y) -> IEq {a, b} p (f x) (f y)
IxCong f Refl = Refl

module Data.Alg

import Data.Coproduct
import Data.Product

%default total

public export
distributePlus : a * (b + c) -> a * b + a * c
distributePlus (fst && (+> x)) = +> (fst && x)
distributePlus (fst && (<+ x)) = <+ (fst && x)

||| distributive property of products over coproducts
public export
distributive : (p * p') * (s + s') -> (p * s) + (p' * s')
distributive ((fst && snd) && (<+ x)) = <+ (fst && x)
distributive ((fst && snd) && (+> x)) = +> (snd && x)

||| distributive property of products over coproducts
public export
distributive' :  (p + q) * (a * b) -> (p * a) + (q * b)
distributive' ((<+ x) && a && b) = <+ (x && a)
distributive' ((+> x) && a && b) = +> (x && b)

||| x + x is 2 * x
multiply : a + a -> Bool * a
multiply = choice (True &&) (False &&)

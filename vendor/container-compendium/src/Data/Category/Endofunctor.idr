module Data.Category.Endofunctor

import Data.Category
import Data.Category.Bifunctor
import Data.Category.Functor
import Data.Category.Functor.Category
import Data.Category.NaturalTransformation as NT
import Data.Category.Monoid

import Data.Product

import Syntax.PreorderReasoning

import Pipeline.Equality

%hide Prelude.Ops.infixl.(|>)
parameters
  {o1, o2, o3, o4 : Type}
  {c1 : Category o1} {c2 : Category o2} {c3 : Category o3} {c4 : Category o4}
  (f : c1 ->> c2) (g : c2 ->> c3) (h : c3 ->> c4)
  public export
  funcCompAssocNTR : (f ⨾⨾ (g ⨾⨾ h)) =>> ((f ⨾⨾ g) ⨾⨾ h)
  funcCompAssocNTR = MkNT
      (\vx => c4.id _)
      (\x, y, m => c4.idLeft _ _ _ `trans` sym (c4.idRight _ _ _) )

  public export
  funcCompAssocNTL : (f ⨾⨾ g) ⨾⨾ h =>> f ⨾⨾ (g ⨾⨾ h)
  funcCompAssocNTL = MkNT
      (\vx => c4.id _)
      (\x, y, m => c4.idLeft _ _ _ `trans` sym (c4.idRight _ _ _) )

  public export
  funcCompAssocNI : (f ⨾⨾ g) ⨾⨾ h =~= f ⨾⨾ (g ⨾⨾ h)
  funcCompAssocNI = MkNaturalIsomorphism
      funcCompAssocNTL
      funcCompAssocNTR
      (\vx => c4.idLeft _ _ _)
      (\vx => c4.idLeft _ _ _)
parameters
  {o1, o2 : Type}
  {c : Category o1} {d : Category o2}
  {f : c ->> d}
  public export
  funcIdRNT : idF c ⨾⨾ f =>> f
  funcIdRNT = MkNT (\vx => d.id _)
    (\x, y, m => d.idLeft _ _ _ `trans` sym (d.idRight _ _ _))

  public export
  funcIdLNT : f ⨾⨾ idF d =>> f
  funcIdLNT = MkNT (\vx => d.id _)
    (\x, y, m => d.idLeft _ _ _ `trans` sym (d.idRight _ _ _))

  public export
  funcIdLNT' : f =>> f ⨾⨾ idF d
  funcIdLNT' = MkNT (\vx => d.id _)
    (\x, y, m => d.idLeft _ _ _ `trans` sym (d.idRight _ _ _))

  public export
  funcIdRNT' : f =>> idF c ⨾⨾ f
  funcIdRNT' = MkNT (\vx => d.id _)
    (\x, y, m => d.idLeft _ _ _ `trans` sym (d.idRight _ _ _) )
public export
Endo : Category o -> Type
Endo c = c ->> c
public export
EndoCat : (c : Category o) -> Category (Endo c)
EndoCat c = FunctorCat c c

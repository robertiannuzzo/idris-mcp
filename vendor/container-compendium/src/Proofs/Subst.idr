module Proofs.Subst

parameters
    {0 a : Type} (0 p : a -> Type)
  export
  subst : (0 _ : x = y) -> (1 _ : p x) -> p y
  subst prf z = replace {p} prf z

  %unbound_implicits off
  export
  substCompose :
      {0 x, y, z :  a} ->
      {0 prf2 : x === y} ->
      {0 prf1 : y === z} ->
      (val : p x) ->
      subst prf1 (subst prf2 val) === subst (trans prf2 prf1) val
  substCompose val = Refl

  export
  subst2Replace : {0 x, y : a} -> (0 val : p x) -> {prf : x === y} ->
                   subst prf val === (replace {p} prf val)
  subst2Replace val = Refl

  export
  evalSubst : {0 x : a} -> (0 val : p x) ->
                   subst Refl val === val
  evalSubst val = Refl





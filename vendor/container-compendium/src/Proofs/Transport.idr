module Proofs.Transport


%unbound_implicits off

parameters
    {0 a : Type} (0 p : a -> Type)
  export
  transport : {0 x, y : a} -> (0 _ : x = y) -> (1 _ : p x) -> p y
  transport prf z = replace {p} prf z

  %unbound_implicits off
  export
  transportCompose :
      {0 x, y, z :  a} ->
      {0 prf2 : x === y} ->
      {0 prf1 : y === z} ->
      (val : p x) ->
      transport prf1 (transport prf2 val) === transport (trans prf2 prf1) val
  transportCompose val = Refl

  export
  transportComposeUIP :
      {0 x, y, z :  a} ->
      {0 prf2 : x === y} ->
      {0 prf1 : y === z} ->
      {0 prf3 : x === z} ->
      (val : p x) ->
      transport prf1 (transport prf2 val) === transport prf3 val
  transportComposeUIP val = Refl

  export
  applyTransport : {0 x, y : a} -> (0 val : p x) -> {prf : x === y} ->
                   transport prf val === (replace {p} prf val)
  applyTransport val = Refl

  export
  applyTransport' : {0 x, y : a} -> (0 val : p x) -> {prf : x === y} ->
                   (replace {p} prf val) === transport prf val
  applyTransport' val = Refl

  export
  applyRefl : {0 x : a} -> (0 val : p x) ->
                   transport Refl val === val
  applyRefl val = Refl

  export
  applyRefl' : {0 x : a} -> (0 val : p x) ->
                   val === transport Refl val
  applyRefl' val = Refl

  export
  transpUIP : {0 x, y : a} -> (0 v : p x) -> {prf, qrf : x === y} ->
              transport prf v === transport qrf v
  transpUIP v = Refl

  export
  applyRefl2 : {0 x : a} -> (0 val : p x) ->
                   transport Refl val === transport Refl val
  applyRefl2 val = Refl

module Data.Category.Proofs

import Data.Category.Notation
import Syntax.PreorderReasoning

import Proofs

%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

--           h1                 h2
--    a ───────────→ b    b ───────────→ e
--    │              │    │              │
--    │              │    │              │
--    │              │    │              │
-- v1 │              │ v2 │              │ v3
--    │              │    │              │
--    │              │    │              │
--    ↓              ↓    ↓              ↓
--    c ───────────→ d    d ───────────→ f
--           h1'                h2'
public export
glueSquares : (cat : Category o) =>
              {0 a, b, c, d, e, f : o} ->
              {0 h1 : a ~> b} ->
              {0 h2 : b ~> e} ->
              {0 v1 : a ~> c} ->
              {0 v2 : b ~> d} ->
              {0 v3 : e ~> f} ->
              {0 h1' : c ~> d} ->
              {0 h2' : d ~> f} ->
              (sq1 : (h1 |> v2 ) {cat, a=a, b=b, c=d}
                 === (v1 |> h1') {cat, a=a, b=c, c=d}) ->
              (sq2 : (h2 |> v3 ) {cat, a=b, b=e, c=f}
                 === (v2 |> h2') {cat, a=b, b=d, c=f}) ->
              Start (a -< h1 >- b -< h2 >- e -< v3 >- End f)
              ===
              Start (a -< v1 >- c -< h1' >- d -< h2' >- End f)
glueSquares sq1 sq2 =
  Calc $ |~  h1 |> (h2  |> v3)
         ~~  h1 |> (v2  |> h2') ...(cong (h1 |>) sq2)
         ~~ (h1 |> v2)  |> h2'  ...(cat.compAssoc _ _ _ _ h1 v2 h2')
         ~~ (v1 |> h1') |> h2'  ...(cong (|> h2') sq1)
         ~~  v1 |> (h1' |> h2') ...(sym (cat.compAssoc _ _ _ _ v1 h1' h2'))


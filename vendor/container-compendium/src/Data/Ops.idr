||| This module export the operators used with their fixity
module Data.Ops

export infixr 10 ^    -- Exponentiation
export prefix 9 <+    -- Left choice
export prefix 9 +>    -- Right choice
export infixr 6 ##    -- Both at once
-- export infix 0 ≅     -- isomorphisms (Unicode operator char; see Data.Category.Ops note)
-- export infix 0 ≡     -- equality (Unicode operator char; see Data.Category.Ops note)

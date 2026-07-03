module Data.Container.Morphism.Chart

-- Vendored for idris-mcp: import the bare Container definition directly
-- rather than the Data.Container aggregator, which pulls in
-- Extension.Properties' proof machinery (indexed equality etc.) that this
-- module doesn't use.
import public Data.Container.Definition

public export
record Chart (a, b : Container) where
  constructor MkChart
  mapShp : a.req -> b.req
  mapPos : (x : a.req) -> a.res x -> b.res (mapShp x)

%name Chart c1, c2, c3, c4

(|>) : Chart a b -> Chart b c -> Chart a c
(|>) (MkChart m1 m2) (MkChart n1 n2) = MkChart
    (n1 . m1)
    (\x, y => n2 (m1 x) (m2 x y))


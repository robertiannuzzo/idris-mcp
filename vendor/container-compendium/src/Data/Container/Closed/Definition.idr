module Data.Container.Closed.Definition

import Data.Container.Definition

import Data.Sigma
public export
record (=&>)(c1, c2 : Container) where
  constructor (!!)
  fn : (x : c1.req) -> Σ (y : c2.req) | c2.res y -> c1.res x
public export
(|&>) : a =&> b -> b =&> c -> a =&> c
(|&>) x y = !! \z => let r : ?
                         r = x.fn z
                         s : ?
                         s = y.fn r.π1
                      in s.π1 ## r.π2 . s.π2
public export
identity : (0 a : Container) -> a =&> a
identity _ = !! \x => x ## id

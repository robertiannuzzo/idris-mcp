module Data.Container.Definition

import Data.Boundary
import Data.Category.Ops
-- import Data.Sigma  -- vendored for idris-mcp: unused in this file, and
                       -- pulls in Proofs.Equality (Unicode-operator-named
                       -- indexed equality type, not fixable by commenting a
                       -- fixity line). See Data.Category.Ops's note.

public export
record Container where
  constructor (!>)
  request : Type
  response : request -> Type
%pair Container request response

public export
(.message) : Container -> Type
(.message) c = c.request
public export
(.msg) : Container -> Type
(.msg) c = c.request
public export
(.req) : Container -> Type
(.req) c = c.request
public export
(.res) : (c : Container) -> c.req -> Type
(.res) c = c.response
public export
(:-) : Type -> Type -> Container
(:-) req res = (x : req) !> res
public export
I : Container
I = Unit :- Unit
public export
One: Container
One = Unit :- Void
Zero : Container
Zero = Void :- Void
public export
continuation : Container -> Type
continuation c = (x : c.request) -> c.response x

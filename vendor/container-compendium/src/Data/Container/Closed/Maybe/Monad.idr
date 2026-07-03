module Data.Container.Closed.Maybe.Monad

import Data.Container.Definition
import Data.Container.Closed
import Data.Container.Maybe.Definition
namespace Any
  public export
  join : Any.Maybe (Any.Maybe a) =&> Any.Maybe a

namespace All
  public export
  join : All.Maybe (All.Maybe a) =&> All.Maybe a

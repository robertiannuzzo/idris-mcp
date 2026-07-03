module Data.Container.Maybe.Definition

import Data.Container.Definition
import public Data.Maybe.Any
import public Data.Maybe.All
namespace Any
  public export
  Maybe : Container -> Container
  Maybe c = (x : Maybe c.request) !> Any c.response x
namespace All
  public export
  Maybe : Container -> Container
  Maybe c = (x : Maybe c.request) !> All c.response x

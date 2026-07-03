module Data.List.Any

import Data.List.Quantifiers
import Data.Coproduct

export
(.extract) : Any p [x] -> p x
(.extract) (Here y) = y

export
(.extract2) : Any p [x, y] -> p x + p y
(.extract2) (Here y) = <+ y
(.extract2) (There (Here y)) = +> y

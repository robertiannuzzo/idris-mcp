module Data.Container.Closed.Sequence

import Data.Container.Sequence.Definition
import Data.Container.Sequence.Bifunctor
import Data.Container.Closed
import Data.Container.Extension

export
(~▷~) : a =&> a' -> b =&> b' -> a ▷ b =&> a' ▷ b'
(~▷~) m n  = toClosed $ fromClosed m ~▷~ fromClosed n

export
fromSeqIdRight : a ▷ I =&> a

export
fromSeqIdLeft : I ▷ a =&> a

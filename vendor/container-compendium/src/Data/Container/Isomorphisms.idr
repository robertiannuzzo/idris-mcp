module Data.Container.Isomorphisms

import Data.Container
import Data.Container.Morphism.Eq
import Data.Container.Maybe.Functor
import Data.Container.Sequence.Monoidal

import Syntax.PreorderReasoning.Generic

congSeqRight : ContIso a b -> ContIso (a ▷ c) (b ▷ c)

congSeqLeft : ContIso a b -> ContIso (c ▷ a) (c ▷ b)

congCoprodRight : ContIso a b -> ContIso (a + c) (b + c)

congCoprodLeft : ContIso a b -> ContIso (c + a) (c + b)

maybeContDef : ContIso MaybeCont (One + I)

leftOneSeq : ContIso (One ▷ a) One

leftUnitor' : ContIso (I ▷ a) a

plusSeqDistrib : ContIso ((a + b) ▷ c) ((a ▷ c) + (b ▷ c))
AnySeqIso : {a : Container} -> ContIso (MaybeCont ▷ a) (One + a)
AnySeqIso = CalcWith {dom = Container} {leq = ContIso} @{ContIsoPre} $
    |~ (MaybeCont ▷ a)
    <~ ((One + I) ▷ a)
    ...(congSeqRight maybeContDef)
    <~ ((One ▷ a) + (I ▷ a))
    ...(plusSeqDistrib)
    <~ ((One ▷ a) + a)
    ...(congCoprodLeft {c = One ▷ a, a = I ▷ a, b = a}
            leftUnitor')
    <~ (One + a)
    ...(congCoprodRight leftOneSeq)
  where
    toAny : MaybeSeq .mapObj a =%> Any.Maybe a
    toAny = ?toAny_rhs
    fromAny : Any.Maybe a =%> MaybeSeq .mapObj a
    fromAny = ?fromAny_rhs
    toFrom : (toAny |%> fromAny) <%≡%> identity (MaybeSeq .mapObj a)
    toFrom = ?toFrom_rhs
    fromTo : (fromAny |%> toAny) <%≡%> identity (Any.Maybe a)
    fromTo = ?fromTo_rhs

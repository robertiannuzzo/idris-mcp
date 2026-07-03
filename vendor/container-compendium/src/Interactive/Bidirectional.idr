module Interactive.Bidirectional

import Data.Container
import Data.Container.Closed
import Data.Container.Closed.Coproduct
import Data.Container.Closed.Sequence
import Data.Container.Closed.Maybe.Functor
import Data.Container.Closed.Kleene
import Data.Container.Apply.Definition
import Data.Container.Maybe.Definition
import Data.Container.Kleene
import Data.Container.Tensor.Definition

import Data.Coproduct
import Data.Product
import Data.Sigma
import Data.List
import Data.Either

%language ElabReflection
data Ty = Var String | Function Ty Ty | One

Eq Ty where
  Var s == Var t = s == t
  (Function f x == Function g y) = f == g && x == y
  One == One = True
  _ == _ = False

showTy : Bool -> Ty -> String
showTy parens (Var str) = str
showTy parens (Function f@(Function _ _) y) = showParens parens "\{showTy True f} -> \{showTy False y}"
showTy parens (Function x y) = showParens parens "\{showTy False x} -> \{showTy False y}"
showTy parens One = "1"

export
Show Ty where
  show = showTy False

Context : Type
Context = List (String, Ty)
-- %runElab derive "Ty" [Eq]
data Mode = Synthesizable | Checkable

data Term : Mode -> Type where
  Variable : String -> Term Synthesizable
  App : (fn : Term Synthesizable) -> (arg : Term Checkable) -> Term Synthesizable
  Annotate : Ty -> Term Checkable -> Term Synthesizable
  Lam : (name : String) -> Term Checkable -> Term Checkable
  Assume : Term Synthesizable -> Term Checkable

Show (Term n) where
  showPrec prec (Variable str) = str
  showPrec prec (App fn arg) = showParens (prec == App) (showPrec (User 0) fn ++ " " ++ showPrec App arg)
  showPrec prec (Annotate ty tm) = showParens (prec > Open) (show tm ++ " : " ++ show ty)
  showPrec prec (Lam name x) = showParens (prec > Open) "λ\{name}. \{show x}"
  showPrec prec (Assume x) = showPrec prec x
record SynQuestion where
  constructor MkSynQ
  ctx : Context
  term : Term Synthesizable

record CheckQuestion where
  constructor MkChkQ
  ctx : Context
  type : Ty
  term : Term Checkable
SynAnswer : Type
SynAnswer = Ty

CheckAnswer : Type
CheckAnswer = Unit

SynGoal : Container
SynGoal = SynQuestion :- SynAnswer

ChkGoal : Container
ChkGoal = CheckQuestion :- CheckAnswer
Typecheck : Container
Typecheck = ChkGoal + SynGoal
data Error = ExpectedFunction (Term Synthesizable) Ty
           | IncompatibleAnn Ty Ty
           | VarNotFound String
           | LamNotFn (Term Checkable) Ty

E : Type -> Type
E = Either Error

TCErr : Container -> Container
TCErr = (E •)
varRule : TCErr SynGoal =&> Any.Maybe I
varRule = !! \case (MkSynQ ctx (Variable var)) => Just () ## \_ =>
                     maybeToEither (VarNotFound var) (lookup var ctx)
                   others => Nothing ## absurd

appRule : TCErr SynGoal =&> Any.Maybe (SynGoal ▷ Any.Maybe ChkGoal)
appRule = !! \case (MkSynQ ctx (App f x)) =>
                     Just (MkEx (MkSynQ ctx f)
                              (\case (Function a b) => Just (MkChkQ ctx a x)
                                     _ => Nothing
                              )
                          )
                     ## (\case (Aye (Function a b ## Aye vy)) => Right b
                               (Aye (t ## _)) => Left (ExpectedFunction f t)
                        )
                   _ => Nothing ## absurd

annRule : SynGoal =&> Any.Maybe ChkGoal
annRule = !! \case (MkSynQ ctx (Annotate ty term)) =>
                       Just (MkChkQ ctx ty term) ## \_ => ty
                   _ => Nothing ## absurd

assume : TCErr ChkGoal =&> Any.Maybe SynGoal
assume = !! \case (MkChkQ ctx ty (Assume term)) =>
                     Just (MkSynQ ctx term) ## (\(Aye sy) =>
                        if sy == ty
                           then Right ()
                           else Left (IncompatibleAnn sy ty)
                           )
                  _ => Nothing ## absurd

lamRule : ChkGoal =&> Any.Maybe ChkGoal
lamRule = !! \case (MkChkQ ctx (Function a b) (Lam var body)) =>
                       Just (MkChkQ ((var, a) :: ctx) b body) ## \_ => ()
                   _ => Nothing ## absurd

IsFn : Container
IsFn = Ty :- Maybe (Ty * Ty)

lamRule' : TCErr ChkGoal =&> Any.Maybe (IsFn ▷ All.Maybe ChkGoal)
lamRule' = !! \case (MkChkQ ctx ty (Lam var body)) =>
                       Just (MkEx ty (map (\fnTy => MkChkQ ((var, fnTy.π1) :: ctx) fnTy.π2 body))) ##
                            \case (Aye (Nothing ## p2)) => Left (LamNotFn (Lam var body) ty) -- the lambda wasn't a function
                                  (Aye (Just x ## (Yay y))) => Right () -- everything went well
                    _ => Nothing ## absurd
%hide Prelude.Ops.infixr.(&&)
private infixl 6 &&
VarGoal : Container
VarGoal = Context * String :- Ty
AppGoal : Container
AppGoal = Context * Term Synthesizable * Term Checkable :- Ty
LamGoal : Container
LamGoal = Context * Ty * String * Term Checkable :- Unit
AnnotateGoal : Container
AnnotateGoal = Context * Ty * Term Checkable :- Ty
AssumeGoal : Container
AssumeGoal = Context * Ty * Term Synthesizable :- Unit
match : ChkGoal + SynGoal =&> VarGoal + AppGoal + LamGoal + AnnotateGoal + AssumeGoal
match = !! \case
                 (<+ (MkChkQ ctx type (Assume t))) => +> (ctx &&  type && t) ## id
                 (+> (MkSynQ ctx (Annotate ty term))) => <+ +> (ctx && ty && term) ## id
                 (<+ (MkChkQ ctx type (Lam name term))) => <+ <+ +> (ctx && type && name && term) ## id
                 (+> (MkSynQ ctx (App fn arg))) => <+ <+ <+ +> (ctx && fn && arg) ## id
                 (+> (MkSynQ ctx (Variable str))) => <+ <+ <+ <+ (ctx && str) ## id
namespace Direct
  export
  varRule : TCErr VarGoal =&> I
  varRule = !! \(ctx && name) => () ## \_ =>
            maybeToEither (VarNotFound name) (lookup name ctx)

  export
  annRule : AnnotateGoal =&> ChkGoal
  annRule = !! \(ctx && ty && term) => MkChkQ ctx ty term ## const ty

  export
  assRule : TCErr AssumeGoal =&> SynGoal
  assRule = !! \(ctx && ty && term) => MkSynQ ctx term ## \ty' =>
            if ty == ty' then Right ()
                         else Left (IncompatibleAnn ty' ty)

  export
  lamRule : TCErr LamGoal =&> IsFn ▷ All.Maybe ChkGoal
  lamRule = !! \(ctx && ty && var && body) =>
            MkEx ty (map (\fnTy => MkChkQ ((var, fnTy.π1) :: ctx) fnTy.π2 body)) ##
            (\case (Nothing ## yy) => Left (LamNotFn (Lam var body) ty)
                   ((Just x) ## yy) => Right ())

  export
  appRule : TCErr AppGoal =&> SynGoal ▷ All.Maybe ChkGoal
  appRule = !! \(ctx && fn && arg) =>
                MkEx (MkSynQ ctx fn) (\case (Function a b) => Just (MkChkQ ctx a arg)
                                            _ => Nothing) ##
                (\case (Function a b ## (Yay x)) => pure b
                       (xs ## ys) => Left (ExpectedFunction fn xs))
distribFPlus5 : f • (a + b + c + d + e) =&> f • a + f • b + f • c + f • d + f • e
distribFPlus5 = !! \x => ?adad ## ?distribFPlus5_rhs

dia5 : a + a + a + a + a =&> I
dia5 = !! \case x => ?dia5_rhs

pushRightSeq : Monad f => f • (a ▷ b) =&> f • (a ▷ f • b)
pushRightSeq = !! \x => x ##
                   (\yy => do y1 ## y2 <- yy
                              map (y1 ##) y2
                   )

distFMaybe : Functor f => f • Any.Maybe a =&> Any.Maybe (f • a)
distFMaybe = !! \case Nothing => Nothing ## absurd
                      (Just x) => Just x ## (\(Aye vx) => map (\y => Aye y) vx )

distFMaybe' : Applicative f => f • All.Maybe a =&> All.Maybe (f • a)
distFMaybe' = !! \case Nothing => Nothing ## (\xs => pure Nay)
                       (Just x) => Just x ## (\(Yay vx) => map (\y => Yay y) vx )
runAll : TCErr VarGoal +
         TCErr AppGoal +
         TCErr LamGoal +
         TCErr AnnotateGoal +
         TCErr AssumeGoal =&>
         I +
         TCErr (SynGoal ▷ All.Maybe ChkGoal) +
         TCErr (IsFn ▷ All.Maybe ChkGoal) +
         TCErr ChkGoal +
         TCErr SynGoal
runAll = varRule
    ~+~ pureRight appRule {a = AppGoal}
    ~+~ pureRight lamRule {a = LamGoal}
    ~+~ fapplyMap annRule
    ~+~ pureRight assRule {a = AssumeGoal}
covering
typecheckRec : Costate (TCErr Typecheck)
covering
adapt1 : TCErr (SynGoal ▷ All.Maybe ChkGoal) =&> TCErr Typecheck
adapt1 = pushRightSeq {f = E, b = All.Maybe ChkGoal}
    |&> fapplyMap {a = SynGoal ▷ TCErr (All.Maybe ChkGoal), b = Typecheck }
        ((identity SynGoal ~▷~ fromChk)
            {a = SynGoal, a' = SynGoal, b = TCErr (All.Maybe ChkGoal), b' = I}
        |&> fromSeqIdRight
        |&> inr {a = ChkGoal, b = SynGoal})
    where
      covering
      fromChk : TCErr (All.Maybe ChkGoal) =&> I
      fromChk = distFMaybe' {a = ChkGoal}
         |&> All.mapMaybe
             (fapplyMap {a = ChkGoal} (inl {b = SynGoal}) |&> typecheckRec)
         |&> All.unitI

isFn : Closed.Costate IsFn
isFn = costate (\case (Function a b) => Just (a && b) ; _ => Nothing)

covering
adaptMaybe : TCErr (All.Maybe ChkGoal) =&> I
adaptMaybe = distFMaybe' {a = ChkGoal}
    |&> All.mapMaybe {a = TCErr ChkGoal, b = I}
        (fapplyMap {a = ChkGoal, b = Typecheck}
            (inl {b = SynGoal}) |&> typecheckRec)
    |&> All.unitI

covering
adapt2 : TCErr (IsFn ▷ All.Maybe ChkGoal) =&> I
adapt2 = fapplyMap {f = E}
    ((isFn ~▷~ identity (All.Maybe ChkGoal))
    |&> fromSeqIdLeft {a = All.Maybe ChkGoal})
    |&> adaptMaybe

adapt3 : TCErr ChkGoal =&> TCErr Typecheck
adapt3 = fapplyMap (inl {a = ChkGoal, b = SynGoal})

adapt4 : TCErr SynGoal =&> TCErr Typecheck
adapt4 = fapplyMap (inr {b = SynGoal, a = ChkGoal})

covering
recAll : I +
         TCErr (SynGoal ▷ All.Maybe ChkGoal) +
         TCErr (IsFn ▷ All.Maybe ChkGoal) +
         TCErr ChkGoal +
         TCErr SynGoal
         =&>
         I + I + I + I + I
recAll = identity I
    ~+~ (adapt1 |&> typecheckRec)
    ~+~ adapt2
    ~+~ (adapt3 |&> typecheckRec)
    ~+~ (adapt4 |&> typecheckRec)
typecheckRec = fapplyMap {f = E} match
    |&> distribFPlus5 {a = VarGoal, b = AppGoal, c = LamGoal, d = AnnotateGoal, e = AssumeGoal, f = E}
    |&> runAll
    |&> recAll
    |&> dia5 {a = I}
covering
runTypechecker : (x : Typecheck .request) -> E (Typecheck .response x)
runTypechecker = runCostate typecheckRec
-- well typesd examples
-- ill-typed examples

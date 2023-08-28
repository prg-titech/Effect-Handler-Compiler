module GPCE2023.Effect where

open import Data.Empty
open import Data.Nat  using (ℕ) renaming (_+_ to add)
open import Data.Bool using (true; false; if_then_else_; _∨_; _∧_) renaming (Bool to 𝔹)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup; []; uncons)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List using ( List; _∷_; []; map; _++_ )
open import Data.Product using ( _×_ ; _,_ )
open import Function using ( _∘_; _$_ )
open import Data.Maybe.Base
open import Relation.Binary.PropositionalEquality

-- ************************
-- Source Language L_s 
-- ************************
data VTy : Set  -- Value types
CTy : Set       -- Computation types
data HTy : Set  -- Handler types

data Sig : Set  -- Effect signatures
Eff : Set       -- Effects

data Sig where
  op : VTy → VTy → Sig

Eff = List Sig

data VTy where
  Unit  : VTy
  _⇒_   : VTy → CTy →
          VTy
  Hand  : HTy → VTy

CTy = VTy × Eff

data HTy where
  _⇒_ : CTy → CTy → HTy

Ctx = List VTy

variable
  A B A' B' : VTy
  E E' E₁ E₂ : Eff
  C D : CTy
  H : HTy
  Γ Γ' Γ₁ Γ₂ : Ctx



data Val (Γ : Ctx) : VTy → Set
data Cmp (Γ : Ctx) : CTy → Set
data Hdl (Γ : Ctx) : HTy → Set
OperationClauses : Ctx → Eff → CTy → Set

data Val Γ where
  Unit : Val Γ Unit
  Var : A ∈ Γ → Val Γ A
  Lam : Cmp (A ∷ Γ) C → Val Γ (A ⇒ C)
  Handler : Hdl Γ H → Val Γ (Hand H)

data Cmp Γ where
  Return : Val Γ A → Cmp Γ (A , E)
  Do : (op A B) ∈ E → Val Γ A → Cmp Γ (B , E)
  Handle_With_  : Cmp Γ C → Val Γ (Hand (C ⇒ D)) 
                          → Cmp Γ D
  App : Val Γ (A ⇒ C) → Val Γ A → Cmp Γ C
  Let_In_ : Cmp Γ (A , E) → (Cmp (A ∷ Γ) (B , E)) 
                          → Cmp Γ (B , E)

data Hdl Γ where
  ƛx_|ƛx,r_ :
    Cmp (A ∷ Γ) C → -- return clause
    OperationClauses Γ E C → -- operation clauses
    Hdl Γ ((A , E) ⇒ C)

OperationClauses Γ E₁ D = 
  All (λ { (op A' B') → Cmp ((B' ⇒ D) ∷ A' ∷ Γ) D }) E₁


-- ************************
-- Intrinsically-typed interpreter:
-- Big-step semantics & type soundness
-- ************************


-- Values after evaluation
data Result : VTy → Set
-- Environment
Env : Ctx → Set

-- Patterns of hole
-- Frame A C ... A is expected type for the hole, C is the type of the whole expression
data Frame : VTy → CTy → Set
-- Shapes of pure continuations
data PureStackFrame : VTy → CTy → Set
-- Shapes of mata continuations
data MetaStackFrame : CTy → CTy → Set

data Result where
  tt   : Result Unit
  clos : ∀{A C Γ} → Cmp (A ∷ Γ) C → Env Γ → Result (A ⇒ C)
  resump : PureStackFrame A C → Result (Hand (C ⇒ D)) → Result (A ⇒ D)
  hand : Hdl Γ H → Env Γ → Result (Hand H)

-- Environment
Env Γ = All (λ A → Result A) Γ

data Frame where
  Let□In_,_ : (Cmp (A ∷ Γ) C) → Env Γ → Frame A C

data PureStackFrame where
  empty : PureStackFrame A (A , E)
  extend : Frame A (A' , E) → PureStackFrame A' (B , E) →
            PureStackFrame A (B , E)

data MetaStackFrame where
  -- empty continuation
  empty : MetaStackFrame (A , []) (A , [])
  -- handler and meta continuation.
  _[_[Handle□With_]] :
    MetaStackFrame (B , E') D →
    PureStackFrame A' (B , E') →
    Result (Hand ((A , E) ⇒ (A' , E'))) →
    MetaStackFrame (A , E) D

-- type-safe, top-level evaluation
eval : Cmp [] (A , []) → Result A

-- type-safe evaluation for pure values
evalv : Val Γ A → Env Γ → Result A

-- type-safe evaluation for effectful computations
{-# TERMINATING #-}
evalc : Cmp Γ (A , E) → Env Γ →
        PureStackFrame A (A' , E) → MetaStackFrame (A' , E) (B , []) →
        Result B

-- Resume continuation by putting given value into the hole of given continuation
resumeCont :
  Result A →
  PureStackFrame A (A' , E) → MetaStackFrame (A' , E) (B , []) →
  Result B


eval c = evalc c [] empty empty


resumeCont v empty (H [ K [Handle□With h ]]) with h
... | (hand (ƛx ret |ƛx,r _) env') =
  evalc ret (v ∷ env') K H
resumeCont v empty empty = v
resumeCont v (extend (Let□In e2 , env) K) =
  evalc e2 (v ∷ env) K 


evalv Unit _          = tt
evalv (Var x) env     = lookup env x
evalv (Lam f) env     = clos f env
evalv (Handler h) env = hand h env

evalc (App v1 v2) env K H with evalv v1 env
... | clos e' env' = evalc e' ((evalv v2 env) ∷ env') K H
... | resump K' h' = resumeCont (evalv v2 env) K' (H [ K [Handle□With h' ]])

evalc (Return v) env K =
  resumeCont (evalv v env) K

evalc (Do l v) env K (H [ K' [Handle□With h ]]) with h
... | hand (ƛx ret |ƛx,r es) env' =
  evalc (lookup es l) ((resump K (hand (ƛx ret |ƛx,r es) env')) ∷ (evalv v env) ∷ env') K' H

evalc (Handle e With h) env K H =
  evalc e env empty $ (H [ K [Handle□With (evalv h env) ]])

evalc (Let e1 In e2) env K =
  evalc e1 env $ extend (Let□In e2 , env) K


-- ****************************
-- Stack & target language L_t
-- ****************************
data SValTy : Set
StackTy : Set

data SValTy where
  ValTy  : VTy → SValTy
  ContTy : Ctx → StackTy → CTy → SValTy
  HandTy : Ctx → StackTy → StackTy → CTy → SValTy

StackTy = List SValTy

variable
  T : SValTy
  S S' S₁ S₂ S₃ : StackTy


-- immediate values
data PVal : VTy → Set where
  unit : PVal Unit


data Code (Γ : Ctx) : StackTy → StackTy → Set
OperationCodes : VTy → Eff → Eff → Ctx → StackTy → StackTy → Set
HandlerCode : Ctx → CTy → CTy → Set
PureCodeCont : Ctx → StackTy → CTy → Set

PureCodeCont Γ S₁ C = ∀{Γ₁ S₂ S₃} → Code Γ (S₁ ++ HandTy Γ₁ S₂ S₃ C ∷ S₂) S₃

data Code Γ where
  -- Push plain value
  PUSH : PVal A → Code Γ (ValTy A ∷ S) S' → Code Γ S S'

  -- generate closure and push it
  ABS :
    -- Function body
    (∀{S₁ S₂ S₃ Γ₁ Γ'₁ A'} → Code (A ∷ Γ) (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E₁) ∷ (S₁ ++ HandTy Γ'₁ S₂ S₃ (A' , E₁) ∷ S₂)) S₃)  →
    Code Γ (ValTy (A ⇒ (B , E₁)) ∷ S) S' → Code Γ S S'

  -- push first-class handlder
  HANDLER : HandlerCode Γ C D → Code Γ (ValTy (Hand (C ⇒ D)) ∷ S) S' → Code Γ S S'

  -- read a value from environment and push it
  LOOKUP : A ∈ Γ → Code Γ (ValTy A ∷ S) S' → Code Γ S S'

  -- application
  APP : PureCodeCont Γ (ValTy B ∷ S₁) (A' , E) → 
        Code Γ (ValTy A ∷ ValTy (A ⇒ (B , E)) ∷ S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E) ∷ S₂) S₃

  -- operation call
  CALLOP : (op A B) ∈ E 
            → PureCodeCont Γ (ValTy B ∷ S₁) (A' , E) -- PureCode code continuation
            → Code Γ (ValTy A ∷ S₁ ++ HandTy Γ₁ S S' (A' , E) ∷ S) S'

  BIND : Code (A ∷ Γ) (ContTy Γ (ValTy B ∷ S) C ∷ (S ++ HandTy Γ₂ S₂ S₃ C ∷ S₂)) S₃ -- let-body
        → PureCodeCont Γ (ValTy B ∷ S) C → Code Γ (ValTy A ∷ (S ++ HandTy Γ₂ S₂ S₃ C ∷ S₂)) S₃

  -- return from function application
  RET : Code Γ (ValTy A ∷ ContTy Γ₁ (ValTy A ∷ S) C ∷ (S ++ HandTy Γ₂ S₂ S₃ C ∷ S₂)) S₃

  -- delimit continuation
  MARK :
    PureCodeCont Γ (ValTy B ∷ S₁) (B' , E₂) → -- meta continuation
    (∀{Γ'₁} → -- computation to be handled
      Code Γ (HandTy Γ'₁ (S₁ ++ HandTy Γ₁ S₂ S₃ (B' , E₂) ∷ S₂) S₃ (A , E₁) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (B' , E₂) ∷ S₂)) S₃ ) →
    Code Γ (ValTy (Hand ((A , E₁) ⇒ (B , E₂))) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (B' , E₂) ∷ S₂)) S₃

  -- call return clause of handler on stack
  UNMARK : Code Γ (ValTy A ∷ HandTy Γ₁ S S' (A , E₁) ∷ S) S'

  -- push top-level handler
  INITHAND : Code Γ (HandTy Γ S (ValTy A ∷ S) (A , []) ∷ S) (ValTy A ∷ S) → Code Γ S (ValTy A ∷ S)

OperationCodes B E₁ E₂ Γ SS S₃ = All (λ {(op A' B') → Code ((B' ⇒ (B , E₂)) ∷ A' ∷ Γ) SS S₃ }) E₁

HandlerCode Γ (A , E₁) (B , E₂) =
  (∀{Γ₁ Γ'₁ S₁ S₂ S₃ A'} →
    Code (A ∷ Γ) (ContTy Γ'₁ (ValTy B ∷ S₁) (A' , E₂) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E₂) ∷ S₂)) S₃ ×
    OperationCodes B E₁ E₂ Γ (ContTy Γ'₁ (ValTy B ∷ S₁) (A' , E₂) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E₂) ∷ S₂)) S₃
  )


data EnvVal : VTy → Set
RuntimeEnv : Ctx → Set
data StackVal : SValTy → Set
Stack : StackTy → Set

data EnvVal where
  -- plain values
  pval : PVal A → EnvVal A
  -- closures
  clos : (∀{Γ₁ Γ'₁ S₁ S₂ S₃ A'} → Code (A ∷ Γ) (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E) ∷ (S₁ ++ HandTy Γ'₁ S₂ S₃ (A' , E) ∷ S₂)) S₃)
          → RuntimeEnv Γ → EnvVal (A ⇒ (B , E))
  -- first-class continuations
  resump :  PureCodeCont Γ (ValTy A ∷ S) (A' , E) × Stack S × RuntimeEnv Γ → 
            EnvVal (Hand ((A' , E) ⇒ (B , E'))) → EnvVal (A ⇒ (B , E'))
  -- first-class handlers
  fc-hand : HandlerCode Γ (A , E₁) (B , E₂) → RuntimeEnv Γ → EnvVal (Hand ((A , E₁) ⇒ (B , E₂)))

RuntimeEnv Γ = All (λ A → EnvVal A) Γ

data StackVal where
  val  : EnvVal A → StackVal (ValTy A)
  cont : PureCodeCont Γ S₁ (A , E) → RuntimeEnv Γ → StackVal (ContTy Γ S₁ (A , E))
  hand : StackVal (ContTy Γ₂ (ValTy B ∷ S₁) (A' , E₂)) -- meta-continuation
          → HandlerCode Γ (A , E₁) (B , E₂) -- handler body
          → RuntimeEnv Γ -- runtime environment of the body
          → StackVal (HandTy Γ (S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E₂) ∷ S₂) S₃ (A , E₁))
  init-hand : StackVal (HandTy Γ S (ValTy A ∷ S) (A , []))

Stack S = All (λ T → StackVal T) S

_++s_ : Stack S → Stack S' → Stack (S ++ S')
[] ++s s = s
(x ∷ xs) ++s s = x ∷ (xs ++s s)

infixr 20 _++s_

split : Stack (S₁ ++ HandTy Γ₁ S S' (A , E) ∷ S) → Stack S₁ × StackVal (HandTy Γ₁ S S' (A , E)) × Stack S
split {S₁ = []} (H ∷ S) = ([] , H , S)
split {S₁ = _ ∷ _} (V ∷ S) with split S
... | (S1 , H , S2) = (V ∷ S1 , H , S2)


{-# TERMINATING #-}
exec : Code Γ S S' → Stack S → RuntimeEnv Γ → Stack S'

exec (PUSH v c) s = exec c $ (val (pval v)) ∷ s

exec (ABS c' c) s env = exec c (val (clos c' env) ∷ s) env

exec (HANDLER h c) s env = exec c (val (fc-hand h env) ∷ s) env

exec (LOOKUP x c) s env = exec c ((val $ lookup env x) ∷ s) env

exec (APP c) (val v ∷ val (clos c' env') ∷ s) env = exec c' (cont c env ∷ s) (v ∷ env')

exec (APP c) (v ∷ val (resump (c' , s' , env₂) (fc-hand h envh)) ∷ s) env = exec c' (v ∷ (s' ++s (hand (cont c env) h envh ∷ s))) env₂

exec (CALLOP l c) (val v ∷ s) env with split s
... | (s1 , (hand mk h env') , s2) with h
... | (_ , ops) = exec (lookup ops l) (mk ∷ s2) (resump (c , s1 , env) (fc-hand h env') ∷ v ∷ env')

exec (BIND c k) (val v ∷ s) env = exec c (cont k env ∷ s) (v ∷ env)

exec RET (val v ∷ cont c env ∷ s) _ = exec c (val v ∷ s) env

exec (MARK mk c) (val (fc-hand h env') ∷ s) env = exec c (hand (cont mk env) h env' ∷ s) env

exec (UNMARK) (val x ∷ (hand mk h env') ∷ s) env with h
... | (ret , ops) = exec ret (mk ∷ s) (x ∷ env')

exec (UNMARK) (val x ∷ init-hand ∷ s) env = val x ∷ s

exec (INITHAND c) s env = exec c (init-hand ∷ s) env

-- ************************
-- Compilers
-- ************************

compileV : Val Γ A → Code Γ (ValTy A ∷ S) S' → Code Γ S S'
compileC : Cmp Γ (A , E) → PureCodeCont Γ (ValTy A ∷ S₁) (A' , E) → Code Γ (S₁ ++ HandTy Γ₁ S S' (A' , E) ∷ S) S'  

compileOps :
  OperationClauses Γ E₁ (B , E₂) →
  ∀{S₁ S₂ S₃ Γ₁ Γ'₁ A} → OperationCodes B E₁ E₂ Γ (ContTy Γ'₁ (ValTy B ∷ S₁) (A , E₂) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (A , E₂) ∷ S₂)) S₃
compileOps {E₁ = []} [] = []
compileOps {E₁ = (op A' B') ∷ E'}{B = B}{E₂ = E₂} (e ∷ es) {S₁} {S₂} {S₃} {Γ₁} {Γ'₁} {A₁} =
  (compileC {S₁ = ContTy Γ'₁ (ValTy B ∷ S₁) (A₁ , E₂) ∷ _} e RET) ∷ (compileOps es)

compileV Unit = PUSH unit
compileV (Var x) = LOOKUP x
compileV {A = A ⇒ (B , E₁)} (Lam e) =
  ABS (λ {S₁ S₂ S₃ Γ₁ Γ'₁ A'} → compileC {S₁ = (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E₁)) ∷ _} e RET)
compileV (Handler {H = (_ , _) ⇒ (B , E₂)} (ƛx ret |ƛx,r ops)) =
  HANDLER (λ {Γ₁ Γ'₁ S₁ S₂ S₃ A'} → compileC {S₁ = ContTy Γ'₁ (ValTy B ∷ S₁) (A' , E₂) ∷ _} ret RET , compileOps ops)

compileC (Handle e With h) k = compileV h $ MARK k (compileC {S₁ = []} e UNMARK)
compileC (Let_In_ {A = A}{E = E₁}{B = B} e1 e2) k =
  compileC e1 $ BIND (compileC {S₁ = (ContTy _ (ValTy B ∷ _) (_ , _) ∷ _)} e2 RET) k
compileC (Return v) k = compileV v k
compileC (Do l v) k = compileV v $ CALLOP l k
compileC (App v1 v2) k = compileV v1 $ compileV v2 $ APP k


compile : Cmp Γ (A , []) → Code Γ S (ValTy A ∷ S)
compile c = INITHAND (compileC {S₁ = []} c UNMARK)


module PEPM2024.Compiler where

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

data Cmp Γ where
  Return : Val Γ A → Cmp Γ (A , E)
  Do : (op A B) ∈ E → Val Γ A → Cmp Γ (B , E)
  Handle_With_  : Cmp Γ C → Hdl Γ (C ⇒ D) → Cmp Γ D
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
PureCodeCont Γ S₁ C = 
  ∀{Γ₁ S₂ S₃} → Code Γ (S₁ ++ HandTy Γ₁ S₂ S₃ C ∷ S₂) S₃

data Code Γ where
  PUSH : PVal A → Code Γ (ValTy A ∷ S) S' → Code Γ S S'
  ABS :
    -- function body
    (∀{S₁ S₂ S₃ Γ₁ Γ'₁ A'} → Code (A ∷ Γ) (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E₁) ∷ (S₁ ++ HandTy Γ'₁ S₂ S₃ (A' , E₁) ∷ S₂)) S₃)  →
    Code Γ (ValTy (A ⇒ (B , E₁)) ∷ S) S' → Code Γ S S'
  LOOKUP : A ∈ Γ → Code Γ (ValTy A ∷ S) S' → Code Γ S S'
  APP : PureCodeCont Γ (ValTy B ∷ S₁) (A' , E) → 
        Code Γ (ValTy A ∷ ValTy (A ⇒ (B , E)) ∷ S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E) ∷ S₂) S₃
  CALLOP : (op A B) ∈ E 
            → PureCodeCont Γ (ValTy B ∷ S₁) (A' , E)
            → Code Γ (ValTy A ∷ S₁ ++ HandTy Γ₁ S S' (A' , E) ∷ S) S'
  BIND : Code (A ∷ Γ) (ContTy Γ (ValTy B ∷ S) C ∷ (S ++ HandTy Γ₂ S₂ S₃ C ∷ S₂)) S₃ -- let body
        → PureCodeCont Γ (ValTy B ∷ S) C → Code Γ (ValTy A ∷ (S ++ HandTy Γ₂ S₂ S₃ C ∷ S₂)) S₃
  RET : Code Γ (ValTy A ∷ ContTy Γ₁ (ValTy A ∷ S) C ∷ (S ++ HandTy Γ₂ S₂ S₃ C ∷ S₂)) S₃
  MARK :
    HandlerCode Γ (A , E₁) (B , E₂) → -- handler
    PureCodeCont Γ (ValTy B ∷ S₁) (B' , E₂) → -- meta-continuation
    -- handled computation
    Code Γ (
      HandTy Γ (ContTy Γ (ValTy B ∷ S₁) (B' , E₂) ∷ S₁ ++ HandTy Γ₁ S₂ S₃ (B' , E₂) ∷ S₂) S₃ (A , E₁) ∷ 
                ContTy Γ (ValTy B ∷ S₁) (B' , E₂) ∷ S₁ ++ HandTy Γ₁ S₂ S₃ (B' , E₂) ∷ S₂
    ) S₃ →
    Code Γ (S₁ ++ HandTy Γ₁ S₂ S₃ (B' , E₂) ∷ S₂) S₃
  UNMARK : Code Γ (ValTy A ∷ HandTy Γ₁ S S' (A , E₁) ∷ S) S'
  INITHAND : Code Γ (HandTy Γ S (ValTy A ∷ S) (A , []) ∷ S) (ValTy A ∷ S) → Code Γ S (ValTy A ∷ S)

OperationCodes B E₁ E₂ Γ SS S₃ = All (λ {(op A' B') → Code ((B' ⇒ (B , E₂)) ∷ A' ∷ Γ) SS S₃ }) E₁

HandlerCode Γ (A , E₁) (B , E₂) =
  (∀{Γ₁ Γ'₁ S₁ S₂ S₃ A'} →
    -- return clause
    Code (A ∷ Γ) (ContTy Γ'₁ (ValTy B ∷ S₁) (A' , E₂) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E₂) ∷ S₂)) S₃ ×
    -- operation clauses
    OperationCodes B E₁ E₂ Γ (ContTy Γ'₁ (ValTy B ∷ S₁) (A' , E₂) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E₂) ∷ S₂)) S₃
  )

data EnvVal : VTy → Set
RuntimeEnv : Ctx → Set

data StackVal : SValTy → Set

Stack : StackTy → Set
Stack S = All (λ T → StackVal T) S

data EnvVal where
  pval : PVal A → EnvVal A
  clos : (∀{Γ₁ Γ'₁ S₁ S₂ S₃ A'} → Code (A ∷ Γ) (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E) ∷ (S₁ ++ HandTy Γ'₁ S₂ S₃ (A' , E) ∷ S₂)) S₃)
          → RuntimeEnv Γ → EnvVal (A ⇒ (B , E))
  fc-resump : 
    PureCodeCont Γ (ValTy A ∷ S) (A' , E) × Stack S × RuntimeEnv Γ → -- continuation body and its stores
    HandlerCode Γ₁ (A' , E) (B , E') × RuntimeEnv Γ₁ → -- handler and its environment
    EnvVal (A ⇒ (B , E'))

RuntimeEnv Γ = All (λ A → EnvVal A) Γ

data StackVal where
  val  : EnvVal A → StackVal (ValTy A)
  cont : PureCodeCont Γ S₁ (A , E) → RuntimeEnv Γ → StackVal (ContTy Γ S₁ (A , E))
  hand :  HandlerCode Γ (A , E₁) (B , E₂) → RuntimeEnv Γ → 
          StackVal (HandTy Γ (ContTy Γ₂ (ValTy B ∷ S₁) (A' , E₂) ∷ S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E₂) ∷ S₂) S₃ (A , E₁))
  init-hand : StackVal (HandTy Γ S (ValTy A ∷ S) (A , []))

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
exec (LOOKUP x c) s env = exec c ((val $ lookup env x) ∷ s) env
exec (APP c) (val v ∷ val (clos c' env') ∷ s) env = exec c' (cont c env ∷ s) (v ∷ env')
exec (APP c) (v ∷ val (fc-resump (c' , s' , env₂) (h , envh)) ∷ s) env =
  exec c' (v ∷ (s' ++s (hand h envh ∷ cont c env ∷ s))) env₂
exec (CALLOP l c) (val v ∷ s) env with split s
... | (s1 , (hand h env') , s2) with h
... | (_ , ops) = exec (lookup ops l) s2 (fc-resump (c , s1 , env) (h , env') ∷ v ∷ env')
exec (BIND c k) (val v ∷ s) env = exec c (cont k env ∷ s) (v ∷ env)
exec RET (val v ∷ cont c env ∷ s) _ = exec c (val v ∷ s) env
exec (MARK h mk c) s env = exec c (hand h env ∷ cont mk env ∷ s) env
exec (UNMARK) (val x ∷ (hand h env') ∷ s) env with h
... | (ret , ops) = exec ret s (x ∷ env')
exec (UNMARK) (val x ∷ init-hand ∷ s) env = val x ∷ s
exec (INITHAND c) s env = exec c (init-hand ∷ s) env

compileV : Val Γ A → Code Γ (ValTy A ∷ S) S' → Code Γ S S'
compileC : Cmp Γ (A , E) → PureCodeCont Γ (ValTy A ∷ S₁) (A' , E) → Code Γ (S₁ ++ HandTy Γ₁ S S' (A' , E) ∷ S) S'
-- auxiliary function for compiling handlers
compileH : Hdl Γ (C ⇒ D) → HandlerCode Γ C D
-- auxiliary function for compiling operation clauses
compileOps :
  OperationClauses Γ E₁ (B , E₂) →
  ∀{S₁ S₂ S₃ Γ₁ Γ'₁ A} → OperationCodes B E₁ E₂ Γ (ContTy Γ'₁ (ValTy B ∷ S₁) (A , E₂) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (A , E₂) ∷ S₂)) S₃

compileV Unit = PUSH unit
compileV (Var x) = LOOKUP x
compileV {A = A ⇒ (B , E₁)} (Lam e) =
  ABS (λ {S₁ S₂ S₃ Γ₁ Γ'₁ A'} → compileC {S₁ = (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E₁)) ∷ _} e RET)

compileC (Handle e With h) k = MARK (compileH h) k (compileC {S₁ = []} e UNMARK)
compileC (Let_In_ {A = A}{E = E₁}{B = B} e1 e2) k =
  compileC e1 $ BIND (compileC {S₁ = (ContTy _ (ValTy B ∷ _) (_ , _) ∷ _)} e2 RET) k
compileC (Return v) k = compileV v k
compileC (Do l v) k = compileV v $ CALLOP l k
compileC (App v1 v2) k = compileV v1 $ compileV v2 $ APP k

compileH {D = (B , E₂)} (ƛx ret |ƛx,r ops) {Γ₁} {Γ'₁} {S₁} {S₂} {S₃} {A'} =
  (compileC {S₁ = ContTy Γ'₁ (ValTy B ∷ S₁) (A' , E₂) ∷ _} ret RET , compileOps ops)

compileOps {E₁ = []} [] = []
compileOps {E₁ = (op A' B') ∷ E'}{B = B}{E₂ = E₂} (e ∷ es) {S₁} {S₂} {S₃} {Γ₁} {Γ'₁} {A₁} =
  (compileC {S₁ = ContTy Γ'₁ (ValTy B ∷ S₁) (A₁ , E₂) ∷ _} e RET) ∷ (compileOps es)

compile : Cmp Γ (A , []) → Code Γ S (ValTy A ∷ S)
compile c = INITHAND (compileC {S₁ = []} c UNMARK)


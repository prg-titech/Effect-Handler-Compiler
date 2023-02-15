module LCWithException where

open import Data.Empty
open import Data.Nat  using (ℕ; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; _∧_)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List using ( List; _∷_; []; map; _++_ )
open import Data.Product using ( _×_ ; _,_ )
open import Function using ( _∘_; _$_ )
open import Data.Unit using (⊤; tt)
open import Data.Maybe.Base renaming (_>>=_ to _»=_)
open import Relation.Binary.PropositionalEquality

-- ********************
-- VTyped Source Language
-- ********************

data VTy : Set
CTy : Set

data VTy where
  N : VTy
  _⇒_ : VTy → CTy → VTy

-- Boolean index that specifies if an expression can throw an exception or not
CTy = VTy × Bool

Ctx : Set
Ctx = List VTy

variable
  a b : Bool
  A B : VTy
  C D : CTy
  Γ : Ctx


data Val (Γ : Ctx) : VTy → Set
data Cmp (Γ : Ctx) : CTy → Set

-- Pure values
data Val Γ where
  val : ℕ → Val Γ N
  var : A ∈ Γ → Val Γ A
  lam : Cmp (A ∷ Γ) C → Val Γ (A ⇒ C)

-- Computations that may cause exception
data Cmp Γ where
  add : Cmp Γ (N , a) → Cmp Γ (N , b) → Cmp Γ (N , a ∨ b)
  app : Val Γ (A ⇒ C) → Val Γ A → Cmp Γ C
  return : Val Γ A → Cmp Γ (A , false)
  throw : Cmp Γ (A , true)
  catch : Cmp Γ (A , a) → Cmp Γ (A , b) → Cmp Γ (A , a ∧ b)
  Let_In_ : Cmp Γ (A , a) → Cmp (A ∷ Γ) (B , b)  → Cmp Γ (B , a ∨ b)



-- ********************
-- VType-safe Evaluation
-- ********************

data Result : VTy → Set
Env : Ctx → Set

-- Values after evaluation
data Result where
  num : ℕ → Result N
  clos : Cmp (A ∷ Γ) C → Env Γ → Result (A ⇒ C)

-- Environment
Env Γ = All (λ T → Result T) Γ


{-# TERMINATING #-}
evalv : Val Γ A → Env Γ → Result A
evalc? : Cmp Γ (A , a) → Env Γ → Maybe (Result A)
evalc : b ≡ false → Cmp Γ (A , b) → Env Γ → Result A
eval : b ≡ false → Cmp [] (A , b) → Result A

-- evaluation for pure values
evalv (val n) _ = num n
evalv (var x) env = lookup env x
evalv (lam f) env = clos f env

-- Evaluation for computation that may cause exception.
-- When the computation causes exception, the result is nothing
evalc? throw env = nothing
evalc? (return v) env = just (evalv v env)
evalc? (catch c h) env with evalc? c env
... | just v = just v
... | nothing = evalc? h env
evalc? (app f e) env with evalv f env
... | clos b env' = evalc? b ((evalv e env) ∷ env')
evalc? (add e1 e2) env =
  evalc? e1 env »= λ { (num n1) →
    evalc? e2 env »= λ { (num n2) →
    just $ num $ n1 + n2 }}
evalc? (Let e1 In e2) env =
  evalc? e1 env »= λ { v →
    evalc? e2 (v ∷ env) }

-- evaluation for computations that cause no exception.
evalc _ (return v) = evalv v
evalc _ (catch {a = true} {b = false} c h) env with evalc? c env
... | just v = v
... | nothing = evalc refl h env

evalc _ (catch {a = false} c h) env = evalc refl c env

evalc p (app f e) env with evalv f env
... | clos b env' = evalc p b ((evalv e env) ∷ env')

evalc _ (add {a = false} {b = false} e1 e2) env with (evalc refl e1 env)
... | (num n1) with evalc refl e2 env
... | (num n2) = num $ n1 + n2

evalc _ (Let_In_ {a = false} {b = false} e1 e2) env with evalc refl e1 env
... | v = evalc refl e2 (v ∷ env)

-- top-level evaluation
eval p c = evalc p c []


-- ********************
-- Target Language
-- ********************

-- VTypes of Stack Results
data SValTy : Set
StackTy : Set

data SValTy where
  ValTy : VTy → SValTy
  HandTy : Ctx → StackTy → StackTy → SValTy
  ContTy : Ctx → StackTy → StackTy → SValTy

infixl 20 _⇒_ 

StackTy = List SValTy

variable
  Γ' Γ₁ : Ctx
  T : SValTy
  S S' S₁ S₂ S₃ : StackTy

-- target code (stack machine)
data Code (Γ : Ctx) : StackTy → StackTy → Set where
  PUSH : ℕ → Code Γ (ValTy N ∷ S) S' → Code Γ S S'
  ADD : Code Γ (ValTy N ∷ S) S' → Code Γ (ValTy N ∷ ValTy N ∷ S) S'

  -- 例外ハンドラを追加
  MARK   : Code Γ S S' → Code Γ (HandTy Γ S S' ∷ S) S' → Code Γ S S'

  -- 例外xハンドラを消去
  UNMARK : Code Γ (T ∷ S) S' → Code Γ (T ∷ HandTy Γ₁ S S' ∷ S) S'

  THROW : Code Γ (S₁ ++ HandTy Γ₁ S S' ∷ S) S'

  HALT  : Code Γ S S

  -- 環境から変数が指す値を読む
  LOOKUP : A ∈ Γ → Code Γ (ValTy A ∷ S) S' → Code Γ S S'

  -- 関数クロージャ生成 ABS c' c ... c'は関数本体、cは継続
  ABS : (∀{S₁ S₂ Γ₁} →
          Code (A ∷ Γ) (ContTy Γ₁ (ValTy B ∷ S₁) S₂ ∷ S₁) S₂) →
        Code Γ (ValTy (A ⇒ (B , false)) ∷ S) S' →
        Code Γ S S'

  -- effectful計算関数用クロージャ生成 ABS c' c ... c'は関数本体、cは継続
  ABSImpure : (∀{S₁ S₂ S₃ Γ₁ Γ'₁} →
          Code (A ∷ Γ) ((ContTy Γ₁ (ValTy B ∷ (S₁ ++ HandTy Γ'₁ S₃ S₂ ∷ S₃)) S₂) ∷ (S₁ ++ HandTy Γ'₁ S₃ S₂ ∷ S₃)) S₂) →
        Code Γ (ValTy (A ⇒ (B , true)) ∷ S) S' →
        Code Γ S S'

  -- return命令
  RET : Code Γ (ValTy A ∷ ContTy Γ₁ (ValTy A ∷ S) S' ∷ S) S'

  -- 関数クロージャを実行する
  APP : Code Γ (ValTy B ∷ S) S' → Code Γ (ValTy A ∷ ValTy (A ⇒ (B , false)) ∷ S) S'

  -- suspended computationを再開
  APPImpure : Code Γ (ValTy B ∷ (S₁ ++ HandTy Γ₁ S₃ S₂ ∷ S₃)) S₂
        → Code Γ (ValTy A ∷ ValTy (A ⇒ (B , true)) ∷ (S₁ ++ HandTy Γ₁ S₃ S₂ ∷ S₃)) S₂

  -- Let Binding let x = e1 in e2
  -- Pop stack, and execute the body adding the value into environment
  BIND :
    -- let-body
    Code (A ∷ Γ) S S' →
    -- code continuation
    Code Γ (ValTy B ∷ S) S' →
    Code Γ (ValTy A ∷ S) S'

-- compiled value from source language
data EnvVal : VTy → Set
-- Stack Results
data StackVal : SValTy → Set
-- Bounded Results
RuntimeEnv : List VTy → Set

data EnvVal where
  num  : ℕ → EnvVal N
  clos : ( ∀{Γ₁ S₁ S₂} → Code (A ∷ Γ) ((ContTy Γ₁ (ValTy B ∷ S₁) S₂) ∷ S₁) S₂) 
    → RuntimeEnv Γ
    → EnvVal (A ⇒ (B , false))
  -- suspended computation
  closImpure : (∀{S₁ S₂ S₃ Γ₁ Γ'₁} →
          Code (A ∷ Γ) ((ContTy Γ₁ (ValTy B ∷ (S₁ ++ HandTy Γ'₁ S₃ S₂ ∷ S₃)) S₂) ∷ (S₁ ++ HandTy Γ'₁ S₃ S₂ ∷ S₃)) S₂)
          → RuntimeEnv Γ
          → EnvVal (A ⇒ (B , true))

data StackVal where
  val  : EnvVal A → StackVal (ValTy A)
  cont : Code Γ S S' → RuntimeEnv Γ → StackVal (ContTy Γ S S')
  hand : Code Γ S S' → RuntimeEnv Γ → StackVal (HandTy Γ S S')

RuntimeEnv Γ = All (λ T → EnvVal T) Γ

Stack : StackTy → Set
Stack S = All (λ A → StackVal A) S


{-# TERMINATING #-}
exec : Code Γ S S' → Stack S → RuntimeEnv Γ → Stack S'
-- Stackの1番頭にあるハンドラコードを実行
fail : Stack (S₁ ++ HandTy Γ S S' ∷ S) → Stack S'

exec (PUSH n c) s = exec c $ (val (num n)) ∷ s
exec (ADD c) ((val (num n)) ∷ (val (num m)) ∷ s) = exec c ((val (num (n + m)) ∷ s))
exec (MARK h c) s env = exec c (hand h env ∷ s) env
exec (UNMARK c) (x ∷ h ∷ s) = exec c (x ∷ s)
exec THROW s _ = fail s
exec HALT s env = s

exec (LOOKUP x c) s env =
  exec c ((val $ lookup env x) ∷ s) env

exec (ABS c' c) s env =
  exec c (val (clos c' env) ∷ s) env

exec (ABSImpure c' c) s env =
  exec c (val (closImpure c' env) ∷ s) env

exec (RET) (val v ∷ cont c env ∷ s) _ =
  exec c (val v ∷ s) env

exec (APP c) (val v ∷ val (clos c' env') ∷ s) env =
  exec c' (cont c env ∷ s) (v ∷ env')

exec (APPImpure c) (val v ∷ val (closImpure c' env') ∷ s) env =
  exec c' (cont c env ∷ s) (v ∷ env')

exec (BIND c k) (val v ∷ s) env =
  exec c s (v ∷ env)

-- Stackの1番頭にあるハンドラコードを実行
fail {S₁ = []} ((hand h env) ∷ s) = exec h s env
fail {S₁ = _ ∷ _} (v ∷ s) = fail s


-- ********************
-- VType-safe Compiler
-- ********************

-- compiler for pure values
compileV : Val Γ A → Code Γ (ValTy A ∷ S) S' → Code Γ S S'
-- compiler for effectful expression
compileC? : Cmp Γ (A , a) → Code Γ (ValTy A ∷ (S₁ ++ HandTy Γ₁ S S' ∷ S)) S' → Code Γ (S₁ ++ HandTy Γ₁ S S' ∷ S) S'
-- compiler for pure computation
compileC : (b ≡ false) → Cmp Γ (A , b) → Code Γ (ValTy A ∷ S) S' → Code Γ S S'

compileV (val n) c = PUSH n c
compileV (var x) c = LOOKUP x c
compileV {Γ = Γ} {A = A ⇒ (B , true)} (lam cmp) c
  = ABSImpure (λ {S₁ S₂ S₃ Γ₁ Γ'₁} → compileC? {S₁ = (ContTy Γ₁ (ValTy B ∷ (S₁ ++ HandTy Γ'₁ S₃ S₂ ∷ S₃)) S₂) ∷ _} cmp RET) c
compileV {A = A ⇒ (B , false)} (lam cmp) c = ABS (compileC refl cmp RET) c

compileC? throw _ = THROW
compileC? (return v) c = compileV v c
compileC? (add e1 e2) c = compileC? e1 $ compileC? {S₁ = ValTy N ∷ _} e2 $ ADD c
compileC? (catch e h) c = MARK (compileC? h c) (compileC? {S₁ = []} e $ UNMARK c)
compileC? {a = false} (app f e) c = compileV f $ compileV e $ APP c
compileC? {a = true} (app f e) c = compileV f $ compileV e $ APPImpure c

compileC _ (return v) c = compileV v c
compileC _ (add {false} {false} e1 e2) c =
  compileC refl e1 $ compileC refl e2 $ ADD c

compileC _ (catch {a = false} e h) c = compileC refl e c

compileC _ (catch {a = true} {b = false} e h) c =
  MARK (compileC refl h c) (compileC? {S₁ = []} e $ UNMARK c)

compileC _ (app {C = (A , false)} f e) c =
  compileV f $ compileV e $ APP c



top-level-compile : b ≡ false → Cmp Γ (A , b) → Code Γ S (ValTy A ∷ S)
top-level-compile p e = compileC p e HALT



-- Equations of Compiler Correctness

-- exec (compile p e c) s ≡ exec c (eval p e ▷ s)

-- exec (compileV v c) (s , env) ≡ exec c (evalv v env ▷ s)

-- exec (compileC? comp c) s = case evalc? c of
--   just v → exec c (n ▷ s)
--   nothing → fail s

-- exec (compileC comp c) s = exec c ((evalc c) ▷ s)


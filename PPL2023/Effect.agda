module Effect where

open import Data.Empty
open import Data.Nat  using (ℕ) renaming (_+_ to add)
open import Data.Bool using (true; false; if_then_else_; _∨_; _∧_) renaming (Bool to 𝔹)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup; []; uncons)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List using ( List; _∷_; []; map; _++_ )
open import Data.Product using ( _×_ ; _,_ )
open import Function using ( _∘_; _$_ )
open import Data.Unit using (⊤; tt)
open import Data.Maybe.Base
open import Relation.Binary.PropositionalEquality

-- *****************
-- types and effects
-- *****************
data VTy : Set
CTy : Set
data HTy : Set

data Sig : Set
Eff : Set

-- Types of values
data VTy where
  Unit   : VTy
  Bool   : VTy
  Nat    : VTy
  _*_    : VTy → VTy → VTy  -- pair
  _⇒_    : VTy → CTy → VTy
  Lst    : VTy → VTy
  Hand   : HTy → VTy

-- Type of computations
CTy = VTy × Eff

-- Type of handlers
data HTy where
  -- A[E]⇒[E']B
  -- A : Input type , B : Output type
  -- E : Effects before handle
  -- E' : Effects after handle
  _⇒_ : CTy → CTy → HTy

-- Effect signatures
data Sig where
  -- recieve parameter type and Return type
  op : VTy → VTy → Sig

-- Effect rows
Eff = List Sig



-- Type context
Ctx = List VTy


variable
  A B A' B' : VTy
  E E' E₁ E₂ : Eff
  C D : CTy
  H : HTy
  Γ Γ' Γ₁ Γ₂ : Ctx


-- ************
-- Intrinsically-typed Syntax
-- ************
data Val (Γ : Ctx) : VTy → Set
data Cmp (Γ : Ctx) : CTy → Set
data Handler (Γ : Ctx) : HTy → Set
OperationClauses : Ctx → Eff → CTy → Set

-- Well-typed values
data Val Γ where
  var   : A ∈ Γ → Val Γ A
  unit  : Val Γ Unit
  fun   : Cmp (A ∷ Γ) C → Val Γ (A ⇒ C)
  handler : Handler Γ H → Val Γ (Hand H)
  bl  : 𝔹 → Val Γ Bool
  num  : ℕ → Val Γ Nat


-- Well-typed computations
data Cmp Γ where
  -- Application
  app : Val Γ (A ⇒ C) → Val Γ A → Cmp Γ C
  -- 値を返すだけの計算
  Return  : Val Γ A → Cmp Γ (A , E)
  -- オペレーション呼び出し
  Do : (op A B) ∈ E → Val Γ A → Cmp Γ (B , E)
  -- エフェクトハンドリング
  Handle_With_ : Cmp Γ C →　Val Γ (Hand (C ⇒ D)) →　Cmp Γ D

  Let_In_ : 
    Cmp Γ (A , E) →
    (Cmp (A ∷ Γ) (B , E)) →
    Cmp Γ (B , E)

  _&_ : Val Γ Bool → Val Γ Bool → Cmp Γ (Bool , E)
  _+_ : Val Γ Nat → Val Γ Nat → Cmp Γ (Nat , E)

-- Well-typed Handlers
data Handler Γ where
  ƛx_|ƛx,r_ :
    -- Return clause
    Cmp (A ∷ Γ) C →
    -- Operation clauses
    OperationClauses Γ E C →
    Handler Γ ((A , E) ⇒ C)

-- Operation clauses
OperationClauses Γ E₁ D =
  All (λ {(op A' B') →
    Cmp ((B' ⇒ D) ∷ A' ∷ Γ) D}
  ) E₁



-- ************************
-- Type-safe Evaluation
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

-- Values after evaluations
data Result where
  tt   : Result Unit
  bl   : 𝔹 → Result Bool
  num  : ℕ → Result Nat
  clos : ∀{A C Γ} → Cmp (A ∷ Γ) C → Env Γ → Result (A ⇒ C)
  list : ∀{A} → List (Result A) → Result (Lst A)
  resump : PureStackFrame A C → Result (Hand (C ⇒ D)) → Result (A ⇒ D)
  hand : Handler Γ H → Env Γ → Result (Hand H)

-- Environment
Env Γ = All (λ A → Result A) Γ

-- Patterns of hole
-- Frame A C ... A is expected type for the hole, C is the type of the whole expression
data Frame where
  app□_,_ : Val Γ A → Env Γ → Frame (A ⇒ C) C
  app_□ : Result (A ⇒ C) → Frame A C

  _&□ : Result Bool → Frame Bool (Bool , E)
  □&_,_ : Val Γ Bool → Env Γ → Frame Bool (Bool , E)
  _+□ : Result Nat → Frame Nat (Nat , E)
  □+_,_ : Val Γ Nat → Env Γ → Frame Nat (Nat , E)

  Let□In_,_ : (Cmp (A ∷ Γ) C) →
              Env Γ →
              Frame A C

  Do_□ : (op A B) ∈ E → Frame A (B , E)

  Handle_With□,_ :
    Cmp Γ (A , E) → Env Γ → Frame (Hand ((A , E) ⇒ (B , E'))) (B , E')

-- Shapes of pure continuation
data PureStackFrame where
  empty : PureStackFrame A (A , E)
  extend : Frame A (A' , E) → PureStackFrame A' (B , E) →
            PureStackFrame A (B , E)

-- Shapes of meta continuation
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
evalv : Val Γ A → Env Γ →
        PureStackFrame A (A' , E) → MetaStackFrame (A' , E) (B , []) →
        Result B

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

resumeCont v empty empty
  = v

resumeCont v (extend (Do l □) K) (H [ K' [Handle□With h ]]) with h
... | hand (ƛx ret |ƛx,r es) env' =
  evalc (lookup es l) ((resump K (hand (ƛx ret |ƛx,r es) env')) ∷ v ∷ env') K' H

resumeCont v (extend (app (resump K' h') □) K) H =
  resumeCont v K' (H [ K [Handle□With h' ]])

resumeCont h (extend (Handle e With□, env') K) H =
  evalc e env' empty $ (H [ K [Handle□With h ]])

resumeCont v (extend (app□ v2 , env) K) =
  evalv v2 env (extend (app v □) K)

resumeCont v (extend (app (clos e' env') □) K) =
  evalc e' (v ∷ env') K

resumeCont v (extend (Let□In e2 , env) K) =
  evalc e2 (v ∷ env) K 

resumeCont (bl a) (extend ((bl b) &□) K) H =
  resumeCont (bl $ b ∧ a) K H

resumeCont v (extend (□& v2 , env) K) H =
  evalv v2 env (extend (v &□) K) H

resumeCont (num n) (extend ((num m) +□) K) H =
  resumeCont (num (add n m)) K H

resumeCont v (extend (□+ v2 , env) K) H =
  evalv v2 env (extend (v +□) K) H


evalv unit _          = resumeCont tt
evalv (var x) env       = resumeCont $ lookup env x
evalv (fun f) env       = resumeCont $ clos f env
evalv (handler h) env   = resumeCont $ hand h env
evalv (bl b) _        = resumeCont $ bl b
evalv (num n) _       = resumeCont $ num n


evalc (app v1 v2) env K =
  evalv v1 env $ extend (app□ v2 , env) K

evalc (Return v) env K =
  evalv v env K

evalc (Do l v) env K =
  evalv v env $ (extend (Do l □) K)

evalc (Handle e With h) env K =
  evalv h env $ extend (Handle e With□, env) K

evalc (Let e1 In e2) env K =
  evalc e1 env $ extend (Let□In e2 , env) K

evalc (v1 & v2) env K = evalv v1 env $ extend (□& v2 , env) K

evalc (v1 + v2) env K = evalv v1 env $ extend (□+ v2 , env) K


-- ************************
-- Target language
-- ************************

-- Target : stack-base abstract machine


data SValTy : Set
StackTy : Set

-- Types of Stack Values
data SValTy where
  ValTy  : VTy → SValTy
  HandTy : Ctx → StackTy → StackTy → CTy → SValTy
  ContTy : Ctx → StackTy → CTy → SValTy

-- Shape of Stack
StackTy = List SValTy

variable
  T : SValTy
  S S' S₁ S₂ S₃ : StackTy

-- immediate values
data PVal : VTy → Set where
  unit : PVal (Unit)
  num : ℕ → PVal (Nat)
  bl : 𝔹 → PVal (Bool)


-- target abstract machine code
data Code (Γ : Ctx) : StackTy → StackTy → Set
-- Codes of operation clauses
OperationCodes : VTy → Eff → Eff → Ctx → StackTy → StackTy → Set
HandlerCode : Ctx → CTy → CTy → Set
ContCode : Ctx → StackTy → CTy → Set

-- target abstract machine code
data Code Γ where
  -- PUSH immediate value into the stack
  PUSH : PVal A → Code Γ (ValTy A ∷ S) S' → Code Γ S S'

  -- Binary operations
  ADD : Code Γ (ValTy Nat ∷ S) S' → Code Γ (ValTy Nat ∷ ValTy Nat ∷ S) S'
  AND : Code Γ (ValTy Bool ∷ S) S' → Code Γ (ValTy Bool ∷ ValTy Bool ∷ S) S'

  -- 計算をハンドルする。
  MARK :
    ContCode Γ (ValTy B ∷ S₁) (B' , E₂) → -- メタ継続
    (∀{Γ'₁} → -- 処理対象の計算
      Code Γ (HandTy Γ'₁ (S₁ ++ HandTy Γ₁ S₂ S₃ (B' , E₂) ∷ S₂) S₃ (A , E₁) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (B' , E₂) ∷ S₂)) S₃ ) →
    Code Γ (ValTy (Hand ((A , E₁) ⇒ (B , E₂))) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (B' , E₂) ∷ S₂)) S₃

  -- ハンドラのreturn節を呼び出す
  UNMARK : Code Γ (ValTy A ∷ HandTy Γ₁ S S' (A , E₁) ∷ S) S'
  -- UNMARK :
  --   Code Γ (ValTy B ∷ S) S'-- メタ継続
  --   Code Γ (ValTy A ∷ HandTy Γ₁ S S' ((A , E₁) ⇒ (B , E₂)) ∷ S) S'

  -- オペレーション呼び出し
  CALLOP :
    (op A B) ∈ E
    → ContCode Γ (ValTy B ∷ S₁) (A' , E) -- 捕捉されたコード継続
    → Code Γ (ValTy A ∷ S₁ ++ HandTy Γ₁ S S' (A' , E) ∷ S) S'

  -- 初期継続をプッシュ
  INITHAND :
    Code Γ (HandTy Γ S (ValTy A ∷ S) (A , []) ∷ S) (ValTy A ∷ S) →
    Code Γ S (ValTy A ∷ S)

  -- Read a value from environment and push into the stack
  LOOKUP : A ∈ Γ → Code Γ (ValTy A ∷ S) S' → Code Γ S S'

  -- Generate function closure and push into the stack
  ABS :
    (∀{S₁ S₂ S₃ Γ₁ Γ'₁ A'} →
      -- Function body
      Code (A ∷ Γ) (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E₁) ∷ (S₁ ++ HandTy Γ'₁ S₂ S₃ (A' , E₁) ∷ S₂)) S₃)  →
    Code Γ (ValTy (A ⇒ (B , E₁)) ∷ S) S' →
    Code Γ S S'

  -- ハンドラ値をプッシュ
  HANDLER : 
    HandlerCode Γ (A , E₁) (B , E₂) → 
    Code Γ (ValTy (Hand ((A , E₁) ⇒ (B , E₂))) ∷ S) S' →
    Code Γ S S'

  -- Return from function execution
  RET : Code Γ (ValTy A ∷ ContTy Γ₁ (ValTy A ∷ S) C ∷ (S ++ HandTy Γ₂ S₂ S₃ C ∷ S₂)) S₃

  -- Application
  APP :
    ContCode Γ (ValTy B ∷ S₁) (A' , E) →
    Code Γ (ValTy A ∷ ValTy (A ⇒ (B , E)) ∷ S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E) ∷ S₂) S₃
  
  -- Let Binding let x = e1 in e2
  -- Pop stack, and execute the body adding the value into environment
  BIND :
    -- let-body
    Code (A ∷ Γ) S S' →
    -- code continuation
    Code Γ (ValTy B ∷ S) S' →
    Code Γ (ValTy A ∷ S) S'

-- operation節のコード
OperationCodes B E₁ E₂ Γ SS S₃ = 
  All (λ {(op A' B') → Code ((B' ⇒ (B , E₂)) ∷ A' ∷ Γ) SS S₃ }) E₁

-- ハンドラコードの型
HandlerCode Γ (A , E₁) (B , E₂) =
  (∀{Γ₁ Γ'₁ S₁ S₂ S₃ A'} →
    Code (A ∷ Γ) (ContTy Γ'₁ (ValTy B ∷ S₁) (A' , E₂) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E₂) ∷ S₂)) S₃ ×
    OperationCodes B E₁ E₂ Γ (ContTy Γ'₁ (ValTy B ∷ S₁) (A' , E₂) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E₂) ∷ S₂)) S₃)

-- 純粋な継続のコードの型
ContCode Γ S₁ (B , E) =
  ∀{Γ₁ S₂ S₃} →
    Code Γ (S₁ ++ HandTy Γ₁ S₂ S₃ (B , E) ∷ S₂) S₃

-- compiled value from source language
data EnvVal : VTy → Set
-- Bounded Values
RuntimeEnv : List VTy → Set
-- Type of stack
Stack : StackTy → Set

-- Values can be included in environment
data EnvVal where
  pval : PVal A → EnvVal A

  -- Function closure
  clos :
    (∀{Γ₁ Γ'₁ S₁ S₂ S₃ A'} →
      Code (A ∷ Γ)
        (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E) ∷ (S₁ ++ HandTy Γ'₁ S₂ S₃ (A' , E) ∷ S₂))
        S₃)
    → RuntimeEnv Γ
    → EnvVal (A ⇒ (B , E))

  -- 捕捉された継続
  resump :
    -- 継続本体とそれが使用するスタックと環境
    ContCode Γ (ValTy A ∷ S) (A' , E) × Stack S × RuntimeEnv Γ →
    -- 継続に対するハンドラ
    EnvVal (Hand ((A' , E) ⇒ (B , E'))) →
    EnvVal (A ⇒ (B , E'))

  -- 第一級のハンドラ値
  hand :
    HandlerCode Γ (A , E₁) (B , E₂) →
    RuntimeEnv Γ →
    EnvVal (Hand ((A , E₁) ⇒ (B , E₂)))


-- Stack Values
data StackVal : SValTy → Set where
  val  : EnvVal A → StackVal (ValTy A)
  -- 継続
  cont :
    ContCode Γ S₁ (A , E) → RuntimeEnv Γ
    → StackVal (ContTy Γ S₁ (A , E))
  -- ハンドラ本体とメタ継続
  hand : 
    StackVal (ContTy Γ₂ (ValTy B ∷ S₁) (A' , E₂)) -- メタ継続
    → HandlerCode Γ (A , E₁) (B , E₂)
    → RuntimeEnv Γ -- ハンドラコードの実行時環境
    → StackVal (HandTy Γ (S₁ ++ HandTy Γ₁ S₂ S₃ (A' , E₂) ∷ S₂) S₃ (A , E₁))
  -- トップレベル計算のための空のハンドラ
  id-hand : StackVal (HandTy Γ S (ValTy A ∷ S) (A , []))

RuntimeEnv Γ = All (λ A → EnvVal A) Γ

Stack S = All (λ T → StackVal T) S

-- concatenate two stack
_++s_ : Stack S → Stack S' → Stack (S ++ S')
[] ++s s = s
(x ∷ xs) ++s s = x ∷ (xs ++s s)

infixr 20 _++s_

-- Split given stack frony and rear of the handler
split : Stack (S₁ ++ HandTy Γ₁ S S' (A , E) ∷ S) → Stack S₁ × StackVal (HandTy Γ₁ S S' (A , E)) × Stack S
split {S₁ = []} (H ∷ S) = ([] , H , S)
split {S₁ = _ ∷ _} (V ∷ S) with split S
... | (S1 , H , S2) =
  (V ∷ S1 , H , S2)

{-# TERMINATING #-}
exec : Code Γ S S' → Stack S → RuntimeEnv Γ → Stack S'

exec (PUSH v c) s = exec c $ (val (pval v)) ∷ s

exec (ADD c) (val (pval (num n)) ∷ val (pval (num m)) ∷ s) =
  exec c ((val $ pval $ num (add n m)) ∷ s)

exec (AND c) (val (pval (bl a)) ∷ val (pval (bl b)) ∷ s) =
  exec c ((val $ pval $ bl (a ∧ b)) ∷ s)

exec (MARK mk c) (val (hand h env') ∷ s) env =
  exec c (hand (cont mk env) h env' ∷ s) env

exec (UNMARK) (val x ∷ (hand mk h env') ∷ s) env with h
... | (ret , ops) = exec ret (mk ∷ s) (x ∷ env')

exec (UNMARK) (val x ∷ id-hand ∷ s) env = val x ∷ s

exec (CALLOP l c) (val v ∷ s) env with split s
... | (s1 , (hand mk h env') , s2) with h
... | (_ , ops) =
  exec (lookup ops l) (mk ∷ s2)
    (resump (c , s1 , env) (hand h env') ∷ v ∷ env')

exec (LOOKUP x c) s env =
  exec c ((val $ lookup env x) ∷ s) env

exec (ABS c' c) s env =
  exec c (val (clos c' env) ∷ s) env

exec (HANDLER h c) s env =
  exec c (val (hand h env) ∷ s) env

exec (RET) (val v ∷ cont c env ∷ s) _ =
  exec c (val v ∷ s) env

exec (APP c) (val v ∷ val (clos c' env') ∷ s) env =
  exec c' (cont c env ∷ s) (v ∷ env')

exec (APP c) (v ∷ val (resump (c' , s' , env₂) (hand h envh)) ∷ s) env =
  exec c' (v ∷ (s' ++s (hand (cont c env) h envh ∷ s))) env₂

exec (BIND c k) (val v ∷ s) env =
  exec c s (v ∷ env)

exec (INITHAND c) s env =
  exec c (id-hand ∷ s) env


-- ************************
-- Type-safe Compilation
-- ************************

-- compiler for pure values
compileV : Val Γ A → Code Γ (ValTy A ∷ S) S' → Code Γ S S'

-- compiler for effectful computation
compileC :
  Cmp Γ (A , E) →
  ContCode Γ (ValTy A ∷ S₁) (A' , E) →
  ∀{Γ₁ S S'} → Code Γ (S₁ ++ HandTy Γ₁ S S' (A' , E) ∷ S) S'

{-# TERMINATING #-}
-- compile operation clauses
compileOps :
  OperationClauses Γ E₁ (B , E₂) →
  ∀{S₁ S₂ S₃ Γ₁ Γ'₁ A} →
    OperationCodes B E₁ E₂ Γ (ContTy Γ'₁ (ValTy B ∷ S₁) (A , E₂) ∷ (S₁ ++ HandTy Γ₁ S₂ S₃ (A , E₂) ∷ S₂)) S₃

compileOps {E₁ = []} [] = []
compileOps {E₁ = (op A' B') ∷ E'}{B = B}{E₂ = E₂} (e ∷ es) {S₁} {S₂} {S₃} {Γ₁} {Γ'₁} {A₁} =
  (compileC {S₁ = ContTy Γ'₁ (ValTy B ∷ S₁) (A₁ , E₂) ∷ _} e RET) ∷ (compileOps es)

compileV (num n) c = PUSH (num n) c
compileV (bl b)  c = PUSH (bl b) c
compileV unit    c = PUSH (unit) c
compileV (var x) c = LOOKUP x c
compileV {A = A ⇒ (B , E₁)} (fun e) c
  = ABS (λ {S₁ S₂ S₃ Γ₁ Γ'₁ A'} →
      compileC {S₁ = (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E₁)) ∷ _} e RET) c

compileV (handler {H = (_ , _) ⇒ (B , E₂)} (ƛx e_ret |ƛx,r e_op)) c =
  HANDLER (λ {Γ₁ Γ'₁ S₁ S₂ S₃ A'} →
    (compileC {S₁ = ContTy Γ'₁ (ValTy B ∷ S₁) (A' , E₂) ∷ _} e_ret RET , compileOps e_op)) c


compileC (v1 & v2) k = compileV v1 $ compileV v2 $ AND k

compileC (v1 + v2) k = compileV v1 $ compileV v2 $ ADD k

compileC (app v1 v2) k = compileV v1 $ compileV v2 $ APP k

compileC (Return v) c = compileV v c

compileC (Do l v) k = compileV v $ CALLOP l k

compileC (Let_In_ {A = A}{E = E₁}{B = B} e1 e2) k =
  ABS (λ {S₁ S₂ S₃ Γ₁ Γ'₁ A'} → 
    compileC {S₁ = (ContTy Γ₁ (ValTy B ∷ S₁) (A' , E₁) ∷ _)} e2 RET) (compileC {S₁ = ValTy (A ⇒ (B , E₁)) ∷ _} e1 $ APP k)

compileC (Handle e With h) k = compileV h $ MARK k (compileC {S₁ = []} e UNMARK)


-- top-level compiler
compile : Cmp Γ (A , []) → Code Γ S (ValTy A ∷ S)
compile c =
  INITHAND (compileC {S₁ = []} c UNMARK)

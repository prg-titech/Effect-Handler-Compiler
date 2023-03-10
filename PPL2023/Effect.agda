module Effect where

open import Data.Empty
open import Data.Nat  using (ā) renaming (_+_ to add)
open import Data.Bool using (true; false; if_then_else_; _āØ_; _ā§_) renaming (Bool to š¹)
open import Data.Unit using (ā¤; tt)
open import Data.List.Relation.Unary.All using (All; _ā·_; lookup; []; uncons)
open import Data.List.Membership.Propositional using (_ā_)
open import Data.List using ( List; _ā·_; []; map; _++_ )
open import Data.Product using ( _Ć_ ; _,_ )
open import Function using ( _ā_; _$_ )
open import Data.Unit using (ā¤; tt)
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
  _*_    : VTy ā VTy ā VTy  -- pair
  _ā_    : VTy ā CTy ā VTy
  Lst    : VTy ā VTy
  Hand   : HTy ā VTy

-- Type of computations
CTy = VTy Ć Eff

-- Type of handlers
data HTy where
  -- A[E]ā[E']B
  -- A : Input type , B : Output type
  -- E : Effects before handle
  -- E' : Effects after handle
  _ā_ : CTy ā CTy ā HTy

-- Effect signatures
data Sig where
  -- recieve parameter type and Return type
  op : VTy ā VTy ā Sig

-- Effect rows
Eff = List Sig



-- Type context
Ctx = List VTy


variable
  A B A' B' : VTy
  E E' Eā Eā : Eff
  C D : CTy
  H : HTy
  Ī Ī' Īā Īā : Ctx


-- ************
-- Intrinsically-typed Syntax
-- ************
data Val (Ī : Ctx) : VTy ā Set
data Cmp (Ī : Ctx) : CTy ā Set
data Handler (Ī : Ctx) : HTy ā Set
OperationClauses : Ctx ā Eff ā CTy ā Set

-- Well-typed values
data Val Ī where
  var   : A ā Ī ā Val Ī A
  unit  : Val Ī Unit
  fun   : Cmp (A ā· Ī) C ā Val Ī (A ā C)
  handler : Handler Ī H ā Val Ī (Hand H)
  bl  : š¹ ā Val Ī Bool
  num  : ā ā Val Ī Nat


-- Well-typed computations
data Cmp Ī where
  -- Application
  app : Val Ī (A ā C) ā Val Ī A ā Cmp Ī C
  -- å¤ćčæćć ćć®čØē®
  Return  : Val Ī A ā Cmp Ī (A , E)
  -- ćŖćć¬ć¼ć·ć§ć³å¼ć³åŗć
  Do : (op A B) ā E ā Val Ī A ā Cmp Ī (B , E)
  -- ćØćć§ćÆććć³ććŖć³ć°
  Handle_With_ : Cmp Ī C āćVal Ī (Hand (C ā D)) āćCmp Ī D

  Let_In_ : 
    Cmp Ī (A , E) ā
    (Cmp (A ā· Ī) (B , E)) ā
    Cmp Ī (B , E)

  _&_ : Val Ī Bool ā Val Ī Bool ā Cmp Ī (Bool , E)
  _+_ : Val Ī Nat ā Val Ī Nat ā Cmp Ī (Nat , E)

-- Well-typed Handlers
data Handler Ī where
  Ęx_|Ęx,r_ :
    -- Return clause
    Cmp (A ā· Ī) C ā
    -- Operation clauses
    OperationClauses Ī E C ā
    Handler Ī ((A , E) ā C)

-- Operation clauses
OperationClauses Ī Eā D =
  All (Ī» {(op A' B') ā
    Cmp ((B' ā D) ā· A' ā· Ī) D}
  ) Eā



-- ************************
-- Type-safe Evaluation
-- ************************

-- Values after evaluation
data Result : VTy ā Set
-- Environment
Env : Ctx ā Set

-- Patterns of hole
-- Frame A C ... A is expected type for the hole, C is the type of the whole expression
data Frame : VTy ā CTy ā Set
-- Shapes of pure continuations
data PureStackFrame : VTy ā CTy ā Set
-- Shapes of mata continuations
data MetaStackFrame : CTy ā CTy ā Set

-- Values after evaluations
data Result where
  tt   : Result Unit
  bl   : š¹ ā Result Bool
  num  : ā ā Result Nat
  clos : ā{A C Ī} ā Cmp (A ā· Ī) C ā Env Ī ā Result (A ā C)
  list : ā{A} ā List (Result A) ā Result (Lst A)
  resump : PureStackFrame A C ā Result (Hand (C ā D)) ā Result (A ā D)
  hand : Handler Ī H ā Env Ī ā Result (Hand H)

-- Environment
Env Ī = All (Ī» A ā Result A) Ī

-- Patterns of hole
-- Frame A C ... A is expected type for the hole, C is the type of the whole expression
data Frame where
  appā”_,_ : Val Ī A ā Env Ī ā Frame (A ā C) C
  app_ā” : Result (A ā C) ā Frame A C

  _&ā” : Result Bool ā Frame Bool (Bool , E)
  ā”&_,_ : Val Ī Bool ā Env Ī ā Frame Bool (Bool , E)
  _+ā” : Result Nat ā Frame Nat (Nat , E)
  ā”+_,_ : Val Ī Nat ā Env Ī ā Frame Nat (Nat , E)

  Letā”In_,_ : (Cmp (A ā· Ī) C) ā
              Env Ī ā
              Frame A C

  Do_ā” : (op A B) ā E ā Frame A (B , E)

  Handle_Withā”,_ :
    Cmp Ī (A , E) ā Env Ī ā Frame (Hand ((A , E) ā (B , E'))) (B , E')

-- Shapes of pure continuation
data PureStackFrame where
  empty : PureStackFrame A (A , E)
  extend : Frame A (A' , E) ā PureStackFrame A' (B , E) ā
            PureStackFrame A (B , E)

-- Shapes of meta continuation
data MetaStackFrame where
  -- empty continuation
  empty : MetaStackFrame (A , []) (A , [])
  -- handler and meta continuation.
  _[_[Handleā”With_]] :
    MetaStackFrame (B , E') D ā
    PureStackFrame A' (B , E') ā
    Result (Hand ((A , E) ā (A' , E'))) ā
    MetaStackFrame (A , E) D

-- type-safe, top-level evaluation
eval : Cmp [] (A , []) ā Result A

-- type-safe evaluation for pure values
evalv : Val Ī A ā Env Ī ā
        PureStackFrame A (A' , E) ā MetaStackFrame (A' , E) (B , []) ā
        Result B

-- type-safe evaluation for effectful computations
{-# TERMINATING #-}
evalc : Cmp Ī (A , E) ā Env Ī ā
        PureStackFrame A (A' , E) ā MetaStackFrame (A' , E) (B , []) ā
        Result B

-- Resume continuation by putting given value into the hole of given continuation
resumeCont :
  Result A ā
  PureStackFrame A (A' , E) ā MetaStackFrame (A' , E) (B , []) ā
  Result B


eval c = evalc c [] empty empty


resumeCont v empty (H [ K [Handleā”With h ]]) with h
... | (hand (Ęx ret |Ęx,r _) env') =
  evalc ret (v ā· env') K H

resumeCont v empty empty
  = v

resumeCont v (extend (Do l ā”) K) (H [ K' [Handleā”With h ]]) with h
... | hand (Ęx ret |Ęx,r es) env' =
  evalc (lookup es l) ((resump K (hand (Ęx ret |Ęx,r es) env')) ā· v ā· env') K' H

resumeCont v (extend (app (resump K' h') ā”) K) H =
  resumeCont v K' (H [ K [Handleā”With h' ]])

resumeCont h (extend (Handle e Withā”, env') K) H =
  evalc e env' empty $ (H [ K [Handleā”With h ]])

resumeCont v (extend (appā” v2 , env) K) =
  evalv v2 env (extend (app v ā”) K)

resumeCont v (extend (app (clos e' env') ā”) K) =
  evalc e' (v ā· env') K

resumeCont v (extend (Letā”In e2 , env) K) =
  evalc e2 (v ā· env) K 

resumeCont (bl a) (extend ((bl b) &ā”) K) H =
  resumeCont (bl $ b ā§ a) K H

resumeCont v (extend (ā”& v2 , env) K) H =
  evalv v2 env (extend (v &ā”) K) H

resumeCont (num n) (extend ((num m) +ā”) K) H =
  resumeCont (num (add n m)) K H

resumeCont v (extend (ā”+ v2 , env) K) H =
  evalv v2 env (extend (v +ā”) K) H


evalv unit _          = resumeCont tt
evalv (var x) env       = resumeCont $ lookup env x
evalv (fun f) env       = resumeCont $ clos f env
evalv (handler h) env   = resumeCont $ hand h env
evalv (bl b) _        = resumeCont $ bl b
evalv (num n) _       = resumeCont $ num n


evalc (app v1 v2) env K =
  evalv v1 env $ extend (appā” v2 , env) K

evalc (Return v) env K =
  evalv v env K

evalc (Do l v) env K =
  evalv v env $ (extend (Do l ā”) K)

evalc (Handle e With h) env K =
  evalv h env $ extend (Handle e Withā”, env) K

evalc (Let e1 In e2) env K =
  evalc e1 env $ extend (Letā”In e2 , env) K

evalc (v1 & v2) env K = evalv v1 env $ extend (ā”& v2 , env) K

evalc (v1 + v2) env K = evalv v1 env $ extend (ā”+ v2 , env) K


-- ************************
-- Target language
-- ************************

-- Target : stack-base abstract machine


data SValTy : Set
StackTy : Set

-- Types of Stack Values
data SValTy where
  ValTy  : VTy ā SValTy
  HandTy : Ctx ā StackTy ā StackTy ā CTy ā SValTy
  ContTy : Ctx ā StackTy ā CTy ā SValTy

-- Shape of Stack
StackTy = List SValTy

variable
  T : SValTy
  S S' Sā Sā Sā : StackTy

-- immediate values
data PVal : VTy ā Set where
  unit : PVal (Unit)
  num : ā ā PVal (Nat)
  bl : š¹ ā PVal (Bool)


-- target abstract machine code
data Code (Ī : Ctx) : StackTy ā StackTy ā Set
-- Codes of operation clauses
OperationCodes : VTy ā Eff ā Eff ā Ctx ā StackTy ā StackTy ā Set
HandlerCode : Ctx ā CTy ā CTy ā Set
ContCode : Ctx ā StackTy ā CTy ā Set

-- target abstract machine code
data Code Ī where
  -- PUSH immediate value into the stack
  PUSH : PVal A ā Code Ī (ValTy A ā· S) S' ā Code Ī S S'

  -- Binary operations
  ADD : Code Ī (ValTy Nat ā· S) S' ā Code Ī (ValTy Nat ā· ValTy Nat ā· S) S'
  AND : Code Ī (ValTy Bool ā· S) S' ā Code Ī (ValTy Bool ā· ValTy Bool ā· S) S'

  -- čØē®ććć³ćć«ććć
  MARK :
    ContCode Ī (ValTy B ā· Sā) (B' , Eā) ā -- ć”ćæē¶ē¶
    (ā{Ī'ā} ā -- å¦ēåÆ¾č±”ć®čØē®
      Code Ī (HandTy Ī'ā (Sā ++ HandTy Īā Sā Sā (B' , Eā) ā· Sā) Sā (A , Eā) ā· (Sā ++ HandTy Īā Sā Sā (B' , Eā) ā· Sā)) Sā ) ā
    Code Ī (ValTy (Hand ((A , Eā) ā (B , Eā))) ā· (Sā ++ HandTy Īā Sā Sā (B' , Eā) ā· Sā)) Sā

  -- ćć³ćć©ć®returnēÆćå¼ć³åŗć
  UNMARK : Code Ī (ValTy A ā· HandTy Īā S S' (A , Eā) ā· S) S'
  -- UNMARK :
  --   Code Ī (ValTy B ā· S) S'-- ć”ćæē¶ē¶
  --   Code Ī (ValTy A ā· HandTy Īā S S' ((A , Eā) ā (B , Eā)) ā· S) S'

  -- ćŖćć¬ć¼ć·ć§ć³å¼ć³åŗć
  CALLOP :
    (op A B) ā E
    ā ContCode Ī (ValTy B ā· Sā) (A' , E) -- ęęćććć³ć¼ćē¶ē¶
    ā Code Ī (ValTy A ā· Sā ++ HandTy Īā S S' (A' , E) ā· S) S'

  -- åęē¶ē¶ćććć·ć„
  INITHAND :
    Code Ī (HandTy Ī S (ValTy A ā· S) (A , []) ā· S) (ValTy A ā· S) ā
    Code Ī S (ValTy A ā· S)

  -- Read a value from environment and push into the stack
  LOOKUP : A ā Ī ā Code Ī (ValTy A ā· S) S' ā Code Ī S S'

  -- Generate function closure and push into the stack
  ABS :
    (ā{Sā Sā Sā Īā Ī'ā A'} ā
      -- Function body
      Code (A ā· Ī) (ContTy Īā (ValTy B ā· Sā) (A' , Eā) ā· (Sā ++ HandTy Ī'ā Sā Sā (A' , Eā) ā· Sā)) Sā)  ā
    Code Ī (ValTy (A ā (B , Eā)) ā· S) S' ā
    Code Ī S S'

  -- ćć³ćć©å¤ćććć·ć„
  HANDLER : 
    HandlerCode Ī (A , Eā) (B , Eā) ā 
    Code Ī (ValTy (Hand ((A , Eā) ā (B , Eā))) ā· S) S' ā
    Code Ī S S'

  -- Return from function execution
  RET : Code Ī (ValTy A ā· ContTy Īā (ValTy A ā· S) C ā· (S ++ HandTy Īā Sā Sā C ā· Sā)) Sā

  -- Application
  APP :
    ContCode Ī (ValTy B ā· Sā) (A' , E) ā
    Code Ī (ValTy A ā· ValTy (A ā (B , E)) ā· Sā ++ HandTy Īā Sā Sā (A' , E) ā· Sā) Sā
  
  -- Let Binding let x = e1 in e2
  -- Pop stack, and execute the body adding the value into environment
  BIND :
    -- let-body
    Code (A ā· Ī) S S' ā
    -- code continuation
    Code Ī (ValTy B ā· S) S' ā
    Code Ī (ValTy A ā· S) S'

-- operationēÆć®ć³ć¼ć
OperationCodes B Eā Eā Ī SS Sā = 
  All (Ī» {(op A' B') ā Code ((B' ā (B , Eā)) ā· A' ā· Ī) SS Sā }) Eā

-- ćć³ćć©ć³ć¼ćć®å
HandlerCode Ī (A , Eā) (B , Eā) =
  (ā{Īā Ī'ā Sā Sā Sā A'} ā
    Code (A ā· Ī) (ContTy Ī'ā (ValTy B ā· Sā) (A' , Eā) ā· (Sā ++ HandTy Īā Sā Sā (A' , Eā) ā· Sā)) Sā Ć
    OperationCodes B Eā Eā Ī (ContTy Ī'ā (ValTy B ā· Sā) (A' , Eā) ā· (Sā ++ HandTy Īā Sā Sā (A' , Eā) ā· Sā)) Sā)

-- ē“ē²ćŖē¶ē¶ć®ć³ć¼ćć®å
ContCode Ī Sā (B , E) =
  ā{Īā Sā Sā} ā
    Code Ī (Sā ++ HandTy Īā Sā Sā (B , E) ā· Sā) Sā

-- compiled value from source language
data EnvVal : VTy ā Set
-- Bounded Values
RuntimeEnv : List VTy ā Set
-- Type of stack
Stack : StackTy ā Set

-- Values can be included in environment
data EnvVal where
  pval : PVal A ā EnvVal A

  -- Function closure
  clos :
    (ā{Īā Ī'ā Sā Sā Sā A'} ā
      Code (A ā· Ī)
        (ContTy Īā (ValTy B ā· Sā) (A' , E) ā· (Sā ++ HandTy Ī'ā Sā Sā (A' , E) ā· Sā))
        Sā)
    ā RuntimeEnv Ī
    ā EnvVal (A ā (B , E))

  -- ęęćććē¶ē¶
  resump :
    -- ē¶ē¶ę¬ä½ćØćććä½æēØććć¹ćæććÆćØē°å¢
    ContCode Ī (ValTy A ā· S) (A' , E) Ć Stack S Ć RuntimeEnv Ī ā
    -- ē¶ē¶ć«åÆ¾ćććć³ćć©
    EnvVal (Hand ((A' , E) ā (B , E'))) ā
    EnvVal (A ā (B , E'))

  -- ē¬¬äøē“ć®ćć³ćć©å¤
  fc-hand :
    HandlerCode Ī (A , Eā) (B , Eā) ā
    RuntimeEnv Ī ā
    EnvVal (Hand ((A , Eā) ā (B , Eā)))


-- Stack Values
data StackVal : SValTy ā Set where
  val  : EnvVal A ā StackVal (ValTy A)
  -- ē¶ē¶
  cont :
    ContCode Ī Sā (A , E) ā RuntimeEnv Ī
    ā StackVal (ContTy Ī Sā (A , E))
  -- ćć³ćć©ę¬ä½ćØć”ćæē¶ē¶
  hand : 
    StackVal (ContTy Īā (ValTy B ā· Sā) (A' , Eā)) -- ć”ćæē¶ē¶
    ā HandlerCode Ī (A , Eā) (B , Eā)
    ā RuntimeEnv Ī -- ćć³ćć©ć³ć¼ćć®å®č”ęē°å¢
    ā StackVal (HandTy Ī (Sā ++ HandTy Īā Sā Sā (A' , Eā) ā· Sā) Sā (A , Eā))
  -- ćććć¬ćć«čØē®ć®ććć®ē©ŗć®ćć³ćć©
  id-hand : StackVal (HandTy Ī S (ValTy A ā· S) (A , []))

RuntimeEnv Ī = All (Ī» A ā EnvVal A) Ī

Stack S = All (Ī» T ā StackVal T) S

-- concatenate two stack
_++s_ : Stack S ā Stack S' ā Stack (S ++ S')
[] ++s s = s
(x ā· xs) ++s s = x ā· (xs ++s s)

infixr 20 _++s_

-- Split given stack frony and rear of the handler
split : Stack (Sā ++ HandTy Īā S S' (A , E) ā· S) ā Stack Sā Ć StackVal (HandTy Īā S S' (A , E)) Ć Stack S
split {Sā = []} (H ā· S) = ([] , H , S)
split {Sā = _ ā· _} (V ā· S) with split S
... | (S1 , H , S2) =
  (V ā· S1 , H , S2)

{-# TERMINATING #-}
exec : Code Ī S S' ā Stack S ā RuntimeEnv Ī ā Stack S'

exec (PUSH v c) s = exec c $ (val (pval v)) ā· s

exec (ADD c) (val (pval (num n)) ā· val (pval (num m)) ā· s) =
  exec c ((val $ pval $ num (add n m)) ā· s)

exec (AND c) (val (pval (bl a)) ā· val (pval (bl b)) ā· s) =
  exec c ((val $ pval $ bl (a ā§ b)) ā· s)

exec (MARK mk c) (val (fc-hand h env') ā· s) env =
  exec c (hand (cont mk env) h env' ā· s) env

exec (UNMARK) (val x ā· (hand mk h env') ā· s) env with h
... | (ret , ops) = exec ret (mk ā· s) (x ā· env')

exec (UNMARK) (val x ā· id-hand ā· s) env = val x ā· s

exec (CALLOP l c) (val v ā· s) env with split s
... | (s1 , (hand mk h env') , s2) with h
... | (_ , ops) =
  exec (lookup ops l) (mk ā· s2)
    (resump (c , s1 , env) (fc-hand h env') ā· v ā· env')

exec (LOOKUP x c) s env =
  exec c ((val $ lookup env x) ā· s) env

exec (ABS c' c) s env =
  exec c (val (clos c' env) ā· s) env

exec (HANDLER h c) s env =
  exec c (val (fc-hand h env) ā· s) env

exec (RET) (val v ā· cont c env ā· s) _ =
  exec c (val v ā· s) env

exec (APP c) (val v ā· val (clos c' env') ā· s) env =
  exec c' (cont c env ā· s) (v ā· env')

exec (APP c) (v ā· val (resump (c' , s' , envā) (fc-hand h envh)) ā· s) env =
  exec c' (v ā· (s' ++s (hand (cont c env) h envh ā· s))) envā

exec (BIND c k) (val v ā· s) env =
  exec c s (v ā· env)

exec (INITHAND c) s env =
  exec c (id-hand ā· s) env


-- ************************
-- Type-safe Compilation
-- ************************

-- compiler for pure values
compileV : Val Ī A ā Code Ī (ValTy A ā· S) S' ā Code Ī S S'

-- compiler for effectful computation
compileC :
  Cmp Ī (A , E) ā
  ContCode Ī (ValTy A ā· Sā) (A' , E) ā
  ā{Īā S S'} ā Code Ī (Sā ++ HandTy Īā S S' (A' , E) ā· S) S'

-- compile operation clauses
compileOps :
  OperationClauses Ī Eā (B , Eā) ā
  ā{Sā Sā Sā Īā Ī'ā A} ā
    OperationCodes B Eā Eā Ī (ContTy Ī'ā (ValTy B ā· Sā) (A , Eā) ā· (Sā ++ HandTy Īā Sā Sā (A , Eā) ā· Sā)) Sā

compileOps {Eā = []} [] = []
compileOps {Eā = (op A' B') ā· E'}{B = B}{Eā = Eā} (e ā· es) {Sā} {Sā} {Sā} {Īā} {Ī'ā} {Aā} =
  (compileC {Sā = ContTy Ī'ā (ValTy B ā· Sā) (Aā , Eā) ā· _} e RET) ā· (compileOps es)

compileV (num n) c = PUSH (num n) c
compileV (bl b)  c = PUSH (bl b) c
compileV unit    c = PUSH (unit) c
compileV (var x) c = LOOKUP x c
compileV {A = A ā (B , Eā)} (fun e) c
  = ABS (Ī» {Sā Sā Sā Īā Ī'ā A'} ā
      compileC {Sā = (ContTy Īā (ValTy B ā· Sā) (A' , Eā)) ā· _} e RET) c

compileV (handler {H = (_ , _) ā (B , Eā)} (Ęx e_ret |Ęx,r e_op)) c =
  HANDLER (Ī» {Īā Ī'ā Sā Sā Sā A'} ā
    (compileC {Sā = ContTy Ī'ā (ValTy B ā· Sā) (A' , Eā) ā· _} e_ret RET , compileOps e_op)) c


compileC (v1 & v2) k = compileV v1 $ compileV v2 $ AND k

compileC (v1 + v2) k = compileV v1 $ compileV v2 $ ADD k

compileC (app v1 v2) k = compileV v1 $ compileV v2 $ APP k

compileC (Return v) c = compileV v c

compileC (Do l v) k = compileV v $ CALLOP l k

compileC (Let_In_ {A = A}{E = Eā}{B = B} e1 e2) k =
  ABS (Ī» {Sā Sā Sā Īā Ī'ā A'} ā 
    compileC {Sā = (ContTy Īā (ValTy B ā· Sā) (A' , Eā) ā· _)} e2 RET) (compileC {Sā = ValTy (A ā (B , Eā)) ā· _} e1 $ APP k)

compileC (Handle e With h) k = compileV h $ MARK k (compileC {Sā = []} e UNMARK)


-- top-level compiler
compile : Cmp Ī (A , []) ā Code Ī S (ValTy A ā· S)
compile c =
  INITHAND (compileC {Sā = []} c UNMARK)

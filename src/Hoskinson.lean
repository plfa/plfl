import Lean
namespace Hoskinson

#eval Lean.versionString

set_option pp.notation true
set_option pp.rawOnError true
set_option hygiene false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

inductive Tp : Type where
  | natural : Tp
  | function : Tp → Tp → Tp
  deriving Repr, Inhabited, DecidableEq

notation:max "ℕ" => Tp.natural
infixr:70 " ⇒ " => Tp.function

example : Tp := ℕ ⇒ ℕ

inductive TpEnv : Type where
  | empty : TpEnv
  | extend : TpEnv → Tp → TpEnv
  deriving Repr, Inhabited, DecidableEq

notation:max "∅" => TpEnv.empty
infixl:50 " ▷ " => TpEnv.extend

example : TpEnv := ∅ ▷ ℕ ⇒ ℕ ▷ ℕ

infix:40  " ∋ " => lookup

inductive lookup : TpEnv → Tp → Type where
  | stop :
       ----------------
       Γ ▷ A ∋ A
  | pop :
       Γ ∋ B
       ----------------
     → Γ ▷ A ∋ B
  deriving Repr, DecidableEq

prefix:90 "S" => lookup.pop
notation:max "Z" => lookup.stop

infix:40  " ⊢ " => term

inductive term : TpEnv → Tp → Type where
  | var :
        Γ ∋ A
        ----------
      → Γ ⊢ A
  | lambda :
        Γ ▷ A ⊢ B
        -----------
      → Γ ⊢ A ⇒ B
  | application :
        Γ ⊢ A ⇒ B
      → Γ ⊢ A
        --------
      → Γ ⊢ B
  | zero :
        --------
        Γ ⊢ ℕ
  | succ :
        Γ ⊢ ℕ
        --------
      → Γ ⊢ ℕ
  | case :
        Γ ⊢ ℕ
      → Γ ⊢ A
      → Γ ▷ ℕ ⊢ A
        ---------------
      → Γ ⊢ A
  | mu :
        Γ ▷ A ⊢ A
        --------------
      → Γ ⊢ A
  deriving Repr

prefix:90 "# " => term.var
prefix:50 "ƛ " => term.lambda
infixl:70 " ⬝ " => term.application
notation:max "o" => term.zero
postfix:80 " +1" => term.succ
notation:max "casesOn" => term.case
prefix:50 "μ " => term.mu

instance : OfNat (Γ ⊢ ℕ) Nat.zero where
  ofNat := o

instance [OfNat (Γ ⊢ ℕ) n] : OfNat (Γ ⊢ ℕ) (Nat.succ n) where
  ofNat := (OfNat.ofNat n) +1

example : 2 = (o +1 +1 : ∅ ⊢ ℕ) := rfl

instance : OfNat (Γ ▷ A ∋ A) Nat.zero where
  ofNat := Z

instance [OfNat (Γ ∋ B) n] : OfNat (Γ ▷ A ∋ B) (Nat.succ n) where
  ofNat := S (OfNat.ofNat n)

example : 2 = (S S Z : ∅ ▷ ℕ ⇒ ℕ ▷ ℕ ▷ ℕ ∋ ℕ ⇒ ℕ) := rfl

def plus : Γ ⊢ ℕ ⇒ ℕ ⇒ ℕ :=
  -- μ ƛ ƛ (casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1))
  μ ƛ ƛ (casesOn (# 0) (# 1) ((# 3 ⬝ # S S Z ⬝ # Z) +1))
def two_plus_two : ∅ ⊢ ℕ :=
  plus ⬝ 2 ⬝ 2

def Ch (A : Tp) : Tp := (A ⇒ A) ⇒ A ⇒ A
def suc_c : Γ ⊢ ℕ ⇒ ℕ :=
  ƛ (# Z +1)
-- twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z")
def two_c : Γ ⊢ Ch A :=
  ƛ ƛ (# S Z ⬝ (# S Z ⬝ # Z))
-- plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ # "m" · # "s" · (# "n" · # "s" · # "z")
def plus_c : Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A :=
  ƛ ƛ ƛ ƛ (# S S S Z ⬝ # S Z ⬝ (# S S Z ⬝ # S Z ⬝ # Z))
def plus_c' : Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A :=
  ƛ ƛ ƛ ƛ ((# 3 : _ ⊢ Ch A) ⬝ # 1 ⬝ ((# 2 : _ ⊢ Ch A) ⬝ # 1 ⬝ # 0))
def two : ∅ ⊢ ℕ := two_c ⬝ suc_c ⬝ 0

def rmap (Γ Δ : TpEnv) : Type :=
  ∀ {A : Tp}, (Γ ∋ A) → (Δ ∋ A)
def smap (Γ Δ : TpEnv) : Type :=
  ∀ {A : Tp}, (Γ ∋ A) → (Δ ⊢ A)
def tmap (Γ Δ : TpEnv) : Type :=
  ∀ {A : Tp}, (Γ ⊢ A) → (Δ ⊢ A)

infix:30 " →ʳ " => rmap
infix:30 " →ˢ " => smap
infix:30 " →ᵗ " => tmap

def ren_ext {Γ Δ : TpEnv} {A :Tp} (ρ : Γ →ʳ Δ) : (Γ ▷ A →ʳ Δ ▷ A)
  | _ , Z  =>  Z
  | _ , S x  =>  S (ρ x)

def ren {Γ Δ : TpEnv} (ρ : Γ →ʳ Δ) : Γ →ᵗ Δ
  | _ , (# x) => # (ρ x)
  | _ , (ƛ N) => ƛ (ren (ren_ext ρ) N)
  | _ , (L ⬝ M) => ren ρ L ⬝ ren ρ M
  | _ , o => o
  | _ , M +1 => ren ρ M +1
  | _ , casesOn L M N => casesOn (ren ρ L) (ren ρ M) (ren (ren_ext ρ) N)
  | _ , μ N => μ (ren (ren_ext ρ) N)

def lift {Γ : TpEnv} {A : Tp} : Γ →ᵗ Γ ▷ A := ren (fun x => S x)

def sub_ext {Γ Δ : TpEnv} {A : Tp} (σ : Γ →ˢ Δ) : (Γ ▷ A →ˢ Δ ▷ A)
  | _ , Z  =>  # Z
  | _ , S x  =>  lift (σ x)

def sub {Γ Δ : TpEnv} (σ : Γ →ˢ Δ) : Γ →ᵗ Δ
  | _ , (# x) => σ x
  | _ , (ƛ N) => ƛ (sub (sub_ext σ) N)
  | _ , (L ⬝ M) => sub σ L ⬝ sub σ M
  | _ , o => o
  | _ , M +1 => sub σ M +1
  | _ , casesOn L M N => casesOn (sub σ L) (sub σ M) (sub (sub_ext σ) N)
  | _ , μ N => μ (sub (sub_ext σ) N)

def sigma_0 (M : Γ ⊢ A) : Γ ▷ A →ˢ Γ
  | _ , Z    =>  M
  | _ , S x  =>  # x

def subst {Γ : TpEnv} {A B : Tp} (N : Γ ▷ A ⊢ B) (M : Γ ⊢ A) : Γ ⊢ B
  := sub (sigma_0 M) N

example : subst (ƛ (# S Z ⬝ (# S Z ⬝ # Z))) suc_c = (ƛ (suc_c ⬝ (suc_c ⬝ # Z)) : ∅ ⊢ ℕ ⇒ ℕ) := rfl

inductive Value : Γ ⊢ A → Type where
  | lambda :
      Value (ƛ N)
  | zero :
      Value o
  | succ :
      Value V → Value (V +1)
  deriving Repr

open Value

infix:30 "~>" => reduce

inductive reduce : Γ ⊢ A → Γ ⊢ A → Type where
  | xi_app_1 :
      L ~> L' → L ⬝ M ~> L' ⬝ M
  | xi_app_2 :
      Value V → reduce M M' → reduce (V ⬝ M) (V ⬝ M')
  | beta :
      Value W → reduce ((ƛ N) ⬝ W) (subst N W)
  | xi_succ :
      reduce M M' → reduce (M +1) (M' +1)
  | xi_case :
      reduce L L' → reduce (casesOn L M N) (casesOn L' M N)
  | beta_zero :
      reduce (casesOn o M N) M
  | beta_succ :
      Value V → reduce (casesOn (V +1) M N) (subst N V)
  | beta_mu :
      reduce (μ N) (subst N (μ N))
  deriving Repr

open reduce


-- inductive star : (Γ ⊢ A) → (Γ ⊢ A) → Type where
--   | none :
--       star M M
--   | one :
--          (M ~> N)
--          ----------
--        → star M N
--    | two :
--          star L M
--        → star M N
--          ----------
--        → star L N
-- infix:20 "~>*" => star
-- instance : Trans (star : (Γ ⊢ A) → (Γ ⊢ A) → Type)
--                  (star : (Γ ⊢ A) → (Γ ⊢ A) → Type)
--                  (star : (Γ ⊢ A) → (Γ ⊢ A) → Type) where
--   trans := star.two

infix:30 "~>>"  => reduce_many

inductive reduce_many : Γ ⊢ A → Γ ⊢ A → Type where
  | nil :
      M ~>> M
  | cons :
      ∀ L, L ~> M
         → M ~>> N
           -------
         → L ~>> N
  deriving Repr

open reduce_many

def one_one : (L ~> M) → (M ~> N) → (L ~>> N)
  | L_to_M, M_to_N => cons _ L_to_M (cons _ M_to_N nil)

def one_many : (L ~> M) → (M ~>> N) → (L ~>> N)
  | L_to_M, M_to_N => cons _ L_to_M M_to_N

def many_one : (L ~>> M) → (M ~> N) → (L ~>> N)
  | nil, M_to_N  => cons _ M_to_N nil
  | cons _ L_to_P P_to_M , M_to_N => cons _ L_to_P (many_one P_to_M M_to_N)

def many_many : (L ~>> M) → (M ~>> N) → (L ~>> N)
  | nil, M_to_N  => M_to_N
  | cons _ L_to_P P_to_M , M_to_N => cons _ L_to_P (many_many P_to_M M_to_N)

instance : Trans (.~>.  : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>.  : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type) where
  trans := one_one

instance : Trans (.~>.  : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type) where
  trans := one_many

instance : Trans (.~>>. : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>.  : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type) where
  trans := many_one

instance : Trans (.~>>. : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type) where
  trans := many_many

example : two ~> (ƛ (suc_c ⬝ (suc_c ⬝ # Z))) ⬝ 0
    := xi_app_1 (beta lambda)

example : (ƛ (suc_c ⬝ (suc_c ⬝ # Z))) ⬝ (0 : ∅ ⊢ ℕ) ~> suc_c ⬝ (suc_c ⬝ 0)
    := beta zero

example : (suc_c ⬝ (suc_c ⬝ 0) : ∅ ⊢ ℕ) ~> suc_c ⬝ 1
    := xi_app_2 lambda (beta zero)

example : (suc_c ⬝ 1 : ∅ ⊢ ℕ) ~> 2
    := beta (succ zero)

def two_to_2 :=
  calc
    (two_c ⬝ suc_c ⬝ 0 : ∅ ⊢ ℕ)
      ~> (ƛ (suc_c ⬝ (suc_c ⬝ # Z))) ⬝ 0  := xi_app_1 (beta lambda)
    _ ~> (suc_c ⬝ (suc_c ⬝ 0))            := beta zero
    _ ~> suc_c ⬝ 1                        := xi_app_2 lambda (beta zero)
    _ ~> 2                                := beta (succ zero)

example : two ~>> 2 := two_to_2

inductive Progress : Γ ⊢ A → Type where
  | step :
      M ~> N → Progress M
  | done :
      Value V → Progress V
  deriving Repr

open Progress

def progress : ∀ (M : ∅ ⊢ A), Progress M
  | (# x) => by contradiction
  | (ƛ N) => done lambda
  | (L ⬝ M) =>
      match progress L with
        | step L_to_L' => step (xi_app_1 L_to_L')
        | done v =>
            match progress M with
              | step M_to_M' => step (xi_app_2 v M_to_M')
              | done w =>
                  match v with
                    | Value.lambda => step (beta w)
  | o => done zero
  | (M +1) =>
      match progress M with
        | step M_to_M' => step (xi_succ M_to_M')
        | done v => done (succ v)
  | (casesOn L M N) =>
      match progress L with
        | step L_to_L' => step (xi_case L_to_L')
        | done v =>
            match v with
              | Value.zero => step beta_zero
              | Value.succ v => step (beta_succ v)
  | (μ N) => step beta_mu

inductive Finished (N : ∅ ⊢ A) : Type where
  | done : Value N → Finished N
  | out_of_gas : Finished N
  deriving Repr

open Finished

inductive Steps (L : ∅ ⊢ A) : Type where
  | steps : (L ~>> N) → Finished N → Steps L
  deriving Repr

open Steps

def evaluate (n : Nat) (L : ∅ ⊢ A) : Steps L :=
  match n with
    | Nat.zero => steps nil out_of_gas
    | Nat.succ n =>
        match progress L with
          | Progress.done v => steps nil (done v)
          | @Progress.step _ _ _ M L_to_M =>
              match evaluate n M with
                | steps M_to_N f => steps (cons L L_to_M M_to_N) f

-- code below by Wojciech Nawrocki

open Lean Elab Meta Command in
elab tk:"#reduce_full" t:term : command => do
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      let e ← withTransparency (mode := TransparencyMode.all) <| Meta.reduce e (explicitOnly := false) (skipProofs := false) (skipTypes := false)
      logInfoAt tk e

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Hoskinson.reduce_many.cons]
partial def reduce_many.delabCons : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``reduce_many.cons 7
  let L ← withNaryArg 4 delab
  let M ← withNaryArg 2 delab
  let r ← withNaryArg 5 delab
  let steps ← withNaryArg 6 go
  `(calc
    $L ~> $M := $r
    $steps*
  )
where go : DelabM (TSyntaxArray ``calcStep) := do
  let e ← getExpr
  if e.isAppOfArity' ``reduce_many.nil 3 then
    return #[]
  guard $ e.isAppOfArity' ``reduce_many.cons 7
  let M ← withNaryArg 2 delab
  let r ← withNaryArg 5 delab
  let s ← `(calcStep|_ ~> $M := $r)
  let rest ← withNaryArg 6 go
  return #[s] ++ rest


-- #eval two_plus_two
-- #eval (evaluate 100 two_plus_two)

#reduce_full two_to_2

#reduce_full two
#reduce_full (evaluate 10 two)

/-
example :
  (evaluate 10 two)
      =
      steps
        (reduce_many.cons
          ((ƛƛ#S Z⬝(#S Z⬝#Z))⬝(ƛ#Z+1)⬝o~>(ƛ(ƛ#Z+1)⬝((ƛ#Z+1)⬝#Z))⬝o)
          ((beta Value.lambda).xi_app_1)
          (reduce_many.cons
            ((ƛ#Z+1)⬝((ƛ#Z+1)⬝o))
            (beta Value.zero)
            (reduce_many.cons
              ((ƛ#Z+1)⬝o+1)
              (xi_app_2 Value.lambda (beta Value.zero))
              (reduce_many.cons
                (o+1+1)
                (beta Value.zero.succ)
                reduce_many.nil))))
        (Finished.done Value.zero.succ.succ)
      :=
        by rfl

set_option pp.notation false

example :
  (evaluate 10 two)
    =
    steps
      (calc
        (ƛƛ#S Z⬝(#S Z⬝#Z))⬝(ƛ#Z+1)⬝o~>(ƛ(ƛ#Z+1)⬝((ƛ#Z+1)⬝#Z))⬝o := (beta Value.lambda).xi_app_1
        _~>(ƛ#Z+1)⬝((ƛ#Z+1)⬝o) := (beta Value.zero)
        _~>(ƛ#Z+1)⬝o+1 := (xi_app_2 Value.lambda (beta Value.zero))
        _~>o+1+1 := beta Value.zero.succ)
      (Finished.done Value.zero.succ.succ)
    :=
      by rfl

-/

#reduce_full two_plus_two
#reduce_full (evaluate 100 two_plus_two)

#check ((μƛƛcasesOn (#Z) (#S Z)
                    ((#S
                              S
                                S
                                  Z⬝#S
                              S
                                Z⬝#Z)+1))⬝o+1+1⬝o+1+1)

-- Exercise. Add products, as detailed in
--  https://plfa.inf.ed.ac.uk/More/#products
-- Pick suitable notations for introduction and elimination
-- of products that won't conflict.

namespace Typesig

set_option pp.notation true
set_option maxRecDepth 1000000

inductive Tp : Type where
| natural : Tp
| function : Tp → Tp → Tp

notation:max "ℕ" => Tp.natural
infixr:70 "⇒" => Tp.function

example : Tp := ℕ ⇒ ℕ

inductive TpEnv : Type where
| empty : TpEnv
| extend : TpEnv → Tp → TpEnv

notation:max "∅" => TpEnv.empty
infixl:50 "▷" => TpEnv.extend

example : TpEnv := ∅ ▷ ℕ ⇒ ℕ ▷ ℕ

inductive lookup : TpEnv → Tp → Type where
  | stop :
       ----------------
       lookup (Γ ▷ A) A
  | pop :
       lookup Γ B
       ----------------
     → lookup (Γ ▷ A) B
  deriving Repr

inductive term : TpEnv → Tp → Type where
  | var :
        lookup Γ A
        ----------
      → term Γ A
  | lambda :
        term (Γ ▷ A) B
        --------------
      → term Γ (A ⇒ B)
  | application :
        term Γ (A ⇒ B)
      → term Γ A
        --------
      → term Γ B
  | zero :
        --------
        term Γ ℕ
  | succ :
        term Γ ℕ
        --------
      → term Γ ℕ
  | case :
        term Γ ℕ
      → term Γ A
      → term (Γ ▷ ℕ) A
        ---------------
      → term Γ A
  | mu :
        term (Γ ▷ A) A
        --------------
      → term Γ A
  deriving Repr

infix:40  "∋" => lookup
infix:40  "⊢" => term

prefix:90 "S" => lookup.pop
notation:max "Z" => lookup.stop

prefix:90 "#" => term.var
prefix:50 "ƛ" => term.lambda
infixl:70 "⬝" => term.application
notation:max "o" => term.zero
postfix:80 "+1" => term.succ
notation:max "switch" => term.case
prefix:50 "μ" => term.mu

instance : OfNat (Γ ⊢ ℕ) Nat.zero where
  ofNat := term.zero

instance [OfNat (Γ ⊢ ℕ) n] : OfNat (Γ ⊢ ℕ) (Nat.succ n) where
  ofNat := term.succ (OfNat.ofNat n)

example : 2 = @term.zero ∅ +1 +1 := rfl

instance : OfNat (Γ ▷ A ∋ A) Nat.zero where
  ofNat := lookup.stop

instance [OfNat (Γ ∋ B) n] : OfNat (Γ ▷ A ∋ B) (Nat.succ n) where
  ofNat := lookup.pop (OfNat.ofNat n)

example : 2 = (S S Z : ∅ ▷ ℕ ⇒ ℕ ▷ ℕ ▷ ℕ ∋ ℕ ⇒ ℕ) := rfl

def plus : Γ ⊢ ℕ ⇒ ℕ ⇒ ℕ :=
  μ ƛ ƛ (switch (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1))
def two_plus_two : ∅ ⊢ ℕ :=
  plus ⬝ 2 ⬝ 2

def one_c : ∅ ⊢ (A ⇒ A) ⇒ A ⇒ A := ƛ ƛ # S Z ⬝ # Z
def one_c' : ∅ ⊢ (A ⇒ A) ⇒ A ⇒ A := ƛ ƛ # 1 ⬝ (# 0 : _ ⊢ A)

def suc_c : Γ ⊢ ℕ ⇒ ℕ :=
  ƛ (# Z +1)
def Ch (A : Tp) : Tp := (A ⇒ A) ⇒ A ⇒ A
def two_c : Γ ⊢ Ch A :=
  ƛ ƛ (# S Z ⬝ (# S Z ⬝ # Z))
-- twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z")
def plus_c : Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A :=
  ƛ ƛ ƛ ƛ (# S S S Z ⬝ # S Z ⬝ (# S S Z ⬝ # S Z ⬝ # Z))
def plus_c' : Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A :=
  ƛ ƛ ƛ ƛ ((# 3 : _ ⊢ Ch A) ⬝ # 1 ⬝ ((# 2 : _ ⊢ Ch A) ⬝ # 1 ⬝ # 0))
-- plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ # "m" · # "s" · (# "n" · # "s" · # "z")
def two : ∅ ⊢ ℕ := two_c ⬝ suc_c ⬝ 0


def rmap (Γ Δ : TpEnv) : Type :=
  ∀ {A : Tp}, (Γ ∋ A) → (Δ ∋ A)

def smap (Γ Δ : TpEnv) : Type :=
  ∀ {A : Tp}, (Γ ∋ A) → (Δ ⊢ A)

def tmap (Γ Δ : TpEnv) : Type :=
  ∀ {A : Tp}, (Γ ⊢ A) → (Δ ⊢ A)

infix:30 "→ʳ" => rmap
infix:30 "→ˢ" => smap
infix:30 "→ᵗ" => tmap

def ren_ext {Γ Δ : TpEnv} {A :Tp} (ρ : Γ →ʳ Δ) : (Γ ▷ A →ʳ Δ ▷ A)
  | _ , Z  =>  Z
  | _ , S x  =>  S (ρ x)

def ren {Γ Δ : TpEnv} (ρ : Γ →ʳ Δ) : Γ →ᵗ Δ
  | _ , (# x) => # (ρ x)
  | _ , (ƛ N) => ƛ (ren (ren_ext ρ) N)
  | _ , (L ⬝ M) => ren ρ L ⬝ ren ρ M
  | _ , o => o
  | _ , M +1 => ren ρ M +1
  | _ , switch L M N =>
        switch (ren ρ L) (ren ρ M) (ren (ren_ext ρ) N)
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
  | _ , switch L M N =>
        switch (sub σ L) (sub σ M) (sub (sub_ext σ) N)
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

inductive reduce : Γ ⊢ A → Γ ⊢ A → Type where
  | xi_app_1 :
      reduce L L' → reduce (L ⬝ M) (L' ⬝ M)
  | xi_app_2 :
      Value V → reduce M M' → reduce (V ⬝ M) (V ⬝ M')
  | beta :
      Value W → reduce ((ƛ N) ⬝ W) (subst N W)
  | xi_succ :
      reduce M M' → reduce (M +1) (M' +1)
  | xi_case :
      reduce L L' → reduce (switch L M N) (switch L' M N)
  | beta_zero :
      reduce (switch o M N) M
  | beta_succ :
      Value V → reduce (switch (V +1) M N) (subst N V)
  | beta_mu :
      reduce (μ N) (subst N (μ N))
  deriving Repr

open reduce

infix:20 "~>" => reduce

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

inductive reduce_many : Γ ⊢ A → Γ ⊢ A → Type where
  | nil :
      reduce_many M M
  | cons :
      ∀ L, reduce L M → reduce_many M N → reduce_many L N
  deriving Repr

open reduce_many

infix:20 "~>>"  => reduce_many

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
    := xi_app_1 (beta Value.lambda)

example : ((ƛ (suc_c ⬝ (suc_c ⬝ # Z))) ⬝ 0 : ∅ ⊢ ℕ) ~> suc_c ⬝ (suc_c ⬝ 0)
    := beta Value.zero

example : (suc_c ⬝ (suc_c ⬝ 0) : ∅ ⊢ ℕ) ~> suc_c ⬝ 1
    := xi_app_2 Value.lambda (beta Value.zero)

example : (suc_c ⬝ 1 : ∅ ⊢ ℕ) ~> 2
    := beta (Value.succ Value.zero)

example : two ~>> 2 :=
  calc
    (two_c ⬝ suc_c ⬝ 0 : ∅ ⊢ ℕ)
      ~> (ƛ (suc_c ⬝ (suc_c ⬝ # Z))) ⬝ 0  := xi_app_1 (beta Value.lambda)
    _ ~> (suc_c ⬝ (suc_c ⬝ 0))            := beta Value.zero
    _ ~> suc_c ⬝ 1                       := xi_app_2 Value.lambda (beta Value.zero)
    _ ~> 2                              := beta (Value.succ Value.zero)

inductive Progress : Γ ⊢ A → Type where
  | step :
      (M ~> N) → Progress M
  | done :
      Value V → Progress V
  deriving Repr

open Progress

def progress : ∀ (M : ∅ ⊢ A), Progress M
  | (# x) => by contradiction
  | (ƛ N) => done Value.lambda
  | (L ⬝ M) =>
      match progress L with
        | step L_to_L' => step (xi_app_1 L_to_L')
        | done v =>
            match progress M with
              | step M_to_M' => step (xi_app_2 v M_to_M')
              | done w =>
                  match v with
                    | Value.lambda => step (beta w)
  | o => done Value.zero
  | (M +1) =>
      match progress M with
        | step M_to_M' => step (xi_succ M_to_M')
        | done v => done (Value.succ v)
  | (switch L M N) =>
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
          | Progress.done v => Steps.steps nil (done v)
          | @Progress.step _ _ _ M L_to_M =>
              match evaluate n M with
                | Steps.steps M_to_N f => Steps.steps (cons L L_to_M M_to_N) f

#check two_plus_two
#eval two_plus_two
#eval (evaluate 100 two_plus_two)

#reduce two_plus_two
#reduce (evaluate 100 two_plus_two)

#eval Lean.versionString

-- Exercise. Add products, as detailed in
--  https://plfa.inf.ed.ac.uk/More/#products
-- Pick suitable notations for introduction and elimination
-- of products that won't conflict.

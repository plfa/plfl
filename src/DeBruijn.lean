# DeBruijn

set_option pp.notation true
set_option maxRecDepth 10000

namespace DeBruijn

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

-- instance : OfNat (Γ ▷ A ∋ A) Nat.zero where
--   ofNat := lookup.stop

-- instance [OfNat (Γ ∋ B) n] : OfNat (Γ ▷ A ∋ B) (Nat.succ n) where
--   ofNat := lookup.pop (OfNat.ofNat n)

def two : ∀ {Γ}, Γ ⊢ ℕ := o +1 +1
def plus : ∀ {Γ}, Γ ⊢ ℕ ⇒ ℕ ⇒ ℕ :=
  μ ƛ ƛ (switch (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1))
def four : ∀ {Γ}, Γ ⊢ ℕ := plus ⬝ two ⬝ two

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
--         (M ~> N)
--         ----------
--       → star M N
--   | two :
--         star L M
--       → star M N
--         ----------
--       → star L N

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

theorem reduce_many_trans : (L ~>> M) → (M ~>> N) → (L ~>> N)
  := by
      intros L_to_M M_to_N
      induction L_to_M with
      | nil =>
        exact M_to_N
      | cons _ L_to_P _ ih =>
        apply cons
        exact L_to_P
        apply ih
        exact M_to_N

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

#check @Progress.step

def evaluate (n : Nat) (L : ∅ ⊢ A) : Steps L :=
  match n with
    | Nat.zero => steps nil out_of_gas
    | Nat.succ n =>
        match progress L with
          | Progress.done v => Steps.steps nil (done v)
          | @Progress.step _ _ _ M L_to_M =>
              match evaluate n M with
                | Steps.steps M_to_N f => Steps.steps (cons L L_to_M M_to_N) f

#eval (evaluate 100 four)
#reduce (evaluate 100 four)



-- Exercise. Add products, as detailed in
--  https://plfa.inf.ed.ac.uk/More/#products
-- Pick suitable notations for introduction and elimination
-- of products that won't conflict.

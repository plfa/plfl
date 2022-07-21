namespace DeBruijn

-- infix:40  "⊢"
-- infix:40  "∋"
-- infixl:50 "▷"
-- infixr:70 "⇒"
-- prefix:50 "ƛ"
-- prefix:50 "μ"
-- infixl:70 "·"
-- postifx:80 "+1"
-- notation:90 "0"
-- prefix:90 "`"
-- prefix:90 "S"
-- prefix:90 "#"

inductive Tp : Type where
| natural : Tp
| function : Tp → Tp → Tp

open Tp

notation:max "ℕ" => natural
infixr:70 "⇒" => function

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


infix:40  "∋" => lookup
infix:40  "⊢" => term

prefix:90 "S" => lookup.pop
notation:max "Z" => lookup.stop

prefix:90 "#" => term.var
prefix:50 "ƛ" => term.lambda
infixl:70 "⬝" => term.application
notation:max "o" => term.zero
postfix:80 "+1" => term.succ
notation:max "switch" L "[ o ⇒" M "| +1 ⇒" N "]" => term.case L M N
prefix:50 "μ" => term.mu

instance : OfNat (Γ ▷ A ∋ A) Nat.zero where
  ofNat := lookup.stop

instance [OfNat (Γ ∋ B) n] : OfNat (Γ ▷ A ∋ B) (Nat.succ n) where
  ofNat := lookup.pop (OfNat.ofNat n)
  
def two : ∀ {Γ}, Γ ⊢ ℕ := o +1 +1
def plus : ∀ {Γ}, Γ ⊢ ℕ ⇒ ℕ ⇒ ℕ :=
  μ ƛ ƛ switch (# Z) [ o ⇒ # S Z | +1 ⇒ (# S S S Z ⬝ # S S Z ⬝ # Z) +1 ]


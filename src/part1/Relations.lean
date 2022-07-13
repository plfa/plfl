open Nat

namespace Relations

inductive le : Nat → Nat → Prop
| refl : ∀ {m}, le m m
| step : ∀ {m n}, le m n → le m (succ n)

open le

instance : LE Nat where
  le := le

def lt (n m : Nat) := le (succ n) m

instance : LT Nat where
  lt := lt

def invert : ∀ {m n : Nat}, succ m ≤ succ n -> m ≤ n
  := by
      intros m n m_le_n
      cases m_le_n with
      | refl =>
         exact refl
      | step m_le_n =>
        cases n with
        | zero => contradiction
        | succ n => apply step; apply invert; assumption

-- Proof is by induction, but induction tactic does not apply.
-- Note explicit application of "invert"

def trans_le : ∀ {m n p : Nat}, m ≤ n → n ≤ p → m ≤ p
  := by
       intros m n p m_le_n n_le_p
       induction n_le_p with
       | refl => assumption
       | step n_le_p ih => apply step; exact ih





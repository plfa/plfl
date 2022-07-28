open Nat

namespace Relations

inductive le : Nat → Nat → Prop
| refl : ∀ {m}, le m m
| step : ∀ {m n}, le m n → le m (succ n)

instance : LE Nat where
  le := le

theorem trans_le : ∀ {m n p : Nat}, m ≤ n → n ≤ p → m ≤ p
  := by
       intros m n p m_le_n n_le_p
       induction n_le_p with
       | refl => assumption
       | step _ ih => apply le.step; exact ih

instance : Trans (.≤. : Nat → Nat → Prop)
                 (.≤. : Nat → Nat → Prop)
                 (.≤. : Nat → Nat → Prop) where
  trans := trans_le

example : 2 ≤ 7 :=
  calc
    2 ≤ 4 := le.step (le.step le.refl)
    _ ≤ 5 := le.step le.refl 
    _ ≤ 7 := le.step (le.step le.refl)

def lt (n m : Nat) := le (succ n) m

instance : LT Nat where
  lt := lt

def invert : ∀ {m n : Nat}, succ m ≤ succ n -> m ≤ n
  := by
      intros m n m_le_n
      cases m_le_n with
      | refl =>
         exact le.refl
      | step m_le_n =>
        cases n with
        | zero => contradiction
        | succ n => apply le.step; apply invert; assumption

-- Proof is by induction, but induction tactic does not apply.
-- Note explicit application of "invert"




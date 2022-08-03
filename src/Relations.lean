open Nat

namespace Relations

-- True and False under propositions as types

inductive True : Prop where
  | tt : True

inductive False : Prop where
  -- this line deliberately left blank

theorem ex_quod_libet : ∀ (P : Prop), False → P
  := by
       intros P f
       cases f

-- Inequality

inductive le : Nat → Nat → Prop
| refl : ∀ {m}, le m m
| step : ∀ {m n}, le m n → le m (succ n)

instance : LE Nat where
  le := le

theorem invert : ∀ {m n : Nat}, succ m ≤ succ n -> m ≤ n
  := by
      intros m n sm_le_sn
      cases sm_le_sn with
      | refl =>
         exact le.refl
      | step sm_le_n =>
         cases n with
         | zero => contradiction
         | succ n => apply le.step; apply invert; assumption

  -- Proof is by induction, but induction tactic does not apply.
  -- Note explicit application of "invert"

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

-- Strict inequality

def lt (n m : Nat) := le (succ n) m

instance : LT Nat where
  lt := lt

theorem le_of_lt : ∀ {m n : Nat}, m < n → m ≤ n
  := by sorry

-- Exercise.
-- Here is a different definition of ≤.
-- Prove the two definitions equivalent,
-- that is, that each implies the other.

inductive le2 : Nat → Nat → Prop
| z_le_n :
      ----------
      le2 zero n
| s_le_s :
      le2 m n
      ---------------------
    → le2 (succ m) (succ n)


-- Exercise.
-- Prove lt, lt2, and lt3 equivalent.

inductive lt2 : Nat → Nat → Prop where
| z_lt_s : ∀ {n}, lt2 zero (succ n)
| s_lt_s : ∀ {m n},
      lt2 m n
      ---------------------
    → lt2 (succ m) (succ n)

inductive lt3 : Nat → Nat → Prop where
| m_lt_sm : ∀ {m}, lt3 m (succ m)
| m_lt_sn : ∀ {m n},
      lt3 m n
      ---------------------
    → lt3 m (succ n)

-- Exercise. Prove the following.
--   m ≤ n iff ∃ p, m + p = n
--   m < n iff ∃ p, p ≠ 0 ∧ m + p = n



open Nat

namespace Relations

inductive True : Prop where
| tt : True

inductive False : Prop where
-- this line deliberately left blank

theorem ex_quod_libet : ∀ (P : Prop), False → P
  := by
       intros P f
       cases f


inductive le : Nat → Nat → Prop
| refl : ∀ {m}, le m m
| step : ∀ {m n}, le m n → le m (succ n)

open le

instance : LE Nat where
  le := le

def lt (n m : Nat) := le (succ n) m

instance : LT Nat where
  lt := lt

theorem invert : ∀ {m n : Nat}, succ m ≤ succ n -> m ≤ n
  := by
      intros m n sm_le_sn
      cases sm_le_sn with
      | refl =>
         exact refl
      | step sm_le_n =>
         cases n with
         | zero => contradiction
         | succ n => apply step; apply invert; assumption

-- Proof is by induction, but induction tactic does not apply.
-- Note explicit application of "invert"

[@trans] def trans_le : ∀ {m n p : Nat}, m ≤ n → n ≤ p → m ≤ p
  := by
       intros m n p m_le_n n_le_p
       induction n_le_p with
       | refl => assumption
       | step n_le_p ih => apply step; exact ih

example : 2 ≤ 5 :=
  calc
    2 ≤ 2  := refl
    _ ≤ 3  := step _

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

open le2

-- Exercise.
-- Prove lt and lt2 equivalent.

inductive lt2 : Nat → Nat → Prop where
| z_lt_s : ∀ {n}, lt2 zero (succ n)
| s_lt_s : ∀ {m n},
      lt2 m n
      ---------------------
    → lt2 (succ m) (succ n)




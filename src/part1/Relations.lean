open Nat

namespace Relations

inductive le : Nat → Nat → Prop
| refl : ∀ {m}, le m m
| step : ∀ {m n}, le m n → le m (succ n)

open le

infix:45 " << " => le

def invert : {m n : Nat} (m_le_n : succ m << succ n) -> m << n
  := sorry


-- | _ , _ , refl  =>  refl
-- | _ , _ , step m_le_n  =>  step (invert m_le_n)


def lt (n m : Nat) := le (succ n) m

infix:45 " < " => lt




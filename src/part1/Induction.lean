open Nat

namespace Induction

theorem add_zero (m : Nat)   : m + zero     = m            := rfl
theorem add_succ (m n : Nat) : m + (succ n) = succ (m + n) := rfl

theorem zero_add : ∀ (n : Nat), zero + n = n
  | zero   =>
    calc
      zero + zero
        = zero              := rfl
  | succ n => 
    calc
      zero + succ n
        =  succ (zero + n)  := rfl
      _ =  succ n           := by rw [zero_add n]

  
  
  -- congrArg succ (zero_add n)


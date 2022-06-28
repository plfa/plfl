open Nat

namespace Induction

theorem add_zero (m : Nat)   : m + zero     = m            := rfl
theorem add_succ (m n : Nat) : m + (succ n) = succ (m + n) := rfl

theorem add_assoc : ∀ (m n p : Nat), (m + n) + p = m + (n + p)
  | m , n , zero =>
    calc
      (m + n) + zero
        = m + n               := by rw [add_zero (m + n)]
      _ = m + (n + zero)      := by rw [add_zero n]
  | m , n , succ p =>
    calc
      (m + n) + succ p
        = succ ((m + n) + p)  := by rw [add_succ (m + n) p]
      _ = succ (m + (n + p))  := by rw [add_assoc m n p]
      _ = m + succ (n + p)    := by rw [add_succ m (n + p)]
      _ = m + (n + succ p)    := by rw [add_succ n p]


theorem zero_add : ∀ (n : Nat), zero + n = n
  | zero =>
    calc
      zero + zero
        = zero              := rfl
  | succ n => 
    calc
      zero + succ n
        =  succ (zero + n)  := rfl
      _ =  succ n           := by rw [zero_add n]

theorem succ_add : ∀ (m n : Nat), (succ m) + n = succ (m + n)
  | m , zero =>
    calc
      (succ m) + zero
        = succ m            := rfl
      _ = succ (m + zero)   := rfl
  | m , succ n =>
    calc
      (succ m) + (succ n)
        = succ ((succ m) + n)  := rfl
      _ = succ (succ (m + n))  := by rw [succ_add m n]
      _ = succ (m + (succ n))  := rfl


  
  -- congrArg succ (zero_add n)


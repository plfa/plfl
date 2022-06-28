open Nat

namespace Induction

example : 3 + (4 + 5) = (3 + 4) + 5 :=
  calc
    3 + (4 + 5)
      =  3 + 9        := rfl
    _ =  12           := rfl
    _ =  7 + 5        := rfl
    _ =  (3 + 4) + 5  := rfl

theorem add_zero (m : Nat)   : m + zero     = m            := rfl
theorem add_succ (m n : Nat) : m + (succ n) = succ (m + n) := rfl

theorem add_assoc : ∀ (m n p : Nat), m + (n + p) = (m + n) + p
  | m , n , zero =>
    calc
      m + (n + zero)
        = m + n               := by rw [add_zero n]
      _ = (m + n) + zero      := by rw [add_zero (m + n)]
  | m , n , succ p =>
    calc
      m + (n + succ p)
        = m + succ (n + p)    := by rw [add_succ n p]
      _ = succ (m + (n + p))  := by rw [add_succ m (n + p)]
      _ = succ ((m + n) + p)  := by rw [add_assoc m n p]
      _ = (m + n) + succ p    := by rw [add_succ (m + n) p]

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

theorem comm_add : ∀ (m n : Nat), m + n = n + m
  | zero , n =>
    calc
      zero + n
        = n                     := by rw [zero_add n]
      _ = n + zero              := rfl
  | succ m , n =>
    calc
      (succ m) + n
        = succ (m + n)          := by rw [succ_add m n]
      _ = succ (n + m)          := by rw [comm_add m n]
      _ = n + (succ m)          := rfl
      
  
  -- congrArg succ (zero_add n)


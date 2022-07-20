open Nat

theorem subst (A : Type) (a b : A) (e : a = b) (P : A → Prop) (h : P a) : P b
  := by rw [<- e]; exact h

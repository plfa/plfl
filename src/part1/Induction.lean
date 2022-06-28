namespace Induction

theorem add_assoc (m n p : Nat) : (m + n) + p = m + (n + p) :=
  by induction p with p where
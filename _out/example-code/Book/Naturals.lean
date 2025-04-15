namespace MyNat

inductive ℕ where
  | zero
  | succ (n : ℕ) : ℕ

end MyNat

namespace MyNat

def ofNat : _root_.Nat → ℕ
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

instance : OfNat ℕ n where
  ofNat := ofNat n

end MyNat

namespace MyNat

abbrev add : ℕ → ℕ → ℕ
  | m, .zero => m
  | m, .succ n => .succ (add m n)

instance : Add ℕ where
  add := add

example : 2 + 2 = (4 : ℕ) := by rfl

end MyNat

#eval 2 + 2

#eval 2 + foo


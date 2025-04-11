namespace MyNats

inductive Nat where
  | zero
  | succ : Nat → Nat

def Nat.ofNat : _root_.Nat → Nat
  | 0 => .zero
  | n + 1 => .succ (.ofNat n)

instance : OfNat Nat n where
  ofNat := .ofNat n

@[match_pattern]
def Nat.add (n k : Nat) : Nat :=
  match k with
  | .zero => n
  | .succ k' => .succ (n.add k')

instance : Add Nat where
  add := Nat.add

def Nat.toNat : MyNats.Nat → _root_.Nat
  | 0 => 0
  | n + 1 => toNat n + 1

end MyNats



namespace Naturals

inductive ℕ where
  | zero : ℕ
  | succ : ℕ → ℕ

open ℕ

def ℕ_of_Nat : Nat → ℕ 
  | Nat.zero    =>  zero
  | Nat.succ n  =>  succ (ℕ_of_Nat n)

instance : OfNat ℕ n where
  ofNat := ℕ_of_Nat n

def add : ℕ → ℕ → ℕ
  | m , zero   => m
  | m , succ n => succ (add m n)

instance : Add ℕ where
  add := add

example : 3 + 2 = (5 : ℕ) :=
  calc
    3 + 2 
      =  succ (3 + 1)         := rfl
    _ =  succ (succ (3 + 0))  := rfl
    _ =  succ (succ 3)        := rfl
    _ =  (5 : ℕ)              := rfl

-- a shorter proof
example : 3 + 2 = 5 := rfl

def mul : ℕ → ℕ → ℕ
  | _ , zero   => zero
  | m , succ n => (mul m n) + m

instance : Mul ℕ where
  mul := mul

example : 3 * 2 = (6 : ℕ) :=
  calc
    3 * 2  
      =  (3 * 1 + 3 : ℕ)     := rfl
    _ =  (3 * 0 + 3 + 3 : ℕ) := rfl
    _ =  (0 + 3 + 3 : ℕ)     := rfl
    _ =  (6 : ℕ)             := rfl

def monus : ℕ → ℕ → ℕ
  | m      , zero    =>  m
  | zero   , succ _  =>  zero
  | succ m , succ n  =>  monus m n

instance : Sub ℕ where
  sub := monus

example : 3 - 2 = (1 : ℕ) :=
  calc
    3 - 2  
      =  (2 - 1 : ℕ)  := rfl
    _ =  (1 - 0 : ℕ)  := rfl
    _ =  (1 : ℕ)     := rfl

example : 2 - 3 = (0 : ℕ) :=
  calc
    2 - 3  
      =  (1 - 2 : ℕ)  := rfl
    _ =  (0 - 1 : ℕ)  := rfl
    _ =  (0 : ℕ)      := rfl








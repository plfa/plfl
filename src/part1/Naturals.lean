namespace Naturals

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

open Nat

def convert : _root_.Nat → Nat 
  | _root_.Nat.zero    =>  zero
  | _root_.Nat.succ n  =>  succ (convert n)

instance : OfNat Nat n where
  ofNat := convert n

def add : Nat → Nat → Nat
  | m , zero   => m
  | m , succ n => succ (add m n)

instance : Add Nat where
  add := add

example : 3 + 2 = (5 : Nat) :=
  calc
    3 + 2 
      =  succ (3 + 1)         := rfl
    _ =  succ (succ (3 + 0))  := rfl
    _ =  succ (succ 3)        := rfl
    _ =  (5 : Nat)            := rfl

-- a shorter proof
example : 3 + 2 = 5 := rfl

def mul : Nat → Nat → Nat
  | _ , zero   => zero
  | m , succ n => (mul m n) + m

instance : Mul Nat where
  mul := mul

example : 3 * 2 = (6 : Nat) :=
  calc
    3 * 2  
      =  (3 * 1 + 3 : Nat)     := rfl
    _ =  (3 * 0 + 3 + 3 : Nat) := rfl
    _ =  (0 + 3 + 3 : Nat)     := rfl
    _ =  (6 : Nat)             := rfl

def monus : Nat → Nat → Nat
  | m      , zero    =>  m
  | zero   , succ _  =>  zero
  | succ m , succ n  =>  monus m n

instance : Sub Nat where
  sub := monus

example : 3 - 2 = (1 : Nat) :=
  calc
    3 - 2  
      =  (2 - 1 : Nat)  := rfl
    _ =  (1 - 0 : Nat)  := rfl
    _ =  (1 : Nat)      := rfl

example : 2 - 3 = (0 : Nat) :=
  calc
    2 - 3  
      =  (1 - 2 : Nat)  := rfl
    _ =  (0 - 1 : Nat)  := rfl
    _ =  (0 : Nat)      := rfl








/-
Copyright (c) Philip Wadler. All rights reserved.
Released under Creative Commons CC-BY License as described in file LICENSE.
Author: Philip Wadler
-/

import VersoManual
import Book.Meta.Lean
import Book.Papers

/-!
Book.Naturals: The natural numbers
-/

-- This gets access to most of the manual genre (which is also useful for
-- textbooks)
open Verso.Genre
open Verso.Genre.Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same
-- process and environment as Verso
open Verso.Genre.Manual.InlineLean


open Book

set_option pp.rawOnError true



#doc (Manual) "The Natural Numbers" =>

```savedLean
#check Nat
@[class] inductive Test : Type where

set_option pp.all true -- in
#check 1 ≤ 2
#check 1 + 2
#check 1 :: 2 :: []
#check 1 = 2




namespace Naturals

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

inductive Bool where
  | true : Bool
  | false : Bool

open Nat

example : Nat := succ (succ zero)

open Nat

def convert : _root_.Nat → Nat
  | _root_.Nat.zero    =>  zero
  | _root_.Nat.succ n  =>  succ (convert n)

instance (n : _root_.Nat) : OfNat Nat n where
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
example : 3 + 2 = (5 : Nat) := rfl

-- from lean4/src/Init/Prelude.lean
-- class Add (α : Type) where
--   add : α → α → α
-- class Mul (α : Type) where
--   mul : α → α → α

-- from lean4/src/Init/Notation.lean (simplified)
-- infixl:65 " + "   => Add.add
-- infixl:70 " * "   => Mul.mul


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

def monus1 : Nat → Nat
| zero => zero
| succ n => n

theorem invert (m n : Nat) : succ m = succ n → m = n
  := by
    intro succ_m_eq_succ_n
    calc
      m = monus1 (succ m)  := by rfl
      _ = monus1 (succ n)  := by rw [succ_m_eq_succ_n]
      _ = n                := by rfl

def is_zero : Nat → Prop
| zero => True
| succ _ => False

theorem invert' (m n : Nat) (h : succ m = succ n) : m = n
  := by injection h with h'

theorem succ_neq_zero (n : Nat) (h : succ n = zero) : False
  := by injection h

theorem succ_neq_zero' (n : Nat) (h : succ n = zero) : False
  := by contradiction
```

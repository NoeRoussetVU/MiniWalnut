import MiniWalnut.Basic

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Powerset

/-

Defines the automatons and number basis used in Walnut

-/

-- Simple enumeration type
inductive B2 where
  | zero
  | one
  deriving Repr, BEq, DecidableEq, Inhabited

inductive binary_logical_ops where
  | and
  | or
  | exclusive_dinjuction
  | impl
  | equiv

-- TODO: add variables and full dfas for the ones below epic meme balls meme haha tuah
structure DFA_Complete (T : Type) (Q : Type) where
  states : List Q
  alphabet : List T
  dead_state : Option Q
  vars : List Char
  automata : DFA T Q

/- msd_2 Automatons -/

def valid_representations : DFA B2 Nat := {
  step := fun x y => match x,y with
    | _, _ => 0
  start := 0
  accept := {x | x=0}
}

def addition : DFA (B2 × B2 × B2) Nat := {
  step := fun x y => match x,y with
    | 0, (B2.zero, B2.zero, B2.zero) => 0
    | 0, (B2.one, B2.one, B2.zero) => 0
    | 0, (B2.one, B2.zero, B2.one) => 0
    | 0, (B2.one, B2.zero, B2.zero) => 1
    | 1, (B2.one, B2.one, B2.one) => 1
    | 1, (B2.zero, B2.one, B2.zero) => 1
    | 1, (B2.zero, B2.zero, B2.one) => 1
    | 1, (B2.zero, B2.one, B2.one) => 0
    | _, _ => 2
  start := 0
  accept := {x | x=0}
}

def equals : DFA (B2 × B2) Nat := {
  step := fun x y => match x,y with
    | 0, (B2.zero, B2.zero) => 0
    | 0, (B2.one, B2.one) => 0
    | _, _ => 1
  start := 0
  accept := {x | x=0}
}

def less_than : DFA (B2 × B2) Nat := {
  step := fun x y => match x,y with
    | 0, (B2.zero, B2.zero) => 0
    | 0, (B2.one, B2.one) => 0
    | 0, (B2.zero, B2.one) => 1
    | 1, (B2.one, B2.one) => 1
    | 1, (B2.zero, B2.one) => 1
    | 1, (B2.one, B2.zero) => 1
    | 1, (B2.zero, B2.zero) => 1
    | _, _ => 2
  start := 0
  accept := {x | x=1}
}

/- Thue-Morse DFAO -/

def thue_morse : DFA B2 Nat := {
  step := fun x y => match x,y with
    | 0, B2.zero => 0
    | 0, B2.one => 1
    | 1, B2.zero => 1
    | 1, B2.one => 0
    | _, _ => 2
  start := 0
  accept := {}
}

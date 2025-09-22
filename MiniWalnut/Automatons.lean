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


inductive MyType where
  | stringValue : String → MyType
  | intValue : Int → MyType

def processMyType (arg : MyType) : String :=
  match arg with
  | MyType.stringValue s => "Got string: " ++ s
  | MyType.intValue i => "Got int: " ++ toString i

#eval processMyType (MyType.stringValue "hello")  -- Create string variant

-- Simple enumeration type
inductive B2 where
  | zero
  | one
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

inductive l_ops where
  | and
  | or
  | exclusive_dinjuction
  | impl
  | equiv

inductive b_ops where
  | equals
  | less_than
  | more_than

inductive binary_ops where
  | logical_op : l_ops → binary_ops
  | comparison_op : b_ops → binary_ops


structure DFA_Complete (T : Type) (Q : Type) where
  states : List Q
  states_accept : List Q
  alphabet : List T
  dead_state : Option Q
  vars : List Char
  alphabet_vars : List T
  automata : DFA T Q

/- msd_2 Automatons -/

def valid_representations : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero] => 0
    | 0, [B2.one] => 0
    | _, _ => 1
  start := 0
  accept := {x | x=0}
}

def addition : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero, B2.zero] => 0
    | 0, [B2.one, B2.one, B2.zero] => 0
    | 0, [B2.one, B2.zero, B2.one] => 0
    | 0, [B2.one, B2.zero, B2.zero] => 1
    | 1, [B2.one, B2.one, B2.one] => 1
    | 1, [B2.zero, B2.one, B2.zero] => 1
    | 1, [B2.zero, B2.zero, B2.one] => 1
    | 1, [B2.zero, B2.one, B2.one] => 0
    | _, _ => 2
  start := 0
  accept := {x | x=0}
}

def equals : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero] => 0
    | 0, [B2.one, B2.one] => 0
    | _, _ => 1
  start := 0
  accept := {x | x=0}
}

def less_than : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero] => 0
    | 0, [B2.one, B2.one] => 0
    | 0, [B2.zero, B2.one] => 1
    | 1, [B2.one, B2.one] => 1
    | 1, [B2.zero, B2.one] => 1
    | 1, [B2.one, B2.zero] => 1
    | 1, [B2.zero, B2.zero] => 1
    | _, _ => 2
  start := 0
  accept := {x | x=1}
}

def greater_than : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero] => 0
    | 0, [B2.one, B2.one] => 0
    | 0, [B2.one, B2.zero] => 1
    | 1, [B2.one, B2.one] => 1
    | 1, [B2.zero, B2.one] => 1
    | 1, [B2.one, B2.zero] => 1
    | 1, [B2.zero, B2.zero] => 1
    | _, _ => 2
  start := 0
  accept := {x | x=1}
}

/- Thue-Morse DFAO -/

def thue_morse : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero] => 0
    | 0, [B2.one] => 1
    | 1, [B2.zero] => 1
    | 1, [B2.one] => 0
    | _, _ => 2
  start := 0
  accept := {}
}

/- Create full DFAs -/

-- Create a DFA that accepts exactly one specific word
def createEqualsDFA {α : Type} [DecidableEq α] (word : List α) (zero : α): DFA α Nat where
  step := fun state symbol =>
    -- If we're at position i and see the expected symbol, advance to i+1
    -- Otherwise, go to a "dead" state (word.length + 1)
    if state < word.length && word[state]? = some symbol then
      state + 1
    else if state = 0 && symbol = zero then
      state
    else
      word.length + 1  -- Dead state
  start := 0
  accept := {word.length}  -- Only the final state after reading the complete word

def createFullEqualsDFA (word : List (List B2)) (zero : List B2) (vars : List Char) : DFA_Complete (List B2) Nat where
  automata := createEqualsDFA word zero
  states := (List.range (word.length + 2))
  states_accept := [word.length]
  alphabet := [[B2.zero], [B2.one]]
  dead_state := some (word.length + 1)
  vars := vars
  alphabet_vars := [[B2.zero], [B2.one]]

def createFullAdditionDFA (vars : List Char) : DFA_Complete (List B2) Nat where
  automata := addition
  states := [0,1,2]
  states_accept := [0]
  alphabet := [[B2.zero, B2.zero, B2.zero],
  [B2.one, B2.one, B2.zero],
  [B2.one, B2.zero, B2.one],
  [B2.one, B2.zero, B2.zero],
  [B2.one, B2.one, B2.one],
  [B2.zero, B2.one, B2.zero],
  [B2.zero, B2.zero, B2.one],
  [B2.zero, B2.one, B2.one]]
  dead_state := some 2
  vars := vars
  alphabet_vars := [[B2.zero], [B2.one]]

def createFullLTDFA (vars : List Char) : DFA_Complete (List B2) Nat where
  automata := less_than
  states := [0,1,2]
  states_accept := [1]
  alphabet := [[B2.zero, B2.zero], [B2.one, B2.one], [B2.zero, B2.one],
  [B2.one, B2.zero]]
  dead_state := some 2
  vars := vars
  alphabet_vars := [[B2.zero], [B2.one]]

def createFullGTDFA (vars : List Char) : DFA_Complete (List B2) Nat where
  automata := greater_than
  states := [0,1,2]
  states_accept := [1]
  alphabet := [[B2.zero, B2.zero], [B2.one, B2.one], [B2.zero, B2.one],
  [B2.one, B2.zero]]
  dead_state := some 2
  vars := vars
  alphabet_vars := [[B2.zero], [B2.one]]

def createThueMorseEqualsDFA (value : Nat)  (vars : List Char) : DFA_Complete (List B2) Nat where
  automata := thue_morse
  states := [0,1,2]
  states_accept := [value]
  alphabet := [[B2.zero], [B2.one]]
  dead_state := some 2
  vars := vars
  alphabet_vars := [[B2.zero], [B2.one]]

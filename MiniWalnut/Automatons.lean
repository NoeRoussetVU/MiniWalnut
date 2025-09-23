import MiniWalnut.Basic

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Data.Set.Basic

/-

  This files contains defintions for automata used to build complex predicates
  and helper functions and custom types

-/

/-

  Custom types for operations in Walnut

-/

-- Base 2 custom type
inductive B2 where
  | zero
  | one
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

-- Extended definition for automata
structure DFA_Complete (T : Type) (Q : Type) where
  states : List Q
  states_accept : List Q
  alphabet : List T
  dead_state : Option Q
  vars : List Char
  alphabet_vars : List T
  automata : DFA T Q

/-

  msd_2 Automatons

-/

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

/-

  Thue-Morse DFAO

-/

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

/-

  Functions to create extended DFAs

-/

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

/-

  Complement Operation

-/

def complement { Input : Type} [DecidableEq Input]
  (M1 : DFA_Complete (List Input) (Nat)) : DFA_Complete (List Input) (Nat) :=
  let new_accepting_states := M1.states.filter (fun x => !M1.states_accept.contains x)
  let new_accept := {p | p ∉ M1.automata.accept ∧ M1.states.contains p}
  let new_automata : DFA (List Input) (Nat) := {step := M1.automata.step, start := M1.automata.start, accept := new_accept}
  {states := M1.states, states_accept := new_accepting_states, alphabet := M1.alphabet, alphabet_vars := M1.alphabet_vars, dead_state := none, vars := M1.vars, automata := new_automata}

/-

  Functions to change states types to natural numbers for a DFA

-/

def assignNumbers {State : Type} [DecidableEq State] [Hashable State] (fullList : List State) (subList : List State) :
  (List ℕ × List ℕ × Std.HashMap State ℕ) :=
  let uniqueElements := fullList.foldl (fun acc elem =>
    if elem ∈ acc then acc else acc ++ [elem]) []

  let mapping := Std.HashMap.ofList uniqueElements.zipIdx

  let lookupNumber (elem : State) : ℕ :=
    mapping[elem]!

  (fullList.map lookupNumber, subList.map lookupNumber, mapping)

def change_states_names {Input State : Type} [Inhabited Input] [DecidableEq Input] [Inhabited State] [DecidableEq State] [Hashable State]
(M1 : DFA_Complete (List Input) State)
 : DFA_Complete (List Input) Nat :=
  let mappingas := (assignNumbers M1.states M1.states_accept)
  let new_states :=  mappingas.fst
  let new_states_accept :=  mappingas.snd.fst

  let og_states := mappingas.snd.snd.keys
  let transitions := og_states.map (fun x => M1.alphabet.map (fun z => ((mappingas.snd.snd[(x)]!, z), mappingas.snd.snd[(M1.automata.step (x) z)]! )))
  let tf := transitions.flatten

  let new_dead_state := match M1.dead_state with
                |none => none
                |some n => some mappingas.snd.snd[n]!

  let automata := {
    -- Transition function pairs the functions of the two DFAs
    -- TODO: add dead state if list length is bad
    step := fun st input =>
    let tr := tf.filter (fun ((x,y),_) => st = x ∧ input = y)
    match tr.head? with
    | some ((x,y),z) => z
    | _ => match new_dead_state with
          | some w => w
          | _ => new_states.length+100
    -- Starting state is the pair of starting states
    start :=  mappingas.snd.snd[M1.automata.start]!
    -- Accepting states are pairs where both components are accepting for AND
    -- either component is accepting for OR
    accept := {p | new_states_accept.contains p}
  }
  {states := new_states, states_accept := new_states_accept, alphabet := M1.alphabet, alphabet_vars := M1.alphabet_vars, dead_state := new_dead_state, vars := M1.vars, automata := automata}


def valid_representations' : DFA (List B2) (Fin 1) := {
  step := fun x y =>
    let x' := x.val
    match x',y with
    | 0, [B2.zero] => 0
    | 0, [B2.one] => 0
    | 0, _ => 0
    | _, _ => 69 -- XD
  start := 0
  accept := {x | x=0}
}

def fin : Fin 2 := 3

#eval fin

#check Fin 2

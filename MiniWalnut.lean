-- This module serves as the root of the `MiniWalnut` library.
-- Import modules here that should be built as part of the library.
import MiniWalnut.Basic
import MiniWalnut.Crossproduct
--import MiniWalnut.Quantification

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Powerset

/-

DFA and NFA defintion with states and alphabet

  Current plans xD
  Function that can create automata of the type a = int with the Base2 class,
  with states as strings

  Fix up cross product
  Fix up quant
  Make my own determinization function with finset and stuff
  Make DFAO class and define sequences with it
  Make it so you can use index with it kinda
  Heaven reached

-/

-- Simple enumeration type
inductive Base2 where
  | zero
  | one
  deriving Repr, BEq, DecidableEq, Inhabited

structure DFA_Complete_' {Q : Type} (alphabet : Finset Base2) (states : Finset Q) where
  automata : DFA Base2 Q

#check Base2.zero
#check Base2

def base2Alphabet : Finset Base2 := {Base2.zero, Base2.one}

def test_dfa : DFA_Complete_' base2Alphabet {"a", "b"}:={
  automata :={
    step := fun x y => match x,y with
    | "PENIS", Base2.zero => "ass"
    | _, Base2.zero => "ass"
    | _, Base2.one => "love"

  }
}

structure DFA_Complete_ (T : Type) (Q : Type) where
  states : List Q
  alphabet : List T
  automata : DFA T Q

structure NFA_Complete_ (T : Type) (Q : Type) where
  states : List Q
  alphabet : List T
  automata : NFA T Q

/-
  DFA Generation
-/

/-
  DFA accepting a given word
  Starting state = 0
  Accepting state = list length
  Dead state = list length + 1
-/

-- Create a DFA that accepts exactly one specific word
def createWordDFA {α : Type} [DecidableEq α] (word : List α) (zero : α): DFA α Nat where
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


-- Example DFA accetping abc
def acceptedWord : List Char := ['a','b','c']
def word_DFA := createWordDFA acceptedWord '0'
#eval word_DFA.eval []
#eval word_DFA.eval ['a']
#eval word_DFA.eval ['a','b','c']
#eval word_DFA.eval ['0','0','a','b','c']
#eval word_DFA.eval ['b']

/-

Cross-product on created DFAs

-/

-- DFA accepting 1

def oneDfa := createWordDFA [1] 0

def dfa_one_ : DFA_Complete_ (Nat) (Nat) := {
  states := (List.range ([1].length + 2))
  alphabet := [0,1]
  automata := oneDfa
}

-- DFA accepting 10

def twoDfa := createWordDFA [1,0] 0

def dfa_two_ : DFA_Complete_ (Nat) (Nat) := {
  states := (List.range ([1,0].length + 2))
  alphabet := [0,1]
  automata := twoDfa
}

#eval dfa_one_.states
#eval dfa_two_.states
#eval combinations_for_list dfa_one_.states dfa_two_.states

-- Cross product of two DFAs
def DFA_Complete_.crossProduct {State1 State2 Input1 Input2 : Type} (M1 : DFA_Complete_ Input1 State1) (conj : String) (M2 : DFA_Complete_ Input2 State2)
 : DFA_Complete_ (Input1 × Input2) (State1 × State2) where
  states := combinations_for_list M1.states M2.states
  alphabet := combinations_for_list M1.alphabet M2.alphabet
  automata := {
    -- Transition function pairs the functions of the two DFAs
    step := fun (q1, q2) a => (M1.automata.step q1 a.fst, M2.automata.step q2 a.snd)
    -- Starting state is the pair of starting states
    start := (M1.automata.start, M2.automata.start)
    -- Accepting states are pairs where both components are accepting for AND
    -- either component is accepting for OR
    accept := if conj == "AND" then {p | p.fst ∈ M1.automata.accept ∧ p.snd ∈ M2.automata.accept}
  else {p | p.fst ∈ M1.automata.accept ∨ p.snd ∈ M2.automata.accept}
  }

def intersectionDFATwo := dfa_one_.crossProduct "OR" dfa_two_

#eval intersectionDFATwo.alphabet
#eval intersectionDFATwo.states

#eval intersectionDFATwo.automata.eval [(0,1),(1,0)]
#eval intersectionDFATwo.automata.eval [(0,1),(1,1)]
#eval intersectionDFATwo.automata.eval [(1,1),(1,0)]


/-

Quantification on cross-product DFA

  First add all the states reachable from the starting state with 0*

-/

/-structure NFA_temp (T : Type) (Q : Type) where
  states : List Q
  alphabet : List T
  step : Q → T → List Q
  start_states : List Q
  accept_states : Set Q-/

-- Helper function to process a single input symbol from a set of current states
def processSymbol {T Q : Type} [DecidableEq Q] (start_states : List Q) (f : Q → T → List Q) (currentStates : List Q) (symbol : T) : List Q :=
  let nextStates := currentStates.foldl (fun acc state =>
    acc ++ f state symbol
  ) []
  nextStates.eraseDups

-- Function to find all states reachable with exactly n zeros
def reachableWithNZeros {T Q : Type} [DecidableEq T] [DecidableEq Q] (start_states : List Q) (f : Q → T → List Q) (n : Nat) (zero : T) : List Q :=
  if n = 0 then
    start_states
  else
    let rec helper (currentStates : List Q) (remaining : Nat) : List Q :=
      if remaining = 0 then
        currentStates
      else
        let nextStates := processSymbol start_states f currentStates zero
        helper nextStates (remaining - 1)
    helper start_states n

-- Main function: Find all states reachable with one or more zeros
def reachableWithOneOrMoreZeros {T Q : Type} [DecidableEq T] [DecidableEq Q] (start_states : List Q) (f : Q → T → List Q) (zero : T) (maxZeros : Nat) : List Q :=
  let allReachableStates := (List.range maxZeros).foldl (fun acc n =>
    if n = 0 then acc
    else acc ++ reachableWithNZeros start_states f n zero
  ) []
  allReachableStates


#eval intersectionDFATwo.automata.step (0,1) (0,0)

#eval intersectionDFATwo.alphabet.map (fun x => intersectionDFATwo.automata.step (0,0) (x))
#eval intersectionDFATwo.states.map (fun x => intersectionDFATwo.alphabet.map (fun y => intersectionDFATwo.automata.step x y))

def quant {State1 State2 Input1 Input2 : Type} [DecidableEq Input1] [DecidableEq Input2] [DecidableEq State1] [DecidableEq State2]
  (M1 : DFA_Complete_ (Input1 × Input2) (State1 × State2)) (zero : Input1):
  NFA_Complete_ (Input1) (State1 × State2) :=
  -- Remove second item from alphabet
  let new_alphabet := M1.alphabet.map (fun (x,_) => x)
  -- Transition function that given input for first tuple, returns list of all reachable states
  let step := fun st input => ((M1.alphabet.filter (fun (x,_) => x == input)).map (fun (_,y) => M1.automata.step st (input, y)))
  -- Finds all states reachable from the starting state with 0*
  let start_states := (reachableWithOneOrMoreZeros {M1.automata.start} step zero M1.states.length).dedup
  -- Build correspdonding NFA (need to change this!!!!)
  let nfa : NFA Input1 (State1 × State2) :={
    step := fun st input => ((M1.alphabet.filter (fun (x,_) => x == input)).map (fun (_,y) => M1.automata.step st (input, y))).toFinset.toSet
    start := start_states.toFinset.toSet
    accept := M1.automata.accept
  }
  {states := M1.states, alphabet := new_alphabet, automata := nfa}


def quantified_dfa : NFA_Complete_ Nat (Nat × Nat) := quant intersectionDFATwo 0

def quantified_nfa : DFA Nat (Set (Nat × Nat)) := quantified_dfa.automata.toDFA

#check quantified_nfa.eval [0]
#eval quantified_nfa.eval [0]

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
decreasing_by
   -- unfolds well-founded recursion auxiliary definitions:
  all_goals simp
  · apply Prod.Lex.left; simp +arith
  · apply Prod.Lex.right; simp +arith
  · apply Prod.Lex.left; simp +arith

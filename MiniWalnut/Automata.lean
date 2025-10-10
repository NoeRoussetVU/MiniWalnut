import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Basic

/-!
# Automata Definitions for Walnut Operations

Implements the necessary components to support base-2 operations in Walnut, as well as the
complement and state renaming operations.

### Main Components

- **Binary alphabet**: Custom type to implement base-2 input for automata
- **Extended DFA structure**: DFA with fields necessary for the decision algorithm
- **Basic Automata**: DFA implementing base-2 operations
- **Automatic Sequence DFAO**: Thue-Morse sequence automaton
- **DFA construction**: Functions initializing DFAs in their extended structure
- **Operations**: Complement and state renaming
-/

/-!
## Custom Types for Walnut Operations

These types support automata-based arithmetic and logical operations.
-/

/-- Binary alphabet with two symbols: zero and one.
    Used for representing numbers in base-2 (msd - most significant digit first).
-/
inductive B2 where
  | zero
  | one
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- Extended DFA structure that includes additional fields beyond the standard DFA.

    This structure wraps a standard DFA with extra information needed for
    automata operations.

    ### Fields
    - `states`: Set of all states in the automaton
    - `states_accept`: Set of accepting states
    - `alphabet`: Set of the input alphabet
    - `dead_state`: Optional dead state for invalid inputs
    - `vars`: Variable names associated with the automaton's inputs
    - `automata`: DFA structure from Mathlib
-/
structure DFA_extended (T : Type) (Q : Type) [Hashable Q] [BEq Q]  where
  states : Std.HashSet Q
  states_accept : Std.HashSet Q
  alphabet : Std.HashSet (List B2)
  dead_state : Option Q
  vars : List Char
  automata : DFA (List B2) Q

/-!

## MSD-2 Automata (Most Significant Digit First, Base 2)

These automata represent different operations in base 2 with most significant digit first
and accepting any amount of leading zeroes. They are used as building blocks to build automata
representing more complex predicates.

Some of the automata take multiple values as input. To support this each automata has an
alphabet of lists, with the value at each index representing the corresponding variable.

-/

/-- Automaton that accepts only valid representations.

    ### States
    - 0: Valid representation (initial state, accepting)
    - 1: Invalid representation (dead state)

    ### Transitions
    - From state 0: Reading [0] or [1] stays in state 0 (valid)
    - Everything else goes to state 1 (invalid)
-/
def valid_representations : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero] => 0
    | 0, [B2.one] => 0
    | _, _ => 1
  start := 0
  accept := {x | x = 0}
}

/-- Automaton for binary addition: accepts (a, b, c) where a = b + c.

    This is a 3-track automaton that reads three binary numbers simultaneously
    and accepts if they form a valid addition relation.

    ### States
    - 0: No carry (initial and accepting state)
    - 1: Has carry from previous position
    - 2: Dead state (invalid input)

    ### Transitions
    - From state 0: If a = b + c is valid ([0,0,0],[1,1,0],[1,0,1]) stay in this state.
      If [1,0,0] is read, a carry is generated and it goes to state 1.
    - From state 1: If a = b + c is an operation with a carry ([1,1,1],[0,0,1],[0,1,0])
      If [0,1,1] is read, the carry is consumed and it goes back to state 0.
    - Anything else is invalid and goes to the dead state, 2.
-/
def addition : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero, B2.zero] => 0  -- 0 = 0 + 0, no carry
    | 0, [B2.one, B2.one, B2.zero] => 0    -- 1 = 1 + 0, no carry
    | 0, [B2.one, B2.zero, B2.one] => 0    -- 1 = 0 + 1, no carry
    | 0, [B2.one, B2.zero, B2.zero] => 1   -- 1 = 0 + 0, carry generated
    | 1, [B2.one, B2.one, B2.one] => 1     -- 1 = 1 + 1 (+ 1), carry continues
    | 1, [B2.zero, B2.one, B2.zero] => 1   -- 0 = 1 + 0 (+ 1), carry continues
    | 1, [B2.zero, B2.zero, B2.one] => 1   -- 0 = 0 + 1 (+ 1), carry continues
    | 1, [B2.zero, B2.one, B2.one] => 0    -- 0 = 1 + 1 (+ 1), carry consumed
    | _, _ => 2                            -- Invalid input - dead state
  start := 0
  accept := {x | x = 0}
}

/-- Example: Prove that 5 = 3 + 2 is accepted -/
example :
    -- [B2.one, B2.zero, B2.one]  5 in binary
    -- [B2.one, B2.one]  3 in binary
    -- [B2.one, B2.zero] 2 in binary
    -- Pad to same length: a=101, b=011, c=010
    let input := [[B2.one, B2.zero, B2.zero], [B2.zero, B2.one, B2.one], [B2.one, B2.one, B2.zero]]
    addition.eval input = 0 := by
  rfl

/-- Example: Prove that 3 ≠ 1 + 1 is rejected -/
example :
    -- [B2.one, B2.one] 3 in binary
    -- [B2.one] 1 in binary
    -- [B2.one] 1 in binary
    -- Pad to same length: a=11, b=01, c=01
    let input := [[B2.one,B2.zero,B2.zero],[B2.one,B2.one,B2.one]]
    addition.eval input ≠ 0 := by
  simp [addition, DFA.eval, DFA.evalFrom]

/-- Automaton for equality: accepts (a, b) where a = b.

    This is a 2-track automaton that reads two binary numbers simultaneously
    and accepts if they are equal digit-by-digit.

    ### States
    - 0: Valid equal relation representation (initial state, accepting)
    - 1: Invalid representation (dead state)

    ### Transitions
    - From state 0: Reading [0,0] or [1,1] stays in state 0 (valid)
    - Everything else goes to state 1 (invalid)
-/
def equals : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero] => 0  -- 0 = 0, Equal bits
    | 0, [B2.one, B2.one] => 0    -- 1 = 1, Equal bits
    | _, _ => 1                   -- Different bits - reject
  start := 0
  accept := {x | x = 0}
}

/-- Automaton for less-than comparison: accepts (a, b) where a < b.

    This is a 2-track automaton that reads two binary numbers simultaneously
    and accepts if the first one is less than the second one.

    ### States
    - 0: Haven't seen difference yet (a = b so far)
    - 1: Seen a < b (accepting state)
    - 2: Dead state (a > b or invalid input)

    ### Transitions
    - From state 0: If a = b stay in this state.
      If a < b ([0,1]) is read, go to the accepting state 1.
      if a > b is read, go to the dead state 2.
    - From state 1: a > b will always hold here so any transition stays in 1.
-/
def less_than : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero] => 0  -- 0 = 0, Still equal
    | 0, [B2.one, B2.one] => 0    -- 1 = 1, Still equal
    | 0, [B2.zero, B2.one] => 1   -- 0 < 1, Difference found
    | 1, [B2.one, B2.one] => 1    -- Once a < b, stays true
    | 1, [B2.zero, B2.one] => 1   -- Once a < b, stays true
    | 1, [B2.one, B2.zero] => 1   -- Once a < b, stays true
    | 1, [B2.zero, B2.zero] => 1  -- Once a < b, stays true
    | _, _ => 2                   -- a > b or invalid
  start := 0
  accept := {x | x = 1}
}

/-- Automaton for greater-than comparison: accepts (a, b) where a > b.

    This is a 2-track automaton that reads two binary numbers simultaneously
    and accepts if the first one is greater than the second one.

    ### States
    - 0: Haven't seen difference yet (a = b so far)
    - 1: Seen a > b (accepting state)
    - 2: Dead state (a < b or invalid input)

    ### Transitions
    - From state 0: If a = b stay in this state.
      If a > b ([1,0]) is read, go to the accepting state 1.
      if a < b is read, go to the dead state 2.
    - From state 1: a > b will always hold here so any transition stays in 1.
-/
def greater_than : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero] => 0  -- 0 = 0, Still equal
    | 0, [B2.one, B2.one] => 0    -- 1 = 1, Still equal
    | 0, [B2.one, B2.zero] => 1   -- 1 > 0, Difference found
    | 1, [B2.one, B2.one] => 1    -- Once a > b, stays true
    | 1, [B2.zero, B2.one] => 1   -- Once a > b, stays true
    | 1, [B2.one, B2.zero] => 1   -- Once a > b, stays true
    | 1, [B2.zero, B2.zero] => 1  -- Once a > b, stays true
    | _, _ => 2                   -- a < b or invalid
  start := 0
  accept := {x | x = 1}
}

/-!
## Thue-Morse Sequence DFAO

The Thue-Morse sequence is a binary sequence obtained by starting with 0 and successively
appending the boolean complement of the sequence obtained thus far.

e.g. 0, 01, 0110, 01101001,...

This automaton computes the Thue-Morse value at position n given n in binary.
-/

/-- Automaton that computes the Thue-Morse sequence value.

    Reads a binary number (position n) and the state represents the Thue-Morse value.

    # States
    - 0: Thue-Morse value at position n is 0
    - 1: Thue-Morse value at position n is 1
    - 2: Dead state
-/
def thue_morse : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero] => 0
    | 0, [B2.one] => 1
    | 1, [B2.zero] => 1
    | 1, [B2.one] => 0
    | _, _ => 2
  start := 0
  accept := {0, 1}
}

/-!
## Extended DFA Construction Functions

These functions create DFA_extended structures that wrap DFAs with all necessary fields.
-/

/-- Creates a DFA that accepts exactly one specific word.

    ### Parameters
    - `word`: The target word to accept
    - `zero`: The "zero" symbol for padding

    ### States
    - 0 to word.length: States representing how much of the word has been matched
    - word.length: Accept only after reading the complete word
    - word.length + 1: Dead state for mismatches

    ### Transitions
    - From state 0: If [0] is read stay in this state, when [1] is read move to state 1
    - From state x > 0: If the input at index x of the accepted word is read, go to state x + 1,
      else go to the dead state. If x = word.length, any input goes to the dead state.
-/
def createEqualsDFA {T : Type} [DecidableEq T]
(word : List T) (zero : T) : DFA T Nat where
  step := fun state symbol =>
    -- If we're at position i and see the expected symbol, advance to i+1
    if state < word.length && word[state]? = some symbol then
      state + 1
    -- Allow leading zeros to stay at state 0
    else if state = 0 && symbol = zero then
      state
    -- Otherwise, go to dead state
    else
      word.length + 1
  start := 0
  accept := {word.length}

/-- Creates a complete extended DFA for word equality.

    ### Parameters
    - `word`: The target word to accept
    - `zero`: The "zero" symbol for padding
    - `vars`: The name of the input track
-/
def createExtendedEqualsDigitDFA (word : List (List B2)) (zero : List B2) (vars : List Char)
 : DFA_extended (List B2) Nat where
  automata := createEqualsDFA word zero
  states := Std.HashSet.emptyWithCapacity.insertMany (List.range (word.length + 2))
  states_accept := Std.HashSet.emptyWithCapacity.insertMany [word.length]
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero], [B2.one]]
  dead_state := some (word.length + 1)
  vars := vars

/-- Creates a complete extended DFA for variable equality.

    ### Parameters
    - `vars`: The name of the input track
-/
def createExtendedEqualsDFA (vars : List Char)
 : DFA_extended (List B2) Nat where
  automata := equals
  states := Std.HashSet.emptyWithCapacity.insertMany [0,1]
  states_accept := Std.HashSet.emptyWithCapacity.insertMany [0]
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero, B2.zero], [B2.one, B2.one]]
  dead_state := some 1
  vars := vars


/-- Creates a complete extended DFA for addition with all metadata.

    ### Parameters
    - `vars`: The name of the input tracks
-/
def createFullAdditionDFA (vars : List Char) : DFA_extended (List B2) Nat where
  automata := addition
  states :=  Std.HashSet.emptyWithCapacity.insertMany [0,1,2]
  states_accept := Std.HashSet.emptyWithCapacity.insertMany [0]
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero, B2.zero, B2.zero],
  [B2.one, B2.one, B2.zero],
  [B2.one, B2.zero, B2.one],
  [B2.one, B2.zero, B2.zero],
  [B2.one, B2.one, B2.one],
  [B2.zero, B2.one, B2.zero],
  [B2.zero, B2.zero, B2.one],
  [B2.zero, B2.one, B2.one]]
  dead_state := some 2
  vars := vars

/-- Creates a complete extended DFA for less-than comparison.

    ### Parameters
    - `vars`: The name of the input track
-/
def createFullLTDFA (vars : List Char) : DFA_extended (List B2) Nat where
  automata := less_than
  states := Std.HashSet.emptyWithCapacity.insertMany [0,1,2]
  states_accept := Std.HashSet.emptyWithCapacity.insertMany [1]
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero, B2.zero], [B2.one, B2.one], [B2.zero, B2.one],
  [B2.one, B2.zero]]
  dead_state := some 2
  vars := vars

/-- Creates a complete extended DFA for greater-than comparison.

    ### Parameters
    - `vars`: The name of the input track
-/
def createFullGTDFA (vars : List Char) : DFA_extended (List B2) Nat where
  automata := greater_than
  states := Std.HashSet.emptyWithCapacity.insertMany [0,1,2]
  states_accept := Std.HashSet.emptyWithCapacity.insertMany [1]
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero, B2.zero], [B2.one, B2.one], [B2.zero, B2.one],
  [B2.one, B2.zero]]
  dead_state := some 2
  vars := vars

/-- Creates a complete extended DFA for Thue-Morse sequence equality.

    ### Parameters
    - `values`: List of Thue-Morse values to accept (typically [0] or [1])
    - `vars`: The name of the input track
-/
def createThueMorseEqualsDFA (values : List Nat) (vars : List Char)
 : DFA_extended (List B2) Nat where
  automata := thue_morse
  states := Std.HashSet.emptyWithCapacity.insertMany [0,1,2]
  states_accept := Std.HashSet.emptyWithCapacity.insertMany values
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero], [B2.one]]
  dead_state := some 2
  vars := vars

/-!
## Automata Operations
-/

/-- Complement operation: creates a DFA that accepts the complement language.

    Takes a DFA and returns a new DFA that accepts exactly the strings
    the original DFA rejects.

    ### Algorithm
    - New accepting states = all states except original accepting states
    - Excludes the dead state from accepting states
    - Preserves the transition function and start state
-/
def complement
  (M1 : DFA_extended (List B2) (Nat)) : DFA_extended (List B2) (Nat) :=
  let new_accepting_states := M1.states.filter (fun x => !M1.states_accept.contains x)
  let new_accept := {p | p ∉ M1.automata.accept ∧ M1.states.contains p}
  let new_automata : DFA (List B2) (Nat) := {
    step := M1.automata.step,
    start := M1.automata.start,
    accept := new_accept
  }
  {
    states := M1.states,
    states_accept := new_accepting_states,
    alphabet := M1.alphabet,
    dead_state := none,
    vars := M1.vars,
    automata := new_automata
  }

/-!
## State Renaming Utilities

Functions to convert DFA states from arbitrary types to natural numbers.
This is useful for normalizing DFAs and enabling comparisons.
-/

/-- Assigns unique natural numbers to states in a DFA.

    ### Parameters
    - `fullList`: All states in the DFA
    - `subList`: Accepting states

    ### Returns
    A triple: (numbered states, numbered accepting states, state→number mapping)
-/
def assignNumbers {State : Type} [DecidableEq State] [Hashable State]
(fullList : List State) (subList : List State) : (List ℕ × List ℕ × Std.HashMap State ℕ) :=
  -- Remove duplicates while preserving order
  let uniqueElements := fullList.foldl (fun acc elem =>
    if elem ∈ acc then acc else acc ++ [elem]) []

  -- Create mapping from states to indices
  let mapping := Std.HashMap.ofList uniqueElements.zipIdx

  -- Helper to look up state numbers
  let lookupNumber (elem : State) : ℕ :=
    mapping[elem]!

  (fullList.map lookupNumber, subList.map lookupNumber, mapping)

/-- Converts a DFA with arbitrary state type to one with Nat states.

    This function renames all states to natural numbers while preserving
    the automaton's structure and behavior.

    ### Algorithm
    1. Assign numbers to all states using assignNumbers
    2. Build transition table with new state numbers
    3. Create new DFA with Nat states
    4. Preserve all metadata (alphabet, variables, etc.)
-/
def change_states_names
(M1 : DFA_extended (List B2) (List Nat))
 : DFA_extended (List B2) Nat :=
  let m1_states_list := M1.states.toList
  let m1_accept_list := M1.states_accept.toList
  let m1_alphabet_list := M1.alphabet.toList
  let mappings := (assignNumbers m1_states_list m1_accept_list)
  let new_states :=  mappings.fst
  let new_states_accept :=  mappings.snd.fst

  -- Build transition table
  let transitions := m1_states_list.flatMap (fun x =>
                      m1_alphabet_list.map (fun z => ((mappings.snd.snd[(x)]!, z),
                                                mappings.snd.snd[(M1.automata.step (x) z)]! )))

  -- Convert dead state if it exists
  let new_dead_state := match M1.dead_state with
                |none => none
                |some n => some mappings.snd.snd[n]!

  -- Build new automaton with Nat states using the transition table
  let automata := {
    step := fun st input =>
      let tr := transitions.filter (fun ((x,y),_) => st = x ∧ input = y)
      match tr.head? with
      | some ((_,_),z) => z
      | _ => match new_dead_state with
            | some w => w
            | _ => new_states.length+1  -- Default dead state
    start :=  mappings.snd.snd[M1.automata.start]!
    accept := {p | new_states_accept.contains p}
  }
  {
    states := Std.HashSet.emptyWithCapacity.insertMany new_states,
    states_accept := Std.HashSet.emptyWithCapacity.insertMany new_states_accept,
    alphabet := M1.alphabet,
    dead_state := new_dead_state,
    vars := M1.vars,
    automata := automata
  }

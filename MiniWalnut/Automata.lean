import Mathlib.Computability.DFA

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
structure DFA_extended (T : Type) (Q : Type) [Hashable Q] [BEq Q] [Hashable T] [BEq T] where
  states : Std.HashSet Q
  states_accept : Std.HashSet Q
  alphabet : Std.HashSet T
  dead_state : Option Q
  vars : List Char
  automata : DFA T Q

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
  accept := {x | x = 0}
}

-- 5 = 3 + 2 is accepted
example :
    let input := [[B2.one, B2.zero, B2.zero], [B2.zero, B2.one, B2.one], [B2.one, B2.one, B2.zero]]
    input ∈ addition.accepts := by
  rfl

-- 3 ≠ 1 + 1 is rejected
example :
    let input := [[B2.one,B2.zero,B2.zero],[B2.one,B2.one,B2.one]]
    input ∉ addition.accepts := by
  simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, addition]

/-- Automaton for equality: accepts (a, b) where a = b.

    ### States
    - 0: Valid equal relation representation (initial state, accepting)
    - 1: Invalid representation (dead state)

    ### Transitions
    - From state 0: Reading [0,0] or [1,1] stays in state 0 (valid)
    - Everything else goes to state 1 (invalid)
-/
def equals : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero] => 0
    | 0, [B2.one, B2.one] => 0
    | _, _ => 1
  start := 0
  accept := {x | x = 0}
}

-- 3 = 3 is accepted
example :
    let input := [[B2.one, B2.one], [B2.one, B2.one]]
    input ∈ equals.accepts := by
  rfl

-- 2 = 2 is accepted
example :
    let input := [[B2.one, B2.one], [B2.zero, B2.zero]]
    input ∈ equals.accepts := by
  rfl

-- 3 ≠ 2 is rejected
example :
    let input := [[B2.one, B2.one], [B2.one, B2.zero]]
    input ∉ equals.accepts := by
  simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, equals]

-- 1 ≠ 0 is rejected
example :
    let input := [[B2.one, B2.zero]]
    input ∉ equals.accepts := by
  simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, equals]

/-- Automaton for less-than comparison: accepts (a, b) where a < b.

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
    | 0, [B2.zero, B2.zero] => 0
    | 0, [B2.one, B2.one] => 0
    | 0, [B2.zero, B2.one] => 1
    | 1, [B2.one, B2.one] => 1
    | 1, [B2.zero, B2.one] => 1
    | 1, [B2.one, B2.zero] => 1
    | 1, [B2.zero, B2.zero] => 1
    | _, _ => 2
  start := 0
  accept := {x | x = 1}
}

-- 1 < 3 is accepted
example :
    let input := [[B2.zero, B2.one], [B2.one, B2.one]]
    input ∈ less_than.accepts := by
  rfl

-- 0 < 1 is accepted
example :
    let input := [[B2.zero, B2.one]]
    input ∈ less_than.accepts := by
  rfl

-- 3 ≮ 2 is rejected (3 > 2)
example :
    let input := [[B2.one, B2.one], [B2.one, B2.zero]]
    input ∉ less_than.accepts := by
  simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, less_than]

-- 2 ≮ 2 is rejected (equal)
example :
    let input := [[B2.one, B2.one], [B2.zero, B2.zero]]
    input ∉ less_than.accepts := by
  simp [DFA.mem_accepts, DFA.eval, DFA.evalFrom, less_than]

/-- Automaton for binary subtraction: accepts (a, b, c) where a = b - c.

    ### States
    - 0: No carry (initial and accepting state)
    - 1: Has carry from previous position
    - 2: Dead state (invalid input)

    ### Transitions
    - From state 0: If a = b - c is valid ([0,0,0],[1,1,0],[0,1,1]) stay in this state.
      If [0,1,0] is read, a carry is generated and it goes to state 1.
    - From state 1: If a = b - c is an operation with a carry ([1,1,1],[0,0,1],[0,1,0])
      If [0,1,1] is read, the carry is consumed and it goes back to state 0.
    - Anything else is invalid and goes to the dead state, 2.
-/
def subtraction : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero, B2.zero] => 0
    | 0, [B2.one, B2.one, B2.zero] => 0
    | 0, [B2.zero, B2.one, B2.one] => 0
    | 0, [B2.zero, B2.one, B2.zero] => 1
    | 1, [B2.one, B2.one, B2.one] => 1
    | 1, [B2.one, B2.zero, B2.zero] => 1
    | 1, [B2.zero, B2.zero, B2.one] => 1
    | 1, [B2.one, B2.zero, B2.one] => 0
    | _, _ => 2
  start := 0
  accept := {x | x = 0}
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

    ### States
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
def build_equals_digit_DFA' {T : Type} [DecidableEq T]
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
def build_equals_digit_DFA (word : List (List B2)) (zero : List B2) (var : Char)
 : DFA_extended (List B2) Nat where
  automata := build_equals_digit_DFA' word zero
  states := Std.HashSet.emptyWithCapacity.insertMany (List.range (word.length + 2))
  states_accept := Std.HashSet.emptyWithCapacity.insertMany [word.length]
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero], [B2.one]]
  dead_state := some (word.length + 1)
  vars := [var]

/-- Creates a complete extended DFA for variable equality.

    ### Parameters
    - `vars`: The name of the input track
-/
def build_equals_DFA (var_1 : Char) (var_2 : Char)
 : DFA_extended (List B2) Nat where
  automata := equals
  states := Std.HashSet.emptyWithCapacity.insertMany [0,1]
  states_accept := Std.HashSet.emptyWithCapacity.insertMany [0]
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero, B2.zero], [B2.one, B2.one]]
  dead_state := some 1
  vars := [var_1, var_2]


/-- Creates a complete extended DFA for addition with all metadata.

    ### Parameters
    - `vars`: The name of the input tracks
-/
def build_addition_DFA (var_1 : Char) (var_2 : Char) (var_3 : Char) : DFA_extended (List B2) Nat where
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
  vars := [var_1, var_2, var_3]

/-- Creates a complete extended DFA for less-than comparison.

    ### Parameters
    - `vars`: The name of the input track
-/
def build_less_than_DFA (var_1 : Char) (var_2 : Char) : DFA_extended (List B2) Nat where
  automata := less_than
  states := Std.HashSet.emptyWithCapacity.insertMany [0,1,2]
  states_accept := Std.HashSet.emptyWithCapacity.insertMany [1]
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero, B2.zero], [B2.one, B2.one], [B2.zero, B2.one],
  [B2.one, B2.zero]]
  dead_state := some 2
  vars := [var_1, var_2]

/-- Creates a complete extended DFA for subtraction with all metadata.

    ### Parameters
    - `vars`: The name of the input tracks
-/
def build_subtraction_DFA (var_1 : Char) (var_2 : Char) (var_3 : Char) : DFA_extended (List B2) Nat where
  automata := subtraction
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
  vars := [var_1, var_2, var_3]

/-- Creates a complete extended DFA for Thue-Morse sequence equality.

    ### Parameters
    - `values`: List of Thue-Morse values to accept (0 or 1)
    - `vars`: The name of the input track
-/
def build_TH_equals_digit_DFA (values : List Nat) (var : Char)
 : DFA_extended (List B2) Nat where
  automata := thue_morse
  states := Std.HashSet.emptyWithCapacity.insertMany [0,1,2]
  states_accept := Std.HashSet.emptyWithCapacity.insertMany ([0,1,2].filter (fun x => values.contains x) )
  alphabet := Std.HashSet.emptyWithCapacity.insertMany [[B2.zero], [B2.one]]
  dead_state := some 2
  vars := [var]

/-!
## Automata Operations
-/

/-- Complement operation: creates a DFA that accepts the complement language. -/
def complement
  (M : DFA_extended (List B2) (Nat)) : DFA_extended (List B2) (Nat) :=
  let new_accepting_states := M.states.filter (fun x => !M.states_accept.contains x)
  let new_accept := {p | p ∉ M.automata.accept ∧ M.states.contains p}
  let new_automata : DFA (List B2) (Nat) := {
    step := M.automata.step,
    start := M.automata.start,
    accept := new_accept
  }
  {
    states := M.states,
    states_accept := new_accepting_states,
    alphabet := M.alphabet,
    dead_state := none,
    vars := M.vars,
    automata := new_automata
  }

/-- Assigns unique natural numbers to states in a DFA.

    ### Returns
    A triple: (numbered states, numbered accepting states, state→number mapping)
-/
def assign_numbers
(all_states : List (List Nat)) (accepting_states : List (List Nat)) : (List ℕ × List ℕ × Std.HashMap (List Nat) ℕ) :=
  -- Pairs each state with its index
  let mapping := Std.HashMap.ofList all_states.zipIdx
  -- Returns appropriate index
  let lookupNumber (elem : (List Nat)) : ℕ :=
    mapping[elem]!
  (all_states.map lookupNumber, accepting_states.map lookupNumber, mapping)

def swapHashMap {α β} [BEq α] [Hashable α] [BEq β] [Hashable β]
    (m : Std.HashMap α β) : Std.HashMap β α :=
  m.fold (init := Std.HashMap.emptyWithCapacity) fun acc key value =>
    acc.insert value key

/-- Converts a DFA with arbitrary state type to one with Nat states.

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
  let mappings := (assign_numbers m1_states_list m1_accept_list)
  let new_states :=  mappings.fst
  let new_states_accept :=  mappings.snd.fst
  let mapp := mappings.snd.snd
  let switched := swapHashMap mapp
  -- Build transition table
  --let transitions := m1_states_list.flatMap (fun x =>
  --                    m1_alphabet_list.map (fun z => ((mappings.snd.snd[(x)]!, z),
  --                                              mappings.snd.snd[(M1.automata.step (x) z)]! )))
  -- Convert dead state if it exists
  let new_dead_state := match M1.dead_state with
                |none => none
                |some n => some mappings.snd.snd[n]!
  -- Build new automaton with Nat states using the transition table
  let automata := {
    step := fun st input => mapp[(M1.automata.step (switched[st]!) input)]!
      /-let tr := transitions.filter (fun ((x,y),_) => st = x ∧ input = y)
      match tr.head? with
      | some ((_,_),z) => z
      | _ => match new_dead_state with
            | some w => w
            | _ => new_states.length+1  -- Default dead state-/
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

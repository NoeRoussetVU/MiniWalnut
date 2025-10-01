import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

import MiniWalnut.Automata

/-!
# Quantification Operations for DFAs

This file implements existential (∃) and universal (∀) quantification over automata,
which is fundamental for building first-order formulas in automata-based decision procedures.

## Theory

Given a DFA M over variables [x₁, x₂, ..., xₙ] and a variable xᵢ:
- **∃xᵢ. M**: Creates a DFA over [x₁, ..., xᵢ₋₁, xᵢ₊₁, ..., xₙ] that accepts when
  there exists some value for xᵢ that makes M accept
- **∀xᵢ. M**: Creates a DFA that accepts when M accepts for all values of xᵢ

## Implementation Strategy

1. **Remove quantified variable**: Remove xᵢ's track from the alphabet
2. **Non-determinization**: For each input on remaining variables, consider all possible
   values for xᵢ - this creates an NFA
3. **Determinization**: Convert the NFA back to DFA using powerset construction
4. **Starting states**: Include states reachable via 0* prefix (for leading zeros)
5. **For ∀**: Use De Morgan's law: ∀x.φ ≡ ¬∃x.¬φ

## Main Components

- **Reachability Analysis**: Finding states reachable with zero prefixes
- **Determinization with Memoization**: Converting NFA to DFA efficiently
- **Quantification Operations**: ∃ and ∀ operators
-/

/-!
## Quantification Operator Type
-/

/-- Quantification operators for automata.

    These correspond to first-order logic quantifiers applied to automata languages.
-/
inductive quant_op where
  | exists   -- ∃x: accepts if there exists a value for x that makes M accept
  | for_all  -- ∀x: accepts if M accepts for all values of x

/-!
## Reachability Analysis

These functions find all states reachable from starting states by reading zero prefixes.
This is important because in MSD (most significant digit first) representation,
numbers can have leading zeros (e.g., 0011 = 11 in binary).
-/

/-- Processes a single input symbol from a set of current states.

    # Purpose
    Given multiple current states in an NFA, apply the transition function
    with a specific symbol and collect all resulting states.

    # Parameters
    - `f`: NFA transition function (returns list of possible next states)
    - `currentStates`: Current set of states
    - `symbol`: Input symbol to process

    # Returns
    All states reachable in one step from any current state via the given symbol.
-/
def processSymbol {T Q : Type} [DecidableEq Q]
(f : Q → T → List Q) (currentStates : List Q) (symbol : T) : List Q :=
  let nextStates := currentStates.foldl (fun acc state =>
    acc ++ f state symbol
  ) []
  nextStates.eraseDups  -- Remove duplicates

/-- Finds all states reachable from starting states with exactly n zero symbols.

    # Purpose
    In MSD representation, we need to handle leading zeros. This function
    computes which states are reachable by reading n consecutive zeros.

    # Algorithm
    Iteratively apply the transition function with 'zero' symbol n times,
    starting from the initial states.

    # Example
    If start = [0] and reading "00" leads to states [0, 1], then
    reachableWithNZeros [0] f 2 zero = [0, 1]
-/
def reachableWithNZeros {T Q : Type} [DecidableEq T] [DecidableEq Q]
(start_states : List Q) (f : Q → T → List Q) (n : Nat) (zero : T) : List Q :=
  if n = 0 then
    start_states
  else
    let rec helper (currentStates : List Q) (remaining : Nat) : List Q :=
      if remaining = 0 then
        currentStates
      else
        let nextStates := processSymbol f currentStates zero
        helper nextStates (remaining - 1)
    helper start_states n

/-- Finds all states reachable with one or more consecutive zeros.

    # Purpose
    Computes the closure of starting states under reading 0* (one or more zeros).
    This is used to determine valid starting states for the quantified automaton.

    # Parameters
    - `start_states`: Initial states
    - `f`: Transition function
    - `zero`: The zero symbol
    - `maxZeros`: Maximum number of zeros to consider (typically = number of states)

    # Returns
    Union of all states reachable with 1, 2, ..., maxZeros consecutive zeros.

    # Why This Matters
    When quantifying over a variable, the resulting automaton must handle
    all possible leading zeros in the representation of that variable.
-/
def reachableWithOneOrMoreZeros {T Q : Type} [DecidableEq T] [DecidableEq Q]
(start_states : List Q) (f : Q → T → List Q) (zero : T) (maxZeros : Nat) : List Q :=
  let allReachableStates := (List.range maxZeros).foldl (fun acc n =>
    if n = 0 then acc
    else acc ++ reachableWithNZeros start_states f n zero
  ) []
  allReachableStates

/-!
## NFA Determinization

After removing a variable, we get an NFA (non-deterministic finite automaton).
We use powerset construction to convert it to a DFA, with memoization for efficiency.
-/

/-- State for the determinization algorithm with memoization.

    # Fields
    - `visited`: Set of states already explored (avoids reprocessing)
    - `memo`: Cache of computed transitions for each state
-/
structure DeterminizeState (Input1 : Type) [BEq Input1] [Hashable Input1] where
  visited : Std.HashSet (List (Nat))
  memo : Std.HashMap (List (Nat)) (List (((List Nat) × Input1) × (List Nat)))

/-- Determinization using depth-first search with memoization.

    # Algorithm (Powerset Construction)
    1. Start with a set of NFA states (represented as List Nat)
    2. For each input symbol, compute all possible next states
    3. Each set of NFA states becomes a single DFA state
    4. Recursively process newly discovered state sets
    5. Use memoization to avoid recomputing transitions

    # Parameters
    - `transition_function`: NFA transition function (state → input → list of states)
    - `alphabet`: Input alphabet
    - `current_state`: Current set of NFA states (forms one DFA state)
    - `num_possible_states`: Bound on recursion depth (prevents infinite loops)
    - `state`: Memoization state (visited sets and cached transitions)

    # Returns
    Pair of (all transitions discovered, updated memoization state)

    # Example
    If NFA states {1, 2} on input 'a' can go to states {2, 3}, then
    the DFA has transition: [1, 2] --'a'--> [2, 3]
-/
def determinizeWithMemo {Input1 : Type} [DecidableEq Input1][BEq Input1] [Hashable Input1]
  (transition_function : (Nat) → Input1 → (List Nat))
  (alphabet : List Input1)
  (current_state : List Nat)
  (num_possible_states : Nat)
  (state : DeterminizeState Input1) :
  List (((List Nat) × Input1) × (List Nat)) × DeterminizeState Input1 :=

  -- Base case: reached recursion limit
  if num_possible_states = 0 then ([], state)
  else
    -- Already processed this state set
    if state.visited.contains current_state then
      ([], state)
    else Id.run do
      -- Mark this state set as visited
      let new_visited := state.visited.insert current_state
      let mut new_state := { state with visited := new_visited }

      -- Compute transitions from current_state for all symbols
      -- For each symbol, collect all states reachable from any state in current_state
      let current_transitions := alphabet.map fun x =>
        let next_states := (current_state.map (fun y =>
          transition_function y x)).flatten.mergeSort.dedup
        ((current_state, x), next_states)

      -- Find all newly reachable state sets
      let reachable_states := (current_transitions.map (·.2)).dedup
      let mut all_transitions := current_transitions

      -- Recursively process each reachable state set
      for next_state in reachable_states do
        if !new_state.visited.contains next_state then
          let (sub_transitions, updated_state) :=
          determinizeWithMemo transition_function alphabet next_state (num_possible_states-1) new_state
          all_transitions := all_transitions ++ sub_transitions
          new_state := updated_state

      -- Cache the result
      let final_state := { new_state with memo := new_state.memo.insert current_state all_transitions }
      (all_transitions, final_state)

/-- Public interface for determinization with memoization.

    Initializes the memoization state and runs the determinization algorithm.

    # Parameters
    - `transition_function`: NFA transition function
    - `alphabet`: Input alphabet
    - `initial_state`: Starting set of NFA states
    - `max_states`: Upper bound on number of states (usually 2^n for powerset)

    # Returns
    List of all transitions in the determinized DFA, where each transition
    is ((source_state_set, input_symbol), target_state_set)
-/
def determinizeMemo {Input1 : Type} [DecidableEq Input1] [BEq Input1] [Hashable Input1]
  (transition_function : Nat → Input1 → (List Nat)) (alphabet : List Input1)
  (initial_state : List Nat) (max_states : Nat) :
  List (((List Nat) × Input1) × (List Nat)) :=
  let initial_state_obj := ⟨Std.HashSet.emptyWithCapacity, Std.HashMap.emptyWithCapacity⟩
  (determinizeWithMemo transition_function alphabet initial_state max_states initial_state_obj).fst

/-!
## Quantification Implementation
-/

/-- Existential quantification over a variable (internal version with List Nat states).

    # Algorithm
    1. **Remove variable**: Remove the quantified variable's track from alphabet
       - Find index of variable in vars list
       - Remove that index from each alphabet symbol

    2. **Create NFA**: Build transition function that considers all possible values
       for the quantified variable
       - For input on remaining variables, try all values for quantified variable
       - Collect all reachable states

    3. **Handle leading zeros**: Find all states reachable via 0* prefix

    4. **Determinize**: Convert NFA to DFA using powerset construction

    5. **Accepting states**: A state set is accepting if it contains any original accepting state
       (existential semantics: ∃ value that leads to acceptance)

    # Example
    Given DFA for "x + y = z" over variables [x, y, z]:
    ∃y. (x + y = z) creates DFA over [x, z] that accepts when there exists y such that x + y = z

    # Parameters
    - `M1`: Original DFA
    - `zero`: Zero symbol for handling leading zeros
    - `var`: Variable to quantify over
    - `alphabet_vars`: All possible values for the quantified variable
-/
def quant' {Input : Type} [DecidableEq Input] [DecidableEq Input] [BEq Input] [Hashable Input]
  (M1 : DFA_extended (List Input) (Nat)) (zero : List Input) (var : Char)
  (alphabet_vars : List (List Input)) : DFA_extended (List Input) (List Nat) :=
  -- Step 1: Find index of quantified variable and create new alphabet
  let idx := M1.vars.findIdx (· = var)
  let new_alphabet := (M1.alphabet.map (fun x => x.eraseIdx idx)).dedup

  -- Step 2: Create NFA transition function
  -- Given a state and input (without quantified variable), try all possible values
  -- for the quantified variable and collect all reachable states
  let step := fun st input =>
    (alphabet_vars.flatten.map (fun x =>
      input.insertIdx idx x)).map (fun y => M1.automata.step st y)

  -- Step 3: Compute bound on number of states in powerset (2^n)
  let num_possible_states := 2^(M1.states.length)

  -- Step 4: Find starting states (including those reachable via 0*)
  let start_states := (reachableWithOneOrMoreZeros [M1.automata.start] step zero (M1.states.length)).dedup.mergeSort

  -- Step 5: Determinize the NFA
  let new_transitions := determinizeMemo step new_alphabet start_states num_possible_states

  -- Step 6: Extract all states from transitions
  let new_states' := (new_transitions.map (fun ((x,_),_) => x))
     ++ (new_transitions.map (fun ((_,_),z) => z))
  let new_states := new_states'.dedup

  -- Step 7: Determine accepting states (existential: any original accepting state in the set)
  let states_acc := new_states.filter (fun x => M1.states_accept.any (fun y => x.contains y))

  -- Step 8: Build the resulting DFA
  let dfa_list : DFA (List Input) (List Nat) :={
    step := fun st input =>
      let transt := (new_transitions.filter (fun ((x,y),_) => st = x ∧ input = y))
      match transt.head? with
      | some ((x,y),z) => z
      | _ => [new_states.length + 1]  -- Dead state if no transition found
    start := start_states
    accept := {p | states_acc.contains p}
  }
  {states := new_states,
   states_accept := states_acc,
   alphabet := new_alphabet,
   dead_state := none,
   vars := M1.vars.eraseIdx idx,
   automata := dfa_list}

/-- Quantification operation (public interface with Nat states).

    Implements both existential (∃) and universal (∀) quantification.

    # Semantics
    - **∃x. M**: Accepts input if there exists a value for x making M accept
    - **∀x. M**: Accepts input if M accepts for all values of x

    # Implementation
    - ∃x. M: Directly apply existential quantification
    - ∀x. M: Use De Morgan's law: ∀x.φ ≡ ¬∃x.¬φ
      1. Complement M to get ¬M
      2. Apply existential quantification: ∃x.¬M
      3. Complement result to get ¬∃x.¬M ≡ ∀x.M

    # Parameters
    - `M1`: DFA to quantify over
    - `zero`: Zero symbol for leading zeros
    - `var`: Variable to quantify
    - `op_type`: Quantifier type (exists or for_all)
    - `alphabet_vars`: Possible values for quantified variable

    # Returns
    DFA_extended with Nat states representing the quantified formula

    # Example Usage
    ```lean
    -- ∃y. (x + y = z) -- "z is reachable from x by addition"
    let exists_y := quant addition_dfa zero 'y' quant_op.exists alphabet_values

    -- ∀y. (x < y) -- "x is less than all y" (impossible unless...)
    let forall_y := quant less_than_dfa zero 'y' quant_op.for_all alphabet_values
    ```
-/
def quant {Input : Type} [DecidableEq Input] [DecidableEq Input] [BEq Input] [Hashable Input]
 [Inhabited Input]
  (M1 : DFA_extended (List Input) (Nat)) (zero : List Input) (var : Char) (op_type : quant_op)
  (alphabet_vars : List (List Input)) :
  DFA_extended (List Input) (Nat) :=
  match op_type with
  | quant_op.exists =>
      change_states_names (quant' M1 zero var alphabet_vars)
  | quant_op.for_all =>
      -- ∀x.φ ≡ ¬∃x.¬φ (De Morgan's law for quantifiers)
      complement (change_states_names ((quant' (complement M1) zero var alphabet_vars)))

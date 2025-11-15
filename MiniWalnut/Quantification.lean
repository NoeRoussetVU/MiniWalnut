import Mathlib.Topology.Basic
import Mathlib.Computability.DFA

import MiniWalnut.Automata

/-!
# Quantification Operations for DFAs

This file implements existential (∃) and universal (∀) quantification over automata,
which is fundamental for building first-order formulas in automata-based decision procedures.

## Main Components

- **Quantification Operator Type**: Custom type implementing operators ∃ and ∀
- **Reachability Analysis**: Finding states reachable with leading zeros
- **Determinization**: Converting NFA to DFA
- **Quantification Operations**: ∃ and ∀ operators over an automaton

## Theory

Given a DFA M over variables [x₁, x₂, ..., xₙ] and a variable xᵢ:
- **∃xᵢ. M**: Creates a DFA over [x₁, ..., xᵢ₋₁, xᵢ₊₁, ..., xₙ] that accepts when
  there exists some value for xᵢ that makes M accept
- **∀xᵢ. M**: Creates a DFA that accepts when M accepts for all values of xᵢ

## Implementation Strategy

1. **Remove Quantified Variable**: Remove xᵢ's track from the alphabet
2. **Non-Determinization**: For each input on remaining variables, consider all possible
   values for xᵢ, this creates an NFA
3. **Find All Initial States**: Find all states reachable with leading zeros from the initial state
3. **Determinization**: Convert the NFA back to DFA
4. **For ∀**: Use De Morgan's law: ∀x.φ ≡ ¬∃x.¬φ
-/

/-!
## Quantification Operator Type
-/

/-- Quantification operators for automata. -/
inductive quant_op where
  | exists
  | for_all

/-!
## Reachability Analysis

These functions find all states reachable from starting states by reading zero prefixes.
When removing a variable track from a DFA, transitions for 0 might be created.
In MSD (most significant digit first) representation, numbers can have leading zeros.
-/

/-- Return all states reachable from `currentStates` using `symbol` and `f`-/
def processSymbol {T Q : Type} [DecidableEq Q]
(f : Q → T → List Q) (currentStates : List Q) (symbol : T) : List Q :=
  let nextStates := currentStates.foldl (fun acc state =>
    acc ++ f state symbol
  ) []
  nextStates.dedup

/-- Finds all states reachable from `start_states` within `n` zeros. -/
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

/-- Finds all states reachable from the initial state with one or more consecutive zeros.

    ### Parameters
    - `start_states`: Initial state
    - `f`: Transition function
    - `zero`: The zero symbol
    - `max_zeros`: Maximum number of zeros to consider (typically = number of states)
-/
def reachableWithOneOrMoreZeros {T Q : Type} [DecidableEq T] [DecidableEq Q]
(start_states : List Q) (f : Q → T → List Q) (zero : T) (max_zeros : Nat) : List Q :=
  let allReachableStates := (List.range max_zeros).foldl (fun acc n =>
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

    ### Fields
    - `visited`: Set of states already explored (avoids reprocessing)
    - `memo`: Cache of computed transitions for each state
-/
structure DeterminizeState (Input1 : Type) [BEq Input1] [Hashable Input1] where
  visited : Std.HashSet (List (Nat))
  memo : Std.HashMap (List (Nat)) (List (((List Nat) × Input1) × (List Nat)))

/-- Determinization using depth-first search with memoization.

    ### Algorithm (Powerset Construction)
    1. Start with a set of NFA states (represented as List Nat)
    2. For each input symbol, compute all possible next states
    3. Each set of NFA states becomes a single DFA state
    4. Recursively process newly discovered state sets
    5. Use memoization to avoid recomputing transitions

    ### Parameters
    - `transition_function`: NFA transition function (state → input → list of states)
    - `alphabet`: Input alphabet
    - `current_state`: Current set of NFA states (forms one DFA state)
    - `num_possible_states`: Bound on recursion depth (prevents infinite loops)
    - `state`: Memoization state (visited sets and cached transitions)

    ### Returns
    Pair of (all transitions discovered, updated memoization state)
-/
def determinizeWithMemo {Input1 : Type} [DecidableEq Input1] [BEq Input1] [Hashable Input1]
  (transition_function : (Nat) → Input1 → (List Nat)) (alphabet : List Input1)
  (current_state : List Nat) (num_possible_states : Nat) (state : DeterminizeState Input1)
   : List (((List Nat) × Input1) × (List Nat)) × DeterminizeState Input1 :=

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
  (initial_state : List Nat) (max_states : Nat) : List (((List Nat) × Input1) × (List Nat)) :=
  let initial_state_obj := ⟨Std.HashSet.emptyWithCapacity, Std.HashMap.emptyWithCapacity⟩
  (determinizeWithMemo transition_function alphabet initial_state max_states initial_state_obj).fst

def allBinaryCombinations_qt : Nat → List (List B2)
  | 0 => [[]]
  | n + 1 =>
    let smaller := allBinaryCombinations_qt n
    smaller.flatMap (fun combo => [B2.zero :: combo, B2.one :: combo])

/-!
## Quantification Implementation
-/

/-- Existential quantification over a variable.

    ### Parameters
    - `M`: Original DFA
    - `zero`: Zero symbol for handling leading zeros
    - `var`: Variable to quantify over
    - `alphabet_vars`: All possible values for the quantified variable

    ### Algorithm
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
       (Exists a value that leads to acceptance)
-/
def quant'
  (M : DFA_extended (List B2) (Nat)) (zero : List B2) (var : Char)
  (alphabet_vars : List (List B2)) : DFA_extended (List B2) (List Nat) :=
  let m1_states_list := M.states.toList
  let m1_accept_list := M.states_accept.toList
  let m1_alphabet_list := M.alphabet.toList
  -- Step 1: Find index of quantified variable and create new alphabet
  let idx := M.vars.findIdx (· = var)
  let new_alphabet := allBinaryCombinations_qt (M.vars.length - 1)
  -- Step 2: Create NFA transition function
  -- Given a state and input (without quantified variable), try all possible values
  -- for the quantified variable and collect all reachable states
  let step := fun st input =>
    (alphabet_vars.flatten.map (fun x =>
      input.insertIdx idx x)).map (fun y => M.automata.step st y)
  -- Step 3: Compute bound on possible number of states in powerset (2^n)
  let num_possible_states := 2^(m1_states_list.length)
  -- Step 4: Find all initial states (those reachable via 0*)
  let start_states := (reachableWithOneOrMoreZeros [M.automata.start] step zero (m1_states_list.length)).dedup.mergeSort
  -- Step 5: Determinize the NFA
  let new_transitions := determinizeMemo step new_alphabet start_states num_possible_states
  -- Step 6: Extract all states from transitions
  let new_states' := (new_transitions.map (fun ((x,_),_) => x))
     ++ (new_transitions.map (fun ((_,_),z) => z))
  let new_states := Std.HashSet.emptyWithCapacity.insertMany new_states'
  -- Step 7: Determine accepting states (any original accepting state in the set)
  let states_acc := new_states.filter (fun x => M.states_accept.any (fun y => x.contains y))
  -- Step 8: Build the resulting DFA
  let dfa_list : DFA (List B2) (List Nat) :={
    step := fun st input =>
      let transt := (new_transitions.filter (fun ((x,y),_) => st = x ∧ input = y))
      match transt.head? with
      | some ((x,y),z) => z
      | _ => [new_states'.length + 1]  -- Dead state if no transition found
    start := start_states
    accept := {p | states_acc.contains p}
  }
  {states := new_states,
   states_accept := states_acc,
   alphabet := Std.HashSet.emptyWithCapacity.insertMany new_alphabet,
   dead_state := none,
   vars := M.vars.eraseIdx idx,
   automata := dfa_list}

/-- Quantification operation (public interface).

    Implements both existential (∃) and universal (∀) quantification.

    - **∃x. M**: Accepts input if there exists a value for x making M accept
    - **∀x. M**: Accepts input if M accepts for all values of x

    ### Parameters
    - `M1`: DFA to quantify over
    - `zero`: Zero symbol for leading zeros
    - `var`: Variable to quantify
    - `op_type`: Quantifier type (exists or for_all)
    - `alphabet_vars`: Possible values for quantified variable

    ### Returns
    DFA_extended with Nat states representing the quantified formula

-/
def quant
  (M : DFA_extended (List B2) (Nat)) (zero : List B2) (var : Char) (op_type : quant_op)
  (alphabet_vars : List (List B2)) : DFA_extended (List B2) (Nat) :=
  match op_type with
  | quant_op.exists =>
      change_states_names (quant' M zero var alphabet_vars)
  | quant_op.for_all =>
      complement (change_states_names ((quant' (complement M) zero var alphabet_vars)))

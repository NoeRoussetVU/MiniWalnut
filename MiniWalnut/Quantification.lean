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
def process_symbol {Input : Type}
(f : Nat → Input → List Nat) (current_states : List Nat) (symbol : Input) (visited : List Nat) : List Nat :=
  let next_states := current_states.foldl (fun acc state =>
    acc ++ f state symbol
  ) []
  (next_states.filter (fun x => !visited.contains x)).dedup

/-- Finds all states reachable from the initial state with one or more consecutive zeros.

    ### Parameters
    - `transition_function`: Transition function returning a list of all reachable states for a
      state and a symbol
    - `zero`: The zero symbol
    - `current_states`: List of current initial states to visit
    - `num_possible_states`: Maximum number of possible initial states
    - `states`: Already visited states
-/
def find_initial_states {Input : Type}
  (transition_function : (Nat) → Input → (List Nat)) (zero : Input)
  (current_states : List Nat) (num_possible_states : Nat) (states : List Nat)
   : List Nat :=
  -- Base case: reached recursion limit
  if num_possible_states = 0 then states
  else
    -- Mark current states as visited
    let visited_states := states ++ current_states
    -- Find all newly reachable state sets
    let reachable_states := process_symbol transition_function current_states zero visited_states
    -- Recursion on newly found states
    find_initial_states transition_function zero reachable_states (num_possible_states-1) visited_states

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
structure determinize_state (Input : Type) where
  visited : Std.HashSet (List (Nat))
  transitions : List (((List Nat) × Input) × (List Nat))

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
def determinize_with_memo {Input : Type} [DecidableEq Input]
  (transition_function : (Nat) → Input → (List Nat)) (alphabet : List Input)
  (current_state : List Nat) (num_possible_states : Nat) (state : determinize_state Input)
   : determinize_state Input :=
  -- Base case: reached recursion limit
  if num_possible_states = 0 then state
  else
    -- Already processed this state set
    if state.visited.contains current_state then state
    else Id.run do
      -- Mark this state set as visited
      let new_visited := state.visited.insert current_state
      -- Add current reachable states and transitions
      let mut new_state := { state with visited := new_visited }
      let mut next_states : List (List ℕ) := []
      let mut current_transitions : List ((List ℕ × Input) × List ℕ):= []
      -- Call the transition function on all current states for each symbol in alphabet
      for symbol in alphabet do
        let next_state := (current_state.map (fun y => transition_function y symbol)).flatten.mergeSort.dedup
        next_states := next_states.insert next_state
        current_transitions := current_transitions.insert ((current_state, symbol), next_state)
      -- Recursively process each reachable state set
      for next_state in next_states do
        if !new_state.visited.contains next_state then
          let reached_states := determinize_with_memo transition_function alphabet next_state (num_possible_states-1) new_state
          let (sub_transitions, updated_state) := (reached_states.transitions, reached_states)
          current_transitions := current_transitions ++ sub_transitions
          new_state := updated_state
      -- Cache the result
      let final_state := { new_state with transitions := current_transitions }
      final_state

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
def determinize_memo {Input : Type} [DecidableEq Input]
  (transition_function : Nat → Input → (List Nat)) (alphabet : List Input)
  (initial_state : List Nat) (max_states : Nat) : determinize_state Input :=
  let initial_state_obj := ⟨Std.HashSet.emptyWithCapacity, []⟩
  determinize_with_memo transition_function alphabet initial_state max_states initial_state_obj

def all_binary_combinations_qt : Nat → List (List B2)
  | 0 => [[]]
  | n + 1 =>
    let smaller := all_binary_combinations_qt n
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
  -- Step 1: Find index of quantified variable and create new alphabet
  let idx := M.vars.findIdx (· = var)
  let new_alphabet := all_binary_combinations_qt (M.vars.length - 1)
  -- Step 2: Create NFA transition function
  -- Given a state and input (without quantified variable), try all possible values
  -- for the quantified variable and collect all reachable states
  let step := fun st input =>
    (alphabet_vars.flatten.map (fun x =>
      input.insertIdx idx x)).map (fun y => M.automata.step st y)
  -- Step 3: Compute bound on possible number of states in powerset (2^n)
  let num_possible_states := 2^(m1_states_list.length)
  -- Step 4: Find all initial states (those reachable via 0*)
  let start_states := find_initial_states step zero [M.automata.start] (m1_states_list.length) []
  -- Step 5: Determinize the NFA
  let new_transitions := determinize_memo step new_alphabet start_states num_possible_states
  -- Step 6: Extract all states from transitions
  let new_states_list := new_transitions.visited.toList
  let new_states := Std.HashSet.emptyWithCapacity.insertMany new_states_list
  -- Step 7: Determine accepting states (any original accepting state in the set)
  let states_acc := new_states.filter (fun x => M.states_accept.any (fun y => x.contains y))
  -- Step 8: Build the resulting DFA
  let dfa_list : DFA (List B2) (List Nat) :={
    step := fun st input =>
      let transt := (new_transitions.transitions.filter (fun ((x,y),_) => st = x ∧ input = y))
      match transt.head? with
      | some ((x,y),z) => z
      | _ => [new_states_list.length + 1]  -- Dead state if no transition found
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
  (M : DFA_extended (List B2) (Nat)) (var : Char) (op_type : quant_op)
  : DFA_extended (List B2) (Nat) :=
  if !M.vars.contains var then
    M
  else
    let zeros := List.replicate (M.vars.length-1) B2.zero
    match op_type with
    | quant_op.exists =>
        change_states_names (quant' M zeros var [[B2.zero], [B2.one]])
    | quant_op.for_all =>
        complement (change_states_names ((quant' (complement M) zeros var [[B2.zero], [B2.one]])))

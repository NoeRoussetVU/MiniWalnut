import MiniWalnut.Automata

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

/-!
# Cross Product Operations for DFAs

This file implements cross product operations over DFAs, which is used
to represent logical operators between two automata languages, and comparison operations for
DFAOs representing automatic languages.

## Main Components

- **Operation Types**: Logical and comparison operators
- **Helper Functions**: Variable alignment and alphabet manipulation
- **Cross Product Construction**: Building product automata from two DFAs

## Theory

The cross product of two DFAs M₁ and M₂ creates a new DFA that:
- Has states Q₁ × Q₂ (Cartesian product of state sets)
- Processes inputs from both M₁ and M₂ simultaneously
- Accepts based on the specified logical/comparison operation

This is used to implement operations like:
- Logical: ∧ (and), ∨ (or), → (implies), ↔ (equivalent), ⊕ (xor)
- Comparison: = (equals), < (less than), > (greater than)
-/

/-!
## Operation Type Definitions
-/

/-- Logical operators for combining automata languages.

    These correspond to standard logical operations on the languages
    accepted by two automata.
-/
inductive l_ops where
  | and                      -- L₁ ∧ L₂: accepts if both automata accept
  | or                       -- L₁ ∨ L₂: accepts if either automaton accepts
  | exclusive_dinjuction     -- L₁ ⊕ L₂: accepts if exactly one automaton accepts (XOR)
  | impl                     -- L₁ → L₂: accepts if M₁ doesn't accept or M₂ accepts
  | equiv                    -- L₁ ↔ L₂: accepts if both accept or both reject

/-- Comparison operators for building automata from arithmetic relations.

    These are used  for operations between two DFAOs when the outputs of the states
    need to be compared
-/
inductive c_ops where
  | equals      -- Accept when state outputs are equal
  | less_than   -- Accept when first state < second state
  | more_than   -- Accept when first state > second state

/-- Combined binary operation type encompassing both logical and comparison operations. -/
inductive binary_ops where
  | logical_op : l_ops → binary_ops        -- Logical operation on languages
  | comparison_op : c_ops → binary_ops     -- Comparison operation on states

/-!
## Helper Functions for Variable and Alphabet Manipulation
-/

/-- Finds the indices in `M₂_vars` where elements from `M₁_vars` appear.

    ### Purpose
    Used to identify which variables are shared between two automata
    so they can be properly aligned in the cross product.

    ### Parameters
    - `M₁_vars`: Variables from automaton M₁
    - `M₂_vars`: Variables from automaton M₂

    ### Example
    ```
    get_idx_same_elements ['k','n'] ['i','k','n'] = [1, 2]
    ```
    The variables 'k' and 'n' from l1 appear at positions 1 and 2 in l2.
-/
def get_idx_same_elements (M₁_vars : List Char) (M₂_vars : List Char) : List Nat :=
  match M₁_vars with
  | [] => []
  | x :: [] => [M₂_vars.findIdx (· = x)]
  | x :: xs => [M₂_vars.findIdx (· = x)] ++ (get_idx_same_elements xs M₂_vars)

/-- Removes elements at specified indices from a list.

    ### Purpose
    When combining automata with shared variables, we need to remove shared variables
    appearing in both automata.

    ### Parameters
    - `alphabet`: The alphabet (list of symbols)
    - `indices`: All valid indices [0, 1, 2, ...]
    - `indices_to_remove`: Which indices to skip

    ### Example
    ```
    remove_indices [B2.zero, B2.one, B2.one] [0,1,2] [2] = [B2.zero, B2.one]
    ```
    Removes the element at index 2.
-/
def remove_indices {T : Type} [Inhabited T] (alphabet : List T)
(indices : List Nat) (indices_to_remove : List Nat) : List T :=
  match indices with
  | [] => []
  | x :: [] => if indices_to_remove.contains x then [] else [alphabet[x]!]
  | x :: xs => if indices_to_remove.contains x then remove_indices alphabet xs indices_to_remove
              else [alphabet[x]!] ++ (remove_indices alphabet xs indices_to_remove)

/-!
## Cross Product Construction
  - Main functions that create the cross product of two given automata.
-/

/-- Determines which states in the cross product should be accepting.

    ### Algorithm
    For each state pair (q₁, q₂):
    - **Logical operations**: Check if q₁ and/or q₂ are accepting based on the operator
    - **Comparison operations**: Check if the state numbers satisfy the comparison

    ### Logical Operation
    - `and`: Accept if both q₁ ∈ F₁ and q₂ ∈ F₂
    - `or`: Accept if q₁ ∈ F₁ or q₂ ∈ F₂
    - `xor`: Accept if exactly one of q₁, q₂ is accepting
    - `impl`: Accept if q₁ ∉ F₁ or q₂ ∈ F₂ (!q₁ ∨ q₂)
    - `equiv`: Accept if both accept or both reject

    ### Comparison Operation
    - `equals`: Accept if q₁ == q₂ (used for equality testing)
    - `less_than`: Accept if q₁ < q₂
    - `more_than`: Accept if q₁ > q₂
-/
def get_accepting_states (states : List (Nat × Nat))
(M₁_accepting : List Nat) (conj : binary_ops) (M₂_accepting : List Nat)
 : List (Nat × Nat) :=
  match conj with
  | binary_ops.logical_op l => match l with
        -- AND: Both must be accepting
        | l_ops.and => states.filter (fun (x,y) =>
            M₁_accepting.contains x ∧ M₂_accepting.contains y)
        -- OR: At least one must be accepting
        | l_ops.or => states.filter (fun (x,y) =>
            M₁_accepting.contains x ∨ M₂_accepting.contains y)
        -- XOR: Exactly one must be accepting
        | l_ops.exclusive_dinjuction => states.filter (fun (x,y) =>
            (Bool.xor (M₁_accepting.contains x) (M₂_accepting.contains y)))
        -- IMPLIES: !M₁ ∨ M₂, equivalent to !(M₁ ∧ M₂)
        | l_ops.impl => states.filter (fun (x,y) =>
            (M₁_accepting.contains x → M₂_accepting.contains y))
        -- EQUIV: (M₁ ∧ M₂) ∨ (!M₁ ∧ !M₂), both accept or both reject
        | l_ops.equiv => states.filter (fun (x,y) =>
            (M₁_accepting.contains x ↔ M₂_accepting.contains y))
  | binary_ops.comparison_op c => match c with
        -- Compare state numbers directly
        | c_ops.equals => states.filter (fun (x,y) => x == y)
        | c_ops.less_than => states.filter (fun (x,y) => x < y)
        | c_ops.more_than => states.filter (fun (x,y) => x > y)

/-- Cross product construction.

    This version creates a DFA with state type (Nat × Nat).
    Use `crossproduct` for the version that converts to Nat states.

    ### Purpose

    Given two automata
    - M₁ := DFA for "a < b" with variables [a, b]
    - M₂ := DFA for "a = b" with variables [a, b]

    Then M₁ | M₂ (OR operation) creates a DFA for "a < b ∨ a = b" (i.e., a ≤ b)
    with the combined variable list [a, b] (duplicates removed).

    ### Parameters
    - `M₁`: First automaton of the operation
    - `operator`: Can be a logical operator or a comparison operator
    - `M₂`: Second automaton of the operation

    ### Algorithm

    1. **State Construction**: Q = Q₁ × Q₂ (Cartesian product)

    2. **Accepting States**: Determined by `get_accepting_states` based on operation

    3. **Alphabet Construction**:
       - Find shared variables between M₁ and M₂
       - Remove duplicate tracks from M₂'s alphabet
       - Combine: each M₁ symbol concatenated with each modified M₂ symbol
       - Example: If M₁ has [a,b] and M₂ has [b,c], and they share 'b':
         * Remove 'b' track from M₂'s alphabet
         * Combine M₁'s [a,b] tracks with M₂'s remaining [c] track
         * Result: [a,b,c] tracks
       - Remove any duplicates obtained in the resulting alphabet

    4. **Variable List**: Union of both variable lists, sorted and deduplicated

    5. **Transition Function**:
       - Create variable→symbol mapping from merged variable list
       - Each component DFA reads only its own variables from the input
       - Transition: (q₁, q₂) --[input]--> (δ₁(q₁, input|vars₁), δ₂(q₂, input|vars₂))

    ### Example
    If M₁ has variables [a, b] and M₂ has variables [b, c]:
    - Get all new states computing the Cartesian product
    - Determine which states are accepting based on the input operator
    - Shared variable: 'b'
    - Combined variables: [a, b, c]
    - Input symbols are triples [v_a, v_b, v_c]
    - M₁ reads [v_a, v_b], M₂ reads [v_b, v_c]
-/
def crossproduct' {Input : Type} [Inhabited Input] [DecidableEq Input]
(M₁ : DFA_extended (List Input) Nat) (operator : binary_ops) (M₂ : DFA_extended (List Input) Nat)
 : DFA_extended (List Input) (Nat × Nat) :=
  -- Step 1: Cartesian product of states
  let states := (M₁.states.map (fun x => M₂.states.map (fun y => (x,y)))).flatten

  -- Step 2: Determine accepting states based on the operation
  let states_accept := get_accepting_states states M₁.states_accept operator M₂.states_accept

  -- Step 3: Construct the combined alphabet
  -- Find which variables are shared and remove duplicate tracks
  let alphabet :=
    -- Find indices of M₁'s variables in M₂'s variable list
    let indices_to_remove := (get_idx_same_elements M₁.vars M₂.vars).filter
                              (fun x => x < M₂.vars.length)
    -- Remove those tracks from M₂'s alphabet (to avoid reading shared variables twice)
    let removed_indices_alphabet := (M₂.alphabet.map (fun x =>
                                    remove_indices x (List.range x.length) indices_to_remove)).dedup
    -- Combine: each M₁ symbol ++ each modified M₂ symbol
    (M₁.alphabet.map (fun x => removed_indices_alphabet.map (fun y => x ++ y))).flatten

  -- Step 4: Dead state exists only if both have dead states
  let dead_state := match M₁.dead_state, M₂.dead_state with
                | _, none => none
                | none, _ => none
                | some n, some y => some ((n,y))

  -- Step 5: Merge and sort variable lists
  let vars := (M₁.vars ++ M₂.vars).dedup.mergeSort

  -- Step 6: Define transition function
  -- Maps input symbols to their corresponding variables, then extracts
  -- the relevant symbols for each component DFA
  let temp_f := fun (st : (Nat × Nat)) (a : (List Input)) =>
      -- Create mapping: variable name → input symbol at that position
      let varias : Std.HashMap Char Input := Std.HashMap.ofList (vars.zip a)
      -- Transition each component using only its variables
      ((M₁.automata.step st.fst (M₁.vars.map (fun x => varias[x]!))),
       (M₂.automata.step st.snd (M₂.vars.map (fun x => varias[x]!))))

  -- Build the product automaton
  let automata := {
    step := fun st input => temp_f st input
    start :=  (M₁.automata.start, M₂.automata.start)
    accept := {p | states_accept.contains p}
  }

  {states := states,
    states_accept := states_accept,
    alphabet := alphabet,
    dead_state := dead_state,
    vars := vars,
    automata := automata}

/-- Cross product construction with Nat states (public interface).

    This is the main function to use for cross product operations.
    It wraps `crossproduct'` and converts the resulting (Nat × Nat) states
    to simple Nat states for easier manipulation and comparison.

    ### Parameters
    - `M₁`: The first automaton part of the crossproduct
    - `operator`: The operator indicating which states will be considered accepting
    - `M₂`: The second automaton part of the crossproduct

    ### Returns
    A DFA_extended with Nat states that accepts the language defined by
    the specified operation on the two input automata.
-/
def crossproduct {Input : Type} [Inhabited Input] [DecidableEq Input]
(M₁ : DFA_extended (List Input) Nat) (operator : binary_ops) (M₂ : DFA_extended (List Input) Nat)
 : DFA_extended (List Input) Nat :=
  change_states_names (crossproduct' M₁ operator M₂)

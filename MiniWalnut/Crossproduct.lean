import MiniWalnut.Automata
import Mathlib.Computability.DFA

/-!
# Cross Product Operations for DFAs

This file implements cross product operations over DFAs, which is used
to represent logical operators between two automata languages, and comparison operations for
DFAOs representing automatic languages.

## Main Components

- **Operation Types**: Logical and comparison operators
- **Alphabet and States Computation**: Creates the cartesian product of states and input symbols
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

/-- Logical operators for combining automata languages. -/
inductive l_ops where
  | and                      -- L₁ ∧ L₂: accepts if both automata accept
  | or                       -- L₁ ∨ L₂: accepts if either automaton accepts
  | xor                      -- L₁ ⊕ L₂: accepts if exactly one automaton accepts (XOR)
  | impl                     -- L₁ → L₂: accepts if M₁ doesn't accept or M₂ accepts
  | equiv                    -- L₁ ↔ L₂: accepts if both accept or both reject

/-- Comparison operators for building automata from arithmetic relations.

    These are used  for operations between two DFAOs when the outputs of the states
    need to be compared
-/
inductive c_ops where
  | equals
  | less_than
  | more_than

/-- Combined binary operation type encompassing both logical and comparison operations. -/
inductive binary_ops where
  | logical_op : l_ops → binary_ops
  | comparison_op : c_ops → binary_ops

/-!
## Cross Product Construction
  - Main functions that create the cross product of two given automata.
-/

/-- Gets the cartesian products of states sets `s1` and `s2` -/
def states_construction (s1 s2 : Std.HashSet Nat) : Std.HashSet (Nat × Nat) :=
  s1.fold (fun acc x =>
    s2.fold (fun acc' y => acc'.insert (x, y)) acc
  ) Std.HashSet.emptyWithCapacity

/-- Gets all possible symbols of length `input_length` -/
def alphabet_construction : (input_length : Nat) → List (List B2)
  | 0 => [[]]
  | n + 1 =>
    let smaller := alphabet_construction n
    smaller.flatMap (fun combo => [B2.zero :: combo, B2.one :: combo])

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
def get_accepting_states (states : Std.HashSet (Nat × Nat))
(M₁_accepting : Std.HashSet Nat) (conj : binary_ops) (M₂_accepting : Std.HashSet Nat)
 : Std.HashSet (Nat × Nat) :=
  match conj with
  | binary_ops.logical_op l => match l with
        -- AND: Both must be accepting
        | l_ops.and => states.filter (fun (x,y) =>
            M₁_accepting.contains x ∧ M₂_accepting.contains y)
        -- OR: At least one must be accepting
        | l_ops.or => states.filter (fun (x,y) =>
            M₁_accepting.contains x ∨ M₂_accepting.contains y)
        -- XOR: Exactly one must be accepting
        | l_ops.xor => states.filter (fun (x,y) =>
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

    ### Parameters
    - `M₁`: First automaton of the operation
    - `operator`: Can be a logical operator or a comparison operator
    - `M₂`: Second automaton of the operation

    ### Algorithm

    1. **State Construction**: Q = Q₁ × Q₂ (Cartesian product)

    2. **Accepting States**: Determined by `get_accepting_states` based on operation

    3. **Variable List**: Union of both variable lists, sorted and deduplicated

    4. **Alphabet Construction**: Gets all combinations of B2.one and B2.zero of length equals
    to the number of variables

    5. **Transition Function**:
       - Create variable→symbol mapping from merged variable list
       - Each component DFA reads only its own variables from the input
       - Transition: (q₁, q₂) --[input]--> (δ₁(q₁, input|vars₁), δ₂(q₂, input|vars₂))
-/
def crossproduct'
(M₁ : DFA_extended (List B2) Nat) (operator : binary_ops) (M₂ : DFA_extended (List B2) Nat)
 : DFA_extended (List B2) (Nat × Nat) :=
  -- Step 1: Cartesian product of states
  let states := states_construction M₁.states M₂.states
  -- Step 2: Determine accepting states based on the operation
  let states_accept := get_accepting_states states M₁.states_accept operator M₂.states_accept
  -- Step 3: Merge and sort variable lists
  let vars := (M₁.vars ++ M₂.vars).dedup
  -- Step 4: Construct the combined alphabet
  let alphabet := Std.HashSet.emptyWithCapacity.insertMany (alphabet_construction vars.length)
  -- Step 5: Dead state exists only if both have dead states
  let dead_state := match M₁.dead_state, M₂.dead_state with
                | _, none => none
                | none, _ => none
                | some n, some y => some ((n,y))
  -- Step 6: Define transition function
  -- Maps input symbols to their corresponding variables, then extracts
  -- the relevant symbols for each component DFA
  let temp_f := fun (st : (Nat × Nat)) (a : (List B2)) =>
      -- Create mapping: variable name → input symbol at that position
      let varias : Std.HashMap Char B2 := Std.HashMap.ofList (vars.zip a)
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

def assign_numbers_cp
(all_states : List (Nat × Nat)) (accepting_states : List (Nat × Nat)) : (List ℕ × List ℕ × Std.HashMap (Nat × Nat) ℕ) :=
  -- Pairs each state with its index
  let mapping := Std.HashMap.ofList all_states.zipIdx
  -- Returns appropriate index
  let lookupNumber (elem : (Nat × Nat)) : ℕ :=
    mapping[elem]!
  (all_states.map lookupNumber, accepting_states.map lookupNumber, mapping)

def change_states_names_cp
(M1 : DFA_extended (List B2) (Nat × Nat))
 : DFA_extended (List B2) Nat :=
  let m1_states_list := M1.states.toList
  let m1_accept_list := M1.states_accept.toList
  let m1_alphabet_list := M1.alphabet.toList
  let mappings := (assign_numbers_cp m1_states_list m1_accept_list)
  let new_states :=  mappings.fst
  let new_states_accept :=  mappings.snd.fst
  let mapp := mappings.snd.snd
  let switched := swapHashMap mapp

  -- Convert dead state if it exists
  let new_dead_state := match M1.dead_state with
                |none => none
                |some n => some mappings.snd.snd[n]!

  -- Build new automaton with Nat states using the transition table
  let automata := {
    step := fun st input => mapp[(M1.automata.step (switched[st]!) input)]!
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

/-- Cross product construction with Nat states (public interface).

    ### Parameters
    - `M₁`: The first automaton part of the crossproduct
    - `operator`: The operator indicating which states will be considered accepting
    - `M₂`: The second automaton part of the crossproduct

    ### Returns
    A DFA_extended with Nat states that accepts the language defined by
    the specified operation on the two input automata.
-/
def crossproduct
(M₁ : DFA_extended (List B2) Nat) (operator : binary_ops) (M₂ : DFA_extended (List B2) Nat)
 : DFA_extended (List B2) (Nat) :=
  change_states_names_cp (crossproduct' M₁ operator M₂)

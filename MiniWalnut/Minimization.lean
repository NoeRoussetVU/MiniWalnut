import Mathlib.Topology.Basic
import Mathlib.Computability.DFA

import MiniWalnut.Automata

/-!
# DFA Minimization

This file implements DFA minimization using Hopcroft's algorithm, which is the
most efficient algorithm for minimizing DFAs (O(n log n) where n is the number of states).

## Main Components

- **Set Operations**: Helper functions for set difference and intersection
- **Hopcroft's Algorithm**: Core minimization algorithm
- **Unreachable State Removal**: BFS to find reachable states

## Theory

DFA minimization creates an equivalent DFA with the minimum number of states by:
1. Removing unreachable states
2. Merging indistinguishable states (states that accept the same language)

Two states are **equivalent** (indistinguishable) if for all input strings w,
starting from either state leads to acceptance or rejection together

## Hopcroft's Algorithm

The algorithm maintains a partition P of states and refines it:
1. Start with partition {F, Q\F} (accepting vs non-accepting)
2. Iteratively split sets based on distinguishability
3. Two states q₁, q₂ are in different sets if there exists an input for which they go
to different states
4. Stop when no more splits are possible
-/

/-!
## Hopcroft's Minimization Algorithm
-/

/-- Hopcroft's algorithm for DFA minimization.

    ### Algorithm Overview

    **Data structures:**
    - P: Partition of states (list of equivalence classes)
    - W: Worklist of sets to process

    **Initial partition:**
    - P = {F, Q\F} where F = accepting states
    - W = P (both sets in worklist)

    **Main loop:**
    While W is not empty:
    1. Remove a set A from W
    2. For each symbol c in alphabet:
       - Compute X = states that can reach A via c (predecessors)
       - For each set Y in partition P:
         * If Y is split by X (some states in Y go to A, others don't):
           - Split Y into (Y ∩ X) and (Y \ X)
           - Update P by replacing Y with the two new sets
           - Update W appropriately

    **Worklist optimization:**
    When splitting Y into Y₁ and Y₂:
    - If Y is in W: add both Y₁ and Y₂ to W
    - If Y is not in W: add the smaller of Y₁, Y₂ to W
    This optimization ensures O(n log n) complexity.

    ### Parameters
    - `Q`: All states
    - `F`: Accepting states
    - `alphabet`: Input alphabet
    - `transition_function`: Transition function

    ### Returns
    List of equivalence classes (each class becomes one state in minimized DFA)
-/
def hopcroft_minimization {State Input : Type} [DecidableEq State] [DecidableEq Input]
    (Q : List State) (F : List State) (alphabet : List Input)
    (transition_function : State → Input → State) : List (List State) :=

  let set_difference (Y X : List State) : List State :=
  Y.filter (fun y => !X.contains y)

  let set_intersection (X Y : List State) : List State :=
  X.filter (fun x => Y.contains x)

  -- Computes predecessors: states that can reach states from A with c
  let get_predecessors (A : List State) (c : Input) : List State :=
    Q.filter (fun q => A.contains (transition_function q c))

  -- Updates worklist when a set Y is split into two new sets
  let update_worklist (W : List (List State)) (old_Y : List State)
  (new_sets : List State × List State) : List (List State) :=
    let (intersection, difference) := new_sets
    if W.contains old_Y then
      -- Y was in worklist: add both new sets
      intersection :: difference :: W.filter (· ≠ old_Y)
    else
      -- Y was not in worklist: add only the smaller set (optimization)
      let smallerSet := if intersection.length ≤ difference.length then intersection else difference
      smallerSet :: W

  -- Initialize partition and worklist
  let non_accepting := set_difference Q F
  let initial_P := [F, non_accepting].filter (fun x => !x.isEmpty)
  let initial_W := initial_P

  -- Main refinement loop
  let rec loop (P : List (List State)) (W : List (List State)) (max_iterations : Nat)
   : List (List State) :=
    if max_iterations <= 0 then P  -- Safety bound to prevent infinite loops
    else
      match W with
      | [] => P  -- Worklist empty: minimization is finished
      | A :: rest_W =>
        let (final_P, final_W) := alphabet.foldl (fun (current_P, current_W) c =>
          let X := get_predecessors A c

          -- Find which sets in current partition need to be split
          -- A set Y needs splitting if some (but not all) states in Y reach A via c
          let sets_to_split := current_P.filter (fun Y =>
            let intersection := set_intersection X Y     -- States in Y that reach A via c
            let difference := set_difference Y X         -- States in Y that don't reach A via c
            !intersection.isEmpty ∧ !difference.isEmpty -- Both parts non-empty means split needed
          )

          -- Apply all necessary splits
          sets_to_split.foldl (fun (acc_P, acc_W) Y =>
            let intersection := set_intersection X Y
            let difference := set_difference Y X
            let new_P := intersection :: difference :: acc_P.filter (· ≠ Y)  -- Replace Y in P with split
            let new_W := update_worklist acc_W Y (intersection, difference)   -- Update worklist
            (new_P, new_W)
          ) (current_P, current_W)

        ) (P, rest_W)

      loop final_P final_W (max_iterations-1)

  loop initial_P initial_W Q.length

/-!
## Unreachable State Removal
-/

/-- Removes unreachable states using breadth-first search.

    ### Algorithm
    1. Start with queue containing only the start state
    2. Mark start state as visited
    3. While queue is not empty:
       - Dequeue state q
       - For each symbol a in alphabet:
         * Compute next state q' = δ(q, a)
         * If q' not visited, add to queue and mark visited
    4. Return all visited states

    ### Parameters
    - `states`: All states in the DFA
    - `alphabet`: Input alphabet
    - `delta`: Transition function
    - `startState`: Initial state

    ### Returns
    List of states reachable from the start state
-/
def remove_unreachable_states {Q T : Type} [DecidableEq Q] [DecidableEq T]
    (states : List Q)
    (alphabet : List T)
    (delta : Q → T → Q)
    (startState : Q) : List Q :=

  -- BFS implementation with explicit iteration bound for termination
  let rec bfs (queue : List Q) (visited : List Q) (max : Nat) : List Q :=
    if max = 0 then visited  -- Safety bound reached
    else
      match queue with
      | [] => visited  -- Queue empty: all reachable states found
      | current_state :: rest_queue =>
        if current_state ∈ visited then
          -- Already processed this state, skip it
          bfs rest_queue visited (max-1)
        else
          -- New state: mark as visited and explore neighbors
          let new_visited := current_state :: visited
          -- Find all states reachable in one step from currentState
          let neighbors := alphabet.foldl (fun acc symbol =>
            acc ++ [delta current_state symbol]
          ) []
          -- Add unvisited neighbors to queue
          let new_queue := rest_queue ++ neighbors.filter (fun s => !(s ∈ new_visited))
          bfs new_queue new_visited (max-1)

  -- Run BFS from start state with reasonable iteration bound
  let reachable_states := bfs [startState] [] (states.length + (states.length * alphabet.length))

  reachable_states


/-!
## Complete Minimization Pipeline
-/

/-- DFA minimization with equivalence class states (internal version).

    ### Algorithm

    1. **Remove unreachable states**: Use BFS from start state
    2. **Apply Hopcroft's algorithm**: Partition equivalent states
    3. **Build minimized DFA**:
       - States: Equivalence partitions
       - Start state: Partition containing original initial state
       - Accepting states: Partitions containing any original accepting state
       - Transitions: Runs the original transition function on the first state of the input partition
          and return the partition containing the obtained state

    ### Parameters
    - `M`: Original DFA to minimize
-/
def minimization' {Input : Type} [Inhabited Input] [DecidableEq Input]
  (M : DFA_extended (List Input) Nat) : DFA_extended (List Input) (List Nat) :=
  let m1_states_list := M.states.toList
  let m1_accept_list := M.states_accept.toList
  let m1_alphabet_list := M.alphabet.toList

  -- Step 1: Remove unreachable states
  let reachable_states := remove_unreachable_states m1_states_list m1_alphabet_list M.automata.step M.automata.start

  -- Step 2: Minimize using Hopcroft's algorithm (only on reachable states)
  let new_states := hopcroft_minimization reachable_states (m1_accept_list ∩ reachable_states) m1_alphabet_list M.automata.step

  -- Step 3: Determine accepting equivalence classes
  -- A class is accepting if it contains any original accepting state
  let new_accept := (new_states.filter (fun x => M.states_accept.any (fun y => x.contains y)))

  -- Step 4: Find start equivalence class (class containing original start)
  let new_start := (new_states.filter (fun x => x.contains M.automata.start)).head!

  -- Step 5: Define transition function for equivalence classes
  -- Use representative (head) of each class to compute transitions
  let temp_f (st : List Nat ) (a : (List B2)) : (List Nat) :=
    if new_states.contains st
    then
      -- Apply transition to representative, find which class it belongs to
      let res := M.automata.step st.head! a
      (new_states.filter (fun x => x.contains res)).flatten
    else []  -- Invalid state

  -- Step 6: Build minimized DFA structure
  let new_automata : DFA (List B2) (List Nat) := {
    step := fun st input => temp_f st input
    start := new_start
    accept := {p | new_accept.contains p}
  }
  {states := Std.HashSet.emptyWithCapacity.insertMany new_states,
   states_accept := Std.HashSet.emptyWithCapacity.insertMany new_accept,
   alphabet := M.alphabet,
   automata := new_automata,
   vars := M.vars,
   dead_state := none}

/-- DFA minimization (public interface).

    Complete minimization that produces a minimal DFA equivalent to the input.
    Rename states to natural numbers (via change_states_names)

    ### Parameters
    - `M`: Original DFA to minimize
-/
def minimization(M : DFA_extended (List B2) Nat) : DFA_extended (List B2) Nat :=
  change_states_names (minimization' M)

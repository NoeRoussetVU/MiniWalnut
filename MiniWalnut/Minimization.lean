import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

import MiniWalnut.Automata

/-!
# DFA Minimization

This file implements DFA minimization using Hopcroft's algorithm, which is the
most efficient algorithm for minimizing DFAs (O(n log n) where n is the number of states).

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

## Main Components

- **Set Operations**: Helper functions for set difference and intersection
- **Hopcroft's Algorithm**: Core minimization algorithm
- **Unreachable State Removal**: BFS to find reachable states
- **Public Interface**: Complete minimization pipeline
-/

/-!
## Set Operation Helpers
-/

/-- Computes set difference Y \ X (elements in Y but not in X).

    ### Example
    ```
    setDifference [1,2,3,4] [2,4] = [1,3]
    ```
-/
def setDifference {α : Type} [DecidableEq α] (Y X : List α) : List α :=
  Y.filter (fun y => !X.contains y)

/-- Computes set intersection X ∩ Y (elements in both X and Y).

    ### Example
    ```
    setIntersection [1,2,3] [2,3,4] = [2,3]
    ```
-/
def setIntersection {α : Type} [DecidableEq α] (X Y : List α) : List α :=
  X.filter (fun x => Y.contains x)

/-!
## Hopcroft's Minimization Algorithm
-/

/-- Hopcroft's algorithm for DFA minimization.

    # Algorithm Overview

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

    ### Example
    If states {1, 2} are equivalent and {3, 4} are equivalent:
    Result = [[1, 2], [3, 4]]
-/
def hopcroftMinimization {State Input : Type} [DecidableEq State] [DecidableEq Input]
    (Q : List State) (F : List State) (alphabet : List Input)
    (transition_function : State → Input → State) : List (List State) :=

  -- Computes predecessors: states q where δ(q, c) ∈ A
  let getPredecessors (A : List State) (c : Input) : List State :=
    Q.filter (fun q => A.contains (transition_function q c))

  -- Updates worklist when a set Y is split into two new sets
  -- Implements the optimization for O(n log n) complexity
  let updateWorklist (W : List (List State)) (oldY : List State)
  (newSets : List State × List State) : List (List State) :=
    let (intersection, difference) := newSets
    if W.contains oldY then
      -- Y was in worklist: add both new sets
      intersection :: difference :: W.filter (· ≠ oldY)
    else
      -- Y was not in worklist: add only the smaller set (optimization)
      let smallerSet := if intersection.length ≤ difference.length then intersection else difference
      smallerSet :: W

  -- Initialize partition and worklist
  let nonAccepting := setDifference Q F
  let initialP := [F, nonAccepting].filter (fun x => !x.isEmpty)  -- Remove empty sets
  let initialW := initialP

  -- Main refinement loop
  let rec loop (P : List (List State)) (W : List (List State)) (max_iterations : Nat)
   : List (List State) :=
    if max_iterations <= 0 then P  -- Safety bound to prevent infinite loops
    else
      match W with
      | [] => P  -- Worklist empty: partition is stable, we're done!
      | A :: restW =>
        -- Process set A from worklist
        let (finalP, finalW) := alphabet.foldl (fun (currentP, currentW) c =>
          -- Compute predecessors of A via symbol c
          let X := getPredecessors A c

          -- Find which sets in current partition need to be split
          -- A set Y needs splitting if some (but not all) states in Y reach A via c
          let setsToSplit := currentP.filter (fun Y =>
            let intersection := setIntersection X Y
            let difference := setDifference Y X
            !intersection.isEmpty ∧ !difference.isEmpty  -- Both parts non-empty means split needed
          )

          -- Apply all necessary splits
          setsToSplit.foldl (fun (accP, accW) Y =>
            let intersection := setIntersection X Y  -- States in Y that reach A via c
            let difference := setDifference Y X      -- States in Y that don't reach A via c
            let newP := intersection :: difference :: accP.filter (· ≠ Y)  -- Replace Y with split
            let newW := updateWorklist accW Y (intersection, difference)   -- Update worklist
            (newP, newW)
          ) (currentP, currentW)

        ) (P, restW)

      loop finalP finalW (max_iterations-1)

  loop initialP initialW Q.length

/-- Public interface for Hopcroft's minimization algorithm.

    Wrapper function that calls hopcroftMinimization with clearer parameter names.
-/
def minimizeDFAHopcroft {State Input : Type} [DecidableEq State] [DecidableEq Input]
    (allStates : List State) (acceptingStates : List State) (alphabet : List Input)
    (transition : State → Input → State) : List (List State) :=
  hopcroftMinimization allStates acceptingStates alphabet transition

/-!
## Unreachable State Removal
-/

/-- Removes unreachable states using breadth-first search.

    ### Purpose
    Before minimization, we must remove states that cannot be reached from
    the start state. These states don't affect the language but complicate minimization.

    ### Algorithm (BFS)
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

    ### Complexity
    O(|Q| × |Σ|) where |Q| = number of states, |Σ| = alphabet size
-/
def removeUnreachableStatesBFS {Q T : Type} [DecidableEq Q] [DecidableEq T]
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
      | currentState :: restQueue =>
        if currentState ∈ visited then
          -- Already processed this state, skip it
          bfs restQueue visited (max-1)
        else
          -- New state: mark as visited and explore neighbors
          let newVisited := currentState :: visited
          -- Find all states reachable in one step from currentState
          let neighbors := alphabet.foldl (fun acc symbol =>
            acc ++ [delta currentState symbol]
          ) []
          -- Add unvisited neighbors to queue
          let newQueue := restQueue ++ neighbors.filter (fun s => !(s ∈ newVisited))
          bfs newQueue newVisited (max-1)

  -- Run BFS from start state with reasonable iteration bound
  let reachableStates := bfs [startState] [] (states.length + (states.length * alphabet.length))

  reachableStates

/-!
## Complete Minimization Pipeline
-/

/-- DFA minimization with equivalence class states (internal version).

    ### Algorithm Pipeline

    1. **Remove unreachable states**: Use BFS from start state
    2. **Apply Hopcroft's algorithm**: Partition reachable states into equivalence classes
    3. **Build minimized DFA**:
       - States: Equivalence classes (List Nat)
       - Start state: Class containing original start state
       - Accepting states: Classes containing any original accepting state
       - Transitions: δ([q], a) = [δ(q, a)] (well-defined since equivalent states
         have identical behavior)

    ### Implementation Note
    The transition function takes the head of an equivalence class as a representative.
    This works because all states in the class have identical transition behavior.

    ### Parameters
    - `M1`: Original DFA to minimize

    ### Returns
    Minimized DFA where states are equivalence classes (List Nat)
-/
def minimization' {Input : Type} [Inhabited Input] [DecidableEq Input]
  (M1 : DFA_extended (List Input) Nat) : DFA_extended (List Input) (List Nat) :=
  -- Step 1: Remove unreachable states
  let reachable_states := removeUnreachableStatesBFS M1.states M1.alphabet M1.automata.step M1.automata.start

  -- Step 2: Minimize using Hopcroft's algorithm (only on reachable states)
  let new_states := minimizeDFAHopcroft reachable_states (M1.states_accept ∩ reachable_states) M1.alphabet M1.automata.step

  -- Step 3: Determine accepting equivalence classes
  -- A class is accepting if it contains any original accepting state
  let new_accept := (new_states.filter (fun x => M1.states_accept.any (fun y => x.contains y)))

  -- Step 4: Find start equivalence class (class containing original start)
  let new_start := (new_states.filter (fun x => x.contains M1.automata.start)).head!

  -- Step 5: Define transition function for equivalence classes
  -- Use representative (head) of each class to compute transitions
  let temp_f (st : List Nat ) (a : (List Input)) : (List Nat) :=
    if new_states.contains st
    then
      -- Apply transition to representative, find which class it belongs to
      let res := M1.automata.step st.head! a
      (new_states.filter (fun x => x.contains res)).flatten
    else []  -- Invalid state

  -- Step 6: Build minimized DFA structure
  let new_automobile : DFA (List Input) (List Nat) := {
    step := fun st input => temp_f st input
    start := new_start
    accept := {p | new_accept.contains p}
  }
  {states := new_states,
   states_accept := new_accept,
   alphabet := M1.alphabet,
   automata := new_automobile,
   vars := M1.vars,
   dead_state := none}

/-- DFA minimization (public interface with Nat states).

    Complete minimization that produces a minimal DFA equivalent to the input.

    ### Guarantees
    The resulting DFA:
    - Accepts exactly the same language as the input DFA
    - Has the minimum possible number of states
    - Has no unreachable states
    - Has states numbered 0, 1, 2, ... for easy manipulation

    ### Algorithm
    1. Remove unreachable states (BFS)
    2. Partition states into equivalence classes (Hopcroft's algorithm)
    3. Build new DFA with equivalence classes as states
    4. Rename states to natural numbers (via change_states_names)

    ### Complexity
    O(n log n) where n is the number of states (Hopcroft's algorithm)

    ### Usage
    ```lean
    let large_dfa := crossproduct dfa1 (binary_ops.logical_op l_ops.or) dfa2
    let minimized := minimization large_dfa  -- Reduce redundant states
    ```

    ### When to Use
    - After cross product operations (which can create many equivalent states)
    - After quantification (which creates powerset states)
    - When you need canonical form for equivalence checking
    - To improve performance of subsequent operations
-/
def minimization {Input : Type} [Inhabited Input] [DecidableEq Input]
(M1 : DFA_extended (List Input) Nat) : DFA_extended (List Input) Nat :=
  change_states_names (minimization' M1)

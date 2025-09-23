import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

import MiniWalnut.Basic
import MiniWalnut.Automatons


def test_state1' := [0,1,2,3]
def test_state2' := [4]
def test_alpha' := [B2.zero, B2.one]
def test_f' (st : Nat) (a : B2) : Nat :=
match st, a with
| 0, B2.zero => 1
| 0, B2.one => 3
| 1, B2.zero => 2
| 1, B2.one => 4
| 2, B2.zero => 1
| 2, B2.one => 4
| 3, B2.zero => 0
| 3, B2.one => 4
| 4, B2.zero => 3
| 4, B2.one => 4
| _, _ => 5

-- Helper function to compute set difference (Y \ X)
def setDifference {α : Type} [DecidableEq α] (Y X : List α) : List α :=
  Y.filter (fun y => ¬X.contains y)

-- Helper function to compute set intersection (X ∩ Y)
def setIntersection {α : Type} [DecidableEq α] (X Y : List α) : List α :=
  X.filter (fun x => Y.contains x)


-- Alternative cleaner implementation with better structure
def hopcroftMinimizationV2 {State Input : Type} [DecidableEq State] [DecidableEq Input]
    (Q : List State)
    (F : List State)
    (Sigma : List Input)
    (delta : State → Input → State)
    : List (List State) :=

  -- Helper to get predecessors of a set A on symbol c
  let getPredecessors (A : List State) (c : Input) : List State :=
    Q.filter (fun q => A.contains (delta q c))

  -- Helper to split a partition based on a splitter set
  let splitPartition (P : List (List State)) (X : List State) : List (List State) :=
    P.foldl (fun acc Y =>
      let intersection := setIntersection X Y
      let difference := setDifference Y X
      if !intersection.isEmpty ∧ !difference.isEmpty then
        intersection :: difference :: acc.filter (· ≠ Y)
      else
        acc
    ) P

  -- Helper to update worklist W when partition P is split
  let updateWorklist (W : List (List State)) (oldY : List State) (newSets : List State × List State) : List (List State) :=
    let (intersection, difference) := newSets
    if W.contains oldY then
      -- Replace Y in W with both new sets
      intersection :: difference :: W.filter (· ≠ oldY)
    else
      -- Add smaller set to W
      let smallerSet := if intersection.length ≤ difference.length then intersection else difference
      smallerSet :: W

  -- Initialize
  let nonAccepting := setDifference Q F
  let initialP := [F, nonAccepting].filter (fun x => !x.isEmpty)
  let initialW := initialP

  -- Main loop
  let rec loop (P : List (List State)) (W : List (List State)) (max_iterations : Nat): List (List State) :=
    if max_iterations <= 0 then P
    else
      match W with
      | [] => P
      | A :: restW =>
        let (finalP, finalW) := Sigma.foldl (fun (currentP, currentW) c =>
          let X := getPredecessors A c

          -- Find sets that need to be split
          let setsToSplit := currentP.filter (fun Y =>
            let intersection := setIntersection X Y
            let difference := setDifference Y X
            !intersection.isEmpty ∧ !difference.isEmpty
          )

          -- Apply splits
          setsToSplit.foldl (fun (accP, accW) Y =>
            let intersection := setIntersection X Y
            let difference := setDifference Y X
            let newP := intersection :: difference :: accP.filter (· ≠ Y)
            let newW := updateWorklist accW Y (intersection, difference)
            (newP, newW)
          ) (currentP, currentW)

        ) (P, restW)

      loop finalP finalW (max_iterations-1)

  loop initialP initialW Q.length

-- Complete interface function
def minimizeDFAHopcroft {State Input : Type} [DecidableEq State] [DecidableEq Input]
    (allStates : List State)
    (acceptingStates : List State)
    (alphabet : List Input)
    (transition : State → Input → State) : List (List State) :=
  hopcroftMinimizationV2 allStates acceptingStates alphabet transition

-- Example usage
def example_states : List Nat := [0, 1, 2, 3, 4]
def example_accepting : List Nat := [3, 4]
def example_alphabet : List Char := ['a', 'b']

def example_transition (state : Nat) (input : Char) : Nat :=
  match state, input with
  | 0, 'a' => 1
  | 0, 'b' => 2
  | 1, 'a' => 3
  | 1, 'b' => 2
  | 2, 'a' => 1
  | 2, 'b' => 4
  | 3, 'a' => 3
  | 3, 'b' => 4
  | 4, 'a' => 3
  | 4, 'b' => 4
  | _, _ => 0  -- Default case

#eval minimizeDFAHopcroft example_states example_accepting example_alphabet example_transition

-- Example usage
def example_states' : List Nat := [1,2,3,4,5,6,7]
def example_accepting' : List Nat := [3, 6]
def example_alphabet' : List Char := ['a', 'b']

def example_transition' (state : Nat) (input : Char) : Nat :=
  match state, input with
  | 1, 'a' => 2
  | 1, 'b' => 4
  | 2, 'a' => 3
  | 2, 'b' => 2
  | 3, 'a' => 3
  | 3, 'b' => 3
  | 4, 'a' => 7
  | 4, 'b' => 5
  | 5, 'a' => 6
  | 5, 'b' => 5
  | 6, 'a' => 6
  | 6, 'b' => 6
  | 7, 'a' => 7
  | 7, 'b' => 7
  | _, _ => 0  -- Default case

#eval minimizeDFAHopcroft example_states' example_accepting' example_alphabet' example_transition'

-- Alternative implementation using breadth-first search
def removeUnreachableStatesBFS {Q T : Type} [DecidableEq Q] [DecidableEq T]
    (states : List Q)
    (alphabet : List T)
    (delta : Q → T → Q)
    (startState : Q) : List Q :=

  -- BFS to find all reachable states
  let rec bfs (queue : List Q) (visited : List Q) (max : Nat) : List Q :=
    if max = 0 then visited
    else
      match queue with
      | [] => visited
      | currentState :: restQueue =>
        if currentState ∈ visited then
          bfs restQueue visited (max-1)
        else
          let newVisited := currentState :: visited
          let neighbors := alphabet.foldl (fun acc symbol =>
            acc ++ [delta currentState symbol]
          ) []
          let newQueue := restQueue ++ neighbors.filter (fun s => ¬(s ∈ newVisited))
          bfs newQueue newVisited (max-1)

  let reachableStates := bfs [startState] [] (states.length + (states.length * alphabet.length))

  -- Return reachable states
  reachableStates

  -- Example usage
def example_states'' : List Nat := [1,2,3,4,5,6,7]
def example_accepting'' : List Nat := [3, 5]
def example_alphabet'' : List Char := ['a', 'b']

def example_transition'' (state : Nat) (input : Char) : Nat :=
  match state, input with
  | 1, 'a' => 2
  | 1, 'b' => 4
  | 2, 'a' => 3
  | 2, 'b' => 2
  | 3, 'a' => 3
  | 3, 'b' => 3
  | 4, 'a' => 4
  | 4, 'b' => 5
  | 5, 'a' => 5
  | 5, 'b' => 5
  | 6, 'a' => 6
  | 6, 'b' => 6
  | 7, 'a' => 7
  | 7, 'b' => 7
  | _, _ => 0  -- Default case

#eval removeUnreachableStatesBFS example_states'' example_alphabet'' example_transition'' 1

def minimization' {Input : Type} [Inhabited Input] [DecidableEq Input]
  (M1 : DFA_Complete (List Input) Nat) : DFA_Complete (List Input) (List Nat) :=
  let reachable_states :=   removeUnreachableStatesBFS M1.states M1.alphabet M1.automata.step M1.automata.start
  let new_states := minimizeDFAHopcroft reachable_states (M1.states_accept ∩ reachable_states) M1.alphabet M1.automata.step
  let new_accept := (new_states.filter (fun x => M1.states_accept.any (fun y => x.contains y)))
  let new_start := (new_states.filter (fun x => x.contains M1.automata.start)).head!

  let temp_funk (st : List Nat ) (a : (List Input)) : (List Nat) :=
    if new_states.contains st
    then
      let res := M1.automata.step st.head! a
      (new_states.filter (fun x => x.contains res)).flatten
    else []

  let new_automobile : DFA (List Input) (List Nat) := {
    step := fun st input => temp_funk st input
    start :=  new_start
    -- Accepting states are pairs where both components are accepting for AND
    -- either component is accepting for OR
    accept := {p | new_accept.contains p}
  }
  {states := new_states, states_accept := new_accept, alphabet := M1.alphabet, alphabet_vars := M1.alphabet_vars, automata := new_automobile, vars := M1.vars, dead_state := none}


def minimization {Input : Type} [Inhabited Input] [DecidableEq Input]
(M1 : DFA_Complete (List Input) Nat) : DFA_Complete (List Input) Nat :=
  change_states_names (minimization' M1)

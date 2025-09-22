import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

import MiniWalnut.Basic
import MiniWalnut.Automatons
import MiniWalnut.Crossproduct
import MiniWalnut.Quantification

def help2 {State1 Input1 : Type} [BEq State1] (fst_states : List State1) (snd_states : List State1)
(alphabet : List Input1) (funk : State1 → Input1 → State1) : List (List State1) :=
match alphabet with
| [] => []
| x :: xs =>
    let reached := fst_states.partition (fun y => !snd_states.contains (funk y x) )
    if reached.fst.isEmpty ∨ reached.snd.isEmpty
    then help2 fst_states snd_states xs funk
    else [reached.fst] ++ [reached.snd] ++ [snd_states]


def test_state1 := ["q0", "q1", "q2", "q3"]
def test_state2 := ["q4"]
def test_alpha := [0,1]
def test_f (st : String) (a : Nat) : String :=
match st, a with
| "q0", 0 => "q1"
| "q0", 1 => "q3"
| "q1", 0 => "q2"
| "q1", 1 => "q4"
| "q2", 0 => "q1"
| "q2", 1 => "q4"
| "q3", 0 => "q0"
| "q3", 1 => "q4"
| "q4", 0 => "q3"
| "q4", 1 => "q4"
| _, _ => "pissofpiss"

#eval help2 test_state1 test_state2 test_alpha test_f
#eval help2 ["q1", "q2", "q3"] ["q0"] test_alpha test_f

def help1 {State1 Input1 : Type} [BEq State1] (state1 : List State1) (states : List (List State1))
(alphabet : List Input1) (funk : State1 → Input1 → State1) : List (List State1) :=
match states with
| [] => [state1] ++ states
| x :: xs =>
    let reached := (help2 state1 x alphabet funk)
    if !reached.isEmpty
    then reached ++ xs
    else
    let reached_reverse := (help2 x state1 alphabet funk)
    if !reached_reverse.isEmpty then reached_reverse ++ xs
    else [x] ++ help1 state1 xs alphabet funk

#eval help1 test_state1 [test_state2] test_alpha test_f

def minimization' {State1 Input1 : Type} [BEq State1] (states : List (List State1)) (alphabet : List Input1)
(funk : State1 → Input1 → State1) (n_of_states : Nat) : List (List State1) :=
  if n_of_states > 0 then
    match states with
    | [] => states
    | x :: xs =>
      let new_states := help1 x xs alphabet funk
      if new_states.isEmpty then
      minimization' xs alphabet funk n_of_states
      else minimization' new_states alphabet funk (n_of_states-1)
  else states

#eval minimization' ([test_state1] ++ [test_state2]) test_alpha test_f 5

def test1 := ["q0", "q1", "q2"]
def test2 := ["q3"]
def test3 := [0,1]
def test4 (st : String) (a : Nat) : String :=
match st, a with
| "q0", 0 => "q1"
| "q0", 1 => "q2"
| "q1", 0 => "q1"
| "q1", 1 => "q3"
| "q2", 0 => "q3"
| "q2", 1 => "q2"
| _, _ => "dead"

def b_equals_4' := createFullEqualsDFA [[B2.one], [B2.zero], [B2.zero]] [B2.zero] ['b']
#eval b_equals_4'.states
def c_equals_3' := createFullEqualsDFA [[B2.one], [B2.one]] [B2.zero] ['c']
#eval c_equals_3'.states
def a_equals_b_p_c' : DFA_Complete (List B2)  Nat := createFullAdditionDFA ['a','b','c']

#eval a_equals_b_p_c'.states

/-def nu_function (st : List ℕ ) (a : List B2) : (List (ℕ)) :=
if nu_states.contains st
then
  let res := a_bc_and_b_equals_4'.automata.step st.head! a
  (nu_states.find? (fun x => x.contains res))
else []


#eval (nu_states.filter (fun x => a_bc_and_b_equals_4'.states_accept.any (fun y => x.contains y))).flatten

#eval nu_function [0] [B2.zero, B2.zero, B2.zero]
#eval nu_function [0] [B2.zero, B2.one, B2.zero]-/

-- Optimized DFA Minimization Functions

-- Helper function to split a state group based on distinguishability
def splitStateGroup {Input : Type} [BEq Input] (group : List Nat) (otherGroups : List (List Nat))
    (alphabet : List Input) (transition : Nat → Input → Nat) : Option (List Nat × List Nat) := do
  -- Find the first symbol that distinguishes states in this group
  let distinguishingSymbol ← alphabet.find? fun symbol =>
    let targetGroups := group.map (fun state =>
      otherGroups.findIdx? (fun grp => grp.contains (transition state symbol)))
    targetGroups.any (fun tgt => targetGroups.head? != some tgt)

    let symbol := distinguishingSymbol
    -- Split based on which group their transitions go to
    let getTargetGroupIdx (state : Nat) : Option Nat :=
      otherGroups.findIdx? (fun grp => grp.contains (transition state symbol))

    let partition := group.partition fun state =>
      match getTargetGroupIdx state, group.head?.bind getTargetGroupIdx with
      | some idx1, some idx2 => idx1 == idx2
      | _, _ => true

    if partition.1.isEmpty || partition.2.isEmpty then none
    else some partition

-- More efficient refinement step
def refinePartition {Input : Type} [BEq Input] (partition : List (List Nat))
    (alphabet : List Input) (transition : Nat → Input → Nat) : List (List Nat) :=
  partition.foldl (fun acc group =>
    match splitStateGroup group partition alphabet transition with
    | some (group1, group2) => group1 :: group2 :: acc.filter (· != group)
    | none => acc
  ) partition

-- Main minimization function with termination check
def dfaMinimization {Input : Type} [BEq Input] (initialPartition : List (List Nat))
    (alphabet : List Input) (transition : Nat → Input → Nat)
    (maxIterations : Nat) : List (List Nat) :=
  let rec loop (partition : List (List Nat)) (iterations : Nat) : List (List Nat) :=
    if iterations <= 0 then partition else
    let newPartition := refinePartition partition alphabet transition
    if newPartition == partition then partition  -- Fixed point reached
    else loop newPartition (iterations - 1)
  loop initialPartition maxIterations

-- Utility function to create initial partition (accepting vs non-accepting states)
def createInitialPartition (allStates : List Nat) (acceptingStates : List Nat) : List (List Nat) :=
  let accepting := allStates.filter acceptingStates.contains
  let nonAccepting := allStates.filter (fun s => !acceptingStates.contains s)
  [accepting, nonAccepting].filter (· != [])

-- Complete DFA minimization with better interface
def minimizeDFA {Input : Type} [BEq Input] (allStates : List Nat)
    (acceptingStates : List Nat) (alphabet : List Input)
    (transition : Nat → Input → Nat) : List (List Nat) :=
  let initialPartition := createInitialPartition allStates acceptingStates
  dfaMinimization initialPartition alphabet transition allStates.length

-- Example usage:
-- def states := [0, 1, 2, 3, 4]
-- def accepting := [2, 4]
-- def alphabet := ['a', 'b']
-- def trans : Nat → Char → Nat := fun state input => ...
-- let minimized := minimizeDFA states accepting alphabet trans


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

#eval minimizeDFA (test_state1' ++ test_state2') test_state2' test_alpha' test_f'

-- Helper function to compute set difference (Y \ X)
def setDifference {α : Type} [DecidableEq α] (Y X : List α) : List α :=
  Y.filter (fun y => ¬X.contains y)

-- Helper function to compute set intersection (X ∩ Y)
def setIntersection {α : Type} [DecidableEq α] (X Y : List α) : List α :=
  X.filter (fun x => Y.contains x)

-- Helper function to check if a set is empty
def isEmpty  {α : Type} (s : List α) : Bool := s.length = 0

-- Helper function to replace an element in a list
def replaceInList {α : Type} [DecidableEq α] (list : List α) (old new1 new2 : α) : List α :=
  list.map (fun x => if x == old then new1 else x) ++ [new2]

-- Main Hopcroft's Algorithm implementation
partial def hopcroftMinimization {State Input : Type} [DecidableEq State] [DecidableEq Input] [DecidableEq (List State)]
    (Q : List State)  -- All states
    (F : List State)  -- Accepting states
    (Sigma : List Input)  -- Alphabet
    (delta : State → Input → State)  -- Transition function
    : List (List State) :=

  -- Initialize P := {F, Q \ F}
  let nonAccepting := setDifference Q F
  let initialP := if isEmpty F then [nonAccepting]
                  else if isEmpty nonAccepting then [F]
                  else [F, nonAccepting]

  -- Initialize W := {F, Q \ F} (same as P initially)
  let initialW := initialP

  -- Main algorithm loop
  let rec mainLoop (P : List (List State)) (W : List (List State)) : List (List State) :=
    if W.isEmpty then
      P  -- W is empty, algorithm terminates
    else
      -- Choose and remove a set A from W
      match W with
      | [] => P  -- Should not happen due to isEmpty check above
      | A :: restW =>
        -- Process each symbol in the alphabet
        let (newP, newW) := Sigma.foldl (fun (currentP, currentW) c =>
          -- Let X be the set of states for which a transition on c leads to a state in A
          let X := Q.filter (fun q => A.contains (delta q c))

          -- Process each set Y in P
          let (updatedP, updatedW) := currentP.foldl (fun (accP, accW) Y =>
            let intersection := setIntersection X Y  -- X ∩ Y
            let difference := setDifference Y X      -- Y \ X

            -- Check if X ∩ Y is nonempty and Y \ X is nonempty
            if ¬isEmpty intersection ∧ ¬isEmpty difference then
              -- Replace Y in P by the two sets X ∩ Y and Y \ X
              let newP := accP.map (fun set =>
                if set == Y then intersection else set) ++ [difference]

              -- Handle W updates
              let newW :=
                if accW.contains Y then
                  -- If Y is in W, replace Y in W by the same two sets
                  accW.map (fun set =>
                    if set == Y then intersection else set) ++ [difference]
                else
                  -- Add the smaller set to W
                  if intersection.length ≤ difference.length then
                    intersection :: accW
                  else
                    difference :: accW

              (newP, newW)
            else
              (accP, accW)  -- No split needed
          ) (currentP, currentW)

          (updatedP, updatedW)
        ) (P, restW)

        -- Continue with updated P and W
        mainLoop newP newW

  -- Start the main loop
  mainLoop initialP initialW

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
      if ¬isEmpty intersection ∧ ¬isEmpty difference then
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
  let initialP := [F, nonAccepting].filter (¬isEmpty ·)
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
            ¬isEmpty intersection ∧ ¬isEmpty difference
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

-- Utility function to create initial partition
def createInitialPartition' {State : Type} [DecidableEq State]
    (allStates : List State) (acceptingStates : List State) : List (List State) :=
  let accepting := acceptingStates.filter (allStates.contains ·)
  let nonAccepting := allStates.filter (fun s => ¬acceptingStates.contains s)
  [accepting, nonAccepting].filter (fun group => ¬isEmpty group)

#eval createInitialPartition' [0,1,2,3,4,5,6,7] [2,5,6]

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
def findUnreachableStatesBFS {Q T : Type} [DecidableEq Q] [DecidableEq T]
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

def unreachable_swag {State Input: Type} [DecidableEq State] [DecidableEq Input]
  (M1 : DFA_Complete Input State) : List State :=
  findUnreachableStatesBFS M1.states M1.alphabet M1.automata.step M1.automata.start

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

#eval findUnreachableStatesBFS example_states'' example_alphabet'' example_transition'' 1


def minimization {Input : Type} [Inhabited Input] [DecidableEq Input]
(M1 : DFA_Complete (Input) Nat) : DFA_Complete (Input) Nat :=
let reachable_states := unreachable_swag M1
let new_states := minimizeDFAHopcroft reachable_states (M1.states_accept ∩ reachable_states) M1.alphabet M1.automata.step
let new_accept := (new_states.filter (fun x => M1.states_accept.any (fun y => x.contains y)))
let new_start := (new_states.filter (fun x => x.contains M1.automata.start)).head!

let mappingas := (assignNumbers' new_states new_accept)
let new_states' :=  mappingas.fst
let new_states_accept' :=  mappingas.snd.fst

let temp_funk (st : List Nat ) (a : Input) : (List Nat) :=
  if new_states.contains st
  then
    let res := M1.automata.step st.head! a
    (new_states.filter (fun x => x.contains res)).flatten
  else []

let transitions : List (List ((ℕ × Input) × ℕ)) := new_states.map (fun x => M1.alphabet.map (fun z => ((mappingas.snd.snd[(x)]!, z), mappingas.snd.snd[(temp_funk (x) z)]! )))
let tf := transitions.flatten

let new_automobile : DFA (Input) Nat := {
  step := fun st input =>
  let tr := tf.filter (fun ((x,y),_) => st = x ∧ input = y)
  match tr.head? with
  | some ((x,y),z) => z
  | _ => new_states'.length + 100
  start :=  mappingas.snd.snd[new_start]!
  -- Accepting states are pairs where both components are accepting for AND
  -- either component is accepting for OR
  accept := {p | new_states_accept'.contains p}
}
{states := new_states', states_accept := new_states_accept', alphabet := M1.alphabet, alphabet_vars := M1.alphabet_vars, automata := new_automobile, vars := M1.vars, dead_state := none}

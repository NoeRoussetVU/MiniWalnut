import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

import MiniWalnut.Automatons

/-

Quantification on cross-product DFA

  First add all the states reachable from the starting state with 0*

-/

-- Helper function to process a single input symbol from a set of current states
def processSymbol {T Q : Type} [DecidableEq Q] (start_states : List Q) (f : Q → T → List Q) (currentStates : List Q) (symbol : T) : List Q :=
  let nextStates := currentStates.foldl (fun acc state =>
    acc ++ f state symbol
  ) []
  nextStates.eraseDups

-- Function to find all states reachable with exactly n zeros
def reachableWithNZeros {T Q : Type} [DecidableEq T] [DecidableEq Q] (start_states : List Q) (f : Q → T → List Q) (n : Nat) (zero : T) : List Q :=
  if n = 0 then
    start_states
  else
    let rec helper (currentStates : List Q) (remaining : Nat) : List Q :=
      if remaining = 0 then
        currentStates
      else
        let nextStates := processSymbol start_states f currentStates zero
        helper nextStates (remaining - 1)
    helper start_states n

-- Main function: Find all states reachable with one or more zeros
def reachableWithOneOrMoreZeros {T Q : Type} [DecidableEq T] [DecidableEq Q] (start_states : List Q) (f : Q → T → List Q) (zero : T) (maxZeros : Nat) : List Q :=
  let allReachableStates := (List.range maxZeros).foldl (fun acc n =>
    if n = 0 then acc
    else acc ++ reachableWithNZeros start_states f n zero
  ) []
  allReachableStates


--#eval intersectionDFATwo.automata.step (0,1) [B2.zero,B2.one]

--#eval intersectionDFATwo.alphabet.map (fun x => intersectionDFATwo.automata.step (0,0) (x))
--#eval intersectionDFATwo.states.map (fun x => intersectionDFATwo.alphabet.map (fun y => intersectionDFATwo.automata.step x y))


/-

  Determinization: Build a list of all states,
  Input: start states list, alphabet and dfa
  for each alphabet input, go through each start state to build a new state
  then if that state isn't in list of all states, add that state to list of all states,
  and use it as new base state
  otherwise end here and move on to new input

  I mean it's just depth-first search basically

-/

def test_states : List Nat := [1,2]
def test_func : Nat → List B2 → List Nat
  | 1, [B2.zero, B2.zero] => [1]
  | 1, [B2.zero, B2.one] => [2, 3]
  | 1, [B2.one, B2.zero] => [1]
  | 1, [B2.one, B2.one] => [1, 3]
  | 2, [B2.zero, B2.zero] => [1]
  | 2, [B2.zero, B2.one] => [1,2]
  | 2, [B2.one, B2.one] => [1]
  | 2, [B2.one, B2.zero] => [1, 2]
  | 3, [B2.zero, B2.zero] => [1, 3]
  | 3, [B2.one, B2.one] => [3]
  | _, _ => [1,2,3]
def test_input : List B2 := [B2.zero, B2.one]
def test_alphabet : List (List B2) := [[B2.zero, B2.zero],[B2.zero, B2.one],[B2.one, B2.zero],[B2.one, B2.one]]

 def determinize_old {State1 Input1 : Type} [DecidableEq Input1] [DecidableEq State1] [BEq State1]
  (transition_function : State1 → Input1 → (List State1)) (alphabet : List Input1)
  (current_state : List State1) (num_possible_states : Nat) (previous_states : List (List State1)) : (List ((List State1 × Input1) × List State1) ) :=
  -- function that takes a list of states, a step function and an input
  -- and goes through the list
  let get_reachable_states (states : List State1) (step : State1 → Input1 → (List State1))
  (input : Input1) : (List (List State1)) := states.map (fun x => step x input)

  if num_possible_states > 0 then
    let current_transitions := alphabet.map (fun x => ((current_state,x),(get_reachable_states current_state transition_function x).flatten.dedup))
    let current_reachable_states := (current_transitions.map (fun ((x,y),z) => z)).dedup
    let next_reachable_states := current_reachable_states.map (fun (x) =>
      if (previous_states.filter (fun w => w.isPerm x)).isEmpty
      then
      (determinize_old transition_function alphabet x (num_possible_states-1) (previous_states++[x]))
      else []
    )
    current_transitions ++ next_reachable_states.flatten
  else []

#eval ((determinize_old test_func test_alphabet [1,2] (2^([1,2,3].length ))) [[1,2]]).dedup.length

/-
[(([1], 'a'), [2, 3]),
(([1], 'b'), [1, 2, 3]),
(([1], 'c'), [1, 2, 3]),
(([2, 3], 'a'), [1, 3]),
  (([2, 3], 'b'), [1, 2, 3]),
  (([2, 3], 'c'), [1, 2, 3]),
   (([1, 3], 'a'), [1, 2, 3]),
   (([1, 3], 'b'), [1, 2, 3]),
  (([1, 3], 'c'), [1, 2, 3]),
  (([1, 2, 3], 'a'), [1, 2, 3]),
  (([1, 2, 3], 'b'), [1, 2, 3]),
  (([1, 2, 3], 'c'), [1, 2, 3])]
-/

#eval [[[1,4]],[[5]],[[3]],[[9,6],[4]],[[4,1]],[[4,9],[6]]].mergeSort


-- Alternative version using memoization for even better performance
structure DeterminizeState (Input1 : Type) [BEq Input1] [Hashable Input1] where
  visited : Std.HashSet (List (Nat))
  memo : Std.HashMap (List (Nat)) (List (((List Nat) × Input1) × (List Nat)))

def determinizeWithMemo {Input1 : Type} [DecidableEq Input1][BEq Input1] [Hashable Input1]
  (transition_function : (Nat) → Input1 → (List Nat))
  (alphabet : List Input1)
  (current_state : List Nat)
  (num_possible_states : Nat)
  (state : DeterminizeState Input1) :
  List (((List Nat) × Input1) × (List Nat)) × DeterminizeState Input1 :=

  if num_possible_states = 0 then ([], state)
  else
    if state.visited.contains current_state then
      ([], state)
    else Id.run do
      let new_visited := state.visited.insert current_state
      let mut new_state := { state with visited := new_visited }

      -- Compute current transitions
      let current_transitions := alphabet.map fun x =>
        let next_states := (current_state.map (fun y => transition_function y x)).flatten.mergeSort.dedup
        ((current_state, x), next_states)

      -- Process reachable states
      let reachable_states := (current_transitions.map (·.2)).dedup
      let mut all_transitions := current_transitions

      for next_state in reachable_states do
        if !new_state.visited.contains next_state then
          let (sub_transitions, updated_state) :=
          determinizeWithMemo transition_function alphabet next_state (num_possible_states-1) new_state
          all_transitions := all_transitions ++ sub_transitions
          new_state := updated_state

      -- Memoize result
      let final_state := { new_state with memo := new_state.memo.insert current_state all_transitions }
      (all_transitions, final_state)

-- User-friendly wrapper for memoized version
def determinizeMemo {Input1 : Type} [DecidableEq Input1] [BEq Input1] [Hashable Input1]
  (transition_function : Nat → Input1 → (List Nat))
  (alphabet : List Input1)
  (initial_state : List Nat)
  (max_states : Nat) :
  List (((List Nat) × Input1) × (List Nat)) :=
  let initial_state_obj : DeterminizeState Input1 := ⟨Std.HashSet.emptyWithCapacity, Std.HashMap.emptyWithCapacity⟩
  (determinizeWithMemo transition_function alphabet initial_state max_states initial_state_obj).fst


-- Version that returns the mapping as well
def assignNumbers' {State : Type} [DecidableEq State] [Hashable State] (fullList : List State) (subList : List State) :
  (List ℕ × List ℕ × Std.HashMap State ℕ) :=
  let uniqueElements := fullList.foldl (fun acc elem =>
    if elem ∈ acc then acc else acc ++ [elem]) []

  let mapping := Std.HashMap.ofList uniqueElements.zipIdx

  let lookupNumber (elem : State) : ℕ :=
    mapping[elem]!

  (fullList.map lookupNumber, subList.map lookupNumber, mapping)


def quant {Input : Type} [DecidableEq Input] [DecidableEq Input] [BEq Input] [Hashable Input]
  (M1 : DFA_Complete (List Input) (Nat)) (zero : List Input) (var : Char):
  DFA_Complete (List Input) (Nat) :=
  -- Remove second item from alphabet (check var and panic and stuff idkdk)
  let idx := M1.vars.findIdx (· = var)
  let new_alphabet := (M1.alphabet.map (fun x => x.eraseIdx idx)).dedup
  -- Transition function that given input for first tuple, returns list of all reachable states
  -- TODO: Save removed index, e.g. removed 0, calling [1], map insertIdx B2 at 0
  -- only problem is I need to know that it's B2 but fuck you I don't care (add new alphabet for alphabet)
  -- let step := fun st input => ((M1.alphabet.filter (fun (x,_) => x == input)).map (fun (_,y) => M1.automata.step st (input, y)))
  let step := fun st input => (M1.alphabet_vars.flatten.map (fun x => input.insertIdx idx x)).map (fun y => M1.automata.step st y)
  -- List of all possible states when determinizing the DFA (powerset)
  let num_possible_states := 2^(M1.states.length)
  -- Finds all states reachable from the starting state with 0*
  let start_states := (reachableWithOneOrMoreZeros [M1.automata.start] step zero (M1.states.length)).dedup.mergeSort
  -- TODO: call reason, get all states, new transition function, accept: any list with accept states in it
  let new_transitions := determinizeMemo step new_alphabet start_states num_possible_states
  let new_states := (new_transitions.map (fun ((x,_),_) => x)) ++ (new_transitions.map (fun ((_,_),z) => z))
  let die := new_states.dedup

  let states_acc := die.filter (fun x => M1.states_accept.any (fun y => x.contains y))
  let mappingas := (assignNumbers' die states_acc)
  let nu_states :=  mappingas.fst
  let nu_accept :=  mappingas.snd.fst
  let nu_transitions := new_transitions.map (fun ((x,y),z) => ((mappingas.snd.snd[x]!,y),mappingas.snd.snd[z]!))

  let dfa_list : DFA (List Input) (Nat) :={
    step := fun st input => let transt := (nu_transitions.filter (fun ((x,y),_) => st = x ∧ input = y))
    match transt.head? with
    | some ((x,y),z) => z
    | _ => nu_states.length+100
    start := match mappingas.snd.snd[start_states]? with
      | some x => x
      | none => nu_states.length+100
    accept := {p | nu_accept.contains p}
  }
  {states := nu_states, states_accept := nu_accept, alphabet := new_alphabet, alphabet_vars := M1.alphabet_vars, dead_state := none, vars := M1.vars.eraseIdx idx, automata := dfa_list}

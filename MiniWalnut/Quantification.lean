import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

import MiniWalnut.Automatons

/-

Quantification on cross-product DFA

  First add all the states reachable from the starting state with 0*

-/

-- Function to generate all possible states when determinizing a NFA
def combinations_rec {α : Type} (l : List α) : List (List α) :=
  match l with
  | [] => []
  | x :: xs =>
    let sub_combos := combinations_rec xs
    [x] :: sub_combos.map (x :: ·) ++ sub_combos

#eval (combinations_rec [1,2,3,4,5,6,7]).length

def number_of_possible_states (list_length : Nat) (num : Nat) : Nat :=
  if list_length > 0 then number_of_possible_states (list_length-1) (num*2 + 1) else num

#eval number_of_possible_states ([1,2,3,4,5,6,7].length) 0

#eval if (combinations_rec [1,2,3]).contains [1,3] then (combinations_rec [1,2,3]).erase [1,3] else (combinations_rec [1,2,3])

#eval (combinations_rec [1,2,3,4,5,6,7,8,9,10]).length

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

 def determinize {State1 Input1 : Type} [DecidableEq Input1] [DecidableEq State1] [BEq State1]
  (transition_function : State1 → Input1 → (List State1)) (alphabet : List Input1)
  (current_state : List State1) (num_possible_states : Nat) (previous_states : List (List State1)) : (List ((List State1 × Input1) × List State1) ) :=
  -- function that takes a list of states, a step function and an input
  -- and goes through the list
  let rec get_reachable_states (states : List State1) (step : State1 → Input1 → (List State1))
  (input : Input1) : (List (List State1)) :=
    states.map (fun x => step x input)

  if num_possible_states > 0 then
    let current_transitions := alphabet.map (fun x => ((current_state,x),(get_reachable_states current_state transition_function x).flatten.dedup))
    let current_reachable_states := (current_transitions.map (fun ((x,y),z) => z)).dedup
    let next_reachable_states := current_reachable_states.map (fun (x) =>
      if (previous_states.filter (fun w => w.isPerm x)).isEmpty
      then
      (determinize transition_function alphabet x (num_possible_states-1) (previous_states++[x]))
      else []
    )
    current_transitions ++ next_reachable_states.flatten
  else []

#eval ((determinize test_func test_alphabet [1,2] (number_of_possible_states [1,2,3].length 0)) [[1,2]]).length

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

def quant {State1 State2 Input : Type} [DecidableEq Input] [DecidableEq State1] [DecidableEq State2]
  (M1 : DFA_Complete (List Input) (State1 × State2)) (zero : List Input) (var : Char):
  DFA_Complete (List Input) (List (State1 × State2)) :=
  -- Remove second item from alphabet (check var and panic and stuff idkdk)
  let idx := M1.vars.findIdx (· = var)
  let new_alphabet := (M1.alphabet.map (fun x => x.eraseIdx idx)).dedup
  -- Transition function that given input for first tuple, returns list of all reachable states
  -- TODO: Save removed index, e.g. removed 0, calling [1], map insertIdx B2 at 0
  -- only problem is I need to know that it's B2 but fuck you I don't care (add new alphabet for alphabet)
  -- let step := fun st input => ((M1.alphabet.filter (fun (x,_) => x == input)).map (fun (_,y) => M1.automata.step st (input, y)))
  let step := fun st input => (M1.alphabet_vars.flatten.map (fun x => input.insertIdx idx x)).map (fun y => M1.automata.step st y)
  -- List of all possible states when determinizing the DFA
  let num_possible_states := number_of_possible_states M1.states.length 0
  -- Finds all states reachable from the starting state with 0*
  let start_states := (reachableWithOneOrMoreZeros {M1.automata.start} step zero M1.states.length).dedup
  -- TODO: call reason, get all states, new transition function, accept: any list with accept states in it
  let transitions := (determinize step new_alphabet start_states num_possible_states [start_states]).dedup
  let new_states := ((transitions.map (fun ((x,_),_) => x)) ++ (transitions.map (fun ((_,_),z) => z)))
  let dfa_list : DFA (List Input) (List (State1 × State2)) :={
    step := fun st input => let transt := (transitions.filter (fun ((x,y),_) => st = x ∧ input = y))
    match transt.head? with
    | some ((x,y),z) => z
    | _ => []
    start := start_states
    accept := {x | ∃ i, i ∈ M1.automata.accept ∧ x.contains i}
  }
  {states := new_states.dedup, alphabet := new_alphabet, alphabet_vars := M1.alphabet_vars, dead_state := none, vars := M1.vars.eraseIdx idx, automata := dfa_list}

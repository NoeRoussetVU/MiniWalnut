-- This module serves as the root of the `MiniWalnut` library.
-- Import modules here that should be built as part of the library.
import MiniWalnut.Basic
import MiniWalnut.Automatons
--import MiniWalnut.Quantification

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Powerset

/-

DFA and NFA definition with states and alphabet


  Fix up quant
  Make my own determinization function with finset or list and stuff


  Make DFAO class and define sequences with it
  Make it so you can use index with it kinda
  Heaven reached

-/

def legalHawkTuah : DFA B2 String := {
    step := fun x y => match x,y with
    | _, B2.zero => "ass"
    | _, B2.one => "love"
    start := "ass"
    accept := {x | x = "love"}
  }

#eval legalHawkTuah.eval [B2.zero,B2.zero]

def test_dfa : DFA_Complete B2 String :={
  alphabet := {B2.zero,B2.one}
  states := {"ass", "love"}
  dead_state := some "tuah"
  vars := ['a']
  alphabet_vars := [B2.zero, B2.one]
  automata := legalHawkTuah
}

#eval test_dfa.dead_state.get!

/-
  DFA Generation
-/

/-
  DFA accepting a given word
  Starting state = 0
  Accepting state = list length
  Dead state = list length + 1
-/

-- Create a DFA that accepts exactly one specific word
def createWordDFA {α : Type} [DecidableEq α] (word : List α) (zero : α): DFA α Nat where
  step := fun state symbol =>
    -- If we're at position i and see the expected symbol, advance to i+1
    -- Otherwise, go to a "dead" state (word.length + 1)
    if state < word.length && word[state]? = some symbol then
      state + 1
    else if state = 0 && symbol = zero then
      state
    else
      word.length + 1  -- Dead state
  start := 0
  accept := {word.length}  -- Only the final state after reading the complete word

-- Example DFA accetping abc
def acceptedWord : List (List B2) := [[B2.one], [B2.zero]]
def word_DFA := createWordDFA acceptedWord [B2.zero]

#eval word_DFA.eval []
#eval word_DFA.eval [[B2.zero]]
#eval word_DFA.eval [[B2.zero],[B2.zero],[B2.zero],[B2.one]]
#eval word_DFA.eval [[B2.one]]
#eval word_DFA.eval [[B2.one], [B2.zero]]
#eval word_DFA.eval [[B2.one],[ B2.zero], [B2.one]]
#eval word_DFA.eval [[B2.one], [B2.one]]

/-

Cross-product on created DFAs

  should think about how variables work a bit more

  M := a < b
  (Input1 × Input2) [a,b]
  L := a = b
  (Input1 × Input2) [a,b]

  M | L
  (Input1 × Input2) [a,b]

  [a,b] ++ [a,b] dedup = [a,b]

  what is going on? what are you doing?

-/

-- DFA accepting a = 1

def oneDfa := createWordDFA [[B2.one]] [B2.zero]

def dfa_one : DFA_Complete (List B2) (Nat) := {
  states := (List.range ([1].length + 2))
  alphabet := [[B2.zero], [B2.one]]
  dead_state := some ([1].length + 1)
  vars := ['a']
  alphabet_vars := [[B2.zero], [B2.one]]
  automata := oneDfa
}

#eval dfa_one.states
#eval dfa_one.dead_state
#eval dfa_one.automata.eval [[B2.zero], [B2.zero], [B2.one]] = dfa_one.dead_state
#eval dfa_one.automata.eval [[B2.zero], [B2.zero], [B2.one], [B2.one]] = dfa_one.dead_state


-- DFA accepting b = 10

def twoDfa := createWordDFA [[B2.one], [B2.zero]] [B2.zero]

def dfa_two : DFA_Complete (List B2) (Nat) := {
  states := (List.range ([1,0].length + 2))
  alphabet := [[B2.zero], [B2.one]]
  dead_state := some ([1,0].length + 1)
  vars := ['b']
  alphabet_vars := [[B2.zero], [B2.one]]
  automata := twoDfa
}


-- DFA accepting c > 2

def banana_muun : DFA (List B2) Nat := {
    step := fun x y => match x,y with
    | 0, [B2.zero] => 0
    | 0, [B2.one] => 1
    | 1, [B2.zero] => 2
    | 1, [B2.one] => 3
    | 2, _ => 3
    | 3, _ => 3
    | _, _ => 4
    start := 0
    accept := {x | x = 3}
  }

def dfa_mt_two : DFA_Complete (List B2) Nat :={
  alphabet := [[B2.zero],[B2.one]]
  states := [0, 1, 2, 3]
  dead_state := none
  vars := ['a']
  alphabet_vars := [[B2.zero], [B2.one]]
  automata := banana_muun
}

-- function that finds indices in l2 of elements from l1
def trash (l1 : List Char) (l2 : List Char) : List Nat :=
match l1 with
| [] => []
| x :: [] => [l2.findIdx (· = x)]
| x :: xs => [l2.findIdx (· = x)] ++ (trash xs l2)

#eval (trash ['a','b'] ['a','b']).filter (fun x => x < 2)

-- actually do something else, I have [[1,1],[1,2],[2,2]] and indices to remove 0
-- I want [1,2,2].dedup = [1,2]
def and_tuah {t : Type} [Inhabited t] (alph : List t) (indices : List Nat) (indices_to_remove : List Nat) : List t :=
match indices with
| [] => []
| x :: [] => if indices_to_remove.contains x then [] else [alph[x]!]
| x :: xs => if indices_to_remove.contains x then and_tuah alph xs indices_to_remove else [alph[x]!] ++ (and_tuah alph xs indices_to_remove)

#eval and_tuah [B2.zero, B2.one] [0,1] [1,3]

def heeeelp {T T' : Type} (wan : T) (tsu : List T') : List (T × T') :=
match tsu with
| [] => []
| y :: [] => [(wan, y)]
| y :: ys => [(wan,y)] ++ heeeelp wan ys

#eval heeeelp B2.zero [B2.zero, B2.one]

def combinations_for_list {T T' : Type } (ass : List T) (titties : List T') : List (T × T') :=
match ass with
| x :: xs => (heeeelp x titties) ++ combinations_for_list xs titties
| _ => []

#eval combinations_for_list dfa_one.states dfa_two.states

def gelp {Input : Type} (wan : List Input) (tsu : List (List Input)) : List (List Input) :=
match tsu with
| [] => []
| y :: [] => [wan ++ y]
| y :: ys => [wan ++ y] ++ gelp wan ys

#eval gelp [B2.zero] [[B2.zero], [B2.one]]

def get_new_alphabet {Input : Type} (alpha_1 : List (List Input)) (alpha_2 : List (List Input))
: List (List Input) :=
match alpha_1 with
| x :: xs => (gelp x alpha_2) ++ get_new_alphabet xs alpha_2
| _ => []

#eval get_new_alphabet dfa_one.alphabet dfa_two.alphabet


#eval (trash ['a','b','c'] ['a','b','d']).filter (fun x => x < ['a','b','d'].length)

#eval (get_new_alphabet [[0,0,0],[0,0,1],[0,1,0],[1,0,1],[1,1,1]] (([[0,0,0],[0,0,1],[0,1,0],[1,0,1],[1,1,1]]).map (fun x => and_tuah x (List.range x.length) [0,1]))).dedup


-- Cross product of two DFAs
def DFA_Complete.crossProduct {State1 State2 Input : Type} [Inhabited Input] [DecidableEq Input] (M1 : DFA_Complete (List Input) State1) (conj : binary_logical_ops) (M2 : DFA_Complete (List Input) State2)
 : DFA_Complete (List Input) (State1 × State2) where
  states := combinations_for_list M1.states M2.states
  -- Check both alphabets, any of the same variable = get the index,
  -- and remove those from M2.alphabet
  alphabet :=
  let indices_to_remove := (trash M1.vars M2.vars).filter (fun x => x < M1.vars.length)
  (get_new_alphabet M1.alphabet (M2.alphabet.map (fun x => and_tuah x (List.range x.length) indices_to_remove))).dedup
  dead_state := match M1.dead_state, M2.dead_state with
                | _, none => none
                | none, _ => none
                |some n, some y => some (n, y)
  vars := (M1.vars ++ M2.vars).dedup.mergeSort
  alphabet_vars := M1.alphabet_vars
  automata := {
    -- Transition function pairs the functions of the two DFAs
    -- TODO: add dead state if list length is bad
    step := fun (q1, q2) a =>
      let varias : Std.HashMap Char Input := Std.HashMap.ofList (((M1.vars ++ M2.vars).dedup.mergeSort).zip a)
      (M1.automata.step q1 (M1.vars.map (fun x => varias[x]!)), M2.automata.step q2 (M2.vars.map (fun x => varias[x]!)))
    -- Starting state is the pair of starting states
    start := (M1.automata.start, M2.automata.start)
    -- Accepting states are pairs where both components are accepting for AND
    -- either component is accepting for OR
    accept := match conj with
          | binary_logical_ops.and => {p | p.fst ∈ M1.automata.accept ∧ p.snd ∈ M2.automata.accept}
          | binary_logical_ops.or => {p | p.fst ∈ M1.automata.accept ∨ p.snd ∈ M2.automata.accept}
          | binary_logical_ops.exclusive_dinjuction => {p | (p.fst ∈ M1.automata.accept ∧ p.snd ∉ M2.automata.accept) ∨ (p.fst ∉ M1.automata.accept ∧ p.snd ∈ M2.automata.accept)}
          | binary_logical_ops.impl => {p | Not (p.fst ∈ M1.automata.accept ∧ p.snd ∉ M2.automata.accept)}
          | binary_logical_ops.equiv => {p | Not (p.fst ∈ M1.automata.accept ∧ p.snd ∉ M2.automata.accept) ∧ Not ( p.snd ∈  M2.automata.accept ∧ p.fst ∉ M1.automata.accept)}
  }

-- accepts a = 1 & b = 2
def intersectionDFATwo := dfa_one.crossProduct binary_logical_ops.or dfa_two

#eval intersectionDFATwo.alphabet
#eval intersectionDFATwo.states
#eval intersectionDFATwo.dead_state
#eval intersectionDFATwo.vars

#eval intersectionDFATwo.automata.eval [[B2.zero,B2.zero]]
#eval intersectionDFATwo.automata.eval [[B2.zero,B2.one]]
#eval intersectionDFATwo.automata.eval [[B2.one,B2.one]]
#eval intersectionDFATwo.automata.eval [[B2.zero,B2.one],[B2.one,B2.zero]]
#eval intersectionDFATwo.automata.eval [[B2.zero,B2.one],[B2.one,B2.one]]
#eval intersectionDFATwo.automata.eval [[B2.one,B2.one],[B2.one,B2.one],[B2.one,B2.zero]]


-- accepts a = 1 | a > 2
def intersectionDFATwoSame := dfa_one.crossProduct binary_logical_ops.or dfa_mt_two

#eval intersectionDFATwoSame.alphabet
#eval intersectionDFATwoSame.states
#eval intersectionDFATwoSame.dead_state
#eval intersectionDFATwoSame.vars

#eval intersectionDFATwoSame.automata.eval []
#eval intersectionDFATwoSame.automata.eval [[B2.zero]]
#eval intersectionDFATwoSame.automata.eval [[B2.one]]
#eval intersectionDFATwoSame.automata.eval [[B2.one],[B2.zero]]

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

#eval combinations_rec [1,2,3]
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


#eval intersectionDFATwo.automata.step (0,1) [B2.zero,B2.one]

#eval intersectionDFATwo.alphabet.map (fun x => intersectionDFATwo.automata.step (0,0) (x))
#eval intersectionDFATwo.states.map (fun x => intersectionDFATwo.alphabet.map (fun y => intersectionDFATwo.automata.step x y))


#eval [1,2] == [2,1]
#eval [[1,2,10],[8,9,3]].flatten.mergeSort

/-- Check if two lists have exactly the same elements (same multiset) -/
def same_elements {T : Type} [DecidableEq T] (l1 l2 : List T) : Bool :=
  l1.toFinset = l2.toFinset

#eval ([[1,2,3], [4,5,6], [1,4,8]].filter (fun x => same_elements x [4,1,8]))
#eval ([1].filter (fun x => x == 2)).isEmpty


/-

  Determinization: Build a list of all states,
  Input: start states list, alphabet and dfa
  for each alphabet input, go through each start state to build a new state
  then if that state isn't in list of all states, add that state to list of all states,
  and use it as new base state
  otherwise end here and move on to new input

  I mean it's just depth-first search basically

-/

-- function that takes a list of states, a step function and an input
-- and goes through the list
def single_inp {State1 Input1 : Type} [DecidableEq Input1] [DecidableEq State1]
  (states : List State1) (step : State1 → Input1 → (List State1)) (input : Input1) :
  (List (List State1)) :=
  states.map (fun x => step x input)

def test_states : List Int := [1,2,3]
def test_func : Int → Char → List Int
  | 1, 'a' => [2, 3]
  | 2, 'a' => [1]
  | 2, 'b' => [1, 2]
  | 3, 'a' => [1, 3]
  | 3, 'c' => [3]
  | _, _ => [1,2,3]
def test_input : Char := 'a'
def test_alphabet : List Char := ['a','b','c']

#eval single_inp test_states test_func test_input
#eval (single_inp test_states test_func test_input).flatten.dedup.mergeSort


partial def reason {State1 Input1 : Type} [DecidableEq Input1] [DecidableEq State1] [BEq State1]
  (funk : State1 → Input1 → (List State1)) (alphabet : List Input1)
  (current_state : List State1) (possible_states : List (List State1)) : (List ((List State1 × Input1) × List State1) ) :=
  match possible_states with
  | [] => []
  | p =>  let newb := alphabet.map (fun x => ((current_state,x),(single_inp current_state funk x).flatten.dedup))
          let rock := newb.map (fun ((x,y),z) =>
            if p.contains z then
            (reason funk alphabet z (p.erase z))
            else []
          )
          newb ++ rock.flatten

#eval (reason test_func test_alphabet [1] (combinations_rec test_states)).dedup
def epibmeal := (reason test_func test_alphabet [1] (combinations_rec test_states)).dedup

#eval (epibmeal.filter (fun ((x,y),_) => [1] = x ∧ 'a' = y)).head!.snd

def ground (one : List Int) (two : Char) : List Int :=
(epibmeal.filter (fun ((x,y),_) => one = x ∧ two = y)).head!.snd

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
  (M1 : DFA_Complete (List Input) (State1 × State2)) (zero : List Input) (wrap : Char):
  DFA_Complete (List Input) (List (State1 × State2)) :=
  -- Remove second item from alphabet (check var and panic and stuff idkdk)
  -- TODO: same principle as crossproduct, ez pz
  let idx := M1.vars.findIdx (· = wrap)
  let new_alphabet := (M1.alphabet.map (fun x => x.eraseIdx idx)).dedup
  -- Transition function that given input for first tuple, returns list of all reachable states
  -- TODO: Save removed index, e.g. removed 0, calling [1], map insertIdx B2 at 0
  -- only problem is I need to know that it's B2 but fuck you I don't care (add new alphabet for alphabet)
  -- let step := fun st input => ((M1.alphabet.filter (fun (x,_) => x == input)).map (fun (_,y) => M1.automata.step st (input, y)))
  let step := fun st input => (M1.alphabet_vars.flatten.map (fun x => input.insertIdx idx x)).map (fun y => M1.automata.step st y)
  -- List of all possible states when determinizing the DFA
  let possible_states := combinations_rec M1.states
  -- Finds all states reachable from the starting state with 0*
  let start_states := (reachableWithOneOrMoreZeros {M1.automata.start} step zero M1.states.length).dedup
  -- TODO: call reason, get all states, new transition function, accept: any list with accept states in it
  let transitions := reason step new_alphabet start_states possible_states
  let new_states := (transitions.map (fun ((x,_),_) => x)).dedup
  let dfa_list : DFA (List Input) (List (State1 × State2)) :={
    step := fun st input => let transt := (transitions.filter (fun ((x,y),_) => st = x ∧ input = y))
    match transt.head? with
    | some ((x,y),z) => z
    | _ => []
    start := start_states
    accept := {x | ∃ i, i ∈ M1.automata.accept ∧ x.contains i}
  }
  {states := new_states, alphabet := new_alphabet, alphabet_vars := M1.alphabet_vars, dead_state := none, vars := ['a'], automata := dfa_list}

  def love_all := quant intersectionDFATwo [B2.zero] 'a'

  #eval love_all.states
  #eval love_all.alphabet

  #eval love_all.automata.eval []
  #eval love_all.automata.eval [[B2.zero]]
  #eval love_all.automata.eval [[B2.one]]

  #eval love_all.automata.eval [[B2.zero], [B2.one]]
  #eval love_all.automata.eval [[B2.zero], [B2.one], [B2.zero]]
  #eval love_all.automata.eval [[B2.zero],[ B2.one], [B2.one]]

  #eval love_all.automata.eval [[B2.zero], [B2.one], [B2.zero], [B2.zero]]
  #eval love_all.automata.eval [[B2.zero], [B2.one], [B2.zero], [B2.one]]

  #eval love_all.automata.eval [[B2.one], [B2.zero]]
  #eval love_all.automata.eval [[B2.one], [B2.one]]
  #eval love_all.automata.eval [[B2.one], [B2.one], [B2.zero]]
  #eval love_all.automata.eval [[B2.one], [B2.one], [B2.one]]

  def tututuah := quant intersectionDFATwoSame [B2.zero] 'a'

  #eval tututuah.states
  #eval tututuah.alphabet

  #eval tututuah.automata.eval []
  #eval tututuah.automata.eval [[B2.zero]]
  #eval tututuah.automata.eval [[B2.one]]

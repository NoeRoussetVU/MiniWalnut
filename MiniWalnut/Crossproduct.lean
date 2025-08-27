import MiniWalnut.Automatons

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

-- function that finds indices in l2 of elements from l1
def get_idx_same_elements (l1 : List Char) (l2 : List Char) : List Nat :=
match l1 with
| [] => []
| x :: [] => [l2.findIdx (· = x)]
| x :: xs => [l2.findIdx (· = x)] ++ (get_idx_same_elements xs l2)

#eval (get_idx_same_elements ['a','b'] ['a','b']).filter (fun x => x < 2)

-- actually do something else, I have [[1,1],[1,2],[2,2]] and indices to remove 0
-- I want [1,2,2]
def remove_indices {t : Type} [Inhabited t] (alph : List t) (indices : List Nat) (indices_to_remove : List Nat) : List t :=
match indices with
| [] => []
| x :: [] => if indices_to_remove.contains x then [] else [alph[x]!]
| x :: xs => if indices_to_remove.contains x then remove_indices alph xs indices_to_remove else [alph[x]!] ++ (remove_indices alph xs indices_to_remove)

#eval remove_indices [B2.zero, B2.one] [0,1] [1,3]

-- Get the combinations of states
def combinations_for_list {T T' : Type } (M1_states : List T) (M2_states : List T') : List (T × T') :=
let rec combinations_for_list_help (M1_state : T) (M2_states' : List T') : List (T × T') :=
  match M2_states' with
  | [] => []
  | y :: [] => [(M1_state, y)]
  | y :: ys => [(M1_state,y)] ++ combinations_for_list_help M1_state ys

match M1_states with
| x :: xs => (combinations_for_list_help x M2_states) ++ combinations_for_list xs M2_states
| _ => []

#eval combinations_for_list [1,2,3,4,5] ['a','b','c']

def get_new_alphabet {Input : Type} (alpha_1 : List (List Input)) (alpha_2 : List (List Input))
: List (List Input) :=
let rec get_new_alphabet_help (alpha_1_single : List Input) (alpha_2' : List (List Input)) : List (List Input) :=
  match alpha_2' with
  | [] => []
  | y :: [] => [alpha_1_single ++ y]
  | y :: ys => [alpha_1_single ++ y] ++ get_new_alphabet_help alpha_1_single ys

match alpha_1 with
| x :: xs => (get_new_alphabet_help x alpha_2) ++ get_new_alphabet xs alpha_2
| _ => []

--#eval get_new_alphabet dfa_one.alphabet dfa_two.alphabet


#eval (get_idx_same_elements ['a','b','c'] ['a','b','d']).filter (fun x => x < ['a','b','d'].length)

#eval (get_new_alphabet [[0,0,0],[0,0,1],[0,1,0],[1,0,1],[1,1,1]] (([[0,0,0],[0,0,1],[0,1,0],[1,0,1],[1,1,1]]).map (fun x => remove_indices x (List.range x.length) [0,1]))).dedup


-- Cross product of two DFAs
def DFA_Complete.crossProduct {State1 State2 Input : Type} [Inhabited Input] [DecidableEq Input] (M1 : DFA_Complete (List Input) State1) (conj : binary_logical_ops) (M2 : DFA_Complete (List Input) State2)
 : DFA_Complete (List Input) (State1 × State2) where
  states := combinations_for_list M1.states M2.states
  -- Check both alphabets, any of the same variable = get the index,
  -- and remove those from M1.alphabet
  alphabet :=
  let indices_to_remove := (get_idx_same_elements M1.vars M2.vars).filter (fun x => x < M1.vars.length)
  (get_new_alphabet M1.alphabet (M2.alphabet.map (fun x => remove_indices x (List.range x.length) indices_to_remove))).dedup
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

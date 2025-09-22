import MiniWalnut.Basic
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

#eval (get_idx_same_elements ['k','n'] ['i','k','n']).filter (fun x => x < 3)

-- actually do something else, I have [[1,1],[1,2],[2,2]] and indices to remove 0
-- I want [1,2,2]
def remove_indices {t : Type} [Inhabited t] (alph : List t) (indices : List Nat) (indices_to_remove : List Nat) : List t :=
  match indices with
  | [] => []
  | x :: [] => if indices_to_remove.contains x then [] else [alph[x]!]
  | x :: xs => if indices_to_remove.contains x then remove_indices alph xs indices_to_remove else [alph[x]!] ++ (remove_indices alph xs indices_to_remove)

#eval remove_indices [B2.zero, B2.one, B2.one] [0,1,2] [2]

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

#eval combinations_for_list [[1,2],[3,4],[5]] [['a'],['b','c']]

--#eval get_new_alphabet dfa_one.alphabet dfa_two.alphabet


#eval (get_idx_same_elements ['a','b','c'] ['a','b','d']).filter (fun x => x < ['a','b','d'].length)

#eval (get_new_alphabet [[0,0,0],[0,0,1],[0,1,0],[1,0,1],[1,1,1]] (([[0,0,0],[0,0,1],[0,1,0],[1,0,1],[1,1,1]]).map (fun x => remove_indices x (List.range x.length) [0,1]))).dedup


-- Version that returns the mapping as well
def assignNumbers {State : Type} [DecidableEq State] [Hashable State] (fullList : List State) (subList : List State) :
  (List ℕ × List ℕ × Std.HashMap State ℕ) :=
  let uniqueElements := fullList.foldl (fun acc elem =>
    if elem ∈ acc then acc else acc ++ [elem]) []

  let mapping := Std.HashMap.ofList uniqueElements.zipIdx

  let lookupNumber (elem : State) : ℕ :=
    mapping[elem]!

  (fullList.map lookupNumber, subList.map lookupNumber, mapping)


def testMap := Std.HashMap.ofList [((0,0),0),((1,1),1),((0,1),2),((1,0),3),((2,2),4)]
def testA := [B2.zero,B2.one]
def unc (st : Nat × Nat)  (ink : B2) : (Nat × Nat)  :=
  match st, ink with
  | (0,0), B2.zero => (0,1)
  | (0,0), B2.one => (1,1)
  | (1,0), B2.one => (0,0)
  | (1,0), B2.zero => (1,0)
  | (1,1), B2.one => (0,1)
  | (0,1), B2.zero => (0,0)
  | _, _ => (2,2)


--#eval getTransitions testMap testA unc

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

def get_accepting_states {Input : Type} (states : List (Nat × Nat))
(M1 : DFA_Complete (List Input) Nat) (conj : binary_ops) (M2 : DFA_Complete (List Input) Nat) : List (Nat × Nat) :=
  match conj with
  | binary_ops.logical_op l => match l with
        | l_ops.and => states.filter (fun (x,y) => M1.states_accept.contains x ∧ M2.states_accept.contains y)
        | l_ops.or => states.filter (fun (x,y) => M1.states_accept.contains x ∨ M2.states_accept.contains y)
        | l_ops.exclusive_dinjuction => states.filter (fun (x,y) => (M1.states_accept.contains x ∧ !M2.states_accept.contains y) ∨ (!M1.states_accept.contains x ∧ M2.states_accept.contains y) )
        | l_ops.impl => states.filter (fun (x,y) => !(M1.states_accept.contains x ∧ !M2.states_accept.contains y) )
        | l_ops.equiv => states.filter (fun (x,y) => !(M1.states_accept.contains x ∧ !M2.states_accept.contains y) ∨ !(!M1.states_accept.contains x ∧ M2.states_accept.contains y) )
  | binary_ops.comparison_op c => match c with
        | b_ops.equals => states.filter (fun (x,y) => x == y)
        | b_ops.less_than => states.filter (fun (x,y) => x < y)
        | b_ops.more_than => states.filter (fun (x,y) => x > y)

-- Cross product of two DFAs
def DFA_Complete.crossProduct {Input : Type} [Inhabited Input] [DecidableEq Input]
(M1 : DFA_Complete (List Input) Nat) (conj : binary_ops) (M2 : DFA_Complete (List Input) Nat)
 : DFA_Complete (List Input) Nat :=
  let states := combinations_for_list M1.states M2.states
  -- Check both alphabets, any of the same variable = get the index,
  -- and remove those from M1.alphabet
  let states_accept := get_accepting_states states M1 conj M2
  let mappingas := (assignNumbers states states_accept)
  let new_states :=  mappingas.fst
  let new_states_accept :=  mappingas.snd.fst
  let alphabet :=
  let indices_to_remove := (get_idx_same_elements M1.vars M2.vars).filter (fun x => x < M2.vars.length)
  (get_new_alphabet M1.alphabet (M2.alphabet.map (fun x => remove_indices x (List.range x.length) indices_to_remove))).dedup
  let dead_state := match M1.dead_state, M2.dead_state with
                | _, none => none
                | none, _ => none
                |some n, some y => some (mappingas.snd.snd[(n,y)]!)
  let vars := (M1.vars ++ M2.vars).dedup.mergeSort
  let alphabet_vars := M1.alphabet_vars

  let temp_funk := fun (st : (Nat × Nat)) (a : (List Input)) =>
      let varias : Std.HashMap Char Input := Std.HashMap.ofList (vars.zip a)
      ((M1.automata.step st.fst (M1.vars.map (fun x => varias[x]!))),  (M2.automata.step st.snd (M2.vars.map (fun x => varias[x]!))))

  let og_states := mappingas.snd.snd.keys
  let transitions := og_states.map (fun x => alphabet.map (fun z => ((mappingas.snd.snd[(x)]!, z), mappingas.snd.snd[(temp_funk (x) z)]! )))
  let tf := transitions.flatten

  let automata := {
    -- Transition function pairs the functions of the two DFAs
    -- TODO: add dead state if list length is bad
    step := fun st input =>
    let tr := tf.filter (fun ((x,y),_) => st = x ∧ input = y)
    match tr.head? with
    | some ((x,y),z) => z
    | _ => match dead_state with
          | some w => w
          | _ => new_states.length+100
    -- Starting state is the pair of starting states
    start :=  mappingas.snd.snd[(M1.automata.start,M2.automata.start)]!
    -- Accepting states are pairs where both components are accepting for AND
    -- either component is accepting for OR
    accept := {p | states_accept.contains p}
  }
  {states := new_states, states_accept := (new_states_accept), alphabet := alphabet, alphabet_vars := alphabet_vars, dead_state := dead_state, vars := vars, automata := automata}

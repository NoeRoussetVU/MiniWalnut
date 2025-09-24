import MiniWalnut.Automata

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA


-- Logical Operators for Cross Product operations
inductive l_ops where
  | and
  | or
  | exclusive_dinjuction
  | impl
  | equiv

-- Comparison Operators for automatic language automata building
inductive c_ops where
  | equals
  | less_than
  | more_than

inductive binary_ops where
  | logical_op : l_ops → binary_ops
  | comparison_op : c_ops → binary_ops

-- function that finds indices in l2 of elements from l1
def get_idx_same_elements (l1 : List Char) (l2 : List Char) : List Nat :=
  match l1 with
  | [] => []
  | x :: [] => [l2.findIdx (· = x)]
  | x :: xs => [l2.findIdx (· = x)] ++ (get_idx_same_elements xs l2)

#eval (get_idx_same_elements ['k','n'] ['i','k','n']).filter (fun x => x < 3)

def remove_indices {t : Type} [Inhabited t] (alph : List t) (indices : List Nat) (indices_to_remove : List Nat) : List t :=
  match indices with
  | [] => []
  | x :: [] => if indices_to_remove.contains x then [] else [alph[x]!]
  | x :: xs => if indices_to_remove.contains x then remove_indices alph xs indices_to_remove else [alph[x]!] ++ (remove_indices alph xs indices_to_remove)

#eval remove_indices [B2.zero, B2.one, B2.one] [0,1,2] [2]

/-

Cross-product on created DFAs

  M := a < b
  (Input1 × Input2) [a,b]
  L := a = b
  (Input1 × Input2) [a,b]

  M | L
  (Input1 × Input2) [a,b]

  [a,b] ++ [a,b] dedup = [a,b]

-/

def get_accepting_states {Input : Type} (states : List (Nat × Nat))
(M1 : DFA_extended (List Input) Nat) (conj : binary_ops) (M2 : DFA_extended (List Input) Nat) : List (Nat × Nat) :=
  match conj with
  | binary_ops.logical_op l => match l with
        | l_ops.and => states.filter (fun (x,y) => M1.states_accept.contains x ∧ M2.states_accept.contains y)
        | l_ops.or => states.filter (fun (x,y) => M1.states_accept.contains x ∨ M2.states_accept.contains y)
        | l_ops.exclusive_dinjuction => states.filter (fun (x,y) => (M1.states_accept.contains x ∧ !M2.states_accept.contains y) ∨ (!M1.states_accept.contains x ∧ M2.states_accept.contains y) )
        | l_ops.impl => states.filter (fun (x,y) => !(M1.states_accept.contains x ∧ !M2.states_accept.contains y) )
        | l_ops.equiv => states.filter (fun (x,y) => !(M1.states_accept.contains x ∧ !M2.states_accept.contains y) ∨ !(!M1.states_accept.contains x ∧ M2.states_accept.contains y) )
  | binary_ops.comparison_op c => match c with
        | c_ops.equals => states.filter (fun (x,y) => x == y)
        | c_ops.less_than => states.filter (fun (x,y) => x < y)
        | c_ops.more_than => states.filter (fun (x,y) => x > y)

-- Cross product of two DFAs
def crossproduct' {Input : Type} [Inhabited Input] [DecidableEq Input]
(M1 : DFA_extended (List Input) Nat) (conj : binary_ops) (M2 : DFA_extended (List Input) Nat)
 : DFA_extended (List Input) (Nat × Nat) :=
  let states := (M1.states.map (fun x => M2.states.map (fun y => (x,y)))).flatten
  -- Check both alphabets, any of the same variable = get the index,
  -- and remove those from M1.alphabet
  let states_accept := get_accepting_states states M1 conj M2
  let alphabet :=
  let indices_to_remove := (get_idx_same_elements M1.vars M2.vars).filter (fun x => x < M2.vars.length)
  let removed_indices_alphabet := (M2.alphabet.map (fun x => remove_indices x (List.range x.length) indices_to_remove)).dedup
  (M1.alphabet.map (fun x => removed_indices_alphabet.map (fun y => x ++ y))).flatten
  let dead_state := match M1.dead_state, M2.dead_state with
                | _, none => none
                | none, _ => none
                |some n, some y => some ((n,y))
  let vars := (M1.vars ++ M2.vars).dedup.mergeSort
  let alphabet_vars := M1.alphabet_vars

  let temp_funk := fun (st : (Nat × Nat)) (a : (List Input)) =>
      let varias : Std.HashMap Char Input := Std.HashMap.ofList (vars.zip a)
      ((M1.automata.step st.fst (M1.vars.map (fun x => varias[x]!))),  (M2.automata.step st.snd (M2.vars.map (fun x => varias[x]!))))

  let automata := {
    -- Transition function pairs the functions of the two DFAs
    -- TODO: add dead state if list length is bad
    step := fun st input => temp_funk st input
    -- Starting state is the pair of starting states
    start :=  (M1.automata.start,M2.automata.start)
    -- Accepting states are pairs where both components are accepting for AND
    -- either component is accepting for OR
    accept := {p | states_accept.contains p}
  }
  {states := states, states_accept := states_accept, alphabet := alphabet, alphabet_vars := alphabet_vars, dead_state := dead_state, vars := vars, automata := automata}

-- Cross product of two DFAs
def crossproduct {Input : Type} [Inhabited Input] [DecidableEq Input]
(M1 : DFA_extended (List Input) Nat) (conj : binary_ops) (M2 : DFA_extended (List Input) Nat)
 : DFA_extended (List Input) Nat :=
  change_states_names (crossproduct' M1 conj M2)

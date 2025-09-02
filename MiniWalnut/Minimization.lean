import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

import MiniWalnut.Basic
import MiniWalnut.Automatons
import MiniWalnut.Crossproduct
import MiniWalnut.Quantification

/-
def help1 fst_states snd_states alphabet funk : List (List State)
  match alphabet with
  [] => []
  x :: xs =>
    let reached := fst_states.partition (fun y => !snd_states.contains(funk y x) )
    if reached.snd is empty
    then help1 fst_states snd_states xs funk
    else [reached.fst] ++ [reached.snd]
-/

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

def minimization {State1 Input1 : Type} [BEq State1] (states : List (List State1)) (alphabet : List Input1)
(funk : State1 → Input1 → State1) (n_of_states : Nat) : List (List State1) :=
  if n_of_states > 0 then
    match states with
    | [] => states
    | x :: xs =>
      let new_states := help1 x xs alphabet funk
      if new_states.isEmpty then
      minimization xs alphabet funk n_of_states
      else minimization new_states alphabet funk (n_of_states-1)
  else states

#eval minimization ([test_state1] ++ [test_state2]) test_alpha test_f 5

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

def a_bc_and_b_equals_4' := a_equals_b_p_c'.crossProduct binary_logical_ops.and b_equals_4'
#eval a_bc_and_b_equals_4'.vars
#eval a_bc_and_b_equals_4'.alphabet

#eval minimization ([test1] ++ [test2]) test3 test4 4

#eval minimization ([[(0, 0), (0, 1), (0, 2), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)]] ++ [[(0,3)]]) a_bc_and_b_equals_4'.alphabet a_bc_and_b_equals_4'.automata.step 11

def nu_states := minimization ([[(0, 0), (0, 1), (0, 2), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)]] ++ [[(0,3)]]) a_bc_and_b_equals_4'.alphabet a_bc_and_b_equals_4'.automata.step 10

def nu_function (st : (List (ℕ × ℕ))) (a : List B2) : (List (ℕ × ℕ)) :=
if nu_states.contains st
then
  let res := a_bc_and_b_equals_4'.automata.step st.head! a
  (nu_states.filter (fun x => x.contains res)).head!
else []

#eval nu_function [(0, 4), (1, 1), (1, 2), (1, 3), (1, 4)] [B2.zero, B2.zero, B2.zero]
#eval nu_function [(0, 4), (1, 1), (1, 2), (1, 3), (1, 4)] [B2.zero, B2.one, B2.zero]

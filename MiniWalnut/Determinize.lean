import Leanp.Basic
import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Basic
import Std.Data.HashMap

/-

DETERMINIZATION NOW NOW IT'S HERE IT'S NOW IT'S RIGHT NOW LET'S GO DETERMINIZE

for each start state, check all transitions,
list of reached states in new start state
for each, check transitions and make new states with list and check the same for those

-/

/-

Determinization: depth-first exploration?
q0 λ = {q0,q1} q0 a = q1, q0 b = {q1,q2}
q1 λ = q1 q1 a = z, q1 b = {q1,q2}
q2 λ = q2  q2 a = q0, q2 b = z


1st: check all transitions for all states --> depth_search map
2nd: combine starting states into one, and combine transitions for all the states its made up of
3rd: do the same for the states obtained from that until...?

-/
-- given list of states and alphabet and transition function find all reachable states for each xD
def depth_search {State1 Input1 : Type} [DecidableEq Input1] [DecidableEq State1] (s : List State1) (a : List Input1) (t : State1 → Input1 → (List State1)) :  List (List (List State1)) :=
match s with
| [] => []
| sx :: [] => [((a).map (fun x => t sx x)).dedup]
| sx :: sl =>
  let reached:= ((a).map (fun x => t sx x)).dedup
  let ret := [reached.dedup] ++ depth_search sl a t
  ret

#eval depth_search hwat.states hwat.alphabet hwat.step

-- given list of states and alphabet and transition function find all reachable states for each xD
def depth_search_map {State1 Input1 : Type} [BEq State1] [Hashable State1] [BEq Input1] [Hashable Input1] [DecidableEq Input1] [DecidableEq State1]
(s : List State1) (a : List Input1) (t : State1 → Input1 → (List State1)) :
Std.HashMap State1 (Std.HashMap Input1 (List State1)) :=
match s with
| [] => Std.HashMap.emptyWithCapacity
| sx :: [] => Std.HashMap.ofList [(sx, Std.HashMap.ofList ((a).map (fun x => (x, (t sx x)))).dedup)]
| sx :: sl =>
  let reached:= Std.HashMap.ofList [(sx, Std.HashMap.ofList ((a).map (fun x => (x, (t sx x)))).dedup)]
  let ret := reached.union (depth_search_map sl a t)
  ret

#eval depth_search_map hwat.states hwat.alphabet hwat.step
def reachability_map : Std.HashMap (String × String) (Std.HashMap Int (List (String × String)))
:= depth_search_map hwat.states hwat.alphabet hwat.step

/-
Std.HashMap.ofList
  [(("b", "b"),
    Std.HashMap.ofList [(0, [("z", "c"), ("z", "z")]), (1, [("z", "c"), ("z", "z")])]),
  (("z", "z"),
    Std.HashMap.ofList [(0, [("z", "z")]), (1, [("z", "z")])]),
  (("z", "c"),
    Std.HashMap.ofList [(0, [("z", "z")]), (1, [("z", "z")])]),
  (("b", "a"),
    Std.HashMap.ofList [(0, [("z", "a"), ("z", "b")]), (1, [("z", "a"), ("z", "b")])]),
  (("b", "z"),
    Std.HashMap.ofList [(0, [("z", "z")]), (1, [("z", "z")])]),
  (("z", "a"),
    Std.HashMap.ofList [(0, [("z", "a"), ("z", "b")]), (1, [("z", "a"), ("z", "b")])]),
  (("a", "c"),
    Std.HashMap.ofList [(0, [("a", "z")]), (1, [("b", "z")])]),
  (("z", "b"),
    Std.HashMap.ofList [(0, [("z", "c"), ("z", "z")]), (1, [("z", "c"), ("z", "z")])]),
  (("b", "c"),
    Std.HashMap.ofList [(0, [("z", "z")]), (1, [("z", "z")])])]

  start states:
    (("a", "a"),
      Std.HashMap.ofList [(0, [("a", "a"), ("a", "b")]), (1, [("b", "a"), ("b", "b")])]),
    (("a", "b"),
      Std.HashMap.ofList [(0, [("a", "c"), ("a", "z")]), (1, [("b", "c"), ("b", "z")])]),
    (("a", "c"),
      Std.HashMap.ofList [(0, [("a", "z")]), (1, [("b", "z")])]),
    (("a", "z"),
      Std.HashMap.ofList [(0, [("a", "z")]), (1, [("b", "z")])]),
-/

#eval hwat.start_states
#eval hwat.edges

#eval reachability_map
#eval (reachability_map.filter (fun x _ => hwat.start_states.contains x))
#eval ((reachability_map.filter (fun x _ => hwat.start_states.contains x)).values.map (fun x => x.get! 1)).flatten.dedup

def dfa_lists : DFA Int (List String) :={
  step := fun x y =>
  match x, y with
  | ["0"], 1 => ["1"]
  | ["1"], 2 => ["2"]
  | _, _ => ["z"]
  start := ["0"]
  accept := {x : List String | x == ["0"]}
}

#eval (reachability_map.get! hwat.start_states.head!).get! 0

def start_states_map
:= (reachability_map.filter (fun x _ => hwat.start_states.contains x)).values
#eval start_states_map

def get_states_from_start (i : Int) := (start_states_map.map (fun x => x.get! i)).flatten.dedup
#eval get_states_from_start 0
#eval get_states_from_start 1

#eval [0,1].map (fun x => get_states_from_start x)

def nu_states_map
:= (reachability_map.filter (fun x _ => [("b", "c"), ("b", "z"), ("b", "a"), ("b", "b")].contains x)).values
#eval nu_states_map

def nu_nu_states_map
:= (reachability_map.filter (fun x _ => [("b", "c"), ("b", "z"), ("b", "a"), ("b", "b")].contains x)).values


def get_states_from_ass (i : Int) := (nu_states_map.map (fun x => x.get! i)).flatten.dedup
def get_states_from_poo (i : Int) := (nu_nu_states_map.map (fun x => x.get! i)).flatten.dedup
#eval [0,1].map (fun x => get_states_from_ass x)

#eval (get_states_from_ass 0)
#eval (get_states_from_poo 1)

def nfa_to_dfa_step
(s: List (String × String))  (t : Int) :
(List (String × String)) :=
if s == [] then []
else
  if hwat.start_states.contains s.head! then
    ((reachability_map.filter (fun x _ => hwat.start_states.contains x)).values.map (fun x => x.get! t)).flatten.dedup
  else (reachability_map.get! s.head!).get! t


#eval nfa_to_dfa_step [("a","a")] 0
#eval nfa_to_dfa_step [("a","c")] 0
#eval nfa_to_dfa_step [("a","z")] 0
#eval nfa_to_dfa_step [("a","b")] 0

#eval nfa_to_dfa_step [("a","a")] 1
#eval nfa_to_dfa_step [("a","c")] 1
#eval nfa_to_dfa_step [("a","z")] 1
#eval nfa_to_dfa_step [("a","b")] 1

def get_reachable_states_from_list_of_states_alt {State1 Input1 : Type} [BEq State1] [Hashable State1] [BEq Input1] [Hashable Input1] [DecidableEq Input1] [DecidableEq State1]
(states : List State1) (inp : Input1) (edges_map : Std.HashMap State1 (Std.HashMap Input1 (List State1)))
: ((List State1) × Input1) × (List State1) :=
let reachable_from_states := (edges_map.filter (fun x _ => states.contains x)).values
let nyan := (reachable_from_states.map (fun y => y.get! inp)).flatten.dedup
((states, inp), nyan)

def get_reachable_states_from_list_of_states {State1 Input1 : Type} [BEq State1] [Hashable State1] [BEq Input1] [Hashable Input1] [DecidableEq Input1] [DecidableEq State1]
(states : List State1) (alph : List Input1) (edges_map : Std.HashMap State1 (Std.HashMap Input1 (List State1)))
: List (((List State1) × Input1) × (List State1)) :=
let reachable_from_states := (edges_map.filter (fun x _ => states.contains x)).values
let nyan := fun x => (reachable_from_states.map (fun y => y.get! x)).flatten.dedup
let tu := alph.map (fun x => ((states, x),nyan x))
tu

#eval get_reachable_states_from_list_of_states [("b", "c"), ("b", "z"), ("b", "a"), ("b", "b")] [0,1] reachability_map

/-
[
  (
    ([("a", "a"), ("a", "b"), ("a", "c"), ("a", "z")], 0),
    [("a", "c"), ("a", "z"), ("a", "a"), ("a", "b")]
  ),
  (
    ([("a", "a"), ("a", "b"), ("a", "c"), ("a", "z")], 1),
    [("b", "c"), ("b", "z"), ("b", "a"), ("b", "b")]
  )
]
-/

def find_all_states {State1 Input1 : Type} [BEq State1] [Hashable State1] [BEq Input1] [Hashable Input1] [DecidableEq Input1] [DecidableEq State1]
(start : List State1) (alph : List Input1) (edges_map : Std.HashMap State1 (Std.HashMap Input1 (List State1)))
: List (((List State1) × Input1) × (List State1)) :=
let reachable_states_from_start := get_reachable_states_from_list_of_states start alph edges_map
let rec looop (current : List (((List State1) × Input1) × (List State1))) :
  List (((List State1) × Input1) × (List State1)) :=
  match current with
    | ((x,y),z) :: ts => if x.toFinset = z.toFinset then [((x,y), z)] ++ looop ts
      else [get_reachable_states_from_list_of_states_alt x y edges_map] ++ (looop (ts ++ get_reachable_states_from_list_of_states z alph edges_map))
    | [] => []
looop reachable_states_from_start

#eval! find_all_states [("a", "a"), ("a", "b"), ("a", "c"), ("a", "z")] [0,1] reachability_map


def determinization_nfa {State1 Input1 : Type}
(nfa : NFA Input1 State1) : DFA_Complete (Input1) (List State1) :=
let edges_map : Std.HashMap State1 (Std.HashMap Input1 (List State1)) := depth_search_map nfa.states nfa.alphabet nfa.step
let start_state_states := (edges_map.filter (fun x _ => nfa.start_states.contains x)).values
let reachable_states_from_start := get_reachable_states_from_list_of_states start_state_states nfa.alphabet edges_map



/-
  get states from start over alphabet = ["a","b"]
    get states from "a" over alphabet = ["a"] == "a" so done
    get states from "b" over alphabet = ["c"]
      get states from "c" over alphabet = ["c"] == "c" so done
-/

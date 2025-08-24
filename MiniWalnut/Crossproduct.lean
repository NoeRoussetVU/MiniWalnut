import MiniWalnut.Basic
import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Basic
import Std.Data.HashMap

#check TopologicalSpace
/-

Complete NFA and DFA Definitions

-/


def heeeelp {T T' : Type} (wan : T) (tsu : List T') : List (T × T') :=
match tsu with
| [] => []
| y :: [] => [(wan, y)]
| y :: ys => [(wan,y)] ++ heeeelp wan ys

def combinations_for_list {T T' : Type } (ass : List T) (titties : List T') : List (T × T') :=
match ass with
| x :: xs => (heeeelp x titties) ++ combinations_for_list xs titties
| _ => []

#eval combinations_for_list [1] [0,1]

structure idk (T: Type) (Q: Type) (alphabet: Finset T) (states: Finset
Q) where
   start: states
   accepting: states -> Bool
   transition: states -> alphabet -> states


structure DFA_Complete (T : Type) (Q : Type) where
  states : List Q
  alphabet : List T
  edges : List ((Q × T) × Q)
  automata : DFA T Q


def alphabet : List Int := {0,1}

-- equals one

def states_one : List String := ["a", "b", "z"]
def edges_one : List ((String × Int) × String) :=
          [(("a",0),"a"),(("a",1),"b"),
          (("b",0),"z"),(("b",1),"z"),
          (("z",0),"z"),(("z",1),"z") ]

def dfa_one : DFA (Int) (String) :={
  step := fun x y => (edges_one.filter (·.fst = ((x,y)))).getLast!.snd
  start := "a"
  accept : Set String := {x : String | x == "b"}
}

def dfa_one_complete : DFA_Complete (Int) (String) := {
  states := ["a", "b", "z"]
  alphabet := alphabet
  edges := edges_one
  automata := dfa_one
}

--#eval dfa_one_complete.automata.eval [0,1]

-- equals two

def states_two : List String := ["a", "b", "c", "z"]
def edges_two : List ((String × Int) × String) :=
          [(("a",0),"a"),(("a",1),"b"),
          (("b",0),"c"),(("b",1),"z"),
          (("c",0),"z"),(("c",1),"z"),
          (("z",0),"z"),(("z",1),"z") ]

def dfa_two : DFA (Int) (String) := {
  step := fun x y => (edges_two.filter (·.fst = ((x,y)))).getLast!.snd
  start := "a"
  accept : Set String := {x : String | x == "c"}
}

def dfa_two_complete : DFA_Complete (Int) (String) := {
  states := states_two
  alphabet := alphabet
  edges := edges_two
  automata := dfa_two
}

def combineTransitions {State1 State2 Input1 Input2 : Type} [DecidableEq Input1] [DecidableEq Input2] [DecidableEq State1] [DecidableEq State2]
  (list1 : List ((State1 × Input1) × State1))
  (list2 : List ((State2 × Input2) × State2)) :
  List (((State1 × State2) × (Input1 × Input2)) × (State1 × State2)) :=
  List.flatten (list1.map fun t1 =>
    list2.filterMap fun t2 =>
      let ((state1, input1), next1) := t1
      let ((state2, input2), next2) := t2
      if true then
        some (((state1, state2), (input1, input2)), (next1, next2))
      else
        none)

-- Example usage
def example1 : List ((String × Int) × String) :=
  [(("a", 0), "a"), (("a", 1), "b"),
   (("b", 0), "z"), (("b", 1), "z"),
   (("z", 0), "z",), (("z", 1), "z")]

def example2 : List ((String × Int) × String) :=
  [(("a", 0), "a"), (("a", 1), "b"),
   (("b", 0), "c"), (("b", 1), "z"),
   (("c", 0), "z"), (("c", 1), "z"),
   (("z", 0), "z"), (("z", 1), "z")]

-- Test
--#eval combineTransitions example1 example2
--#eval (combineTransitions example1 example2).unzip.fst.unzip.snd
--#eval (combineTransitions example1 example2).unzip.snd
--#eval (combineTransitions example1 example2).unzip.snd.dedup

--#eval combinations_for_list [0,1] ["a","b"]


-- Define the cross product of two DFAs
def crossProduct {State1 State2 Input1 Input2 : Type} [DecidableEq Input1] [DecidableEq Input2] [DecidableEq State1] [DecidableEq State2]
  (M1 : DFA_Complete Input1 State1) (conj : String)
  (M2 : DFA_Complete Input2 State2) : DFA_Complete (Input1 × Input2) (State1 × State2) :=
  let new_edges := combineTransitions M1.edges M2.edges
  let new_states := new_edges.unzip.snd.dedup
  let new_alphabet : List (Input1 × Input2) := combinations_for_list M1.alphabet M2.alphabet
  let crossDFA : DFA (Input1 × Input2) (State1 × State2) := {
    step := fun state input =>
      let (s1, s2) := state
      let (i1, i2) := input
      let next1 := M1.automata.step s1 i1
      let next2 := M2.automata.step s2 i2
      (next1, next2)
    start := (M1.automata.start, M2.automata.start)
    accept := if conj == "AND" then {p | p.fst ∈ M1.automata.accept ∧ p.snd ∈ M2.automata.accept}
  else {p | p.fst ∈ M1.automata.accept ∨ p.snd ∈ M2.automata.accept}  }
  {states := new_states, alphabet := new_alphabet, edges := new_edges, automata := crossDFA}

-- Test
def crossproduct_one_two := crossProduct dfa_one_complete "AND" dfa_two_complete

def crossproduct_one_two_one_two := crossProduct crossproduct_one_two "AND" crossproduct_one_two


--#eval crossproduct_one_two.automata.eval [(0,1),(1,0)]
--#eval crossproduct_one_two.automata.eval [(0,0),(0,0),(0,0),(0,1),(1,0)]
--#eval crossproduct_one_two.automata.eval [(0,1),(1,1)]
--#eval crossproduct_one_two.automata.eval [(1,1),(1,0)]
--#eval crossproduct_one_two.states

--#eval crossproduct_one_two_one_two.automata.eval [((0,0),(0,0)),((0,1),(1,1))]



-- Is coffee good for you?
-- given state type and alphabet make a DFA?

-- help function that gets all reachable states over given alphabet from a given state (REPLACED WITH MAP)
def reachable {State1 Input1 : Type} [DecidableEq Input1] [DecidableEq State1] (s : State1) (a : List Input1) (t : State1 → Input1 → (List State1)) : List (List State1) :=
match a with
| [] => []
| ax :: [] => [t s ax]
| ax :: al => [t s ax] ++ reachable s al t


def alpha_2 : Finset Int := {0,1}

structure MDFA (T: Type) (Q: Type) (alphabet: Finset T) (states: Finset Q) where
  alphabet: Finset T
  states : Finset Q
  automata : DFA T Q

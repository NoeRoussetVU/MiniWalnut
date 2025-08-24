import MiniWalnut.Basic
import MiniWalnut.Crossproduct
import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Basic
import Std.Data.HashMap


-- NEED TO DO THE REMOVE ONE INPUT OF THE DFA AND GET NFA
-- EASY PEAZY

def love_n_peace {T T' : Type} (kk : List (T × T')) : List T :=
match kk with
| [] => []
| (x,_) :: xs => [x] ++ love_n_peace xs

--#eval love_n_peace [(0,"a"),(1,"b"),(2,"c"),(3,"d"),(4,"e")]

--#eval (combineTransitions example1 example2).map (fun (((a,a'), (b,_)), (c,c')) => ((a++a', b), c++c'))

def studentGrades : Std.HashMap String Int :=
  Std.HashMap.emptyWithCapacity
    |>.insert "Alice" 95
    |>.insert "Bob" 87
    |>.insert "Charlie" 92
    |>.insert "Diana" 88

--#eval studentGrades.filter (fun x y => x = "Alice" ∨ y < 92)

structure NFA (T : Type) (Q : Type) where
  states : List Q
  alphabet : List T
  edges : List ((Q × T) × Q)
  step : Q → T → List Q
  start_states : List Q
  accept_states : Set Q

/-

NEXT STEP IS CHECKING ALL STATES REACHABLE WITH 0* FROM START STATE
THEN ADD THEM TO START SET AND THEN DETERMINIZE

just keep doing 0 and add every state on the way until you reach dead state <-- to do

-/

-- Helper function to process a single input symbol from a set of current states
def processSymbol {T Q : Type} [DecidableEq Q] (nfa : NFA T Q) (currentStates : List Q) (symbol : T) : List Q :=
  let nextStates := currentStates.foldl (fun acc state =>
    acc ++ nfa.step state symbol
  ) []
  nextStates.eraseDups

-- Function to find all states reachable with exactly n zeros
def reachableWithNZeros {T Q : Type} [DecidableEq T] [DecidableEq Q] (nfa : NFA T Q) (n : Nat) (zero : T) : List Q :=
  if n = 0 then
    nfa.start_states
  else
    let rec helper (currentStates : List Q) (remaining : Nat) : List Q :=
      if remaining = 0 then
        currentStates
      else
        let nextStates := processSymbol nfa currentStates zero
        helper nextStates (remaining - 1)
    helper nfa.start_states n

-- Main function: Find all states reachable with one or more zeros
def reachableWithOneOrMoreZeros {T Q : Type} [DecidableEq T] [DecidableEq Q] (nfa : NFA T Q) (zero : T) (maxZeros : Nat) : List Q :=
  let allReachableStates := (List.range maxZeros).foldl (fun acc n =>
    if n = 0 then acc
    else acc ++ reachableWithNZeros nfa n zero
  ) []
  allReachableStates


-- I <3 AI

def quantify {State1 State2 Input1 Input2 : Type} [DecidableEq Input1] [DecidableEq Input2] [DecidableEq State1] [DecidableEq State2]
  (M1 : DFA_Complete (Input1 × Input2) (State1 × State2)) (zero : Input1):
   NFA (Input1) (State1 × State2) :=
  let new_edges := M1.edges.map (fun ((a, (b,_)), c) => ((a, b), c))
  let new_states := new_edges.unzip.snd.dedup
  let new_alphabet := love_n_peace M1.alphabet
  let step := fun x y => (new_edges.filter (·.fst = ((x,y)))).unzip.snd.dedup
  let nfa_temp : NFA (Input1) (State1 × State2) := {states := new_states, alphabet := new_alphabet, edges := new_edges, step := step, start_states := [M1.automata.start], accept_states := M1.automata.accept}
  {states := new_states, alphabet := new_alphabet, edges := new_edges, step := step, start_states := (reachableWithOneOrMoreZeros nfa_temp zero nfa_temp.states.length).dedup, accept_states := M1.automata.accept}


def hwat := quantify crossproduct_one_two 0

--#eval hwat.step ("a","a") 0
--#eval hwat.step ("a","a") 1
--#eval hwat.step ("z","b") 0
--#eval hwat.step ("z","b") 1
--#eval hwat.step ("z","z") 0
--#eval hwat.step ("a","c") 1
--#eval hwat.step ("a","c") 0

--#eval processSymbol hwat [("a","a"),("a","b"),("a","c"),("a","z")] 0
--#eval (reachableWithOneOrMoreZeros hwat 0 hwat.states.length).dedup
--#eval hwat.start_states

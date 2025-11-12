import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Computability.Language
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic
import MiniWalnut.Automata

/-!
# Cross Product Proof

This file implements proofs for a simplified version of the cross product operation.
The simplified version creates a product automaton that processes two tracks simultaneously.
We show examples and proofs to verify its correctness.

## Main Components

- **Cross product function**: Builds the cartesian product of two automata
- **Examples of cross product**: Examples showing cross product accepting the tuple list of the
two original accepted lists
- **Proofs for empty input and single input**: Proofs showing `step`, `eval`, and `evalFrom` for
cross product computes the same as the tuple of the original two automata for empty and single
inputs
- **Proofs for list input**: Proofs showing `eval` and `evalFrom` for cross product computes
the same as the tuple of the original two automata for a list input

-/

/-- Define the cross product of two DFAs with product alphabet -/
def DFA.crossProduct {T1 : Type u1} {T2 : Type u2} {Q1 : Type v1} {Q2 : Type v2} (M1 : DFA T1 Q1) (M2 : DFA T2 Q2)
 : DFA (T1 × T2) (Q1 × Q2) where
  step := fun (q1, q2) (t1, t2) => (M1.step q1 t1, M2.step q2 t2)
  start := (M1.start, M2.start)
  accept := {p | p.1 ∈ M1.accept ∧ p.2 ∈ M2.accept}

/-!
## Example Cross Product

Cross product of two automata that accept [0, 1] and [1, 0] should accept [(0, 1), (1, 0)]
-/

-- Accepts 0*1
def accepts_1 : DFA B2 Nat where
  step := fun x y => match x,y with
    | 0, B2.zero => 0
    | 0, B2.one => 1
    | _, _ => 2
  start := 0
  accept := {1}

-- Accepts 0*10
def accepts_2 : DFA B2 Nat where
  step := fun x y => match x,y with
    | 0, B2.zero => 0
    | 0, B2.one => 1
    | 1, B2.zero => 2
    | _, _ => 3
  start := 0
  accept := {2}

def accepts_1_2 : DFA (B2 × B2) (Nat × Nat) :=
  accepts_1.crossProduct accepts_2

-- Accepts ((0,1),(1,0))
example :
    let input := [(B2.zero, B2.one), (B2.one, B2.zero)]
    accepts_1_2.eval input ∈ accepts_1_2.accept := by
  simp [accepts_1_2, DFA.crossProduct, DFA.eval, DFA.evalFrom, accepts_1, accepts_2]

-- Does not accept invalid input ((1,1),(0,0))
example :
    let input := [(B2.one, B2.one),(B2.zero, B2.zero)]
    accepts_1_2.eval input ∉ accepts_1_2.accept := by
  simp [accepts_1_2, DFA.crossProduct, DFA.eval, DFA.evalFrom, accepts_1, accepts_2]

-- Same accepting state as (accepts_1, accepts_2)
example :
    let input_one := [B2.zero, B2.one]
    let input_two := [B2.one, B2.zero]
    (accepts_1.eval input_one, accepts_2.eval input_two) ∈ accepts_1_2.accept := by
  simp [accepts_1_2, DFA.crossProduct, DFA.eval, DFA.evalFrom, accepts_1, accepts_2]

variable {T1 : Type u1} {T2 : Type u2} {Q1 : Type v1} {Q2 : Type v2}
(M1 : DFA T1 Q1) (M2 : DFA T2 Q2)

@[simp]
theorem crossProduct_evalFrom_nil
    (s1 : Q1) (s2 : Q2)
    : (M1.crossProduct M2).evalFrom (s1, s2) [] = (s1, s2) :=
  rfl

@[simp]
theorem crossProduct_evalFrom_singleton
    (s1 : Q1) (s2 : Q2) (x : T1) (y : T2)
    :  (M1.crossProduct M2).evalFrom (s1, s2) [(x,y)] = (M1.crossProduct M2).step (s1, s2) (x,y) :=
  rfl

@[simp]
theorem crossProduct_evalFrom_append_singleton
    (s1 : Q1 × Q2) (a : T1 × T2) (x : List (T1 × T2)) :
    (M1.crossProduct M2).evalFrom s1 (x ++ [a]) = (M1.crossProduct M2).step ((M1.crossProduct M2).evalFrom s1 x) a := by
  simp only [DFA.evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp]
theorem crossProduct_evalFrom_nil_split
    (s1 : Q1) (s2 : Q2) :
    (M1.crossProduct M2).evalFrom (s1, s2) [] = (M1.evalFrom s1 [], M2.evalFrom s2 []) :=
  rfl

@[simp]
theorem crossProduct_evalFrom_single_split
    (s1 : Q1) (s2 : Q2) (x : T1) (y : T2):
    (M1.crossProduct M2).evalFrom (s1, s2) [(x,y)] = (M1.evalFrom s1 [x], M2.evalFrom s2 [y]) :=
  rfl

@[simp]
lemma crossProduct_step_single_split
    (s1 : Q1) (s2 : Q2) (x : T1) (y : T2) :
    (M1.crossProduct M2).step (s1, s2) (x, y) = (M1.step s1 x, M2.step s2 y) := by
    rfl

@[simp]
theorem crossProduct_eval_nil_split : (M1.crossProduct M2).eval [] = (M1.eval [], M2.eval []) :=
  rfl

@[simp]
theorem crossProduct_eval_single_split
    (x : T1) (y : T2):
    (M1.crossProduct M2).eval [(x,y)] = (M1.eval [x], M2.eval [y]) :=
  rfl

@[simp]
theorem crossProduct_eval_single_split_hyper
    (x : T1 × T2) :
    (M1.crossProduct M2).eval [x] = (M1.eval [x.fst], M2.eval [x.snd]) :=
  rfl

@[simp]
theorem eval_nil
  : (M1.crossProduct M2).eval [] = (M1.crossProduct M2).start :=
  rfl

@[simp]
theorem eval_singleton (x : T1) (y : T2)
     : (M1.crossProduct M2).eval [(x,y)] = (M1.crossProduct M2).step (M1.crossProduct M2).start (x,y) :=
  rfl

@[simp]
theorem eval_append_singleton
     (a : T1 × T2) (x : List (T1 × T2)) :
  (M1.crossProduct M2).eval (x ++ [a]) = (M1.crossProduct M2).step ((M1.crossProduct M2).eval x) a :=
  crossProduct_evalFrom_append_singleton _ _ _ _ _

theorem evalFrom_of_append (start : (Q1 × Q2)) (x y : List (T1 × T2)) :
    (M1.crossProduct M2).evalFrom start (x ++ y) = (M1.crossProduct M2).evalFrom ((M1.crossProduct M2).evalFrom start x) y :=
  List.foldl_append

/-- For a list of tuple with `xy` as input for `(x,y) = xy.unzip` and starting
from state `(s1,s2)`, `(M1.crossProduct M2).evalFrom (s1,s2) xy` evaluates the same
reached state as `(M1.evalFrom s1 x, M2.evalFrom s2 y)` -/
lemma DFA.evalFrom_crossProduct_unzip
  (s1 : Q1)
  (s2 : Q2)
  (xy : List (T1 × T2)) :
    (M1.crossProduct M2).evalFrom (s1, s2) xy = (M1.evalFrom s1 xy.unzip.1, M2.evalFrom s2 xy.unzip.2) := by
  induction xy using List.reverseRecOn with
  | nil =>
    rfl
  | append_singleton xs p ih =>
    simp [ih]
    rw [crossProduct_step_single_split]

/-- For a list of tuple with `xy` as input for `(x,y) = xy.unzip`,
`(M1.crossProduct M2).eval xy` evaluates the same reached state as `(M1.eval x, M2.eval y)` -/
lemma DFA.step_crossProduct_unzip
  (xy : List (T1 × T2)) :
    (M1.crossProduct M2).eval xy = (M1.eval xy.unzip.1, M2.eval xy.unzip.2) := by
  induction xy using List.reverseRecOn with
  | nil =>
    rfl
  | append_singleton xs p ih =>
    simp [ih]
    rw [crossProduct_step_single_split]

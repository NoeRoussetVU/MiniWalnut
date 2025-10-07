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

universe u1 u2 v1 v2

-- Proof that DFA cross product with product alphabet computes Cartesian product of languages

-- First, we need to define what we mean by Cartesian product of languages
def Language.cartesianProduct {T1 : Type u1} {T2 : Type u2} (L1 : Language T1) (L2 : Language T2) : Language (T1 × T2) :=
  {xy | ∃ x y, x ∈ L1 ∧ y ∈ L2 ∧ xy = List.zip x y}

-- Define the cross product of two DFAs with product alphabet
def DFA.crossProduct {T1 : Type u1} {T2 : Type u2} {Q1 : Type v1} {Q2 : Type v2} (M1 : DFA T1 Q1) (M2 : DFA T2 Q2)
 : DFA (T1 × T2) (Q1 × Q2) where
  -- Transition function for the product automaton
  step := fun (q1, q2) (t1, t2) => (M1.step q1 t1, M2.step q2 t2)
  -- Starting state is the pair of starting states
  start := (M1.start, M2.start)
  -- Accepting states are pairs where both components are accepting
  accept := {p | p.1 ∈ M1.accept ∧ p.2 ∈ M2.accept}


variable {T1 : Type u1} {T2 : Type u2} {Q1 : Type v1} {Q2 : Type v2} (M1 : DFA T1 Q1) (M2 : DFA T2 Q2)

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

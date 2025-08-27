-- This module serves as the root of the `MiniWalnut` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

import MiniWalnut.Basic
import MiniWalnut.Automatons
import MiniWalnut.Crossproduct
import MiniWalnut.Quantification

/-

DFA and NFA definition with states and alphabet


  Fix up quant
  Make my own determinization function with finset or list and stuff


  Make DFAO class and define sequences with it
  Make it so you can use index with it kinda
  Heaven reached

-/

/-
  DFA Generation
-/

/-
  DFA accepting a given word
  Starting state = 0
  Accepting state = list length
  Dead state = list length + 1
-/

-- Example DFA accetping abc
def acceptedWord : List (List B2) := [[B2.one], [B2.zero]]
def word_DFA := createEqualsDFA acceptedWord [B2.zero]

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

def oneDfa := createEqualsDFA [[B2.one]] [B2.zero]

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

def twoDfa := createEqualsDFA [[B2.one], [B2.zero]] [B2.zero]

def dfa_two : DFA_Complete (List B2) (Nat) := {
  states := (List.range ([1,0].length + 2))
  alphabet := [[B2.zero], [B2.one]]
  dead_state := some ([1,0].length + 1)
  vars := ['a']
  alphabet_vars := [[B2.zero], [B2.one]]
  automata := twoDfa
}


-- DFA accepting c > 2

def mt_2 : DFA (List B2) Nat := {
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
  automata := mt_2
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

  Automatic Languages implementation now! It's gonna be sick! maybe!

  Indexing automatic words (idk how that is supposed to work but I will figure it out!!!)

    M(Q, q₀, δ, Σ, S_2) as DFAO for automatic word W

    W[x] = @a is the automaton: (Q, q₀, F, δ, S_2)

    where F = {q: O(q) = a}

    W₁[x] = W₂[y]

    (M₁ × M₂)(F) where F contains all (q₁,q₂) where q₁ and q₂ have the same output
    (works same for different comparison operators!)

    What if indices are arithmetic expressions and/or predicates with one free var?
    In that case go fuck yourself, bitch

    W[e1] = W[e2]

    eᵢ as predicates
    xᵢ free vars in eᵢ

    xₖ = vₖ for all k
    aᵢ = vₖ when xₖ is the free variable in eᵢ


  -/

def a_equals_b_p_c : DFA_Complete (List B2) (Nat) := {
  states := (List.range ([1].length + 2))
  alphabet := [[B2.zero, B2.zero, B2.zero],
  [B2.one, B2.one, B2.zero],
  [B2.one, B2.zero, B2.one],
  [B2.one, B2.zero, B2.zero],
  [B2.one, B2.one, B2.one],
  [B2.zero, B2.one, B2.zero],
  [B2.zero, B2.zero, B2.one],
  [B2.zero, B2.one, B2.one]]
  dead_state := some ([1].length + 1)
  vars := ['a', 'b', 'c']
  alphabet_vars := [[B2.zero], [B2.one]]
  automata := addition
}

#eval a_equals_b_p_c.states

def a_bc_and_b_equals_2 := a_equals_b_p_c.crossProduct binary_logical_ops.and dfa_two

#eval a_bc_and_b_equals_2.alphabet
#eval a_bc_and_b_equals_2.states
#eval a_bc_and_b_equals_2.vars

#eval a_bc_and_b_equals_2.automata.eval []
#eval a_bc_and_b_equals_2.automata.eval [[B2.one,B2.one,B2.zero],[B2.zero,B2.zero,B2.zero]]
#eval a_bc_and_b_equals_2.automata.eval [[B2.one,B2.zero,B2.zero],[B2.zero,B2.one,B2.one]]


def a_bc_and_E_a_equals_2 := quant a_bc_and_b_equals_2 [B2.zero] 'a'

#eval a_bc_and_E_a_equals_2.alphabet
-- [[B2.one, B2.zero], [B2.one, B2.one], [B2.zero, B2.zero], [B2.zero, B2.one]]
#eval a_bc_and_E_a_equals_2.states
/-
[[(0, 0), (1, 1), (2, 2), (2, 3)],
[(2, 0), (0, 1), (1, 2), (2, 3)],
[(2, 0), (2, 1), (0, 2), (1, 3), (2, 3)],
  [(2, 0), (2, 1), (2, 2), (0, 3), (1, 3), (2, 3)]]
-/

#eval a_bc_and_E_a_equals_2.automata.eval []
#eval a_bc_and_E_a_equals_2.automata.eval [[B2.zero, B2.zero]]
#eval a_bc_and_E_a_equals_2.automata.eval [[B2.one, B2.one]]

#eval a_bc_and_E_a_equals_2.automata.eval [[B2.zero, B2.one]]
#eval a_bc_and_E_a_equals_2.automata.eval [[B2.zero, B2.one],[B2.zero, B2.zero]]
#eval a_bc_and_E_a_equals_2.automata.eval [[B2.zero, B2.one],[B2.zero, B2.one]]
#eval a_bc_and_E_a_equals_2.automata.eval [[B2.zero, B2.one],[B2.one, B2.zero]]
#eval a_bc_and_E_a_equals_2.automata.eval [[B2.zero, B2.one],[B2.one, B2.one]]

#eval a_bc_and_E_a_equals_2.automata.eval [[B2.one, B2.zero]]
#eval a_bc_and_E_a_equals_2.automata.eval [[B2.one, B2.zero],[B2.zero, B2.one]]

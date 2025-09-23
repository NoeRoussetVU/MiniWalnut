-- This module serves as the root of the `MiniWalnut` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.NFA

import MiniWalnut.Basic
import MiniWalnut.Automatons
import MiniWalnut.Crossproduct
import MiniWalnut.Quantification
import MiniWalnut.Minimization

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

-- DFA accepting a = 1

def dfa_one := createFullEqualsDFA [[B2.one]] [B2.zero] ['a']

#eval dfa_one.states
#eval dfa_one.dead_state
#eval dfa_one.automata.eval [[B2.zero], [B2.zero], [B2.one]] = dfa_one.dead_state
#eval dfa_one.automata.eval [[B2.zero], [B2.zero], [B2.one], [B2.one]] = dfa_one.dead_state


-- DFA accepting b = 10

def dfa_two := createFullEqualsDFA [[B2.one], [B2.zero]] [B2.zero] ['b']

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
  states_accept := [3]
  dead_state := none
  vars := ['a']
  alphabet_vars := [[B2.zero], [B2.one]]
  automata := mt_2
}


-- accepts a = 1 || b = 2
def intersectionDFATwo := crossproduct dfa_one (binary_ops.logical_op l_ops.or) dfa_two

#eval intersectionDFATwo.alphabet
#eval intersectionDFATwo.states
#eval intersectionDFATwo.states_accept
#eval intersectionDFATwo.dead_state
#eval intersectionDFATwo.vars

#eval intersectionDFATwo.automata.eval [[B2.zero,B2.zero]]
#eval intersectionDFATwo.automata.eval [[B2.zero,B2.one]]
#eval intersectionDFATwo.automata.eval [[B2.one,B2.one]]
#eval intersectionDFATwo.automata.eval [[B2.zero,B2.one],[B2.one,B2.zero]]
#eval intersectionDFATwo.automata.eval [[B2.zero,B2.one],[B2.one,B2.one]]
#eval intersectionDFATwo.automata.eval [[B2.one,B2.one],[B2.one,B2.one],[B2.one,B2.zero]]


def tutu := quant intersectionDFATwo [B2.zero] 'b' quant_op.exists

#eval tutu.states
#eval tutu.states_accept
#eval tutu.dead_state
#eval tutu.automata.eval [[B2.zero],[B2.one],[B2.zero]]

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

def b_equals_4 := createFullEqualsDFA [[B2.one], [B2.zero], [B2.zero]] [B2.zero] ['b']
#eval b_equals_4.states_accept
#eval b_equals_4.alphabet
def c_equals_1 := createFullEqualsDFA [[B2.one]] [B2.zero] ['c']
#eval c_equals_1.states_accept
def a_equals_b_p_c : DFA_Complete (List B2)   Nat := createFullAdditionDFA ['a','b','c']

#eval a_equals_b_p_c.states_accept

def a_bc_and_b4 := crossproduct a_equals_b_p_c (binary_ops.logical_op l_ops.and) b_equals_4

#eval a_bc_and_b4.alphabet
#eval a_bc_and_b4.states
#eval a_bc_and_b4.states_accept
#eval a_bc_and_b4.vars

#eval a_bc_and_b4.automata.eval []
#eval a_bc_and_b4.automata.eval [[B2.one,B2.one,B2.zero],[B2.zero,B2.zero,B2.zero]]
#eval a_bc_and_b4.automata.eval [[B2.one,B2.zero,B2.zero],[B2.zero,B2.one,B2.one]]


def a_bc_b4_c1 := crossproduct a_bc_and_b4 (binary_ops.logical_op l_ops.and) c_equals_1

#eval a_bc_b4_c1.alphabet
#eval a_bc_b4_c1.states.length
#eval a_bc_b4_c1.states_accept
#eval a_bc_b4_c1.dead_state


#eval a_bc_b4_c1.automata.eval [[B2.one, B2.one, B2.zero],[B2.zero, B2.zero, B2.zero],[B2.one, B2.zero, B2.one]]

#eval a_bc_b4_c1.automata.eval []
#eval a_bc_b4_c1.automata.eval [[B2.zero, B2.zero, B2.zero]]
#eval a_bc_b4_c1.automata.eval [[B2.zero, B2.one, B2.zero]]
#eval a_bc_b4_c1.automata.eval [[B2.zero, B2.one, B2.zero],[B2.zero, B2.zero, B2.zero] ]
#eval a_bc_b4_c1.automata.eval [[B2.zero, B2.one, B2.zero],[B2.zero, B2.one, B2.zero] ]

#eval a_bc_b4_c1.automata.eval [[B2.zero, B2.one, B2.zero],[B2.zero, B2.zero, B2.zero], [B2.zero, B2.zero, B2.zero] ]
#eval a_bc_b4_c1.automata.eval [[B2.zero, B2.one, B2.zero],[B2.zero, B2.zero, B2.zero], [B2.zero, B2.one, B2.zero] ]

#eval a_bc_b4_c1.automata.eval [[B2.zero, B2.one, B2.zero],[B2.zero, B2.zero, B2.zero], [B2.zero, B2.zero, B2.zero], [B2.zero, B2.zero, B2.zero] ]
#eval a_bc_b4_c1.automata.eval [[B2.zero, B2.one, B2.zero],[B2.zero, B2.zero, B2.zero], [B2.zero, B2.zero, B2.zero], [B2.zero, B2.one, B2.zero] ]

def Imtoast := quant a_bc_b4_c1 [B2.zero, B2.zero] 'b' quant_op.exists

#eval Imtoast.states
#eval Imtoast.states_accept
#eval Imtoast.alphabet
#eval Imtoast.vars

#eval Imtoast.automata.eval [[B2.one,B2.zero],[B2.zero,B2.zero],[B2.one,B2.one]]

def Imbread := quant Imtoast [B2.zero] 'c' quant_op.exists

#eval Imbread.states
#eval Imbread.states_accept
#eval Imbread.automata.eval [[B2.one],[B2.zero],[B2.one]]

def thue_morse_a1 := createThueMorseEqualsDFA 1 ['a']

#eval thue_morse_a1.automata.eval [[B2.one],[B2.zero],[B2.one]]


def createThueMorseDFA (vars : List Char) : DFA_Complete (List B2) Nat where
  automata := thue_morse
  states := [0,1,2]
  states_accept := [0,1]
  alphabet := [[B2.zero], [B2.one]]
  dead_state := some 2
  vars := vars
  alphabet_vars := [[B2.zero], [B2.one]]


def thue_morse_a := createThueMorseDFA ['a']
def thue_morse_b := createThueMorseDFA ['b']

def t_a_equals_t_b := minimization (crossproduct thue_morse_a (binary_ops.comparison_op c_ops.equals) thue_morse_b)


#eval t_a_equals_t_b.states
#eval t_a_equals_t_b.states_accept
#eval t_a_equals_t_b.dead_state
#eval t_a_equals_t_b.automata.eval [[B2.zero, B2.zero]]
#eval t_a_equals_t_b.automata.eval [[B2.one, B2.zero]]
#eval t_a_equals_t_b.automata.eval [[B2.one, B2.one]]
#eval t_a_equals_t_b.automata.eval [[B2.zero, B2.one],[B2.zero, B2.zero]]

#eval t_a_equals_t_b.automata.eval [[B2.zero, B2.one],[B2.one, B2.one],[B2.zero, B2.zero]]
#eval t_a_equals_t_b.automata.eval [[B2.one, B2.zero], [B2.one, B2.zero]]

#eval t_a_equals_t_b.automata.eval [[B2.one, B2.zero], [B2.one, B2.zero]]


def a_equals_i_p_k : DFA_Complete (List B2)  Nat := createFullAdditionDFA ['a','i','k']
def b_equals_i_p_c : DFA_Complete (List B2)  Nat := createFullAdditionDFA ['b','i','c']
def c_equals_n_p_k : DFA_Complete (List B2)  Nat := createFullAdditionDFA ['c','n','k']


def t_a_equals_t_b_and_a_equals_ik := (crossproduct t_a_equals_t_b (binary_ops.logical_op l_ops.and) a_equals_i_p_k)

#eval (t_a_equals_t_b_and_a_equals_ik).states
#eval (t_a_equals_t_b_and_a_equals_ik).states_accept
#eval (t_a_equals_t_b_and_a_equals_ik).dead_state
#eval (t_a_equals_t_b_and_a_equals_ik).vars

#eval (t_a_equals_t_b_and_a_equals_ik).automata.eval [[B2.one,B2.one,B2.zero,B2.zero]]
#eval (t_a_equals_t_b_and_a_equals_ik).automata.eval [[B2.one,B2.one,B2.zero,B2.zero],[B2.zero,B2.one,B2.one,B2.one]]


#eval (minimization t_a_equals_t_b_and_a_equals_ik).states
#eval (minimization t_a_equals_t_b_and_a_equals_ik).states_accept
#eval (minimization t_a_equals_t_b_and_a_equals_ik).dead_state

#eval (minimization t_a_equals_t_b_and_a_equals_ik).automata.eval [[B2.zero,B2.one]]


def Ea_t_a_equals_t_b_and_a_equals_ik := quant t_a_equals_t_b_and_a_equals_ik [B2.zero, B2.zero, B2.zero] 'a' quant_op.exists

#eval (Ea_t_a_equals_t_b_and_a_equals_ik).dead_state


def t_a_equals_t_b_and_a_ik_and_b_ic := minimization (crossproduct Ea_t_a_equals_t_b_and_a_equals_ik (binary_ops.logical_op l_ops.and) b_equals_i_p_c)
def Eab_t_a_equals_t_b_and_a_ik_and_b_ic := quant t_a_equals_t_b_and_a_ik_and_b_ic [B2.zero, B2.zero, B2.zero] 'b' quant_op.exists
def t_a_equals_t_b_and_a_ik_and_b_ink := minimization (crossproduct Eab_t_a_equals_t_b_and_a_ik_and_b_ic (binary_ops.logical_op l_ops.and) c_equals_n_p_k)
#eval t_a_equals_t_b_and_a_ik_and_b_ink.vars
#eval t_a_equals_t_b_and_a_ik_and_b_ink.states.length


#eval t_a_equals_t_b_and_a_ik_and_b_ic.states

def Eabc_t_a_equals_t_b_and_a_ik_and_b_ink := minimization (quant t_a_equals_t_b_and_a_ik_and_b_ink [B2.zero,B2.zero,B2.zero] 'c' quant_op.exists)

#eval Eabc_t_a_equals_t_b_and_a_ik_and_b_ink.states.length

#eval Eabc_t_a_equals_t_b_and_a_ik_and_b_ink.automata.eval [[B2.zero, B2.one, B2.zero],[B2.zero, B2.one, B2.one],[B2.one, B2.one, B2.zero], [B2.one, B2.one, B2.one]]


#eval Eabc_t_a_equals_t_b_and_a_ik_and_b_ink.vars


def k_lt_n := createFullLTDFA ['k','n']

def k_lt_n_imp_th_ik_equals_th_ink := minimization (crossproduct k_lt_n (binary_ops.logical_op l_ops.impl) Eabc_t_a_equals_t_b_and_a_ik_and_b_ink)
#eval k_lt_n_imp_th_ik_equals_th_ink.states
#eval k_lt_n_imp_th_ik_equals_th_ink.states_accept

#eval [[24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], [1], [8], [16], [14], [13], [18], [2], [3], [4], [5], [17], [23],
  [11], [10], [21], [6], [9], [20], [19], [7], [22], [12], [15], [0]].length

#eval [[24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], [1], [8], [16], [14], [13], [18], [2], [3], [4], [5], [11], [10],
  [6], [9], [20], [7], [12], [0]].length

def Ak_k_lt_n_impl_t_ik_equals_t_ink :=  minimization (quant k_lt_n_imp_th_ik_equals_th_ink [B2.zero, B2.zero] 'k' quant_op.for_all)
#eval Ak_k_lt_n_impl_t_ik_equals_t_ink.states.length


#eval k_lt_n_imp_th_ik_equals_th_ink.vars
#eval k_lt_n_imp_th_ik_equals_th_ink.alphabet



def n_gt := createFullGTDFA ['n','a']
def a_0 := createFullEqualsDFA [] [B2.zero] ['a']

def n_gt_a0 := crossproduct n_gt (binary_ops.logical_op l_ops.and) a_0

def n_gt0 := minimization (quant n_gt_a0 [B2.zero] 'a' quant_op.exists)

def squares_in_th_word :=  minimization (crossproduct n_gt0 (binary_ops.logical_op l_ops.and) Ak_k_lt_n_impl_t_ik_equals_t_ink)
def order_of_squares_in_th_word  := minimization (quant squares_in_th_word [B2.zero] 'i' quant_op.exists)


#eval squares_in_th_word.states.length
#eval order_of_squares_in_th_word.states.length

#eval n_gt0.states
#eval n_gt0.vars
#eval n_gt0.states_accept
#eval n_gt0.alphabet

#eval n_gt0.automata.eval []
#eval n_gt0.automata.eval [[B2.zero]]
#eval n_gt0.automata.eval [[B2.one]]
#eval n_gt0.automata.eval [[B2.one], [B2.one]]
#eval n_gt0.automata.eval [[B2.one], [B2.zero]]

#eval squares_in_th_word.states_accept
#eval squares_in_th_word.vars


#eval squares_in_th_word.automata.eval []
#eval squares_in_th_word.automata.eval [[B2.zero, B2.zero]]
#eval squares_in_th_word.automata.eval [[B2.one, B2.zero]]
#eval squares_in_th_word.automata.eval [[B2.one, B2.zero], [B2.zero, B2.zero]]
#eval squares_in_th_word.automata.eval [[B2.one, B2.zero], [B2.one, B2.zero]]
#eval squares_in_th_word.automata.eval [[B2.one, B2.zero], [B2.zero, B2.one]]
#eval squares_in_th_word.automata.eval [[B2.one, B2.zero], [B2.one, B2.one]]



#eval squares_in_th_word.automata.eval [[B2.zero, B2.one]]
#eval squares_in_th_word.automata.eval [[B2.one, B2.one]]


#eval order_of_squares_in_th_word.automata.eval []
#eval order_of_squares_in_th_word.automata.eval [[B2.zero]]

#eval order_of_squares_in_th_word.automata.eval [[B2.one]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.zero]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.zero], [B2.zero]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.zero], [B2.zero], [B2.zero]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.zero], [B2.zero], [B2.one]]


#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.zero], [B2.one]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.zero], [B2.one], [B2.zero]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.zero], [B2.one], [B2.one]]

#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one], [B2.zero]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one], [B2.zero], [B2.zero]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one], [B2.zero], [B2.one]]

#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one], [B2.one]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one], [B2.one], [B2.zero]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one], [B2.one], [B2.one]]


#eval order_of_squares_in_th_word.states_accept

def th_does_not_have_overlap  := minimization (quant order_of_squares_in_th_word [B2.zero] 'n' quant_op.exists)

#eval th_does_not_have_overlap.states
#eval th_does_not_have_overlap.states_accept
#eval th_does_not_have_overlap.vars

/-

DFA:
states
states_accepting

def idk automata
  states_without_accepting := states.filter (fun x => !accepting.contains x)
  minimizing (states_without_accepting ++ accepting) alphabet funk

-/

import Mathlib.Topology.Basic
import Mathlib.Computability.DFA

import MiniWalnut.Automata
import MiniWalnut.Crossproduct
import MiniWalnut.Quantification
import MiniWalnut.Minimization

def order_of_squares_in_th_word : DFA_extended (List B2) Nat :=
  let thue_morse_a := createThueMorseEqualsDFA [0,1] ['a']
  let thue_morse_b := createThueMorseEqualsDFA [0,1] ['b']
  let t_a_equals_t_b := minimization (crossproduct thue_morse_a (binary_ops.comparison_op c_ops.equals) thue_morse_b)

  let a_equals_i_p_k : DFA_extended (List B2)  Nat := createFullAdditionDFA ['a','i','k']
  let b_equals_i_p_c : DFA_extended (List B2)  Nat := createFullAdditionDFA ['b','i','c']
  let c_equals_n_p_k : DFA_extended (List B2)  Nat := createFullAdditionDFA ['c','n','k']

  let t_a_equals_t_b_and_a_equals_ik := (crossproduct t_a_equals_t_b (binary_ops.logical_op l_ops.and) a_equals_i_p_k)
  let Ea_t_a_equals_t_b_and_a_equals_ik := quant t_a_equals_t_b_and_a_equals_ik [B2.zero, B2.zero, B2.zero] 'a' quant_op.exists [[B2.zero], [B2.one]]

  let t_a_equals_t_b_and_a_ik_and_b_ic := minimization (crossproduct Ea_t_a_equals_t_b_and_a_equals_ik (binary_ops.logical_op l_ops.and) b_equals_i_p_c)
  let Eab_t_a_equals_t_b_and_a_ik_and_b_ic := quant t_a_equals_t_b_and_a_ik_and_b_ic [B2.zero, B2.zero, B2.zero] 'b' quant_op.exists [[B2.zero], [B2.one]]
  let t_a_equals_t_b_and_a_ik_and_b_ink := minimization (crossproduct Eab_t_a_equals_t_b_and_a_ik_and_b_ic (binary_ops.logical_op l_ops.and) c_equals_n_p_k)
  let Eabc_t_a_equals_t_b_and_a_ik_and_b_ink := minimization (quant t_a_equals_t_b_and_a_ik_and_b_ink [B2.zero,B2.zero,B2.zero] 'c' quant_op.exists [[B2.zero], [B2.one]])

  let k_lt_n := createFullLTDFA ['k','n']
  let k_lt_n_imp_th_ik_equals_th_ink := minimization (crossproduct k_lt_n (binary_ops.logical_op l_ops.impl) Eabc_t_a_equals_t_b_and_a_ik_and_b_ink)
  let Ak_k_lt_n_impl_t_ik_equals_t_ink :=  minimization (quant k_lt_n_imp_th_ik_equals_th_ink [B2.zero, B2.zero] 'k' quant_op.for_all [[B2.zero], [B2.one]])

  let n_lt_a := createFullLTDFA ['n','a']
  let n_eq_a := createExtendedEqualsDFA ['n','a']
  let n_lteq_a := minimization (crossproduct n_lt_a (binary_ops.logical_op l_ops.or) n_eq_a)
  let a_0 := createExtendedEqualsDigitDFA [] [B2.zero] ['a']
  let n_lteq_0 := minimization (crossproduct n_lteq_a (binary_ops.logical_op l_ops.and) a_0)
  let n_gt_0' :=  quant (n_lteq_0) [B2.zero] 'a' quant_op.exists [[B2.zero], [B2.one]]
  let n_gt_0 :=  complement n_gt_0'

  let squares_in_th_word :=  minimization (crossproduct n_gt_0 (binary_ops.logical_op l_ops.and) Ak_k_lt_n_impl_t_ik_equals_t_ink)
  minimization (quant squares_in_th_word [B2.zero] 'i' quant_op.exists [[B2.zero], [B2.one]])

#eval order_of_squares_in_th_word.states
#eval order_of_squares_in_th_word.states_accept

#eval order_of_squares_in_th_word.automata.eval []
#eval order_of_squares_in_th_word.automata.eval [[B2.zero]]

#eval order_of_squares_in_th_word.automata.eval [[B2.one]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.zero]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one]]

#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one], [B2.one]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one], [B2.one], [B2.zero]]
#eval order_of_squares_in_th_word.automata.eval [[B2.one], [B2.one], [B2.one], [B2.one]]


def thue_morse_does_not_have_overlaps : DFA_extended (List B2) Nat :=
  let thue_morse_a := createThueMorseEqualsDFA [0,1] ['a']
  let thue_morse_b := createThueMorseEqualsDFA [0,1] ['b']
  let t_a_equals_t_b := minimization (crossproduct thue_morse_a (binary_ops.comparison_op c_ops.equals) thue_morse_b)

  let a_equals_i_p_k : DFA_extended (List B2)  Nat := createFullAdditionDFA ['a','i','k']
  let b_equals_i_p_c : DFA_extended (List B2)  Nat := createFullAdditionDFA ['b','i','c']
  let c_equals_n_p_k : DFA_extended (List B2)  Nat := createFullAdditionDFA ['c','n','k']

  let t_a_equals_t_b_and_a_equals_ik := (crossproduct t_a_equals_t_b (binary_ops.logical_op l_ops.and) a_equals_i_p_k)
  let Ea_t_a_equals_t_b_and_a_equals_ik := quant t_a_equals_t_b_and_a_equals_ik [B2.zero, B2.zero, B2.zero] 'a' quant_op.exists [[B2.zero], [B2.one]]

  let t_a_equals_t_b_and_a_ik_and_b_ic := minimization (crossproduct Ea_t_a_equals_t_b_and_a_equals_ik (binary_ops.logical_op l_ops.and) b_equals_i_p_c)
  let Eab_t_a_equals_t_b_and_a_ik_and_b_ic := quant t_a_equals_t_b_and_a_ik_and_b_ic [B2.zero, B2.zero, B2.zero] 'b' quant_op.exists [[B2.zero], [B2.one]]
  let t_a_equals_t_b_and_a_ik_and_b_ink := minimization (crossproduct Eab_t_a_equals_t_b_and_a_ik_and_b_ic (binary_ops.logical_op l_ops.and) c_equals_n_p_k)
  let Eabc_t_a_equals_t_b_and_a_ik_and_b_ink := minimization (quant t_a_equals_t_b_and_a_ik_and_b_ink [B2.zero,B2.zero,B2.zero] 'c' quant_op.exists [[B2.zero], [B2.one]])

  let k_lt_n := createFullLTDFA ['k','n']
  let k_eq_n := createExtendedEqualsDFA ['k','n']
  let k_lteq_n := minimization (crossproduct k_lt_n (binary_ops.logical_op l_ops.or) k_eq_n)

  let k_lteq_n_imp_th_ik_equals_th_ink := minimization (crossproduct k_lteq_n (binary_ops.logical_op l_ops.impl) Eabc_t_a_equals_t_b_and_a_ik_and_b_ink)
  let Ak_k_lteq_n_impl_t_ik_equals_t_ink :=  minimization (quant k_lteq_n_imp_th_ik_equals_th_ink [B2.zero, B2.zero] 'k' quant_op.for_all [[B2.zero], [B2.one]])

  let n_lt_a := createFullLTDFA ['n','a']
  let n_eq_a := createExtendedEqualsDFA ['n','a']
  let n_lteq_a := minimization (crossproduct n_lt_a (binary_ops.logical_op l_ops.or) n_eq_a)
  let a_0 := createExtendedEqualsDigitDFA [] [B2.zero] ['a']
  let n_lteq_0 := minimization (crossproduct n_lteq_a (binary_ops.logical_op l_ops.and) a_0)
  let n_gt_0' :=  quant (n_lteq_0) [B2.zero] 'a' quant_op.exists [[B2.zero], [B2.one]]
  let n_gt_0 :=  complement n_gt_0'

  let n_gt_0_and_Ak_k_lteq_n_impl_t_ik_eq_t_ink :=  minimization (crossproduct n_gt_0 (binary_ops.logical_op l_ops.and) Ak_k_lteq_n_impl_t_ik_equals_t_ink)
  let Ei_above := minimization (quant n_gt_0_and_Ak_k_lteq_n_impl_t_ik_eq_t_ink [B2.zero] 'i' quant_op.exists [[B2.zero], [B2.one]])
  let En_above := minimization (quant Ei_above [B2.zero] 'n' quant_op.exists [[B2.zero], [B2.one]])
  complement En_above

#eval thue_morse_does_not_have_overlaps.states
#eval thue_morse_does_not_have_overlaps.states_accept

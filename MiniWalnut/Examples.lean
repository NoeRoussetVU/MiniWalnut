import Mathlib.Computability.DFA

import MiniWalnut.Automata
import MiniWalnut.Crossproduct
import MiniWalnut.Quantification
import MiniWalnut.Minimization

/-- For which n does the Thue-Morse word have a square xx where |x| = n ?

eval tmsquarelengths "Ej Ai (i < n) => T[j+i] = T[j+n+i]": -/
def tmsquarelengths : DFA_extended (List B2) Nat :=
  -- T[a] = T[b]
  let thue_morse_a := build_TH_equals_digit_DFA [0,1] 'a'
  let thue_morse_b := build_TH_equals_digit_DFA [0,1] 'b'
  let t_a_equals_t_b := minimization (crossproduct thue_morse_a (binary_ops.comparison_op c_ops.equals) thue_morse_b)
  -- a = j + i, b = j + c, c = n + i
  let a_equals_j_p_i : DFA_extended (List B2)  Nat := build_addition_DFA 'a' 'j' 'i'
  let b_equals_j_p_c : DFA_extended (List B2)  Nat := build_addition_DFA 'b' 'j' 'c'
  let c_equals_n_p_i : DFA_extended (List B2)  Nat := build_addition_DFA 'c' 'n' 'i'
  -- Ea T[a] = T[b] & a = j + i
  let Ta_equals_Tb_and_a_ji := (crossproduct t_a_equals_t_b (binary_ops.logical_op l_ops.and) a_equals_j_p_i)
  let Ea_Ta_equals_Tb_and_a_ji := (quant Ta_equals_Tb_and_a_ji 'a' quant_op.exists)
  -- T[j+i] = T[j+n+i]
  let Ta_equals_Tb_and_a_ji_and_b_jc := minimization (crossproduct Ea_Ta_equals_Tb_and_a_ji (binary_ops.logical_op l_ops.and) b_equals_j_p_c)
  let Eab_Ta_equals_Tb_and_a_ji_and_b_jc := minimization (quant Ta_equals_Tb_and_a_ji_and_b_jc 'b' quant_op.exists)
  let Ta_equals_Tb_and_a_ik_and_b_ink := minimization (crossproduct Eab_Ta_equals_Tb_and_a_ji_and_b_jc (binary_ops.logical_op l_ops.and) c_equals_n_p_i)
  let Eabc_Ta_equals_Tb_and_a_ik_and_b_ink := minimization (quant Ta_equals_Tb_and_a_ik_and_b_ink 'c' quant_op.exists)
  -- i < n & T[i+k] = T[j+n+i]
  let i_lt_n := build_less_than_DFA 'i' 'n'
  let i_lt_n_impl_Tik_equals_Tink := minimization (crossproduct i_lt_n (binary_ops.logical_op l_ops.impl) Eabc_Ta_equals_Tb_and_a_ik_and_b_ink)
  -- Ej Ai (i < n) => T[j+i] = T[j+n+i]
  let Ai_i_lt_n_and_Tik_equals_Tink := minimization (quant i_lt_n_impl_Tik_equals_Tink 'i' quant_op.for_all)
  let Ej_Ai_i_lt_n_and_Tik_equals_Tink := minimization (quant Ai_i_lt_n_and_Tik_equals_Tink 'j' quant_op.exists)
  Ej_Ai_i_lt_n_and_Tik_equals_Tink

/-- For which n does the Thue-Morse word have a palindrome of length n?

eval paltm "Ei Aj (j<n) => T[i+j] = T[(i+n)-(j+1)]": -/
def paltm : DFA_extended (List B2) Nat :=
  -- T[a] = T[b]
  let thue_morse_a := build_TH_equals_digit_DFA [0,1] 'a'
  let thue_morse_b := build_TH_equals_digit_DFA [0,1] 'b'
  let t_a_equals_t_b := (minimization (crossproduct thue_morse_a (binary_ops.comparison_op c_ops.equals) thue_morse_b))
  -- a = i + j, b = c - d, c = i + p, d = j + e, e = 1
  let a_equals_i_p_j : DFA_extended (List B2)  Nat := build_addition_DFA 'a' 'i' 'j'
  let b_equals_c_m_d : DFA_extended (List B2)  Nat := build_subtraction_DFA 'b' 'c' 'd'
  let c_equals_i_p_n : DFA_extended (List B2)  Nat := build_addition_DFA 'c' 'i' 'n'
  let d_equals_j_p_e : DFA_extended (List B2)  Nat := build_addition_DFA 'd' 'j' 'e'
  let e_equals_1 := build_equals_digit_DFA [[B2.one]] [B2.zero] 'e'
  -- d = j + 1
  let d_equals_jpe_eq_1 := minimization (crossproduct d_equals_j_p_e (binary_ops.logical_op l_ops.and) e_equals_1)
  let d_equals_jp1 := minimization (quant d_equals_jpe_eq_1 'e' quant_op.exists)
  -- b = (i+n)-(j+1)
  let b_equals_c_m_d_and_c_ipn := minimization (crossproduct b_equals_c_m_d (binary_ops.logical_op l_ops.and) c_equals_i_p_n)
  let b_equals_ipn_m_d := minimization (quant b_equals_c_m_d_and_c_ipn 'c' quant_op.exists)
  let b_equals_ipn_m_d_and_d_jp1 := minimization (crossproduct b_equals_ipn_m_d (binary_ops.logical_op l_ops.and) d_equals_jp1)
  let in_minus_j1 := minimization (quant b_equals_ipn_m_d_and_d_jp1 'd' quant_op.exists)
  -- T[i+j] = T[(i+n)-(j+1)]
  let Ta_equals_Tb_and_a_ij := minimization (crossproduct t_a_equals_t_b (binary_ops.logical_op l_ops.and) a_equals_i_p_j)
  let Ea_Ta_equals_Tb_and_a_ij := minimization (quant Ta_equals_Tb_and_a_ij 'a' quant_op.exists)
  let Tij_equals_Tb_and_b_in_minus_j1 := minimization (crossproduct Ea_Ta_equals_Tb_and_a_ij (binary_ops.logical_op l_ops.and) in_minus_j1)
  let Eb_Tij_equals_Tb_and_b_in_minus_j1 := minimization (quant Tij_equals_Tb_and_b_in_minus_j1 'b' quant_op.exists)
  -- (j < n )
  let j_lt_n := build_less_than_DFA 'j' 'n'
  -- Ei Aj (j<n) => T[i+j] = T[(i+n)-(j+1)]
  let j_lt_n_impl_Tij_equals_Tin_m_j1 := minimization (crossproduct j_lt_n (binary_ops.logical_op l_ops.impl) Eb_Tij_equals_Tb_and_b_in_minus_j1)
  let Ai_i_lt_n_and_Tik_equals_Tink := minimization (quant j_lt_n_impl_Tij_equals_Tin_m_j1 'j' quant_op.for_all)
  let Ej_Ai_i_lt_n_and_Tik_equals_Tink := minimization (quant Ai_i_lt_n_and_Tik_equals_Tink 'i' quant_op.exists)
  Ej_Ai_i_lt_n_and_Tik_equals_Tink

/-- Is the Thue-Morse sequence ultimately periodic, yes or no?

eval tmup "En Ei n>=1 & Aj (j>=i) => T[j] = T[n+j]": -/
def tmup : DFA_extended (List B2) Nat :=
  let thue_morse_j := build_TH_equals_digit_DFA [0,1] 'j'
  let thue_morse_b := build_TH_equals_digit_DFA [0,1] 'b'
  let t_j_equals_t_b := minimization (crossproduct thue_morse_j (binary_ops.comparison_op c_ops.equals) thue_morse_b)

  let b_equals_n_p_j : DFA_extended (List B2)  Nat := build_addition_DFA 'b' 'n' 'j'

  let Tj_equals_Tb_and_b_nj := minimization (crossproduct t_j_equals_t_b (binary_ops.logical_op l_ops.and) b_equals_n_p_j)
  let Eb_Tj_equals_Tb_and_b_nj := minimization (quant Tj_equals_Tb_and_b_nj 'b' quant_op.exists)

  -- i <= j
  let i_lt_j := build_less_than_DFA 'i' 'j'
  let i_eq_j := build_equals_DFA 'i' 'j'
  let i_lteq_j := minimization (crossproduct i_lt_j (binary_ops.logical_op l_ops.or) i_eq_j)

  let j_geq_i_impl_Tj_Tnj := minimization (crossproduct i_lteq_j (binary_ops.logical_op l_ops.impl) Eb_Tj_equals_Tb_and_b_nj)
  let Aj_j_geq_i_impl_Tj_Tnj := minimization (quant j_geq_i_impl_Tj_Tnj 'j' quant_op.for_all)
  --0 < n
  let a_lt_n := build_less_than_DFA 'a' 'n'
  let a_eq_0 := build_equals_digit_DFA [] [B2.zero] 'a'
  let a_lt_n_and_a_eq_0 := minimization (crossproduct a_lt_n (binary_ops.logical_op l_ops.and) a_eq_0)
  let n_geq_1 :=  minimization (quant (a_lt_n_and_a_eq_0) 'a' quant_op.exists)

  let n_geq_1_and_Aj_j_geq_i_impl_Tj_Tnj := minimization (crossproduct n_geq_1 (binary_ops.logical_op l_ops.and) Aj_j_geq_i_impl_Tj_Tnj)
  let Ei_final := minimization (quant (n_geq_1_and_Aj_j_geq_i_impl_Tj_Tnj) 'i' quant_op.exists)
  let En_Ei_final := minimization (quant (Ei_final) 'n' quant_op.exists)
  En_Ei_final

/-- For which n does the Thue-Morse sequence have a square or order n?

eval order_of_squares_in_thue_morse_word "Ei n > 0 & (Ak k < n => T [i + k] = T [i + n + k])": -/
def order_of_squares_in_th_word : DFA_extended (List B2) Nat :=
  let thue_morse_a := build_TH_equals_digit_DFA [0,1] 'a'
  let thue_morse_b := build_TH_equals_digit_DFA [0,1] 'b'
  let t_a_equals_t_b := minimization (crossproduct thue_morse_a (binary_ops.comparison_op c_ops.equals) thue_morse_b)

  let a_equals_i_p_k : DFA_extended (List B2)  Nat := build_addition_DFA 'a' 'i' 'k'
  let b_equals_i_p_c : DFA_extended (List B2)  Nat := build_addition_DFA 'b' 'i' 'c'
  let c_equals_n_p_k : DFA_extended (List B2)  Nat := build_addition_DFA 'c' 'n' 'k'

  let t_a_equals_t_b_and_a_equals_ik := minimization (crossproduct t_a_equals_t_b (binary_ops.logical_op l_ops.and) a_equals_i_p_k)
  let Ea_t_a_equals_t_b_and_a_equals_ik := minimization (quant t_a_equals_t_b_and_a_equals_ik 'a' quant_op.exists)

  let t_a_equals_t_b_and_a_ik_and_b_ic := minimization (crossproduct Ea_t_a_equals_t_b_and_a_equals_ik (binary_ops.logical_op l_ops.and) b_equals_i_p_c)
  let Eab_t_a_equals_t_b_and_a_ik_and_b_ic := minimization (quant t_a_equals_t_b_and_a_ik_and_b_ic 'b' quant_op.exists)
  let t_a_equals_t_b_and_a_ik_and_b_ink := minimization (crossproduct Eab_t_a_equals_t_b_and_a_ik_and_b_ic (binary_ops.logical_op l_ops.and) c_equals_n_p_k)
  let Eabc_t_a_equals_t_b_and_a_ik_and_b_ink := minimization (quant t_a_equals_t_b_and_a_ik_and_b_ink 'c' quant_op.exists)

  let k_lt_n := build_less_than_DFA 'k' 'n'
  let k_lt_n_imp_th_ik_equals_th_ink := minimization (crossproduct k_lt_n (binary_ops.logical_op l_ops.impl) Eabc_t_a_equals_t_b_and_a_ik_and_b_ink)
  let Ak_k_lt_n_impl_t_ik_equals_t_ink :=  minimization (quant k_lt_n_imp_th_ik_equals_th_ink 'k' quant_op.for_all)

  let n_lt_a := build_less_than_DFA 'n' 'a'
  let n_eq_a := build_equals_DFA 'n' 'a'
  let n_lteq_a := minimization (crossproduct n_lt_a (binary_ops.logical_op l_ops.or) n_eq_a)
  let a_0 := build_equals_digit_DFA [] [B2.zero] 'a'
  let n_lteq_0 := minimization (crossproduct n_lteq_a (binary_ops.logical_op l_ops.and) a_0)
  let n_gt_0' :=  minimization (quant (n_lteq_0) 'a' quant_op.exists)
  let n_gt_0 :=  complement n_gt_0'

  let squares_in_th_word :=  minimization (crossproduct n_gt_0 (binary_ops.logical_op l_ops.and) Ak_k_lt_n_impl_t_ik_equals_t_ink)
  minimization (quant squares_in_th_word 'i' quant_op.exists)

/-- Does the Thue-Morse sequence contains any overlaps?

eval thue_morse_does_not_have_overlaps "∼ (Ei , n n > 0 & (Ak k <= n => T [i + k] = T [i + n + k]))": -/
def thue_morse_does_not_have_overlaps : DFA_extended (List B2) Nat :=
  let thue_morse_a := build_TH_equals_digit_DFA [0,1] 'a'
  let thue_morse_b := build_TH_equals_digit_DFA [0,1] 'b'
  let t_a_equals_t_b := minimization (crossproduct thue_morse_a (binary_ops.comparison_op c_ops.equals) thue_morse_b)

  let a_equals_i_p_k : DFA_extended (List B2)  Nat := build_addition_DFA 'a' 'i' 'k'
  let b_equals_i_p_c : DFA_extended (List B2)  Nat := build_addition_DFA 'b' 'i' 'c'
  let c_equals_n_p_k : DFA_extended (List B2)  Nat := build_addition_DFA 'c' 'n' 'k'

  let t_a_equals_t_b_and_a_equals_ik := (crossproduct t_a_equals_t_b (binary_ops.logical_op l_ops.and) a_equals_i_p_k)
  let Ea_t_a_equals_t_b_and_a_equals_ik := minimization (quant t_a_equals_t_b_and_a_equals_ik 'a' quant_op.exists)

  let t_a_equals_t_b_and_a_ik_and_b_ic := minimization (crossproduct Ea_t_a_equals_t_b_and_a_equals_ik (binary_ops.logical_op l_ops.and) b_equals_i_p_c)
  let Eab_t_a_equals_t_b_and_a_ik_and_b_ic := minimization (quant t_a_equals_t_b_and_a_ik_and_b_ic 'b' quant_op.exists)
  let t_a_equals_t_b_and_a_ik_and_b_ink := minimization (crossproduct Eab_t_a_equals_t_b_and_a_ik_and_b_ic (binary_ops.logical_op l_ops.and) c_equals_n_p_k)
  let Eabc_t_a_equals_t_b_and_a_ik_and_b_ink := minimization (quant t_a_equals_t_b_and_a_ik_and_b_ink 'c' quant_op.exists)

  let k_lt_n := build_less_than_DFA 'k' 'n'
  let k_eq_n := build_equals_DFA 'k' 'n'
  let k_lteq_n := minimization (crossproduct k_lt_n (binary_ops.logical_op l_ops.or) k_eq_n)

  let k_lteq_n_imp_th_ik_equals_th_ink := minimization (crossproduct k_lteq_n (binary_ops.logical_op l_ops.impl) Eabc_t_a_equals_t_b_and_a_ik_and_b_ink)
  let Ak_k_lteq_n_impl_t_ik_equals_t_ink :=  minimization (quant k_lteq_n_imp_th_ik_equals_th_ink 'k' quant_op.for_all)

  let n_lt_a := build_less_than_DFA 'n' 'a'
  let n_eq_a := build_equals_DFA 'n' 'a'
  let n_lteq_a := minimization (crossproduct n_lt_a (binary_ops.logical_op l_ops.or) n_eq_a)
  let a_0 := build_equals_digit_DFA [] [B2.zero] 'a'
  let n_lteq_0 := minimization (crossproduct n_lteq_a (binary_ops.logical_op l_ops.and) a_0)
  let n_gt_0' :=  minimization (quant (n_lteq_0) 'a' quant_op.exists)
  let n_gt_0 :=  complement n_gt_0'

  let n_gt_0_and_Ak_k_lteq_n_impl_t_ik_eq_t_ink :=  minimization (crossproduct n_gt_0 (binary_ops.logical_op l_ops.and) Ak_k_lteq_n_impl_t_ik_equals_t_ink)
  let Ei_above := minimization (quant n_gt_0_and_Ak_k_lteq_n_impl_t_ik_eq_t_ink 'i' quant_op.exists)
  let En_above := minimization (quant Ei_above 'n' quant_op.exists)
  complement En_above

/-- For which n does the Thue-Morse word have an unbordered factor of length n?
(A factor is "bordered" if it begins and ends with the same word,
in a nontrivial way.  It is unbordered otherwise.)

eval tmunb "Ei Aj (j>=1 & 2*j<=n) => Et (t < j) & T[i+t] != T[(i+n+t)-j]": -/
def tmunb : DFA_extended (List B2) Nat :=
  let thue_morse_a := build_TH_equals_digit_DFA [0,1] 'a'
  let thue_morse_b := build_TH_equals_digit_DFA [0,1] 'b'
  let t_a__not_equals_t_b := complement (minimization (crossproduct thue_morse_a (binary_ops.comparison_op c_ops.equals) thue_morse_b))

  let a_equals_i_p_t : DFA_extended (List B2)  Nat := build_addition_DFA 'a' 'i' 't'

  let b_equals_c_m_j : DFA_extended (List B2)  Nat := build_subtraction_DFA 'b' 'c' 'j'
  let c_equals_i_p_d : DFA_extended (List B2)  Nat := build_addition_DFA 'c' 'i' 'd'
  let d_equals_n_p_t : DFA_extended (List B2)  Nat := build_addition_DFA 'd' 'n' 't'

  let t_a_nequals_t_b_and_a_equals_it := minimization (crossproduct t_a__not_equals_t_b (binary_ops.logical_op l_ops.and) a_equals_i_p_t)
  let Ea_t_a_nequals_t_b_and_a_equals_it := minimization (quant t_a_nequals_t_b_and_a_equals_it 'a' quant_op.exists)

  let t_a_nequals_t_b_and_a_it_and_b_cj := minimization (crossproduct Ea_t_a_nequals_t_b_and_a_equals_it (binary_ops.logical_op l_ops.and) b_equals_c_m_j)
  let Eab_t_a_nequals_t_b_and_a_ik_and_b_cj := minimization (quant t_a_nequals_t_b_and_a_it_and_b_cj 'b' quant_op.exists)

  let t_a_nequals_t_b_and_a_ik_and_b_ind := minimization (crossproduct Eab_t_a_nequals_t_b_and_a_ik_and_b_cj (binary_ops.logical_op l_ops.and) c_equals_i_p_d)
  let Eabc_t_a_equals_t_b_and_a_ik_and_b_ind := minimization (quant t_a_nequals_t_b_and_a_ik_and_b_ind 'c' quant_op.exists)

  let t_a_nequals_t_b_and_a_ik_and_b_intj := minimization (crossproduct Eabc_t_a_equals_t_b_and_a_ik_and_b_ind (binary_ops.logical_op l_ops.and) d_equals_n_p_t)
  let Tik_neq_Tintj := minimization (quant t_a_nequals_t_b_and_a_ik_and_b_intj 'd' quant_op.exists)
  let t_lt_j := build_less_than_DFA 't' 'j'
  let t_lt_j_and_Tik_neq_Tintj := minimization (crossproduct t_lt_j (binary_ops.logical_op l_ops.and) Tik_neq_Tintj)
  let Et_t_lt_j_and_Tik_neq_Tintj := minimization (quant t_lt_j_and_Tik_neq_Tintj 't' quant_op.exists)
  -- j >= 1
  let a_lt_j := build_less_than_DFA 'a' 'j'
  let a_eq_0 := build_equals_digit_DFA [] [B2.zero] 'a'
  let a_lt_j_and_a_eq_0 := minimization (crossproduct a_lt_j (binary_ops.logical_op l_ops.and) a_eq_0)
  let j_geq_1 :=  minimization (quant (a_lt_j_and_a_eq_0) 'a' quant_op.exists)
  -- a <= n
  let a_lt_n := build_less_than_DFA 'a' 'n'
  let n_eq_a := build_equals_DFA 'n' 'a'
  let a_lteq_n := minimization (crossproduct a_lt_n (binary_ops.logical_op l_ops.or) n_eq_a)
  -- a = 2*j := a= j + j
  let a_eq_j_p_j := build_addition_DFA 'a' 'j' 'j'
  -- crossproduct and (2*j<=n)
  let a_eq_jj_and_a_lteq_n := minimization (crossproduct a_eq_j_p_j (binary_ops.logical_op l_ops.and) a_lteq_n)
  let jj_lteq_n :=  minimization (quant (a_eq_jj_and_a_lteq_n) 'a' quant_op.exists)
  -- crossproduct j>=1 and 2*j<=n
  let j_geq_1_and_jj_lteq_n := minimization (crossproduct j_geq_1 (binary_ops.logical_op l_ops.and) jj_lteq_n)
  -- crossproduct imply
  let j_geq_1_and_jj_lteq_n_imp_T := minimization (crossproduct j_geq_1_and_jj_lteq_n (binary_ops.logical_op l_ops.impl) Et_t_lt_j_and_Tik_neq_Tintj)
  -- for all j
  let final_0 :=  minimization (quant (j_geq_1_and_jj_lteq_n_imp_T) 'j' quant_op.for_all)
  -- exists i
  let final_1 :=  minimization (quant (final_0) 'i' quant_op.exists)
  Et_t_lt_j_and_Tik_neq_Tintj

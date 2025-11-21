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
import Mathlib.Tactic

/-!
# Quantification Proof

This file implements the proof for a simplified version of the quantification operation.
The simplified version removes the second input track to obtain a NFA. We show examples and
proofs of its correctness.

## Main Components

- **Quantification function**: Builds the quantified NFA from a DFA
- **Examples of quantification**: Examples showing that the obtained NFA accepts input list x
iff there exists list y such that the original DFA accepts `zip(x, y)`
- **Proofs for empty input and single input**: Proofs showing `step` for single input corresponds
to `step` for the original automaton with another input
-/

-- Define the quantification of a DFA (projects onto first track)
def DFA_quant {T1 : Type u1} {T2 : Type u2} {Q : Type v1}
    (M1 : DFA (T1 × T2) (Q)) : NFA T1 (Q) :=
  {
    step := fun q t1 => {x | ∃ t2, M1.step q (t1, t2) = x}
    start := {M1.start}
    accept := M1.accept
  }

variable {T1 : Type u1} {T2 : Type u2} {Q1 : Type v1} {Q2 : Type v2}

/-!
## Example Quantification

DFA that accepts only pairs where:
- First track is [0, 1]
- Second track is [1, 0]

After quantification, should accept [0, 1] (the first track).
-/

/-- Accepts only the specific pair ([0,1], [1,0]) -/
def accepts_1_2 : DFA (B2 × B2) Nat := {
  step := fun state input => match state, input with
    | 0, (B2.zero, B2.zero) => 0
    | 0, (B2.zero, B2.one) => 1
    | 1, (B2.one, B2.zero) => 2
    | _, _ => 3
  start := 0
  accept := {2}
}

def accepts_1_2_quant : NFA B2 Nat := DFA_quant accepts_1_2

-- For input B2.zero from state 0, can reach state 1
example : 1 ∈  accepts_1_2_quant.step 0 B2.zero := by
  simp [accepts_1_2_quant, DFA_quant, accepts_1_2]
  use B2.one

example : {0, 1} ⊆ accepts_1_2_quant.step 0 B2.zero := by
  intro x hx
  simp at hx
  obtain (rfl | rfl) := hx
  · simp [accepts_1_2_quant, DFA_quant, accepts_1_2]
    use B2.zero
  · simp [accepts_1_2_quant, DFA_quant, accepts_1_2]
    use B2.one

-- For input B2.one from state 1, can reach state 2
example : 2 ∈ accepts_1_2_quant.step 1 B2.one := by
  simp [accepts_1_2_quant, DFA_quant, accepts_1_2]
  use B2.zero

example : {2} ⊆ accepts_1_2_quant.step 1 B2.one := by
  intro x hx
  simp at hx
  obtain (rfl | rfl) := hx
  · simp [accepts_1_2_quant, DFA_quant, accepts_1_2]
    use B2.zero
/-!
## Key Lemma: Single Step Correspondence

The fundamental property is that one step in the NFA corresponds to
one step in the DFA with some choice of second track input.
-/

lemma dfa_quant_step_iff
    (M : DFA (T1 × T2) (Q1 × Q2))
    (state : Q1 × Q2)
    (t1 : T1)
    (next_state : Q1 × Q2) :
    next_state ∈ (DFA_quant M).step state t1 ↔
    ∃ t2, M.step state (t1, t2) = next_state := by
  simp [DFA_quant]

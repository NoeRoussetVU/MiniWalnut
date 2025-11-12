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
# Complement Proof

This file implements the proof for a simplified version of the complement operation.

## Main Components

  - **Complement function**: Builds the complement of an automaton
  - **Examples of complement**: Examples showing complement switching which inputs are
  accepts and rejected
  - **Proof for accepted language**: Proof showing that the language accepted by the complement of
  a DFA is the complement of that language
-/

-- Define DFA complement
def DFA_complement {T : Type} {Q : Type}
    (M : DFA T Q) : DFA T Q :=
  {
    step := M.step
    start := M.start
    accept := M.acceptᶜ
  }

variable {T : Type} {Q : Type}
(M : DFA T Q)

/-!
## Example Complement
-/

-- Accepts if a = b
def equals' : DFA (List B2) Nat := {
  step := fun x y => match x,y with
    | 0, [B2.zero, B2.zero] => 0
    | 0, [B2.one, B2.one] => 0
    | _, _ => 1
  start := 0
  accept := {x | x = 0}
}

-- Complement: accepts if a ≠ b
def not_equals : DFA (List B2) Nat := DFA_complement equals'

-- [0, 0] accepted by equals
example :
    let input := [[B2.one, B2.one]]
    equals'.eval input ∈ equals'.accept := by
  simp [equals']

-- [0, 0] is rejected by not_equals
example :
    let input := [[B2.one, B2.one]]
    not_equals.eval input ∉ not_equals.accept := by
  change (DFA_complement equals).eval [[B2.one, B2.one]] ∉ (DFA_complement equals).accept
  simp only [DFA_complement]
  simp [equals]

-- [0, 1] is rejected by equals
example :
    let input := [[B2.zero, B2.one]]
    equals'.eval input ∉ equals'.accept := by
  simp [equals']

-- [0, 1] is accepted by not_equals
example :
    let input := [[B2.one, B2.zero]]
    not_equals.eval input ∈ not_equals.accept := by
  change (DFA_complement equals).eval [[B2.one, B2.zero]] ∈ (DFA_complement equals).accept
  simp only [DFA_complement]
  simp [equals]


/-- The complement DFA accepts exactly those words that M rejects -/
@[simp]
theorem dfa_complement_language
    (w : List T) :
    w ∈ (DFA_complement M).accepts ↔ w ∉ M.accepts := by
  simp [DFA.mem_accepts]
  rfl

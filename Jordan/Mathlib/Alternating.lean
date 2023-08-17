/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.alternating
-/
import Mathbin.Tactic.Group
import Mathbin.GroupTheory.Solvable
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.GroupTheory.SpecificGroups.Alternating
import Oneshot.ForMathlib.Commutators

/-!
* `three_cycle_is_commutator`, `three_cycle_mem_commutator` : every 3-cycle
is a commutor of even permutations, resp belongs to the commutator subgroup of the alternating group.
* `alternating_group.is_perfect` : the alternating group is perfect (aka equal to its wn
commutator subgroup).
* `alternating_group.commutator_group_eq` : the commutator subgroup of `perm α` is the alternating group.
-/


-- → group_theory.specific_groups.alternating
variable {β : Type _}

section ThreeCycles

open Equiv Function Finset

open Equiv.Perm Subgroup

variable (α : Type _) [Fintype α] [DecidableEq α]

variable {α}

theorem three_cycle_is_commutator
    -- {α : Type*} [decidable_eq α] [fintype α]
    (h5 : 5 ≤ Fintype.card α)
    {g : alternatingGroup α} (hg : IsThreeCycle (g : Perm α)) :
    g ∈ commutatorSet (alternatingGroup α) :=
  by
  --  ∃ (p q : alternating_group α), g = p * q * p⁻¹ * q⁻¹  :=
  apply mem_commutatorSet_of_isConj_sq
  apply alternatingGroup.isThreeCycle_isConj h5 hg
  exact hg.is_three_cycle_sq
#align three_cycle_is_commutator three_cycle_is_commutator

theorem three_cycle_is_commutator' (h5 : 5 ≤ Fintype.card α) {g : Perm α} (hg : g.IsThreeCycle) :
    ∃ p q : alternatingGroup α, g = p * q * p⁻¹ * q⁻¹ :=
  by
  let g_mem : g ∈ alternatingGroup α := Equiv.Perm.IsThreeCycle.sign hg
  let γ : alternatingGroup α := ⟨g, g_mem⟩
  rw [← SetLike.coe_mk g g_mem] at hg 
  obtain ⟨p, q, h⟩ := three_cycle_is_commutator h5 hg
  use p; use q
  simp only [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← commutatorElement_def, h, coe_mk]
#align three_cycle_is_commutator' three_cycle_is_commutator'

theorem three_cycle_mem_commutator
    -- {α : Type*} [decidable_eq α] [fintype α]
    (h5 : 5 ≤ Fintype.card α)
    {g : alternatingGroup α} (hg : IsThreeCycle (g : Perm α)) :
    g ∈ commutator (alternatingGroup α) :=
  by
  rw [commutator_eq_closure]
  apply Subgroup.subset_closure
  exact three_cycle_is_commutator h5 hg
#align three_cycle_mem_commutator three_cycle_mem_commutator

end ThreeCycles

section Perfect

variable (α : Type _) [Fintype α] [DecidableEq α]

variable {α}

open Subgroup Equiv Equiv.Perm

/-- If n ≥ 5, then the alternating group on n letters is perfect -/
theorem alternatingGroup_is_perfect (h5 : 5 ≤ Fintype.card α) :
    commutator (alternatingGroup α) = ⊤ :=
  by
  suffices closure {b : alternatingGroup α | (b : perm α).IsThreeCycle} = ⊤
    by
    rw [eq_top_iff, ← this, Subgroup.closure_le]
    intro b hb
    exact three_cycle_mem_commutator h5 hb
  rw [← closure_three_cycles_eq_alternating]
  apply Subgroup.closure_closure_coe_preimage
#align alternating_group_is_perfect alternatingGroup_is_perfect

theorem alternatingGroup_is_perfect' (h5 : 5 ≤ Fintype.card α) :
    ⁅alternatingGroup α, alternatingGroup α⁆ = alternatingGroup α := by
  rw [← Subgroup.commutator_eq', alternatingGroup_is_perfect h5, Subgroup.map_top_eq_range,
    Subgroup.subtype_range]
#align alternating_group_is_perfect' alternatingGroup_is_perfect'

theorem alternatingGroup.commutator_group_le : commutator (Perm α) ≤ alternatingGroup α :=
  by
  rw [commutator_eq_closure, Subgroup.closure_le]
  intro x
  rintro ⟨p, q, rfl⟩
  simp only [SetLike.mem_coe, mem_alternating_group, map_commutatorElement,
    commutatorElement_eq_one_iff_commute]
  apply Commute.all
#align alternating_group.commutator_group_le alternatingGroup.commutator_group_le

/-- The commutator subgroup of the permutation group is the alternating group -/
theorem alternatingGroup.commutator_group_eq (h5 : 5 ≤ Fintype.card α) :
    commutator (Perm α) = alternatingGroup α :=
  by
  apply le_antisymm alternatingGroup.commutator_group_le
  --  rw commutator_def (equiv.perm α),
  have : (alternatingGroup α : Subgroup (perm α)) ≤ ⊤ := le_top
  apply le_trans _ (commutator_mono this this)
  simp only [alternatingGroup_is_perfect' h5, le_refl]
#align alternating_group.commutator_group_eq alternatingGroup.commutator_group_eq

end Perfect


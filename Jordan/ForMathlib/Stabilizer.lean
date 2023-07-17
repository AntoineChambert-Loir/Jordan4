/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.stabilizer
-/

import Jordan.ForMathlib.Set

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Data.Finset.Pointwise

/-!

# Various lemmas on stabilizers of sets

* `stabilizer_compl` : the stabilizer of the complement is the stabilizer of the set.

* `le_stabilizer_iff` : proves inclusion of a *subgroup* `H` in `stabilizer G s`
from inclusions `g • s ⊆ s`  for all `g ∈ H`.

# Instances

* `mul_action.of_stabilizer G s`: the action of `stabilizer G s` on `s`.

## TODO

Put in group_theory.group_action.basic ?

-/


namespace MulAction

open scoped Pointwise

variable (G : Type _) [Group G] {α : Type _} [MulAction G α]

/-- The stabilizer of the complement is the stabilizer of the set. -/
@[simp]
theorem stabilizer_compl {s : Set α} : stabilizer G (sᶜ) = stabilizer G s :=
  by
  have : ∀ s : Set α, stabilizer G s ≤ stabilizer G (sᶜ) :=
    by
    intro s g h
    rw [mem_stabilizer_iff, smul_compl_set, mem_stabilizer_iff.1 h]
  refine' le_antisymm _ (this _)
  convert this _
  exact (compl_compl _).symm
#align mul_action.stabilizer_compl MulAction.stabilizer_compl

/-- The instance that makes the stabilizer of a set acting on that set -/
instance HasSmul.ofStabilizer (s : Set α) : SMul (stabilizer G s) s where 
  smul g x := ⟨g • ↑x, by
    conv_rhs => rw [← mem_stabilizer_iff.mp g.prop]
    exact Set.smul_mem_smul_set x.prop⟩
#align mul_action.has_smul.of_stabilizer MulAction.HasSmul.ofStabilizer

@[simp]
theorem HasSmul.smul_stabilizer_def (s : Set α) (g : stabilizer G s) (x : s) :
    (g • x : α) = (g : G) • (x : α) := rfl
#align mul_action.has_smul.smul_stabilizer_def MulAction.HasSmul.smul_stabilizer_def

/-- The mul_action of stabilizer a set on that set -/
instance ofStabilizer (s : Set α) : MulAction (stabilizer G s) s
    where
  one_smul x := by rw [← Subtype.coe_inj, HasSmul.smul_stabilizer_def, 
    Subgroup.coe_one, one_smul]
  mul_smul g k x := by
    simp only [← Subtype.coe_inj, HasSmul.smul_stabilizer_def, Subgroup.coe_mul,
      MulAction.mul_smul]
#align mul_action.of_stabilizer MulAction.ofStabilizer

theorem of_stabilizer_def (s : Set α) (g : stabilizer G s) (x : s) :
    (g : G) • (x : α) = g • (x : α) := rfl
#align mul_action.of_stabilizer_def MulAction.of_stabilizer_def

theorem of_stabilizer_set_def (s : Set α) (g : stabilizer G s) (t : Set α) : 
  (g : G) • t = g • t := rfl
#align mul_action.of_stabilizer_set_def MulAction.of_stabilizer_set_def

/-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions.-/
theorem le_stabilizer_iff_smul_le (s : Set α) (H : Subgroup G) : 
  H ≤ stabilizer G s ↔ ∀ g ∈ H, g • s ⊆ s :=
  by
  constructor
  · intro hyp g hg
    apply Eq.subset
    rw [← mem_stabilizer_iff]
    exact hyp hg
  intro hyp
  intro g hg
  rw [mem_stabilizer_iff]
  apply subset_antisymm
  exact hyp g hg
  intro x hx; use g⁻¹ • x; constructor
  apply hyp g⁻¹ (inv_mem hg)
  simp only [Set.smul_mem_smul_set_iff, hx]
  simp only [smul_inv_smul]
#align mul_action.le_stabilizer_iff MulAction.le_stabilizer_iff_smul_le

/-- To prove membership to stabilizer of a *finite set*, it is enough to prove one inclusion. -/
theorem mem_stabilizer_of_finite_iff_smul_le (s : Set α) (hs : s.Finite) (g : G) :
    g ∈ stabilizer G s ↔ g • s ⊆ s :=
  by
  haveI : Fintype s := Set.Finite.fintype hs
  haveI : Fintype (g • s : Set α) := Fintype.ofFinite (g • s)
  rw [mem_stabilizer_iff]
  constructor
  exact Eq.subset
  · rw [← Set.toFinset_inj, ← Set.toFinset_subset_toFinset]
    intro h
    apply Finset.eq_of_subset_of_card_le h
    apply le_of_eq
    apply symm
    suffices : (g • s).toFinset = Finset.map ⟨_, MulAction.injective g⟩ hs.toFinset
    rw [this, Finset.card_map, Set.toFinite_toFinset]
    rw [← Finset.coe_inj]
    simp only [Set.coe_toFinset, Set.toFinite_toFinset, Finset.coe_map, Function.Embedding.coeFn_mk, Set.image_smul]
#align mul_action.mem_stabilizer_of_finite_iff_smul_le MulAction.mem_stabilizer_of_finite_iff_smul_le

/-- To prove membership to stabilizer of a *finite set*, it is enough to prove one inclusion. -/
theorem mem_stabilizer_of_finite_iff_le_smul (s : Set α) (hs : s.Finite) (g : G) :
  g ∈ stabilizer G s ↔ s ⊆ g • s := by
  rw [← @inv_mem_iff, mem_stabilizer_of_finite_iff_smul_le G s hs]
  exact Set.subset_set_smul_iff.symm
#align mul_action.mem_stabilizer_of_finite_iff_le_smul MulAction.mem_stabilizer_of_finite_iff_le_smul

theorem fixingSubgroup_le_stabilizer (s : Set α) : fixingSubgroup G s ≤ stabilizer G s :=
  by
  intro k hk
  rw [mem_fixingSubgroup_iff] at hk 
  rw [mem_stabilizer_iff]
  change (fun x => k • x) '' s = s
  conv_rhs => rw [← Set.image_id s]
  apply Set.image_congr
  simp only [id.def]
  exact hk
#align mul_action.fixing_subgroup_le_stabilizer MulAction.fixingSubgroup_le_stabilizer

end MulAction

-- #lint

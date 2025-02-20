/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.stabilizer
-/

import Jordan.Mathlib.Set

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Data.Finset.Pointwise.Basic

/-!

# Various lemmas on stabilizers of sets

* `MulAction.stabilizer_compl` : the stabilizer of the complement is the stabilizer of the set.

* `MulAction.le_stabilizer_iff_smul_le` : proves inclusion of a *subgroup* `H` in `stabilizer G s`
from inclusions `g • s ⊆ s`  for all `g ∈ H`.

# Instances

* `MulAction.ofStabilizer G s`: the action of `stabilizer G s` on `s`.

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
  refine le_antisymm ?_ (this _)
  convert this _
  exact (compl_compl _).symm

/-- The instance that makes the stabilizer of a set acting on that set -/
instance _root_.SMul.ofStabilizer (s : Set α) : SMul (stabilizer G s) s where
  smul g x := ⟨g • ↑x, by
    conv_rhs => rw [← mem_stabilizer_iff.mp g.prop]
    exact Set.smul_mem_smul_set x.prop⟩

@[simp]
theorem _root_.SMul.smul_stabilizer_def (s : Set α) (g : stabilizer G s) (x : s) :
    ((g • x : ↥s) : α) = (g : G) • (x : α) := rfl

/-- The MulAction of the stabilizer a set on that set -/
instance ofStabilizer (s : Set α) : MulAction (stabilizer G s) s where
  one_smul x := by
    simp only [← Subtype.coe_inj, SMul.smul_stabilizer_def, OneMemClass.coe_one, one_smul]
  mul_smul g k x := by
    simp only [← Subtype.coe_inj, SMul.smul_stabilizer_def, Subgroup.coe_mul,
      MulAction.mul_smul]

theorem of_stabilizer_def (s : Set α) (g : stabilizer G s) (x : s) :
    (g : G) • (x : α) = g • (x : α) := rfl

theorem of_stabilizer_set_def (s : Set α) (g : stabilizer G s) (t : Set α) :
  (g : G) • t = g • t := rfl

theorem fixingSubgroup_le_stabilizer (s : Set α) : fixingSubgroup G s ≤ stabilizer G s := by
  intro k hk
  rw [mem_fixingSubgroup_iff] at hk
  rw [mem_stabilizer_iff]
  change (fun x => k • x) '' s = s
  conv_rhs => rw [← Set.image_id s]
  apply Set.image_congr
  simp only [id]
  exact hk

end MulAction

-- #lint

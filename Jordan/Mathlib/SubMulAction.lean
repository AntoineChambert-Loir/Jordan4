/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.sub_mul_actions
-/
import Mathlib.Data.Finset.Pointwise
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Jordan.EquivariantMap

open scoped Pointwise

variable (G : Type _) [Group G] {X : Type _} [MulAction G X]

open MulAction


/-- Action on the complement of an invariant subset -/
instance : HasCompl (SubMulAction G X) where
  compl := fun Y ↦ {
    carrier := Yᶜ
    smul_mem' := fun g x ↦ by
      simp only [SetLike.mem_coe, Set.mem_compl_iff, SubMulAction.smul_mem_iff', imp_self] }
#align sub_mul_action_of_compl HasCompl

theorem SubMulAction.compl_carrier (Y : SubMulAction G X) : 
  Yᶜ.carrier = Yᶜ := rfl
#align sub_mul_action_of_compl_def SubMulAction.compl_carrier

/-- Action of stabilizer of a point on the complement -/
def SubMulAction.ofStabilizer (a : X) : SubMulAction (stabilizer G a) X
    where
  carrier := {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not]
    rw [smul_eq_iff_eq_inv_smul]
    intro hgx; rw [hgx]
    apply symm; rw [← smul_eq_iff_eq_inv_smul]
    conv_rhs => rw [← mem_stabilizer_iff.mp (SetLike.coe_mem g)]
#align sub_mul_action_of_stabilizer SubMulAction.ofStabilizer

-- Impossible to use the notation →[stabilizer G a] here ?

/-- The inclusion of the sub_mul_action of the stabilizer, as an equivariant map -/
def SubMulAction.ofStabilizer.inclusion (a : X) :
    EquivariantMap (stabilizer G a).subtype (SubMulAction.ofStabilizer G a) X where
  toFun x := id x
  map_smul' _ _ := rfl
#align sub_mul_action_of_stabilizer.inclusion SubMulAction.ofStabilizer.inclusion

theorem SubMulAction.ofStabilizer_def (a : X) : (SubMulAction.ofStabilizer G a).carrier = {a}ᶜ :=
  rfl
#align sub_mul_action_of_stabilizer_def SubMulAction.ofStabilizer_def

theorem mem_SubMulAction.ofStabilizer_iff (a : X) (x : X) :
    x ∈ SubMulAction.ofStabilizer G a ↔ x ≠ a :=
  Iff.rfl
#align mem_sub_mul_action_of_stabilizer_iff mem_SubMulAction.ofStabilizer_iff

theorem SubMulAction.ofStabilizer_neq (a : X) (x : SubMulAction.ofStabilizer G a) : ↑x ≠ a :=
  x.property
#align sub_mul_action_of_stabilizer_neq SubMulAction.ofStabilizer_neq


/- 
  instance SubMulAction.ofStabilizerLift (a : X) : HasLiftT (SubMulAction.ofStabilizer G a) X :=
  coeToLift
#align sub_mul_action_of_stabilizer_lift SubMulAction.ofStabilizerLift

-/


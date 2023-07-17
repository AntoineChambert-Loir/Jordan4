/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.sub_mul_actions
-/
import Mathbin.Data.Finset.Pointwise
import Mathbin.GroupTheory.GroupAction.SubMulAction
import Mathbin.GroupTheory.GroupAction.FixingSubgroup
import Oneshot.EquivariantMap

open scoped Pointwise

variable (G : Type _) [Group G] {X : Type _} [MulAction G X]

open MulAction

/-- Action on the complement of an invariant subset -/
def subMulActionOfCompl (Y : SubMulAction G X) : SubMulAction G X
    where
  carrier := Yᶜ
  smul_mem' g x := by
    simp only [SetLike.mem_coe, Set.mem_compl_iff, SubMulAction.smul_mem_iff', imp_self]
#align sub_mul_action_of_compl subMulActionOfCompl

theorem subMulActionOfCompl_def (Y : SubMulAction G X) : (subMulActionOfCompl G Y).carrier = Yᶜ :=
  rfl
#align sub_mul_action_of_compl_def subMulActionOfCompl_def

/-- Action of stabilizer of a point on the complement -/
def subMulActionOfStabilizer (a : X) : SubMulAction (stabilizer G a) X
    where
  carrier := {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not]
    rw [smul_eq_iff_eq_inv_smul]
    intro hgx; rw [hgx]
    apply symm; rw [← smul_eq_iff_eq_inv_smul]
    conv_rhs => rw [← mem_stabilizer_iff.mp (SetLike.coe_mem g)]
    rfl
#align sub_mul_action_of_stabilizer subMulActionOfStabilizer

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The inclusion of the sub_mul_action of the stabilizer, as an equivariant map -/
def subMulActionOfStabilizer.inclusion (a : X) : subMulActionOfStabilizer G a →[stabilizer G a] X
    where
  toFun x := id x
  map_smul' g x := rfl
#align sub_mul_action_of_stabilizer.inclusion subMulActionOfStabilizer.inclusion

theorem subMulActionOfStabilizer_def (a : X) : (subMulActionOfStabilizer G a).carrier = {a}ᶜ :=
  rfl
#align sub_mul_action_of_stabilizer_def subMulActionOfStabilizer_def

theorem mem_subMulActionOfStabilizer_iff (a : X) (x : X) :
    x ∈ subMulActionOfStabilizer G a ↔ x ≠ a :=
  Iff.rfl
#align mem_sub_mul_action_of_stabilizer_iff mem_subMulActionOfStabilizer_iff

theorem subMulActionOfStabilizer_neq (a : X) (x : ↥(subMulActionOfStabilizer G a)) : ↑x ≠ a :=
  x.Prop
#align sub_mul_action_of_stabilizer_neq subMulActionOfStabilizer_neq

instance subMulActionOfStabilizerLift (a : X) : HasLiftT (subMulActionOfStabilizer G a) X :=
  coeToLift
#align sub_mul_action_of_stabilizer_lift subMulActionOfStabilizerLift


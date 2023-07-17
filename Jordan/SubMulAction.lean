/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module sub_mul_action
-/
import Mathbin.Data.Finset.Pointwise
import Mathbin.GroupTheory.GroupAction.SubMulAction
import Mathbin.GroupTheory.GroupAction.FixingSubgroup
import Oneshot.EquivariantMap

/-!

# Complements on sub_mul_actions

-/


open scoped Pointwise

namespace SubMulAction

variable {H G X : Type _} [SMul G X]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def inclusion (Y : SubMulAction G X) : Y →[G] X
    where
  toFun := coe
  map_smul' g y := rfl
#align sub_mul_action.inclusion SubMulAction.inclusion

theorem inclusion.toFun_eq_coe (Y : SubMulAction G X) : (inclusion Y).toFun = coe :=
  rfl
#align sub_mul_action.inclusion.to_fun_eq_coe SubMulAction.inclusion.toFun_eq_coe


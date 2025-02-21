/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.pretransitive
-/
import Mathlib.GroupTheory.GroupAction.Basic

/-! # Complements to pretransitive actions

Given `mul_action G X` where `G` is a group,

- `is_pretransitive.mk_base G a` shows that `is_pretransitive G X`
iff every element is translated from `a`

- `orbit.is_pretransitive_iff G a` shows that `is_pretransitive G X`
iff the `orbit G a` is full.

## TODO

They should probably go to `group_theory.group_action.defs` and `group.theory.group_action.basic`
respectively.

-/

variable (G : Type _) [Group G] {X : Type _} [MulAction G X]

namespace MulAction

open MulAction

variable {G}

theorem IsPretransitive.mk_base_iff (a : X) : IsPretransitive G X ↔ ∀ x : X, ∃ g : G, g • a = x :=
  by
  constructor
  · intro hG x; let hG_eq := hG.exists_smul_eq
    exact hG_eq a x
  · intro hG
    apply IsPretransitive.mk
    intro x y
    obtain ⟨g, hx⟩ := hG x
    obtain ⟨h, hy⟩ := hG y
    use h * g⁻¹
    rw [← hx]; rw [smul_smul, inv_mul_cancel_right]
    exact hy

theorem IsPretransitive.mk_base (a : X) (hG : ∀ x : X, ∃ g : G, g • a = x) : IsPretransitive G X :=
  by
  apply IsPretransitive.mk
  intro x y
  obtain ⟨g, hx⟩ := hG x
  obtain ⟨h, hy⟩ := hG y
  use h * g⁻¹
  rw [← hx]; rw [smul_smul, inv_mul_cancel_right]
  exact hy

/-- An action is pretransitive iff the orbit of every given element is full -/
theorem orbit.isPretransitive_iff (a : X) : orbit G a = ⊤ ↔ IsPretransitive G X :=
  by
  rw [IsPretransitive.mk_base_iff a]
  rw [Set.ext_iff]
  apply forall_congr'
  intro x
  simp_rw [Set.top_eq_univ, Set.mem_univ, iff_true, mem_orbit_iff]

end MulAction

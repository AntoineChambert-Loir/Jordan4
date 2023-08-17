/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.group_theory__subgroup__basic
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.Data.Fintype.Perm

theorem MonoidHom.range_isCommutative {G H : Type _} [Group G] [Group H] (f : G →* H)
    (hG : IsCommutative G (· * ·)) : f.range.IsCommutative :=
  by
  apply Subgroup.IsCommutative.mk
  apply IsCommutative.mk
  rintro ⟨_, a, rfl⟩; rintro ⟨_, b, rfl⟩
  rw [← Subtype.coe_inj]
  change f a * f b = f b * f a
  simp only [← map_mul]
  rw [hG.comm]
#align monoid_hom.range_is_commutative MonoidHom.range_isCommutative

theorem Equiv.perm_is_nontrivial {α : Type _} [DecidableEq α] [Fintype α] :
    1 < Fintype.card α ↔ Nontrivial (Equiv.Perm α) := by
  rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_perm, Nat.one_lt_factorial]
#align equiv.perm_is_nontrivial Equiv.perm_is_nontrivial

theorem Monoid.isCommutative_of_order_le_2 {G : Type _} [DecidableEq G] [Fintype G] [Monoid G]
    (hG : Fintype.card G ≤ 2) : IsCommutative G (· * ·) :=
  by
  suffices : ∀ (a b : G) (ha : a ≠ 1) (hb : b ≠ 1), a = b
  apply IsCommutative.mk
  intro a b
  cases' dec_em (a = 1) with ha ha
  · rw [ha]; simp only [one_mul, mul_one]
  cases' dec_em (b = 1) with hb hb
  · rw [hb]; simp only [one_mul, mul_one]
  rw [this a b ha hb]
  by_contra; apply not_lt.mpr hG
  push_neg at h 
  obtain ⟨a, b, hab1⟩ := h
  rw [Fintype.two_lt_card_iff]
  use a; use b; use 1
  simp only [hab1, Ne.def, not_false_iff, and_self_iff]
#align monoid.is_commutative_of_order_le_2 Monoid.isCommutative_of_order_le_2

/-
lemma group.is_commutative_of_order_le_2' {G: Type*} [decidable_eq G] [fintype G] [group G] (hG : fintype.card G ≤ 2) :
  is_commutative G (*) := monoid.is_commutative_of_order_le_2 hG

lemma group.is_commutative_of_order_le_2 {G: Type*} [fintype G] [group G] (hG : fintype.card G ≤ 2) :
  is_commutative G (*) :=
begin
  apply is_commutative.mk,
  suffices : ∀ (a : G), a = a⁻¹,
  { intros a b,
    rw this (a*b),
    simp only [mul_inv_rev],
    rw ← this a, rw ← this b, },

  intro a,
  by_contradiction,
  apply not_lt.mpr hG,
  rw fintype.two_lt_card_iff,
  use a, use a⁻¹, use 1,
  split, exact h,
  suffices : a ≠ 1,
  split,
  exact this,
  simp only [ne.def, inv_eq_one], exact this,

  intro h1, apply h,
  rw h1, simp only [inv_one],
end
-/
theorem Equiv.Perm.isCommutative_iff {α : Type _} [DecidableEq α] [Fintype α] :
    Fintype.card α ≤ 2 ↔ IsCommutative (Equiv.Perm α) (· * ·) :=
  by
  cases' Nat.lt_or_ge (Fintype.card α) 3 with hα hα
  · rw [Nat.lt_succ_iff] at hα 
    simp only [hα, true_iff_iff]
    apply Monoid.isCommutative_of_order_le_2
    have : Nat.factorial 2 = 2 := by norm_num
    rw [← this, Fintype.card_perm]
    exact Nat.factorial_le hα
  · rw [Nat.succ_le_iff] at hα 
    rw [← not_lt]
    simp only [hα, not_true, false_iff_iff]
    intro h
    rw [Fintype.two_lt_card_iff] at hα 
    obtain ⟨a, b, c, hab, hac, hbc⟩ := hα
    have : Equiv.swap a c * Equiv.swap a b = Equiv.swap a b * Equiv.swap a c
    apply h.comm
    rw [Equiv.ext_iff] at this 
    /- specialize this b,
        simp only [equiv.perm.coe_mul, function.comp_app, equiv.swap_apply_left, equiv.swap_apply_right] at this,
        rw equiv.swap_apply_of_ne_of_ne hab.symm hbc at this,
        simp only [equiv.swap_apply_right] at this,
        exact hac this.symm,  -/
    /- specialize this c,
        simp only [equiv.perm.coe_mul, function.comp_app, equiv.swap_apply_left, equiv.swap_apply_right] at this,
        rw equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm at this,
        simp only [equiv.swap_apply_right] at this,
        exact hab this, -/
    specialize this a
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right] at this 
    rw [Equiv.swap_apply_of_ne_of_ne hab.symm hbc] at this 
    rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm] at this 
    exact hbc this
#align equiv.perm.is_commutative_iff Equiv.Perm.isCommutative_iff


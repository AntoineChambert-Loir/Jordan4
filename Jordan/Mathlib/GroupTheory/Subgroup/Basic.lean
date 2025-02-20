/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.group_theory__subgroup__basic
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Perm

theorem MonoidHom.range_isCommutative {G H : Type _} [Group G] [Group H] (f : G →* H)
    (hG : Std.Commutative (α := G) (· * ·)) : f.range.IsCommutative := by
  apply Subgroup.IsCommutative.mk
  constructor
  rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
  rw [← Subtype.coe_inj]
  simp only [Submonoid.coe_mul, ← map_mul, hG.comm]

theorem Equiv.perm_is_nontrivial {α : Type _} [DecidableEq α] [Fintype α] :
    1 < Fintype.card α ↔ Nontrivial (Equiv.Perm α) := by
  rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_perm, Nat.one_lt_factorial]

theorem Monoid.isCommutative_of_fintype_card_le_2
    {G : Type _} [DecidableEq G] [Fintype G] [Monoid G] (hG : Fintype.card G ≤ 2) :
    Std.Commutative (α := G) (· * ·) := by
  suffices ∀ (a b : G) (_ : a ≠ 1) (_ : b ≠ 1), a = b by
    constructor
    intro a b
    cases' dec_em (a = 1) with ha ha
    · rw [ha]; simp only [one_mul, mul_one]
    cases' dec_em (b = 1) with hb hb
    · rw [hb]; simp only [one_mul, mul_one]
    rw [this a b ha hb]
  by_contra h
  apply not_lt.mpr hG
  push_neg at h
  obtain ⟨a, b, ha1, hb1, hab⟩ := h
  rw [Fintype.two_lt_card_iff]
  exact ⟨a, b, 1, hab, ha1, hb1⟩

theorem Equiv.Perm.isCommutative_iff {α : Type _} [DecidableEq α] [Fintype α] :
    Std.Commutative (α := Equiv.Perm α) (· * ·) ↔ Fintype.card α ≤ 2 := by
  cases' Nat.lt_or_ge 2 (Fintype.card α) with hα hα
  · rw [← not_lt]
    simp only [hα, not_true_eq_false, iff_false]
    intro h
    rw [Fintype.two_lt_card_iff] at hα
    obtain ⟨a, b, c, hab, hac, hbc⟩ := hα
    apply hbc
    -- follows from applying `(a c) (a b) = (a b) (a c)` to `a`
    convert Equiv.ext_iff.mp (h.comm (Equiv.swap a c) (Equiv.swap a b)) a
    rw [coe_mul, Function.comp_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab.symm hbc]
    rw [coe_mul, Function.comp_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  · simp only [hα, iff_true]
    apply Monoid.isCommutative_of_fintype_card_le_2
    rw [← Nat.factorial_two, Fintype.card_perm]
    exact Nat.factorial_le hα

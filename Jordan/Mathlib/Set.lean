/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.set
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card

/-! # Stuff to put somewhere in mathlib

Various lemmas on intersection and complement

The first part could go to `data.set.lattice`,
the second to `data.set.pointwise.basic`

-/


-- import data.set.pointwise.basic
-- import data.set.pointwise.basic
open scoped Pointwise

section encard

variable {α : Type*}

lemma Set.one_lt_encard_iff_nontrivial (s : Set α) :
    1 < s.encard ↔ Set.Nontrivial s := by
  unfold Set.Nontrivial
  rw [Set.one_lt_encard_iff]
  constructor
  all_goals {
    rintro ⟨a, b, c, d, e⟩
    exact ⟨a, c, b, d, e⟩ }

-- lemma Set.nontrivial_iff_not_encard_le_one {α : Type _} (B : Set α) :
--     Set.Nontrivial B ↔ ¬(Set.encard B ≤ 1) := by
--   rw [not_le, Set.one_lt_encard_iff_nontrivial]

lemma Set.one_lt_ncard_iff_nontrivial (s : Set α) [Finite s] :
    1 < s.ncard ↔ Set.Nontrivial s := by
  rw [← Set.one_lt_encard_iff_nontrivial, ← Set.Finite.cast_ncard_eq (toFinite s),
    Nat.one_lt_cast]

-- lemma Set.nontrivial_iff_not_ncard_le_one {α : Type _} [Finite α] (B : Set α) :
--     Set.Nontrivial B ↔ ¬(Set.ncard B ≤ 1) := by
--   rw [not_le, Set.one_lt_ncard_iff_nontrivial]


lemma Set.subsingleton_iff_encard_le_one {α : Type _} (B : Set α) :
  Set.Subsingleton B ↔ Set.encard B ≤ 1 := by
  rw [← Set.not_nontrivial_iff, not_iff_comm, not_le, Set.one_lt_encard_iff_nontrivial]

lemma Set.subsingleton_iff_ncard_le_one {α : Type _} [Finite α] (B : Set α) :
  Set.Subsingleton B ↔ Set.ncard B ≤ 1 := by
  rw [← Set.not_nontrivial_iff, not_iff_comm, not_le, ← Set.one_lt_ncard_iff_nontrivial]

lemma Set.eq_top_iff_ncard {α : Type _} [Fintype α] (B : Set α) :
    B = ⊤ ↔ Set.ncard B = Fintype.card α := by
  rw [top_eq_univ, ← Set.compl_empty_iff, ← Set.ncard_eq_zero]
  rw [← Nat.card_eq_fintype_card]
  rw [← Set.ncard_add_ncard_compl B]
  constructor
  · intro H
    rw [H, add_zero]
  · intro H
    exact Nat.add_left_cancel H.symm

lemma WithTop.add_eq_add_iff (c : ℕ∞) (m n : ℕ) :
    c + m = n + m ↔ c = n := by
  rw [WithTop.add_right_cancel_iff]
  exact WithTop.coe_ne_top

-- lemma Set.encard_add_eq_add_iff (s : Set α) (m n : ℕ) :
--     s.encard + m = n + m ↔ s.encard = n := by
--   rw [WithTop.add_right_cancel_iff]
--   exact WithTop.coe_ne_top

lemma WithTop.add_one_eq_coe_succ_iff (c : ℕ∞) (n : ℕ) :
    c + 1 = n.succ ↔ c = n := by
  rw [← Nat.cast_one, Nat.succ_eq_add_one, Nat.cast_add, WithTop.add_eq_add_iff]

-- lemma Set.encard_add_one_eq_succ_iff (s : Set α) (n : ℕ) :
--     s.encard + 1 = n.succ ↔ s.encard = n := by
--   rw [← Nat.cast_one, Nat.succ_eq_add_one, Nat.cast_add, Set.encard_add_eq_add_iff]

lemma WithTop.add_coe_lt_add_iff (c : ℕ∞) (m n : ℕ) :
    c + m < n + m ↔ c < n := by
  rw [WithTop.add_lt_add_iff_right]
  exact WithTop.coe_ne_top

-- lemma Set.encard_add_coe_lt_add_iff (s : Set α) (m n : ℕ) :
--     s.encard + m < n + m ↔ s.encard < n := by
--   rw [WithTop.add_lt_add_iff_right]
--   exact WithTop.coe_ne_top


lemma WithTop.add_one_lt_coe_succ_iff (c : ℕ∞) (n : ℕ) :
    c + 1 < n.succ ↔ c < n := by
  rw [← Nat.cast_one, Nat.succ_eq_add_one, Nat.cast_add, WithTop.add_coe_lt_add_iff]

-- lemma Set.encard_add_one_lt_succ_iff (s : Set α) (n : ℕ) :
--     s.encard + 1 < n.succ ↔ s.encard < n := by
--   rw [← Nat.cast_one, Nat.succ_eq_add_one, Nat.cast_add, Set.encard_add_coe_lt_add_iff]

lemma WithTop.add_coe_le_add_iff (c : ℕ∞) (m n : ℕ) :
    c + m ≤ n + m ↔ c ≤ n :=
  WithTop.add_le_add_iff_right (by exact WithTop.coe_ne_top)

-- lemma Set.encard_add_coe_le_add_iff (s : Set α) (m n : ℕ) :
--     s.encard + m ≤ n + m ↔ s.encard ≤ n := by
--   rw [WithTop.add_le_add_iff_right]
--   exact WithTop.coe_ne_top

lemma WithTop.add_one_le_coe_succ_iff (c : ℕ∞) (n : ℕ) :
    c + 1 ≤ n.succ ↔ c ≤ n := by
  rw [← Nat.cast_one, Nat.succ_eq_add_one, Nat.cast_add, WithTop.add_coe_le_add_iff]

-- lemma Set.encard_add_one_le_succ_iff (s : Set α) (n : ℕ) :
--     s.encard + 1 ≤ n.succ ↔ s.encard ≤ n := by
--   rw [← Nat.cast_one, Nat.succ_eq_add_one, Nat.cast_add, Set.encard_add_coe_le_add_iff]

lemma WithTop.coe_lt_iff_succ_le (n : ℕ) (c : ℕ∞) : n < c ↔ n.succ ≤ c := by
  induction c using WithTop.recTopCoe with
  | top =>
    simp only [Nat.cast_succ, le_top, iff_true]
    apply WithTop.coe_lt_top
  | coe m =>
    simp only [ENat.some_eq_coe, Nat.cast_lt, Nat.cast_le]
    exact Nat.lt_iff_add_one_le

open Function

variable {α β G X : Type _} {ι : Sort _} {κ : ι → Sort _}


/-
@[simp] lemma Inter_of_empty (s : ι → set α) [is_empty ι] : (⋂ i, s i) = univ := infi_of_empty _
@[simp] lemma Union_of_empty (s : ι → set α) [is_empty ι] : (⋃ i, s i) = ∅ := supr_of_empty _
-/
/- Can be avoided -/
theorem _root_.Function.Injective.image_iInter_eq [Nonempty ι] {f : α → β} (hf : Injective f) (s : ι → Set α) :
    (f '' ⋂ i : ι, s i) = ⋂ i, f '' s i := by
  -- rw [injOn_of_injective hf]
  rw [Set.InjOn.image_iInter_eq (Set.injOn_of_injective hf)]

theorem Set.subset_of_eq {α : Type _} {s t : Set α} (h : s = t) : s ⊆ t := by
  rw [h]


namespace MulAction

variable [Group α] [MulAction α β]

@[simp]
theorem smul_compl_set (a : α) (s : Set β) : a • sᶜ = (a • s)ᶜ :=
  Set.image_compl_eq <| MulAction.bijective _

theorem smul_set_iInter (a : α) (s : ι → Set β) : (a • ⋂ i, s i) = ⋂ i, a • s i :=
  by
  obtain _ | _ := isEmpty_or_nonempty ι
  · refine Eq.trans ?_ (Set.iInter_of_empty _).symm
    rw [Set.iInter_of_empty]
    exact Set.smul_set_univ
  · exact (MulAction.injective _).image_iInter_eq _

theorem smul_set_iInter₂ (a : α) (s : ∀ i, κ i → Set β) :
    (a • ⋂ (i) (j), s i j) = ⋂ (i) (j), a • s i j := by
    simp_rw [smul_set_iInter]

theorem smul_set_encard_eq (a : α) (s : Set β) :
    Set.encard (a • s) = Set.encard s :=
  (MulAction.injective a).encard_image s

theorem smul_set_ncard_eq [DecidableEq β] (a : α) (s : Set β) :
    Set.ncard (a • s) = Set.ncard s :=
  Set.ncard_image_of_injective s (MulAction.injective a)

/-
theorem smul_set_card_eq' [DecidableEq β] (a : α) (s : Set β) [Fintype s] :
    Fintype.card (a • s) = Fintype.card s := by
  change Fintype.card ((fun x => a • x) '' s) = _
  simp_rw [Set.image_eq_range (fun x => a • x) s]
  rw [Set.card_range_of_injective]
  apply Subtype.restrict_injective
  exact MulAction.injective a


theorem smul_set_card_eq [DecidableEq β] (a : α) (s : Set β) :
    Nat.card (a • s) = Nat.card s := by
  apply symm
  apply Nat.card_congr
  refine Equiv.Set.imageOfInjOn _ s (s.injOn_of_injective (MulAction.injective a))
 -/
end MulAction

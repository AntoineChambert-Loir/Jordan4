/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.cardinal
-/
import Mathbin.SetTheory.Cardinal.Finite
import Mathbin.Data.Finite.Card

/-!

# Finite cardinals and part_enat

This file proves a few lemmas that are useful for handling finite cardinals
via their `.to_part_enat` coercions, in particular `part_enat.card` of types.

-/


open scoped Cardinal

open PartENat Cardinal

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option pp.universes -/
set_option pp.universes true

universe u v w

variable {α : Type u}

namespace Cardinal

#print Cardinal.toNat_eq_iff_eq_of_lt_aleph0 /-
/-- Two finite cardinals are equal iff they are equal their to_nat are equal -/
theorem toNat_eq_iff_eq_of_lt_aleph0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
    c.toNat = d.toNat ↔ c = d := by
  rw [← nat_cast_inj, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]
#align cardinal.to_nat_eq_iff_eq_of_lt_aleph_0 Cardinal.toNat_eq_iff_eq_of_lt_aleph0
-/

#print Cardinal.toPartENat_lift /-
theorem toPartENat_lift (c : Cardinal.{v}) : (Cardinal.lift.{u, v} c).toPartENat = c.toPartENat :=
  by
  cases' lt_or_ge c ℵ₀ with hc hc
  · rw [to_part_enat_apply_of_lt_aleph_0 hc, Cardinal.toPartENat_apply_of_lt_aleph0 _]
    simp only [to_nat_lift]
    rw [← lift_aleph_0, lift_lt]; exact hc
  · rw [to_part_enat_apply_of_aleph_0_le hc, Cardinal.toPartENat_apply_of_aleph0_le _]
    rw [← lift_aleph_0, lift_le]; exact hc
#align cardinal.to_part_enat_lift Cardinal.toPartENat_lift
-/

#print Cardinal.toPartENat_congr /-
theorem toPartENat_congr {β : Type v} (e : α ≃ β) : (#α).toPartENat = (#β).toPartENat := by
  rw [← to_part_enat_lift, lift_mk_eq.mpr ⟨e⟩, to_part_enat_lift]
#align cardinal.to_part_enat_congr Cardinal.toPartENat_congr
-/

end Cardinal

namespace PartENat

#print PartENat.card_congr /-
theorem card_congr {α : Type _} {β : Type _} (f : α ≃ β) : PartENat.card α = PartENat.card β :=
  Cardinal.toPartENat_congr f
#align part_enat.card_congr PartENat.card_congr
-/

#print PartENat.card_uLift /-
theorem card_uLift (α : Type _) : card (ULift α) = card α :=
  card_congr Equiv.ulift
#align part_enat.card_ulift PartENat.card_uLift
-/

#print PartENat.card_pLift /-
@[simp]
theorem card_pLift (α : Type _) : card (PLift α) = card α :=
  card_congr Equiv.plift
#align part_enat.card_plift PartENat.card_pLift
-/

#print PartENat.card_image_of_injOn /-
theorem card_image_of_injOn {α : Type u} {β : Type v} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm
#align part_enat.card_image_of_inj_on PartENat.card_image_of_injOn
-/

#print PartENat.card_image_of_injective /-
theorem card_image_of_injective {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s (Set.injOn_of_injective h s)).symm
#align part_enat.card_image_of_injective PartENat.card_image_of_injective
-/

-- Add other similar lemmas?
theorem succ_le_iff {n : ℕ} {e : PartENat} : ↑n.succ ≤ e ↔ ↑n < e :=
  by
  rw [coe_lt_iff, coe_le_iff]
  apply forall_congr'; intro a; rw [Nat.succ_le_iff]
#align part_enat.succ_le_iff PartENat.succ_le_iff

/- The line
-- obtain ⟨m, hm⟩ := cardinal.lt_aleph_0.mp h,
extract an integer m from a cardinal c such that h : c < ℵ₀
It may appear easier to use than the rewrites I finally use … -/
theorem coe_nat_le_iff_le {n : ℕ} {c : Cardinal} : ↑n ≤ toPartENat c ↔ ↑n ≤ c :=
  by
  cases lt_or_ge c ℵ₀
  · rw [to_part_enat_apply_of_lt_aleph_0 h, coe_le_coe, ← to_nat_cast n]
    rw [to_nat_le_iff_le_of_lt_aleph_0 (nat_lt_aleph_0 n) h]
    simp only [to_nat_cast]
  · apply iff_of_true
    · rw [to_part_enat_apply_of_aleph_0_le h]
      exact le_top
    · apply le_trans (le_of_lt _) h
      rw [lt_aleph_0]
      use n
#align part_enat.coe_nat_le_iff_le PartENat.coe_nat_le_iff_le

theorem le_coe_nat_iff_le {c : Cardinal} {n : ℕ} : toPartENat c ≤ n ↔ c ≤ n :=
  by
  cases lt_or_ge c ℵ₀
  · rw [to_part_enat_apply_of_lt_aleph_0 h, coe_le_coe, ← to_nat_cast n]
    rw [to_nat_le_iff_le_of_lt_aleph_0 h (nat_lt_aleph_0 n)]
    simp only [to_nat_cast]
  · apply iff_of_false
    · rw [to_part_enat_apply_of_aleph_0_le h]
      simp only [top_le_iff, coe_ne_top, not_false_iff]
    · rw [not_le]
      apply lt_of_lt_of_le (nat_lt_aleph_0 n) h
#align part_enat.le_coe_nat_iff_le PartENat.le_coe_nat_iff_le

theorem coe_nat_eq_iff_eq {n : ℕ} {c : Cardinal} : ↑n = toPartENat c ↔ ↑n = c :=
  by
  cases lt_or_ge c Cardinal.aleph0
  · rw [to_part_enat_apply_of_lt_aleph_0 h, coe_inj]
    rw [← to_nat_cast n]
    rw [Cardinal.toNat_eq_iff_eq_of_lt_aleph0 (nat_lt_aleph_0 n) h]
    simp only [to_nat_cast]
  · apply iff_of_false
    · rw [Cardinal.toPartENat_apply_of_aleph0_le h]
      exact coe_ne_top n
    · apply ne_of_lt
      apply lt_of_lt_of_le (Cardinal.nat_lt_aleph0 n) h
#align part_enat.coe_nat_eq_iff_eq PartENat.coe_nat_eq_iff_eq

theorem eq_coe_nat_iff_eq {c : Cardinal} {n : ℕ} : Cardinal.toPartENat c = n ↔ c = n :=
  by
  constructor
  · intro h; apply symm; exact coe_nat_eq_iff_eq.mp h.symm
  · intro h; apply symm; exact coe_nat_eq_iff_eq.mpr h.symm
#align part_enat.eq_coe_nat_iff_eq PartENat.eq_coe_nat_iff_eq

#print Cardinal.natCast_lt_toPartENat_iff /-
theorem natCast_lt_toPartENat_iff {n : ℕ} {c : Cardinal} : ↑n < toPartENat c ↔ ↑n < c :=
  by
  cases lt_or_ge c ℵ₀
  · rw [to_part_enat_apply_of_lt_aleph_0 h, coe_lt_coe, ← to_nat_cast n]
    rw [to_nat_lt_iff_lt_of_lt_aleph_0 (nat_lt_aleph_0 n) h]
    simp only [to_nat_cast]
  · apply iff_of_true
    · rw [to_part_enat_apply_of_aleph_0_le h]; exact coe_lt_top n
    · exact lt_of_lt_of_le (nat_lt_aleph_0 n) h
#align part_enat.coe_nat_lt_coe_iff_lt Cardinal.natCast_lt_toPartENat_iff
-/

theorem lt_coe_nat_iff_lt {n : ℕ} {c : Cardinal} : toPartENat c < n ↔ c < n :=
  by
  cases lt_or_ge c ℵ₀
  · rw [to_part_enat_apply_of_lt_aleph_0 h, coe_lt_coe, ← to_nat_cast n]
    rw [to_nat_lt_iff_lt_of_lt_aleph_0 h (nat_lt_aleph_0 n)]
    simp only [to_nat_cast]
  · apply iff_of_false
    · rw [to_part_enat_apply_of_aleph_0_le h]
      simp
    · rw [not_lt]
      refine' le_trans (le_of_lt (nat_lt_aleph_0 n)) h
#align part_enat.lt_coe_nat_iff_lt PartENat.lt_coe_nat_iff_lt

#print PartENat.card_eq_zero_iff_empty /-
theorem card_eq_zero_iff_empty (α : Type _) : card α = 0 ↔ IsEmpty α :=
  by
  rw [← Cardinal.mk_eq_zero_iff]
  conv_rhs => rw [← Nat.cast_zero]
  rw [← eq_coe_nat_iff_eq]
  unfold PartENat.card
  simp only [Nat.cast_zero]
#align part_enat.card_eq_zero_iff_empty PartENat.card_eq_zero_iff_empty
-/

#print PartENat.card_le_one_iff_subsingleton /-
theorem card_le_one_iff_subsingleton (α : Type _) : card α ≤ 1 ↔ Subsingleton α :=
  by
  rw [← le_one_iff_subsingleton]
  conv_rhs => rw [← Nat.cast_one]
  rw [← le_coe_nat_iff_le]
  unfold PartENat.card
  simp only [Nat.cast_one]
#align part_enat.card_le_one_iff_subsingleton PartENat.card_le_one_iff_subsingleton
-/

#print PartENat.one_lt_card_iff_nontrivial /-
theorem one_lt_card_iff_nontrivial (α : Type _) : 1 < card α ↔ Nontrivial α :=
  by
  rw [← Cardinal.one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← coe_nat_lt_coe_iff_lt]
  unfold PartENat.card
  simp only [Nat.cast_one]
#align part_enat.one_lt_card_iff_nontrivial PartENat.one_lt_card_iff_nontrivial
-/

#print PartENat.card_eq_coe_nat_card /-
theorem card_eq_coe_nat_card (α : Type _) [Finite α] : card α = Nat.card α :=
  by
  unfold PartENat.card
  apply symm
  rw [coe_nat_eq_iff_eq]
  exact Finite.cast_card_eq_mk
#align part_enat.card_of_finite PartENat.card_eq_coe_nat_card
-/

-- Necessary ?
theorem card_of_fintype (α : Type _) [Fintype α] : card α = Fintype.card α :=
  by
  rw [card_of_finite]
  simp only [Nat.card_eq_fintype_card]
#align part_enat.card_of_fintype PartENat.card_of_fintype

theorem is_finite_of_card {α : Type _} {n : ℕ} (hα : PartENat.card α = n) : Finite α :=
  by
  apply Or.resolve_right (finite_or_infinite α)
  intro h; skip
  apply PartENat.natCast_ne_top n
  rw [← hα]
  exact PartENat.card_eq_top_of_infinite
#align part_enat.is_finite_of_card PartENat.is_finite_of_card

/- Probably unnecessary

noncomputable def is_fintype_of_card (α : Type) {n : ℕ} (hα : part_enat.card α = n) :
  fintype α :=
begin
  letI := is_finite_of_card α hα,
  exact fintype.of_finite α,
end -/
end PartENat

#lint


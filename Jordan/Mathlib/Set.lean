/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.set
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Pointwise
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
  rw [Set.InjOn.image_iInter_eq (Set.injOn_of_injective hf _)]
#align set.image_Inter' Function.Injective.image_iInter_eq

theorem Set.subset_of_eq {α : Type _} {s t : Set α} (h : s = t) : s ⊆ t :=
  h ▸ Set.Subset.refl _
#align set.set.subset_of_eq Set.subset_of_eq


namespace MulAction

variable [Group α] [MulAction α β]

@[simp]
theorem smul_compl_set (a : α) (s : Set β) : a • sᶜ = (a • s)ᶜ :=
  Set.image_compl_eq <| MulAction.bijective _
#align mul_action.smul_compl_set MulAction.smul_compl_set

theorem smul_set_iInter (a : α) (s : ι → Set β) : (a • ⋂ i, s i) = ⋂ i, a • s i :=
  by
  obtain _ | _ := isEmpty_or_nonempty ι
  · refine' Eq.trans _ (Set.iInter_of_empty _).symm
    rw [Set.iInter_of_empty]
    exact Set.smul_set_univ
  · exact (MulAction.injective _).image_iInter_eq _
#align mul_action.smul_set_Inter MulAction.smul_set_iInter

theorem smul_set_iInter₂ (a : α) (s : ∀ i, κ i → Set β) :
    (a • ⋂ (i) (j), s i j) = ⋂ (i) (j), a • s i j := by     
    simp_rw [smul_set_iInter]
#align mul_action.smul_set_Inter₂ MulAction.smul_set_iInter₂

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
#align mul_action.smul_set_card_eq MulAction.smul_set_card_eq'


theorem smul_set_card_eq [DecidableEq β] (a : α) (s : Set β) :
    Nat.card (a • s) = Nat.card s := by
  apply symm
  apply Nat.card_congr
  refine Equiv.Set.imageOfInjOn _ s (s.injOn_of_injective (MulAction.injective a))
 -/
end MulAction


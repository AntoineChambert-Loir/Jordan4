/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module perm_iwasawa
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Jordan.Mathlib.Set
import Jordan.Mathlib.GroupTheory.Subgroup.Basic
import Jordan.Mathlib.Alternating
import Jordan.MulActionCombination
import Jordan.Jordan
import Jordan.PermMaximal
import Jordan.Iwasawa

/-!
# Normal subgroups of the symmetric group

* `Equiv.Perm.normal_subgroups` : a nontrivial normal subgroup of `Equiv.Perm α` contains the alternating group.
* `iwasawa_two`: the Iwasawa structure for the symmetric group `equiv.perm α` acting on ordered pairs.

-/


open scoped Pointwise

namespace Equiv.Perm

open MulAction

variable {α : Type _} [DecidableEq α] [Fintype α]

def Iwt (s : Finset α) := (Equiv.Perm.ofSubtype : Equiv.Perm (s : Set α) →* Equiv.Perm α)
def IwasawaT (s : Finset α) : Subgroup (Equiv.Perm α) := (Iwt s).range

def IwasawaT' (s : Finset α) := fixingSubgroup (Equiv.Perm α) (sᶜ : Set α)

lemma fixingSubgroup_conj {G α : Type*} [Group G] [MulAction G α]
    (s : Set α) (g : G) :
    fixingSubgroup G (g • s) = MulAut.conj g • (fixingSubgroup G s) := by
  ext k
  simp only [mem_fixingSubgroup_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rw [Equiv.forall_congr (toPerm g⁻¹)]
  intro x
  simp only [toPerm_apply]
  rw [← Set.mem_smul_set_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, mul_smul, smul_inv_smul, smul_left_cancel_iff]

omit [Fintype α] in
lemma IwasawaT'_isConj (s : Finset α) (g : Equiv.Perm α) :
    IwasawaT' (g • s) = MulAut.conj g • (IwasawaT' s) := by
  ext k
  unfold IwasawaT'
  simp only [Finset.coe_smul_finset, mem_fixingSubgroup_iff,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rw [Equiv.forall_congr (toPerm g⁻¹)]
  intro x
  simp only [toPerm_apply]
  rw [← Set.mem_smul_set_iff_inv_smul_mem]
  simp only [Set.mem_compl_iff, Perm.smul_def, smul_compl_set, MulAut.smul_def,
    MulAut.conj_inv_apply, coe_mul, Function.comp_apply, apply_inv_self,
    EmbeddingLike.apply_eq_iff_eq]

omit [DecidableEq α] [Fintype α] in
lemma Equiv.Perm.ofSubtype_range_eq (s : Set α) [DecidablePred fun a ↦ a ∈ s]:
  (Equiv.Perm.ofSubtype : Equiv.Perm s →* Equiv.Perm α).range =
    fixingSubgroup (Equiv.Perm α) (sᶜ : Set α) := by
  ext k
  simp only [mem_fixingSubgroup_iff, Set.mem_compl_iff, Finset.mem_coe, Perm.smul_def, Finset.coe_sort_coe,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    intro y hy
    rw [ofSubtype_apply_of_not_mem k hy]
  · intro h
    have hks : s = k • s := by
      apply le_antisymm
      · intro x hx
        rw [Set.mem_smul_set_iff_inv_smul_mem, Perm.smul_def]
        by_contra hx'
        rw [← h _ hx', apply_inv_self] at hx'
        exact hx' hx
      · intro a ha
        by_contra ha'
        rw [← h _ ha', ← Perm.smul_def, Set.smul_mem_smul_set_iff] at ha
        exact ha' ha
    suffices hk' : _ by
      use Equiv.Perm.subtypePerm k hk'
      rw [Equiv.Perm.ofSubtype_subtypePerm]
      simp only [ne_eq, Finset.mem_coe]
      intro x
      rw [not_imp_comm]
      exact h x
    intro x
    rw [← Equiv.Perm.smul_def]
    nth_rewrite 2 [hks]
    rw [Set.smul_mem_smul_set_iff]

lemma _root_.MulAction.smul_compl_set_eq {G α : Type*} [Group G] [MulAction G α]
    (s : Set α) (g : G) :
    (g • s)ᶜ = g • sᶜ := by
  ext k
  simp only [Set.mem_compl_iff, smul_compl_set]


lemma this1 (G H : Type*) [Group H] [Group G] (f : H →* G) (g : G) :
    MulAut.conj g • f.range = ((MulAut.conj g).toMonoidHom.comp f).range := by
  simp only [← MonoidHom.map_range]
  rfl

def Equiv.permCongrMul {α β : Type*} (e : α ≃ β) :
    Equiv.Perm α ≃* Equiv.Perm β := {
  Equiv.permCongr e with
  map_mul' := fun f g ↦ by ext b; simp }

omit [Fintype α] in
theorem IwasawaT_is_conj' (s : Finset α) (g : Equiv.Perm α) :
    IwasawaT (g • s) = MulAut.conj g • (IwasawaT s) := by
  unfold IwasawaT
  unfold Iwt
  simp only [Equiv.Perm.ofSubtype_range_eq]
  simp only [Finset.coe_smul_finset, ← smul_compl_set]
  apply Equiv.Perm.fixingSubgroup_conj

omit [Fintype α] in
theorem IwasawaT_is_conj (s : Finset α) (g : Equiv.Perm α) :
    IwasawaT (g • s) = MulAut.conj g • (IwasawaT s) := by
  unfold IwasawaT

  have hkg : ∀ a, a ∈ s ↔ g a ∈ g • s := by
    intro a
    rw [← Equiv.Perm.smul_def, Finset.smul_mem_smul_finset_iff]

  let kg : s ≃ (g • s : Finset α) := Equiv.subtypeEquiv g hkg
  let kg' := Equiv.permCongrMul kg

  /-
  Iwt (g • s) : Perm (g • s) → Perm α
  Iwt s : Perm s → Perm α

  kg' : Perm s → Perm (g • s), h ↦ g ∘ h ∘ g⁻¹
    kg' h (g • x) = g • (h x)

  Iwt (g • s) ∘ kg' : Perm s → Perm α
    h ↦ g ∘ h ∘ g⁻¹ sur g • s, identité ailleurs
        g • x ↦ g • (h x)

        = g * (Iwt s x) * g⁻¹
        = g ∘ (Iwt s) ∘ g⁻¹
  -/

  suffices (Iwt (g • s)).comp kg'.toMonoidHom
    = ((MulAut.conj g).toMonoidHom.comp (Iwt s)) by
    rw [this1, ← this, ← SetLike.coe_set_eq]
    simp only [Finset.coe_sort_coe, MonoidHom.coe_range, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      EquivLike.surjective_comp, EquivLike.range_comp]

  ext h x
  unfold Iwt
  simp only [Finset.coe_sort_coe, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, coe_mul]
  by_cases hx : g⁻¹ x ∈ s
  · suffices hx' : x ∈ g • s by
      rw [ofSubtype_apply_of_mem h hx]
      rw [ofSubtype_apply_of_mem ((Equiv.permCongrMul kg) h) hx']
      unfold Equiv.permCongrMul
      simp only [toFun_as_coe, invFun_as_coe, permCongr_symm, subtypeEquiv_symm, MulEquiv.coe_mk,
        coe_fn_mk, permCongr_apply, subtypeEquiv_apply, EmbeddingLike.apply_eq_iff_eq]
      rfl
    exact Finset.inv_smul_mem_iff.mp hx
  · suffices hx' : x ∉ g • s by
      rw [ofSubtype_apply_of_not_mem h hx]
      rw [ofSubtype_apply_of_not_mem ((Equiv.permCongrMul kg) h) hx']
      simp only [apply_inv_self]
    rw [← Finset.inv_smul_mem_iff]
    exact hx

-- The Iwasawa structure for the symmetric group acting on ordered pairs
def iwasawa_two : IwasawaStructure (Equiv.Perm α) (Nat.Combination α 2) where
  T := fun s ↦ IwasawaT (s.val)
  is_comm := fun s ↦ by
    simp only [IwasawaT, Finset.coe_sort_coe, Iwt]
    suffices Std.Commutative (α := Perm s) (· * ·) by
      let _ : CommGroup (Perm s) :=
      { __ := (inferInstance : Group (Perm s)),
        mul_comm := this.comm }
      apply MonoidHom.range_isCommutative
    rw [Equiv.Perm.isCommutative_iff]
    apply le_of_eq
    simp only [Finset.mem_coe, Fintype.card_coe]
    exact s.prop
  is_conj g := fun s ↦ IwasawaT_is_conj s.val g
  is_generator := by
    rw [eq_top_iff]
    rw [← Equiv.Perm.closure_isSwap]
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    obtain ⟨a, b, hab, rfl⟩ := hg
    let s : Nat.Combination α 2 := ⟨{a, b}, Finset.card_pair hab⟩
    apply Subgroup.mem_iSup_of_mem s
    unfold IwasawaT
    unfold Iwt
    rw [Equiv.Perm.ofSubtype_range_eq]
    rw [mem_fixingSubgroup_iff]
    intro x hx
    simp only [s, Finset.mem_singleton, Finset.coe_insert, Finset.coe_singleton, Set.mem_singleton_iff] at hx
    simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_insert_iff] at hx
    rw [not_or] at hx
    apply Equiv.swap_apply_of_ne_of_ne hx.left hx.right

/-- If α has at least 5 elements, then
the only nontrivial normal sugroup of (perm α) is the alternating_group. -/
theorem Equiv.Perm.normal_subgroups {α : Type _} [DecidableEq α] [Fintype α]
    (hα : 5 ≤ Fintype.card α) {N : Subgroup (Equiv.Perm α)} (hnN : N.Normal) (ntN : Nontrivial N) :
    alternatingGroup α ≤ N := by
  rw [← alternatingGroup.commutator_group_eq hα]
  refine commutator_le_iwasawa ?_ iwasawa_two hnN ?_
  · -- quasipreprimitive action
    apply IsPreprimitive.isQuasipreprimitive
    apply Nat.Combination_isPreprimitive
    norm_num
    apply lt_of_lt_of_le _ hα; norm_num
    apply ne_of_gt
    apply lt_of_lt_of_le _ hα; norm_num
  -- N acts nontrivially
  intro h
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN
  obtain ⟨s, hs⟩ := Nat.combination.mulAction_faithful
    (G := Equiv.Perm α) (α := α) (g := g) 2
    (by norm_num)
    (by rw [ENat.card_eq_coe_fintype_card, ENat.coe_le_coe]
        apply le_trans (by norm_num) hα)
    (by exact hg_ne)
  apply hs
  suffices s ∈ fixedPoints N (Nat.Combination α 2) by
    rw [mem_fixedPoints] at this
    exact this ⟨g, hgN⟩
  rw [h, Set.top_eq_univ]
  apply Set.mem_univ

end Equiv.Perm

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
import Jordan.MulActionFinset
import Jordan.Jordan
import Jordan.PermMaximal

/-!
# Normal subgroups of the symmetric group

* `Equiv.Perm.normal_subgroups` : a nontrivial normal subgroup of `Equiv.Perm α` contains the alternating group.
* `Iw2`: the Iwasawa structure for the symmetric group `equiv.perm α` acting on ordered pairs.

-/


open scoped Pointwise

namespace Equiv.Perm

open MulAction

variable {α : Type _} [DecidableEq α] [Fintype α]

def Iwt (s : Finset α) := (Equiv.Perm.ofSubtype : Equiv.Perm (s : Set α) →* Equiv.Perm α)
def IwT (s : Finset α) : Subgroup (Equiv.Perm α) := (Iwt s).range
set_option linter.uppercaseLean3 false in 
#align equiv.perm.Iw_T Equiv.Perm.IwT


lemma this1 (G H : Type*) [Group H] [Group G] (f : H →* G) (g : G) :
    MulAut.conj g • f.range = ((MulAut.conj g).toMonoidHom.comp f).range := by
  simp only [← MonoidHom.map_range]
  rfl

def Equiv.permCongrMul {α β : Type*} (e : α ≃ β) : 
    Equiv.Perm α ≃* Equiv.Perm β := {
  Equiv.permCongr e with
  map_mul' := fun f g ↦ by
    ext b
    simp only [toFun_as_coe_apply, permCongr_apply, coe_mul, Function.comp_apply, symm_apply_apply] }

theorem IwT_is_conj (s : Finset α) (g : Equiv.Perm α) : 
    IwT (g • s) = MulAut.conj g • (IwT s) := by
  unfold IwT
  
  let kg : s ≃ (g • s) := Equiv.subtypeEquiv g
    (by intro a
        rw [← Equiv.Perm.smul_def, Finset.smul_mem_smul_finset_iff])
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
    
  suffices : (Iwt (g • s)).comp kg'.toMonoidHom 
    = ((MulAut.conj g).toMonoidHom.comp (Iwt s))
  rw [this1]
  rw [← this]
  rw [← SetLike.coe_set_eq]
  simp only [Finset.coe_sort_coe, MonoidHom.coe_range, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    EquivLike.surjective_comp, EquivLike.range_comp]
  
  ext h x
  unfold Iwt
  simp only [Finset.coe_sort_coe, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply,
    coe_mul]
  unfold Equiv.permCongrMul
  simp only [toFun_as_coe, invFun_as_coe, permCongr_symm, subtypeEquiv_symm, MulEquiv.coe_mk, coe_fn_mk]
  by_cases hx : g⁻¹ x ∈ s
  · rw [ofSubtype_apply_of_mem h hx]
    rw [ofSubtype_apply_of_mem]
    simp only [Finset.coe_sort_coe, permCongr_apply, subtypeEquiv_symm, subtypeEquiv_apply,
      EmbeddingLike.apply_eq_iff_eq]
    rfl
    simp only [Finset.coe_smul_finset]
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact hx
  · rw [ofSubtype_apply_of_not_mem h hx]
    rw [ofSubtype_apply_of_not_mem]
    simp only [apply_inv_self]
    simp only [Finset.coe_smul_finset]
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact hx
#align equiv.perm.IwT_is_conj Equiv.Perm.IwT_is_conj

-- The Iwasawa structure for the symmetric group acting on ordered pairs
def iw2 : IwasawaStructure (Equiv.Perm α) (Nat.Combination α 2) where
  T s := sorry -- IwT ↑s
  is_comm s := by
    apply MonoidHom.range_isCommutative
    rw [← Equiv.Perm.isCommutative_iff]
    apply le_of_eq
    simp only [coeSort_coeBase, Fintype.card_coe]
    exact s.prop
  IsConj g s := IwT_is_conj (↑s) g
  is_generator := by
    rw [eq_top_iff]
    rw [← Equiv.Perm.closure_isSwap]
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq] at hg 
    obtain ⟨a, b, hab, rfl⟩ := hg
    let s : Nat.finset α 2 := ⟨{a, b}, Finset.card_doubleton hab⟩
    apply Subgroup.mem_iSup_of_mem s
    dsimp [Iw_T, Iw_t]
    let a' : ↥s :=
      ⟨a, by
        change a ∈ ↑s; dsimp [s]
        exact Finset.mem_insert_self a {b}⟩
    let b' : ↥s :=
      ⟨b, by
        change b ∈ ↑s; dsimp [s]
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_singleton]⟩
    use Equiv.swap a' b'
    ext
    have : x ∈ {a, b} ↔ x = a ∨ x = b := by rw [Finset.mem_insert, Finset.mem_singleton]
    cases' em (x ∈ {a, b}) with hx hx
    · rw [Equiv.Perm.ofSubtype_apply_of_mem (Equiv.swap a' b') hx]
      cases' this.mp hx with ha hb
      · conv_rhs => rw [ha]
        have ha' : a' = ⟨x, hx⟩; rw [← Subtype.coe_inj]; change a = x; exact ha.symm
        rw [ha']
        simp only [Equiv.swap_apply_left]; rfl
      · conv_rhs => rw [hb]
        have hb' : b' = ⟨x, hx⟩; rw [← Subtype.coe_inj]; change b = x; exact hb.symm
        rw [hb']
        simp only [Equiv.swap_apply_right]; rfl
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem (Equiv.swap a' b') hx]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · intro ha; apply hx; rw [this]; apply Or.intro_left; exact ha
      · intro hb; apply hx; rw [this]; apply Or.intro_right; exact hb
#align equiv.perm.Iw2 Equiv.Perm.iw2

/-
lemma finset.mem_doubleton_iff (a b x : α) : x ∈ ({a, b} : finset α) ↔ (x = a ∨ x = b) :=
begin
  rw [finset.mem_insert, finset.mem_singleton],
end
 -/
/-- If α has at least 5 elements, then
the only nontrivial normal sugroup of (perm α) is the alternating_group. -/
theorem Equiv.Perm.normal_subgroups {α : Type _} [DecidableEq α] [Fintype α]
    (hα : 5 ≤ Fintype.card α) {N : Subgroup (Equiv.Perm α)} (hnN : N.Normal) (ntN : Nontrivial N) :
    alternatingGroup α ≤ N :=
  by
  rw [← alternatingGroup.commutator_group_eq hα]
  refine' commutator_le_iwasawa _ Iw2 hnN _
  · -- quasipreprimitive action
    apply IsPreprimitive.isQuasipreprimitive
    apply nat.finset_is_preprimitive_of
    norm_num
    apply lt_of_lt_of_le _ hα; norm_num
    apply ne_of_gt
    apply lt_of_lt_of_le _ hα; norm_num
  -- N acts nontrivially
  intro h
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN
  obtain ⟨s, hs⟩ := Nat.finset.mulAction_faithful 2 _ _ _
  apply hs
  suffices : s ∈ fixed_points N (Nat.finset α 2)
  rw [mem_fixed_points] at this ; exact this ⟨g, hgN⟩
  rw [h]; rw [Set.top_eq_univ]; apply Set.mem_univ
  infer_instance
  norm_num
  apply lt_of_lt_of_le _ hα; norm_num
  convert hg_ne; ext x; rfl
#align equiv.perm.equiv.perm.normal_subgroups Equiv.Perm.Equiv.Perm.normal_subgroups

end Equiv.Perm


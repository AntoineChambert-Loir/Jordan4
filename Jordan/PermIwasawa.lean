/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module perm_iwasawa
-/
import Mathbin.Tactic.Basic
import Mathbin.Tactic.Group
import Mathbin.GroupTheory.Solvable
import Mathbin.GroupTheory.GroupAction.SubMulAction
import Oneshot.ForMathlib.Set
import Oneshot.ForMathlib.GroupTheorySubgroupBasic
import Oneshot.ForMathlib.Alternating
import Oneshot.MulActionFinset
import Oneshot.Jordan
import Oneshot.PermMaximal

/-!
# Normal subgroups of the symmetric group

* `equiv.perm.normal_subgroups` : a nontrivial normal subgroup of `equiv.perm α` contains the alternating group.
* `Iw2`: the Iwasawa structure for the symmetric group `equiv.perm α` acting on ordered pairs.

-/


open scoped Pointwise

namespace Equiv.Perm

open MulAction

variable {α : Type _} [DecidableEq α] [Fintype α]

def iwT (s : Finset α) : Equiv.Perm s →* Equiv.Perm α :=
  Equiv.Perm.ofSubtype
#align equiv.perm.Iw_t Equiv.Perm.iwT

/- warning: equiv.perm.Iw_T clashes with equiv.perm.Iw_t -> Equiv.Perm.iwT
Case conversion may be inaccurate. Consider using '#align equiv.perm.Iw_T Equiv.Perm.iwTₓ'. -/
#print Equiv.Perm.iwT /-
def iwT (s : Finset α) : Subgroup (Equiv.Perm α) :=
  (iwT s).range
#align equiv.perm.Iw_T Equiv.Perm.iwT
-/

theorem IwT_is_conj (s : Finset α) (g : Equiv.Perm α) : iwT (g • s) = MulAut.conj g • iwT s :=
  by
  unfold Iw_T
  let ts := Iw_t s; let tgs := Iw_t (g • s)
  let Ts := Iw_T s; let Tgs := Iw_T (g • s)
  let kg : ↥s ≃ ↥(g • s) :=
    Equiv.subtypeEquiv g
      (by
        intro a
        rw [← Equiv.Perm.smul_def]
        rw [Finset.smul_mem_smul_finset_iff])
  have this1 : MulAut.conj g • (Iw_t s).range = ((MulAut.conj g).toMonoidHom.comp (Iw_t s)).range
  simp only [← MonoidHom.map_range]; rfl
  rw [this1]
  suffices this2 : tgs.range = ((MulAut.conj g).toMonoidHom.comp ts).range
  rw [this2]
  let pg : Equiv.Perm ↥s → Equiv.Perm ↥(g • s) := fun k => (kg.symm.trans k).trans kg
  let pg' : Equiv.Perm ↥(g • s) → Equiv.Perm ↥s := fun k => (kg.trans k).trans kg.symm
  have hpgg' : ∀ k, k = pg (pg' k) := by
    intro k
    change k = (kg.symm.trans ((kg.trans k).trans kg.symm)).trans kg
    simp only [← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]
    rw [Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl]
  /- Useless
    have hpg'g : ∀ k, k = pg' (pg k) ,
    { intro k,
      change k = (kg.trans ((kg.symm.trans k).trans kg)).trans kg.symm,
      simp only [← equiv.trans_assoc, equiv.self_trans_symm, equiv.refl_trans],
      rw [equiv.trans_assoc, equiv.self_trans_symm, equiv.trans_refl], }, -/
  suffices this3 : ∀ k : Equiv.Perm ↥s, ((MulAut.conj g).toMonoidHom.comp ts) k = tgs (pg k)
  ext
  constructor
  rintro ⟨k, rfl⟩; use pg' k; conv_rhs => rw [hpgg' k]; rw [this3]
  rintro ⟨k, rfl⟩; use pg k; rw [this3]
  intro k
  ext x
  cases' em (x ∈ g • s) with hx hx'
  · -- x ∈ g • s
    dsimp only [tgs, Iw_T, Iw_t]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    dsimp only [pg]
    simp only [Subtype.coe_mk, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, Equiv.Perm.coe_mul, Equiv.subtypeEquiv_symm, Equiv.coe_trans,
      Equiv.subtypeEquiv_apply, EmbeddingLike.apply_eq_iff_eq]
    dsimp [ts, Iw_T, Iw_t]; rw [Equiv.Perm.ofSubtype_apply_of_mem]
    apply congr_arg; apply congr_arg
    rw [← Subtype.coe_inj]; simp only [Subtype.coe_mk]
    rfl
    · rw [← Equiv.Perm.smul_def, Finset.inv_smul_mem_iff]; exact hx
    exact hx
  · -- x ∉ g • s
    dsimp only [tgs, Iw_T, Iw_t]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    dsimp only [ts, Iw_T, Iw_t]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply,
      Equiv.Perm.coe_mul]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    simp only [Equiv.Perm.apply_inv_self]
    · intro hx; apply hx'; rw [← Finset.inv_smul_mem_iff]; exact hx
    exact hx'
#align equiv.perm.IwT_is_conj Equiv.Perm.IwT_is_conj

-- The Iwasawa structure for the symmetric group acting on ordered pairs
def iw2 : IwasawaStructure (Equiv.Perm α) (Nat.finset α 2)
    where
  t s := iwT ↑s
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


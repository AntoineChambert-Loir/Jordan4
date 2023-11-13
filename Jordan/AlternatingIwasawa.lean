/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module alternating_iwasawa
-/
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Jordan.Mathlib.Alternating
import Jordan.IndexNormal
import Jordan.Primitive
import Jordan.MultipleTransitivity
import Jordan.PermIwasawa
import Jordan.AlternatingMaximal
import Jordan.V4

-- import tactic.basic tactic.group
-- import group_theory.solvable
open scoped Pointwise

/-
namespace alternatingGroup

variable (α : Type*) [DecidableEq α] [Fintype α]

def iwasawa_three : IwasawaStructure (alternatingGroup α) (Nat.Combination α 3) where
  T := fun s => Subgroup.subgroupOf (Equiv.Perm.IwasawaT s.val) _
  is_comm := sorry
  is_conj := fun g s => by
    dsimp only [Nat.combination_mulAction.coe_apply']
    have : g • (s : Finset α) = (g : Equiv.Perm α) • (s : Finset α)
    rfl
    rw [this, Equiv.Perm.IwasawaT_is_conj]
    sorry
  is_generator := sorry }

def iwasawa_four : IwasawaStructure (alternatingGroup α) (Nat.Combination α 4) where
  T := fun s => Subgroup.subgroupOf (Equiv.Perm.IwasawaT s.val) _
  is_comm := sorry
  is_conj := sorry
  is_generator := sorry }

end alternatingGroup
-/

open MulAction

theorem Subgroup.smul_le_iff_le_inv_smul {G : Type _} [Group G] (g : G) (H K : Subgroup G) :
    MulAut.conj g • H ≤ K ↔ H ≤ MulAut.conj g⁻¹ • K := by
  simp only [← SetLike.coe_subset_coe, Subgroup.coe_pointwise_smul, map_inv,
    Set.set_smul_subset_iff]
#align subgroup.smul_le_iff_le_inv_smul Subgroup.smul_le_iff_le_inv_smul

theorem mulAut_smul_subgroupOf_eq {G : Type _} [Group G] {N H : Subgroup G}
    (f : MulAut G) (f' : MulAut N) (hff' : ∀ n : N, f n = f' n) :
    (f • H).subgroupOf N = f' • H.subgroupOf N := by
  -- dsimp [SMul.smul, MulDistribMulAction.toMonoidHom]
  -- change (subgroup.map f.to_monoid_hom H).subgroup_of N = subgroup.map f'.to_monoid_hom _,
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MonoidHom.coe_mk,
    exists_prop]
  constructor
  · rintro ⟨y, hy, hyx⟩
    dsimp only [MulDistribMulAction.toMonoidEnd_apply,
      MulDistribMulAction.toMonoidHom_apply, MulAut.smul_def] at hyx
    use! y
    · -- y ∈ N
      suffices y = f'.symm x by
        rw [this]
        apply SetLike.coe_mem
      rw [← MulEquiv.apply_eq_iff_eq f, hyx, hff', Subtype.coe_inj, MulEquiv.apply_symm_apply]
    apply And.intro hy
    simp only [MulDistribMulAction.toMonoidEnd_apply,
      MulDistribMulAction.toMonoidHom_apply, MulAut.smul_def,
      SetLike.coe_eq_coe]
    rw [← Subtype.coe_inj, ← hff' _]
    exact hyx
  · rintro ⟨y, hy, rfl⟩
    use ↑y
    apply And.intro hy
    apply hff'
#align mul_aut_smul_subgroup_of_eq mulAut_smul_subgroupOf_eq

def Subgroup.mulEquivOfMulEquiv {G G' : Type _} [Group G] [Group G'] (f : G ≃* G') {H : Subgroup G}
    {H' : Subgroup G'} (h : ∀ g : G, g ∈ H ↔ f g ∈ H') : H ≃* H' :=
  by
  refine' MonoidHom.toMulEquiv _ _ _ _
  · apply MonoidHom.codRestrict (MonoidHom.restrict f.toMonoidHom H) H'
    rintro ⟨g, hg⟩
    simp only [MonoidHom.restrict_apply, Subgroup.coe_mk, MulEquiv.coe_toMonoidHom]
    rw [← h]; exact hg
  · apply MonoidHom.codRestrict (MonoidHom.restrict f.symm.toMonoidHom H') H
    rintro ⟨g', hg'⟩
    rw [h _]
    simp only [MonoidHom.restrict_apply, Subgroup.coe_mk, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    exact hg'
  · ext; simp
  · ext; simp
#align subgroup.mul_equiv_of_mul_equiv Subgroup.mulEquivOfMulEquiv

variable {α : Type _} [Fintype α] [DecidableEq α]

namespace Equiv.Perm

theorem mem_iff_smul_mem_smul_set (s : Finset α) (g : Equiv.Perm α) (a : α) :
    a ∈ s ↔ g a ∈ g • s := by
  rw [← Finset.smul_mem_smul_finset_iff g, Equiv.Perm.smul_def]

def IwConj (s : Finset α) (g : Equiv.Perm α) :
    Equiv.Perm s ≃* Equiv.Perm (g • s : Finset α) :=
  { Equiv.permCongr (Equiv.subtypeEquiv g (mem_iff_smul_mem_smul_set s g)) with
    map_mul' := fun h k => Equiv.ext fun x => by simp }
set_option linter.uppercaseLean3 false in
#align equiv.perm.Iw_conj Equiv.Perm.IwConj

/-
def iwConj' {s t : Finset α} {g : Equiv.Perm α} (htgs : t = g • s) :
    Equiv.Perm s ≃* Equiv.Perm t :=
  {
    Equiv.permCongr
      (@Equiv.subtypeEquiv α α _ _ (g : α ≃ α)
        (by
          intro a
          rw [htgs, ← Equiv.Perm.smul_def, ← Finset.smul_mem_smul_finset_iff g])) with
    map_mul' := fun h k =>
      Equiv.ext fun x => by simp }
#align equiv.perm.Iw_conj' Equiv.Perm.iwConj'

theorem iwConj'_trans {s t u : Finset α} {g k : Equiv.Perm α} (htgs : t = g • s)
    (hukt : u = k • t) :
    let hukgs : u = (k * g) • s := by rw [mul_smul, ← htgs, hukt]
    (iwConj' htgs).trans (iwConj' hukt) = iwConj' hukgs :=
  by
  intro hukgs
  rfl
#align equiv.perm.Iw_conj'_trans Equiv.Perm.iwConj'_trans

theorem iwConj'_symm {s t : Finset α} {g : Equiv.Perm α} (htgs : t = g • s) :
    let hsg't : s = g⁻¹ • t := by rw [htgs, inv_smul_smul]
    (iwConj' htgs).symm = iwConj' hsg't :=
  by
  intro hsg't
  rfl
#align equiv.perm.Iw_conj'_symm Equiv.Perm.iwConj'_symm

theorem iwConj'_eq_apply {s t : Finset α} {g : Equiv.Perm α} (htgs : t = g • s) (k : Equiv.Perm s) :
    (MulAut.conj g).toMonoidHom.comp (Equiv.Perm.ofSubtype : Equiv.Perm s →* Equiv.Perm α) k =
      (Equiv.Perm.ofSubtype : Equiv.Perm t →* Equiv.Perm α) (iwConj' htgs k) :=
  by
  dsimp only [Iw_conj']
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply,
    coe_mul, Equiv.toFun_as_coe, MulEquiv.coe_mk]
  cases' em (x ∈ t) with hx hx
  · -- x ∈ t
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    rfl; exact hx
  · -- x ∉ t
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    simp only [apply_inv_self]
    exact hx
    rw [htgs, ← Finset.inv_smul_mem_iff] at hx
    exact hx
#align equiv.perm.Iw_conj'_eq_apply Equiv.Perm.iwConj'_eq_apply

theorem iwConj'_eq {s t : Finset α} {g : Equiv.Perm α} (htgs : t = g • s) :
    Equiv.Perm.ofSubtype.comp (iwConj' htgs).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp Equiv.Perm.ofSubtype :=
  by
  ext k x
  rw [Iw_conj'_eq_apply]
  rfl
#align equiv.perm.Iw_conj'_eq Equiv.Perm.iwConj'_eq

-/

theorem IwConj_eq (s : Finset α) (g : Equiv.Perm α) (k : Equiv.Perm ↥s) :
    (MulAut.conj g).toMonoidHom.comp (Equiv.Perm.ofSubtype : Equiv.Perm s →* Equiv.Perm α) k =
      (Equiv.Perm.ofSubtype : Equiv.Perm (g • s : Finset α) →* Equiv.Perm α) (IwConj s g k) :=
  by
  dsimp only [IwConj]
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply,
    Equiv.Perm.coe_mul]
  cases' em (x ∈ g • s) with hx hx'
  · -- x ∈ g • s
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    simp only [Subtype.coe_mk, Equiv.subtypeEquiv_symm, Equiv.toFun_as_coe, MulEquiv.coe_mk,
      Equiv.permCongr_apply, Equiv.subtypeEquiv_apply, EmbeddingLike.apply_eq_iff_eq]
    apply congr_arg; apply congr_arg
    rw [← Subtype.coe_inj]; simp only [Subtype.coe_mk]; rfl
    exact hx
    -- rw [← Finset.inv_smul_mem_iff] at hx ; exact hx
  · -- x ∉ g • s
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    simp only [Equiv.Perm.apply_inv_self]
    exact hx'
    · rw [← Finset.inv_smul_mem_iff] at hx' ; exact hx'
set_option linter.uppercaseLean3 false in
#align equiv.perm.Iw_conj_eq Equiv.Perm.IwConj_eq

theorem Iw_is_conj' (s : Finset α) (g : Equiv.Perm α) :
    Equiv.Perm.ofSubtype.comp (IwConj s g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp Equiv.Perm.ofSubtype :=
  by
  ext k x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply,
    Equiv.Perm.coe_mul]
  rw [← IwConj_eq]
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply,
    Equiv.Perm.coe_mul]
set_option linter.uppercaseLean3 false in
#align equiv.perm.Iw_is_conj' Equiv.Perm.Iw_is_conj'

/-
theorem iwConj'_sign {s t : Finset α} {g : Equiv.Perm α} (htgs : t = g • s) (k : Equiv.Perm s) :
    ((iwConj' htgs) k).sign = k.sign :=
  by
  dsimp only [Iw_conj', Equiv.permCongr, Equiv.equivCongr]
  refine' Equiv.Perm.sign_symm_trans_trans k _
#align equiv.perm.Iw_conj'_sign Equiv.Perm.iwConj'_sign

theorem Iw_conj_symm'_sign {s t : Finset α} {g : Equiv.Perm α} (htgs : t = g • s)
    (k : Equiv.Perm t) : ((iwConj' htgs).symm k).sign = k.sign :=
  by
  conv_rhs => rw [← MulEquiv.apply_symm_apply (Iw_conj' htgs) k]
  rw [Iw_conj'_sign]
#align equiv.perm.Iw_conj_symm'_sign Equiv.Perm.Iw_conj_symm'_sign

-/

theorem IwConj_sign (s : Finset α) (g : Equiv.Perm α) (k : Equiv.Perm s) :
    Equiv.Perm.sign ((IwConj s g) k) = Equiv.Perm.sign k :=
  by
  dsimp only [IwConj, Equiv.permCongr, Equiv.equivCongr]
  refine' Equiv.Perm.sign_symm_trans_trans k _
set_option linter.uppercaseLean3 false in
#align equiv.perm.Iw_conj_sign Equiv.Perm.IwConj_sign

theorem IwConj_symm_sign (s : Finset α) (g : Equiv.Perm α) (k : Equiv.Perm (g • s : Finset α)) :
    Equiv.Perm.sign ((IwConj s g).symm k) = Equiv.Perm.sign k :=
  by
  let e : s ≃ (g • s : Finset α) := by
    apply Equiv.subtypeEquiv g
    · intro a
      rw [← Finset.smul_mem_smul_finset_iff g, Equiv.Perm.smul_def]
  suffices ∀ k, (IwConj s g).symm k = (Equiv.permCongr e.symm) k
    by
    rw [this]
    dsimp only [Equiv.permCongr, Equiv.equivCongr]
    simp only [Equiv.coe_fn_mk]
    rw [Equiv.Perm.sign_symm_trans_trans k e.symm]
  · intro k; rfl
set_option linter.uppercaseLean3 false in
#align equiv.perm.Iw_conj_symm_sign Equiv.Perm.IwConj_symm_sign

end Equiv.Perm

namespace alternatingGroup

open Equiv.Perm

def Subgroup.equivMk {G G' : Type _} [Group G] [Group G'] (e : G ≃* G') {H : Subgroup G}
    {H' : Subgroup G'} (h : ∀ g : G, g ∈ H ↔ e g ∈ H') : H ≃* H'
    where
  toFun g := ⟨e g, (h g).mp g.prop⟩
  invFun g' := ⟨e.symm g', (h _).mpr (by simp only [MulEquiv.apply_symm_apply, SetLike.coe_mem])⟩
  left_inv g := by simp only [Subgroup.coe_mk, MulEquiv.symm_apply_apply, SetLike.eta]
  right_inv g' := by simp only [MulEquiv.apply_symm_apply, Subgroup.coe_mk, SetLike.eta]
  map_mul' x y := by simp only [Subgroup.coe_mul, map_mul, MulMemClass.mk_mul_mk]
#align alternating_group.subgroup.equiv_mk alternatingGroup.Subgroup.equivMk

/- def iwConj' {s t : Finset α} {g : Equiv.Perm α} (htgs : t = g • s) :
    alternatingGroup s ≃* alternatingGroup t :=
  Subgroup.equivMk (Equiv.Perm.iwConj' htgs) fun k => by
    simp only [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.iwConj'_sign]
#align alternating_group.Iw_conj' alternatingGroup.iwConj'
-/

theorem Iw_is_conj_alt (s : Finset α) (g : alternatingGroup α) :
    (Subgroup.map (Equiv.Perm.ofSubtype : Equiv.Perm (g • s : Finset α) →* Equiv.Perm α)
            (alternatingGroup (g • s : Finset α))).subgroupOf
        (alternatingGroup α) =
      MulAut.conj g •
        (Subgroup.map (Equiv.Perm.ofSubtype : Equiv.Perm s →* Equiv.Perm α)
              (alternatingGroup s)).subgroupOf
          (alternatingGroup α) :=
  by
  rw [← mulAut_smul_subgroupOf_eq (MulAut.conj ↑g) (MulAut.conj g)]
  apply congr_arg
  suffices
    Subgroup.map (Equiv.Perm.ofSubtype : Equiv.Perm (g • s : Finset α) →* Equiv.Perm α)
        (alternatingGroup (g • s : Finset α)) =
      Subgroup.map (Equiv.Perm.ofSubtype.comp (Equiv.Perm.IwConj s g).toMonoidHom)
        (alternatingGroup (s : Finset α))
    by
    rw [this]
    change _ = Subgroup.map (MulAut.conj g).toMonoidHom _
    rw [Subgroup.map_map]
    apply congr_arg₂
    apply Equiv.Perm.Iw_is_conj'
    rfl
  · simp only [← Subgroup.map_map]
    apply congr_arg
    ext k
    simp only [Subgroup.mem_map, Equiv.Perm.mem_alternatingGroup, MulEquiv.coe_toMonoidHom,
      exists_prop]
    constructor
    · intro hk
      use (IwConj s ↑g).symm k
      simp only [IwConj_symm_sign, MulEquiv.apply_symm_apply]
      constructor
      exact Equiv.Perm.mem_alternatingGroup.mp hk
      sorry
    · rintro ⟨x, hx, hx'⟩
      rw [← hx']
      change sign ((IwConj s g) x) = 1
      simp only [IwConj_sign]
      exact hx
  ·-- ∀ n…
    intro n;
    rfl
#align alternating_group.Iw_is_conj_alt alternatingGroup.Iw_is_conj_alt

theorem isThreeCycle_is_ofSubtype (g : alternatingGroup α)
    (hg : Equiv.Perm.IsThreeCycle (g : Equiv.Perm α)) :
    ∃ s : Finset α,
      s.card = 3 ∧
        g ∈
          (Subgroup.map (Equiv.Perm.ofSubtype : Equiv.Perm s →* Equiv.Perm α)
                (alternatingGroup s)).subgroupOf
            (alternatingGroup α) :=
  by
  use (g : Equiv.Perm α).support
  constructor
  exact Equiv.Perm.IsThreeCycle.card_support hg
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.mem_map]
  let k : Equiv.Perm (g : Equiv.Perm α).support :=
    Equiv.Perm.subtypePerm (g : Equiv.Perm α) fun a => by simp only [Equiv.Perm.apply_mem_support]
  use k
  suffices : Equiv.Perm.ofSubtype k = g
  constructor
  -- because `rw equiv.perm.mem_alternating_group` does not work
  rw [@Equiv.Perm.mem_alternatingGroup (g : Equiv.Perm α).support _ _]
  rw [← Equiv.Perm.sign_ofSubtype, this]
  exact Equiv.Perm.IsThreeCycle.sign hg
  exact this
  · -- k.of_subtype = g
    apply Equiv.Perm.ofSubtype_subtypePerm
    · intro a; simp only [Equiv.Perm.mem_support, imp_self]
#align alternating_group.is_three_cycle_is_of_subtype alternatingGroup.isThreeCycle_is_ofSubtype

theorem Subgroup.map_closure_eq {G H : Type _} [Group G] [Group H] (f : H →* G) (s : Set H) :
    Subgroup.map f (Subgroup.closure s) = Subgroup.closure (Set.image f s) :=
  by
  apply symm
  apply Subgroup.closure_eq_of_le
  · intro g; rintro ⟨k, hk, rfl⟩
    exact ⟨k, Subgroup.subset_closure hk, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap]
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe]
    apply Subgroup.subset_closure
    apply Set.mem_image_of_mem; exact hg
#align alternating_group.subgroup.map_closure_eq alternatingGroup.Subgroup.map_closure_eq

theorem Subgroup.closure_subgroupOf_eq {G : Type _} [Group G] (N : Subgroup G) (s : Set G)
    (hs : s ≤ ↑N) : Subgroup.closure (N.Subtype ⁻¹' s) = (Subgroup.closure s).subgroupOf N :=
  by
  dsimp only [Subgroup.subgroupOf]
  have hN : Function.Injective N.subtype := by
    simp only [Subgroup.coeSubtype, Subtype.coe_injective]
  apply Subgroup.map_injective hN
  rw [subgroup.map_closure_eq]
  suffices : N.subtype '' (N.subtype ⁻¹' s) = s
  rw [this]
  rw [Subgroup.map_comap_eq]
  simp only [Subgroup.subtype_range, right_eq_inf, Subgroup.closure_le]
  exact hs
  rw [Set.image_preimage_eq_inter_range, Subgroup.coeSubtype, Subtype.range_coe_subtype,
    Set.inter_eq_left_iff_subset]
  exact hs
#align alternating_group.subgroup.closure_subgroup_of_eq alternatingGroup.Subgroup.closure_subgroupOf_eq

theorem closure_three_cycles_alternating_eq_top :
    Subgroup.closure {g : alternatingGroup α | Equiv.Perm.IsThreeCycle (g : Equiv.Perm α)} = ⊤ :=
  by
  suffices : Function.Injective (alternatingGroup α).Subtype
  apply Subgroup.map_injective this
  rw [subgroup.map_closure_eq]
  suffices :
    (alternatingGroup α).Subtype ''
        {g : alternatingGroup α | Equiv.Perm.IsThreeCycle (g : Equiv.Perm α)} =
      {g : Equiv.Perm α | Equiv.Perm.IsThreeCycle g}
  rw [this]
  rw [Equiv.Perm.closure_three_cycles_eq_alternating]
  rw [← Subgroup.comap_top _, Subgroup.map_comap_eq, Subgroup.subtype_range, inf_top_eq]
  · ext g
    simp only [Subgroup.coeSubtype, Set.mem_image, Set.mem_setOf_eq]
    constructor
    rintro ⟨k, hk, rfl⟩; exact hk
    intro hg
    use g
    rw [Equiv.Perm.mem_alternatingGroup]
    exact Equiv.Perm.IsThreeCycle.sign hg
    exact ⟨hg, rfl⟩
  simp only [Subgroup.coeSubtype, Subtype.coe_injective]
#align alternating_group.closure_three_cycles_alternating_eq_top alternatingGroup.closure_three_cycles_alternating_eq_top

theorem is_three_cycles_exists_ofSubtype (g : alternatingGroup α)
    (hg : Equiv.Perm.IsThreeCycle (g : Equiv.Perm α)) :
    ∃ s : Finset α,
      s.card = 3 ∧
        g ∈
          (Subgroup.map (Equiv.Perm.ofSubtype : Equiv.Perm s →* Equiv.Perm α)
                (alternatingGroup s)).subgroupOf
            (alternatingGroup α) :=
  by
  use (g : Equiv.Perm α).support
  constructor
  exact Equiv.Perm.IsThreeCycle.card_support hg
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.mem_map]
  let k : Equiv.Perm (g : Equiv.Perm α).support :=
    Equiv.Perm.subtypePerm (g : Equiv.Perm α) fun a => by simp only [Equiv.Perm.apply_mem_support]
  use k
  suffices : Equiv.Perm.ofSubtype k = g
  constructor
  -- because `rw equiv.perm.mem_alternating_group` does not work
  rw [@Equiv.Perm.mem_alternatingGroup (g : Equiv.Perm α).support _ _]
  rw [← Equiv.Perm.sign_ofSubtype, this]
  exact Equiv.Perm.IsThreeCycle.sign hg
  exact this
  · -- k.of_subtype = g
    apply Equiv.Perm.ofSubtype_subtypePerm
    · intro a; simp only [Equiv.Perm.mem_support, imp_self]
#align alternating_group.is_three_cycles_exists_of_subtype alternatingGroup.is_three_cycles_exists_ofSubtype

theorem Iw_is_generator_alt :
    (iSup fun s : { s : Finset α // s.card = 3 } =>
        (Subgroup.map Equiv.Perm.ofSubtype (alternatingGroup (s : Finset α))).subgroupOf
          (alternatingGroup α)) =
      ⊤ :=
  by
  rw [← closure_three_cycles_alternating_eq_top]
  have lemma1 :
    {g : alternatingGroup α | (g : Equiv.Perm α).IsThreeCycle} =
      (alternatingGroup α).Subtype ⁻¹' {g : Equiv.Perm α | g.IsThreeCycle} :=
    by ext g; simp only [Subgroup.coeSubtype, Set.preimage_setOf_eq]
  have lemma2 : {g : Equiv.Perm α | g.IsThreeCycle} ≤ alternatingGroup α :=
    by
    intro k hk
    -- simp only [set_like.mem_coe],
    apply Equiv.Perm.IsThreeCycle.mem_alternatingGroup
    exact hk
  apply le_antisymm
  · -- supr ≤ closure
    rw [lemma1]
    rw [subgroup.closure_subgroup_of_eq (alternatingGroup α) _ lemma2]
    rw [Equiv.Perm.closure_three_cycles_eq_alternating]
    rw [iSup_le_iff]
    rintro ⟨s, hs⟩
    dsimp only [Subgroup.subgroupOf]
    refine' Subgroup.comap_mono _
    intro g
    rintro ⟨k, hk, rfl⟩
    simp only [SetLike.mem_coe] at hk
    rw [Equiv.Perm.mem_alternatingGroup]
    rw [Equiv.Perm.sign_ofSubtype]
    exact equiv.perm.mem_alternating_group.mp hk
  · -- closure ≤ supr
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨s, hs3, hsg⟩ := is_three_cycles_exists_of_subtype g hg
    simp only [SetLike.mem_coe]
    apply Subgroup.mem_iSup_of_mem
    swap; exact ⟨s, hs3⟩
    exact hsg
#align alternating_group.Iw_is_generator_alt alternatingGroup.Iw_is_generator_alt

def iw3 : IwasawaStructure (alternatingGroup α) (Nat.finset α 3)
    where
  t := fun s : Nat.finset α 3 =>
    (Subgroup.map (Equiv.Perm.ofSubtype : Equiv.Perm (s : Finset α) →* Equiv.Perm α)
          (alternatingGroup (s : Finset α))).subgroupOf
      (alternatingGroup α)
  is_comm := fun ⟨s, hs⟩ => by
    apply Subgroup.subgroupOf_isCommutative _
    haveI : (alternatingGroup (s : Finset α)).IsCommutative :=
      {
        is_comm := by
          apply alternatingGroup.isCommutative_of_order_three
          rw [Fintype.card_coe]; exact hs }
    apply Subgroup.map_isCommutative (alternatingGroup (s : Finset α))
  IsConj := fun g ⟨s, hs⟩ => Iw_is_conj_alt s g
  is_generator := Iw_is_generator_alt
#align alternating_group.Iw3 alternatingGroup.iw3

/-- If α has at least 5 elements, but not 6, then
the only nontrivial normal sugroup of (alternating_group α) is the alternating_group itself. -/
theorem is_normal_subgroup_iff_of_ne_6 {α : Type _} [DecidableEq α] [Fintype α]
    (hα : 5 ≤ Fintype.card α) (hα' : Fintype.card α ≠ 6) {N : Subgroup (alternatingGroup α)}
    (hnN : N.Normal) : N = ⊥ ∨ N = ⊤ :=
  by
  cases' Subgroup.bot_or_nontrivial N with hN hN
  apply Or.intro_left; exact hN
  apply Or.intro_right
  rw [eq_top_iff]
  rw [← alternatingGroup_is_perfect hα]
  apply commutator_le_iwasawa _ Iw3 hnN _
  · apply IsPreprimitive.isQuasipreprimitive
    apply alternatingGroup.Nat.finset_isPreprimitive_of_alt 3
    norm_num
    exact lt_of_lt_of_le (by norm_num) hα
    exact hα'
  · intro h
    obtain ⟨g, hgN, hg⟩ := N.nontrivial_iff_exists_ne_one.mp hN
    obtain ⟨s, hs⟩ := Nat.finset.mulAction_faithful 3 (by norm_num) _ _
    apply hs
    suffices : s ∈ fixed_points N (Nat.finset α 3)
    rw [mem_fixed_points] at this ; exact this ⟨g, hgN⟩
    rw [h]; rw [Set.top_eq_univ]; apply Set.mem_univ
    infer_instance
    exact lt_of_lt_of_le (by norm_num) hα
    intro hg'; apply hg
    ext; simp only [Subgroup.coe_one, ← hg']; rfl
#align alternating_group.is_normal_subgroup_iff_of_ne_6 alternatingGroup.is_normal_subgroup_iff_of_ne_6

def iw4T (s : Finset α) : Subgroup (alternatingGroup α) :=
  (Subgroup.map
        (MonoidHom.comp (Equiv.Perm.ofSubtype : Equiv.Perm (s : Finset α) →* Equiv.Perm α)
          (alternatingGroup (s : Finset α)).Subtype)
        (commutator (alternatingGroup (s : Finset α)))).subgroupOf
    (alternatingGroup α)
#align alternating_group.Iw4T alternatingGroup.iw4T

def AlternatingGroup.ofSubtype {α : Type _} [DecidableEq α] [Fintype α] {s : Finset α} :
    alternatingGroup s →* alternatingGroup α :=
  by
  apply MonoidHom.codRestrict (MonoidHom.restrict Equiv.Perm.ofSubtype (alternatingGroup s))
  intro k
  simpa only [mem_alternating_group, MonoidHom.restrict_apply, sign_of_subtype] using k.prop
#align alternating_group.alternating_group.of_subtype alternatingGroup.AlternatingGroup.ofSubtype

def iw4T' (s : Finset α) : Subgroup (alternatingGroup α) :=
  Subgroup.map AlternatingGroup.ofSubtype (commutator (alternatingGroup s))
#align alternating_group.Iw4T' alternatingGroup.iw4T'

theorem iw4T'_is_conj (g : alternatingGroup α) (s : Finset α) :
    iw4T' (g • s : Finset α) = MulAut.conj g • iw4T' s :=
  by
  dsimp [Iw4T']
  simp only [commutator, Subgroup.map_commutator]
  change _ = Subgroup.map (MulAut.conj g).toMonoidHom _
  have htop : ⊤ = Subgroup.map (Iw_conj' (rfl : g • s = g • s)).toMonoidHom ⊤ := by
    rw [Subgroup.map_top_of_surjective]; exact MulEquiv.surjective _
  simp only [htop, Subgroup.map_map, Subgroup.map_commutator]
  suffices
  refine' congr_arg₂ _ this this
  · apply congr_arg₂
    ext ⟨k, hk⟩ x
    dsimp only [Iw_conj', subgroup.equiv_mk, alternating_group.of_subtype]
    simp only [MonoidHom.comp_apply]
    dsimp
    rw [← Equiv.Perm.iwConj'_eq_apply]; rfl
    rfl
#align alternating_group.Iw4T'_is_conj alternatingGroup.iw4T'_is_conj

theorem iw4T_is_conj (g : alternatingGroup α) (s : Finset α) (hs : s.card = 4) :
    iw4T (g • s : Finset α) = MulAut.conj g • iw4T s :=
  by
  dsimp [Iw4T]
  rw [← mulAut_smul_subgroupOf_eq (MulAut.conj ↑g) (MulAut.conj g)]
  apply congr_arg
  change _ = Subgroup.map (MulAut.conj ↑g).toMonoidHom _
  simp only [Subgroup.map_map]
  simp only [commutator, Subgroup.map_commutator]
  suffices :
    Subgroup.map (equiv.perm.of_subtype.comp (alternatingGroup ↥(g • s)).Subtype) ⊤ =
      Subgroup.map
        ((MulEquiv.toMonoidHom (MulAut.conj ↑g)).comp
          (equiv.perm.of_subtype.comp (alternatingGroup ↥s).Subtype))
        ⊤
  rw [this]
  have hg : g • s = g • s; rfl
  suffices :
    (equiv.perm.of_subtype.comp (alternatingGroup ↥(g • s)).Subtype).comp
        (Iw_conj' hg).toMonoidHom =
      (MulEquiv.toMonoidHom (MulAut.conj ↑g)).comp
        (equiv.perm.of_subtype.comp (alternatingGroup ↥s).Subtype)
  rw [← this]
  conv_rhs => rw [← Subgroup.map_map]
  apply congr_arg₂
  rfl
  rw [Subgroup.map_top_of_surjective]
  exact MulEquiv.surjective _
  · ext ⟨k, hk⟩ x; dsimp only [Iw_conj', subgroup.equiv_mk]
    simp only [MonoidHom.comp_apply]
    dsimp
    rw [← Equiv.Perm.iwConj'_eq_apply]; rfl
  · intro n; rfl
#align alternating_group.Iw4T_is_conj alternatingGroup.iw4T_is_conj

open Equiv.Perm Equiv alternatingGroup Subgroup

theorem isSwap_iff_cycleType_eq {g : Equiv.Perm α} : g.IsSwap ↔ g.cycleType = {2} :=
  by
  constructor
  · intro hg
    rw [Equiv.Perm.IsCycle.cycleType (Equiv.Perm.IsSwap.isCycle hg)]
    rw [← card_support_eq_two] at hg
    rw [hg]
    simp only [Multiset.coe_singleton]
  · intro hg
    suffices hg' : g.is_cycle
    rw [Equiv.Perm.IsCycle.cycleType hg'] at hg
    simp only [Multiset.coe_singleton, Multiset.singleton_inj, card_support_eq_two] at hg
    exact hg
    simp only [← Equiv.Perm.card_cycleType_eq_one, hg, Multiset.card_singleton]
#align alternating_group.is_swap_iff_cycle_type_eq alternatingGroup.isSwap_iff_cycleType_eq

theorem isSwap_eq' {g : Equiv.Perm α} (hg : IsSwap g) {a : α} (ha : a ∈ g.support) :
    g = Equiv.swap a (g a) := by
  obtain ⟨x, y, hxy, h⟩ := hg
  rw [Equiv.Perm.mem_support, h, Equiv.swap_apply_ne_self_iff] at ha
  /-  wlog hx : a = x using [x y, y x],
    exact ha.2,
    { suffices hy : y = g a,
      rw [← hy, hx, h],
      rw [h, hx, swap_apply_left], },
    apply this (ne.symm hxy),
    rw [equiv.swap_comm, h],
    exact ⟨ne.symm ha.1, or.symm ha.2⟩, -/
  cases' ha.2 with hx hy
  · suffices hy : y = g a
    rw [← hy, hx, h]
    rw [h, hx, swap_apply_left]
  · suffices hx : x = g a
    rw [← hx, hy, Equiv.swap_comm, h]
    rw [h, ← Equiv.swap_apply_eq_iff, swap_apply_left, hy]
#align alternating_group.is_swap_eq' alternatingGroup.isSwap_eq'

theorem swap_mul_swap_mem (hα : 5 ≤ Fintype.card α) {g k : Equiv.Perm α} (hg : IsSwap g)
    (hk : IsSwap k) : g * k ∈ Subgroup.closure {g : Equiv.Perm α | g.cycleType = {2, 2}} :=
  by
  suffices hdis :
    ∀ {g k : Equiv.Perm α} (hg : is_swap g) (hk : is_swap k) (hgk : g.Disjoint k),
      g * k ∈ Subgroup.closure {g : Equiv.Perm α | g.cycleType = {2, 2}}
  by_cases h22 : g.disjoint k
  -- case disjoint
  exact hdis hg hk h22
  -- case not disjoint
  rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.not_disjoint_iff] at h22
  obtain ⟨a, hag, hak⟩ := h22
  rw [is_swap_eq' hg hag]; rw [is_swap_eq' hk hak]
  by_cases h1 : k a = g a
  · rw [h1]; rw [Equiv.swap_mul_self]; refine' Subgroup.one_mem _
  · suffices : ∃ b c : α, b ∉ ({a, g a, k a} : Finset α) ∧ c ∉ ({a, g a, k a} : Finset α) ∧ b ≠ c
    obtain ⟨b, c, hb, hc, hbc⟩ := this
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hc
    simp only [not_or] at hb hc
    rw [← one_mul (swap a (k a))]
    rw [← Equiv.swap_mul_self b c]
    nth_rw 1 [mul_assoc]; rw [← mul_assoc]
    refine' Subgroup.mul_mem _ _ _
    · rw [Equiv.Perm.mem_support] at hag
      apply hdis _ _
      rw [disjoint_iff_disjoint_support, Equiv.Perm.support_swap _, Equiv.Perm.support_swap _]
      simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton,
        Finset.disjoint_insert_left, Finset.disjoint_singleton, Ne.def, not_or]
      exact ⟨⟨Ne.symm hb.1, Ne.symm hc.1⟩, ⟨hb.2.1, Ne.symm hc.2.1⟩⟩
      exact hbc
      exact Ne.symm hag
      exact ⟨a, g a, Ne.symm hag, rfl⟩
      exact ⟨b, c, hbc, rfl⟩
    · rw [Equiv.Perm.mem_support] at hak
      apply hdis _ _
      rw [disjoint_iff_disjoint_support, Equiv.Perm.support_swap _, Equiv.Perm.support_swap _]
      simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton,
        Finset.disjoint_insert_left, Finset.disjoint_singleton, Ne.def, not_or]
      exact ⟨⟨hb.1, hb.2.2⟩, ⟨Ne.symm hc.1, hc.2.2⟩⟩
      exact Ne.symm hak
      exact hbc
      exact ⟨b, c, hbc, rfl⟩
      exact ⟨a, k a, Ne.symm hak, rfl⟩
    · simp_rw [← Finset.mem_compl]
      rw [← Finset.one_lt_card_iff]
      rw [Finset.card_compl]
      rw [Nat.lt_iff_add_one_le]
      apply le_tsub_of_add_le_right
      apply le_trans _ hα
      suffices : Finset.card {a, g a, k a} ≤ 3
      apply le_trans (add_le_add_left this 2); norm_num
      apply le_trans (Finset.card_insert_le _ _); rw [Nat.succ_le_succ_iff]
      apply le_trans (Finset.card_insert_le _ _); rw [Nat.succ_le_succ_iff]
      simp only [Finset.card_singleton]
  -- hdis
  · intro g k hg hk h22
    apply Subgroup.subset_closure; simp only [Set.mem_setOf_eq]
    rw [Equiv.Perm.Disjoint.cycleType h22]
    rw [is_swap_iff_cycle_type_eq] at hg hk
    rw [hg, hk, Multiset.singleton_add, Multiset.insert_eq_cons]
#align alternating_group.swap_mul_swap_mem alternatingGroup.swap_mul_swap_mem

theorem closure_perm22_eq_top (hα : 5 ≤ Fintype.card α) :
    Subgroup.closure {g : Equiv.Perm α | g.cycleType = {2, 2}} = alternatingGroup α :=
  by
  apply Subgroup.closure_eq_of_le
  · intro g hg
    simp only [SetLike.mem_coe, mem_alternating_group, Equiv.Perm.sign_of_cycleType]
    simp only [Set.mem_setOf_eq] at hg
    rw [hg]; norm_num
  suffices hind :
    ∀ (n : ℕ) (l : List (Equiv.Perm α)) (hl : ∀ g, g ∈ l → is_swap g) (hn : l.length = 2 * n),
      l.Prod ∈ Subgroup.closure {σ : perm α | σ.cycleType = {2, 2}}
  · intro g hg
    obtain ⟨l, rfl, hl⟩ := trunc_swap_factors g
    obtain ⟨n, hn⟩ := (prod_list_swap_mem_alternating_group_iff_even_length hl).1 hg
    rw [← two_mul] at hn
    exact hind n l hl hn
  intro n
  induction' n with n hrec
  · intro l hl hn
    simp only [Nat.zero_eq, MulZeroClass.mul_zero, List.length_eq_zero] at hn
    rw [hn, List.prod_nil]
    refine' one_mem _
  · intro l hl hn
    suffices : 2 * n.succ = (2 * n).succ.succ
    rw [this] at hn
    obtain ⟨a, l1, rfl⟩ := l.exists_of_length_succ hn
    simp only [List.length, Nat.succ_inj'] at hn
    obtain ⟨b, l2, rfl⟩ := l1.exists_of_length_succ hn
    simp only [List.length, Nat.succ_inj'] at hn
    simp only [List.prod_cons, ← mul_assoc]
    refine' Subgroup.mul_mem _ _ _
    · simp only [List.mem_cons, forall_eq_or_imp] at hl
      /- obtain ⟨a1, a2, ha, rfl⟩ := hl.1,
            obtain ⟨b1, b2, hb, rfl⟩ := hl.2.1, -/
      exact swap_mul_swap_mem hα hl.1 hl.2.1
    refine' hrec l2 _ hn
    · intro g hg; apply hl g; apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem; exact hg
    rw [Nat.mul_succ]
#align alternating_group.closure_perm22_eq_top alternatingGroup.closure_perm22_eq_top

theorem closure_perm22_alternating_eq_top (hα : 5 ≤ Fintype.card α) :
    Subgroup.closure {g : alternatingGroup α | (g : Equiv.Perm α).cycleType = {2, 2}} = ⊤ :=
  by
  suffices : Function.Injective (alternatingGroup α).Subtype
  apply Subgroup.map_injective this
  rw [subgroup.map_closure_eq]
  suffices :
    (alternatingGroup α).Subtype ''
        {g : alternatingGroup α | (g : Equiv.Perm α).cycleType = {2, 2}} =
      {g : Equiv.Perm α | g.cycleType = {2, 2}}
  rw [this]
  rw [closure_perm22_eq_top hα]
  rw [← Subgroup.comap_top _, Subgroup.map_comap_eq, Subgroup.subtype_range, inf_top_eq]
  · ext g
    simp only [Subgroup.coeSubtype, Set.mem_image, Set.mem_setOf_eq]
    constructor
    rintro ⟨k, hk, rfl⟩; exact hk
    intro hg
    use g
    rw [Equiv.Perm.mem_alternatingGroup]
    rw [Equiv.Perm.sign_of_cycleType]; rw [hg]; norm_num
    exact ⟨hg, rfl⟩
  simp only [Subgroup.coeSubtype, Subtype.coe_injective]
#align alternating_group.closure_perm22_alternating_eq_top alternatingGroup.closure_perm22_alternating_eq_top

theorem is_perm22_exists_of_subtype (g : alternatingGroup α)
    (hg : (g : Equiv.Perm α).cycleType = {2, 2}) : ∃ s : Finset α, s.card = 4 ∧ g ∈ iw4T s :=
  by
  have hs4 : (g : Equiv.Perm α).support.card = 4 := by rw [← Equiv.Perm.sum_cycleType]; rw [hg]; rfl
  use (g : Equiv.Perm α).support
  apply And.intro hs4
  simp only [Iw4T]
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.mem_map]
  let k : Equiv.Perm (g : Equiv.Perm α).support :=
    Equiv.Perm.subtypePerm (g : Equiv.Perm α) fun a => by simp only [Equiv.Perm.apply_mem_support]
  suffices : Equiv.Perm.ofSubtype k = g
  use k
  simp only [mem_alternating_group]
  rw [← Equiv.Perm.sign_ofSubtype]; rw [this]
  rw [Equiv.Perm.sign_of_cycleType]; rw [hg]; rfl
  constructor
  rw [← V4_eq_commutator]
  rw [← Subgroup.mem_carrier]
  rw [V4_carrier_eq]
  apply Or.intro_right
  rw [Subgroup.coe_mk]
  rw [← Equiv.Perm.cycleType_ofSubtype]
  rw [this]
  exact hg
  simp only [Fintype.card_coe, hs4]
  simp only [Fintype.card_coe, hs4]
  simp only [MonoidHom.coe_comp, Subgroup.coeSubtype, Function.comp_apply, Subgroup.coe_mk]
  exact this
  · -- k.of_subtype = g
    apply Equiv.Perm.ofSubtype_subtypePerm
    · intro a; simp only [Equiv.Perm.mem_support, imp_self]
#align alternating_group.is_perm22_exists_of_subtype alternatingGroup.is_perm22_exists_of_subtype

theorem Iw4_is_generator_alt (hα : 5 ≤ Fintype.card α) :
    (iSup fun s : Nat.finset α 4 => iw4T (s : Finset α)) = ⊤ :=
  by
  --  supr (λ (s : { s : finset α // s.card = 4}), Iw4T (s : finset α)) =  ⊤ :=
  rw [← closure_perm22_alternating_eq_top hα]
  have lemma1 :
    {g : alternatingGroup α | (g : Equiv.Perm α).cycleType = {2, 2}} =
      (alternatingGroup α).Subtype ⁻¹' {g : Equiv.Perm α | g.cycleType = {2, 2}} :=
    by ext g; simp only [Subgroup.coeSubtype, Set.preimage_setOf_eq]
  have lemma2 : {g : Equiv.Perm α | g.cycleType = {2, 2}} ≤ alternatingGroup α :=
    by
    intro k hk
    -- simp only [set_like.mem_coe],
    simp only [Set.mem_setOf_eq] at hk
    simp only [SetLike.mem_coe, mem_alternating_group, Equiv.Perm.sign_of_cycleType, hk]
    norm_num
  apply le_antisymm
  · -- supr ≤ closure
    rw [lemma1]
    rw [subgroup.closure_subgroup_of_eq (alternatingGroup α) _ lemma2]
    rw [closure_perm22_eq_top hα]
    rw [iSup_le_iff]
    rintro ⟨s, hs⟩
    dsimp only [Subgroup.subgroupOf]
    refine' Subgroup.comap_mono _
    intro g
    rintro ⟨k, hk, rfl⟩
    simp only [SetLike.mem_coe] at hk
    rw [Equiv.Perm.mem_alternatingGroup]
    simp only [MonoidHom.coe_comp, Subgroup.coeSubtype, sign_of_subtype]
    simpa only using Subtype.prop k
  · -- closure ≤ supr
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨s, hs4, hsg⟩ := is_perm22_exists_of_subtype g hg
    simp only [SetLike.mem_coe]
    apply Subgroup.mem_iSup_of_mem
    swap; exact ⟨s, hs4⟩
    exact hsg
#align alternating_group.Iw4_is_generator_alt alternatingGroup.Iw4_is_generator_alt

def iw4 (hα : 5 ≤ Fintype.card α) : IwasawaStructure (alternatingGroup α) (Nat.finset α 4)
    where
  t s := iw4T (s : Finset α)
  is_comm := fun ⟨s, hs⟩ =>
    by
    have hs' : Fintype.card (s : Finset α) = 4 := by rw [Fintype.card_coe]; exact hs
    apply Subgroup.subgroupOf_isCommutative _
    have : (commutator (alternatingGroup (s : Finset α))).IsCommutative :=
      by
      rw [← V4_eq_commutator _ hs']
      apply V4_is_commutative _ hs'
    apply Subgroup.map_isCommutative (commutator (alternatingGroup (s : Finset α)))
  IsConj := fun g ⟨s, hs⟩ => iw4T_is_conj g s hs
  is_generator := Iw4_is_generator_alt hα
#align alternating_group.Iw4 alternatingGroup.iw4

theorem Finset.mem_doubleton_iff (a b x : α) : x ∈ ({a, b} : Finset α) ↔ x = a ∨ x = b := by
  rw [Finset.mem_insert, Finset.mem_singleton]
#align alternating_group.finset.mem_doubleton_iff alternatingGroup.Finset.mem_doubleton_iff

/-- If α has at least 5 elements, but not 6,
then the only nontrivial normal sugroup of (perm α) is the alternating_group. -/
theorem AlternatingGroup.normal_subgroups_6 {α : Type _} [DecidableEq α] [Fintype α]
    (hα : 5 ≤ Fintype.card α) (hα' : Fintype.card α ≠ 6) {N : Subgroup (alternatingGroup α)}
    (hnN : N.Normal) (ntN : Nontrivial N) : N = ⊤ :=
  by
  rw [eq_top_iff]
  rw [← alternatingGroup_is_perfect hα]
  refine' commutator_le_iwasawa _ Iw3 hnN _
  · -- quasipreprimitive action
    apply IsPreprimitive.isQuasipreprimitive
    apply nat.finset_is_preprimitive_of_alt
    norm_num
    apply lt_of_lt_of_le _ hα; norm_num
    exact hα'
  -- N acts nontrivially
  intro h
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN
  have hg_ne' : (to_perm g : Equiv.Perm α) ≠ 1 :=
    by
    intro hg_ne'; apply hg_ne
    ext; simp only [Subgroup.coe_one, ← hg_ne']
    rfl
  obtain ⟨s, hs⟩ := @Nat.finset.mulAction_faithful α _ _ _ _ 3 _ _ _ g hg_ne'
  apply hs
  suffices : s ∈ fixed_points N (Nat.finset α 3)
  rw [mem_fixed_points] at this ; exact this ⟨g, hgN⟩
  rw [h]; rw [Set.top_eq_univ]; apply Set.mem_univ
  norm_num
  apply lt_of_lt_of_le _ hα; norm_num
#align alternating_group.alternating_group.normal_subgroups_6 alternatingGroup.AlternatingGroup.normal_subgroups_6

/-- If α has at least 5 elements, but not 8,
then the only nontrivial normal sugroup of (alternating_group α) is the alternating_group. -/
theorem AlternatingGroup.normal_subgroups_8 {α : Type _} [DecidableEq α] [Fintype α]
    (hα : 5 ≤ Fintype.card α) (hα' : Fintype.card α ≠ 8) {N : Subgroup (alternatingGroup α)}
    (hnN : N.Normal) (ntN : Nontrivial N) : N = ⊤ :=
  by
  rw [eq_top_iff]
  rw [← alternatingGroup_is_perfect hα]
  refine' commutator_le_iwasawa _ (Iw4 hα) hnN _
  · -- quasipreprimitive action
    apply IsPreprimitive.isQuasipreprimitive
    apply nat.finset_is_preprimitive_of_alt
    norm_num
    apply lt_of_lt_of_le _ hα; norm_num
    exact hα'
  -- N acts nontrivially
  intro h
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN
  have hg_ne' : (to_perm g : Equiv.Perm α) ≠ 1 :=
    by
    intro hg_ne'; apply hg_ne
    ext; simp only [Subgroup.coe_one, ← hg_ne']
    rfl
  obtain ⟨s, hs⟩ := @Nat.finset.mulAction_faithful α _ _ _ _ 4 _ _ _ g hg_ne'
  apply hs
  suffices : s ∈ fixed_points N (Nat.finset α 4)
  rw [mem_fixed_points] at this ; exact this ⟨g, hgN⟩
  rw [h]; rw [Set.top_eq_univ]; apply Set.mem_univ
  norm_num
  apply lt_of_lt_of_le _ hα; norm_num
#align alternating_group.alternating_group.normal_subgroups_8 alternatingGroup.AlternatingGroup.normal_subgroups_8

/-- If α has at least 5 elements,
  then the only nontrivial normal sugroup of (alternating_group α) is ⊤. -/
theorem AlternatingGroup.normal_subgroups {α : Type _} [DecidableEq α] [Fintype α]
    (hα : 5 ≤ Fintype.card α) {N : Subgroup (alternatingGroup α)} (hnN : N.Normal)
    (ntN : Nontrivial N) : N = ⊤ :=
  by
  by_cases hα' : Fintype.card α = 6
  · apply alternating_group.normal_subgroups_8 hα _ hnN ntN
    rw [hα']; norm_num
  exact alternating_group.normal_subgroups_6 hα hα' hnN ntN
#align alternating_group.alternating_group.normal_subgroups alternatingGroup.AlternatingGroup.normal_subgroups

/-- If `α` has at least 5 elements, then `alternatingGroup α` is simple. -/
theorem alternatingGroup.isSimpleGroup {α : Type*} [DecidableEq α] [Fintype α]
    (hα : 5 ≤ Fintype.card α) :
    IsSimpleGroup (alternatingGroup α) := by
  have : Nontrivial (alternatingGroup α) :=
    alternatingGroup.nontrivial_of_three_le_card (le_trans (by norm_num) hα)
  constructor
  intro N hNnormal
  cases' N.bot_or_nontrivial with hN hN
  · left
    exact hN
  · right
    exact AlternatingGroup.normal_subgroups hα hNnormal hN

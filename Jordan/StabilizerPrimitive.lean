/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module stabilizer_primitive
-/
import Jordan.Mathlib.Alternating
import Jordan.Mathlib.Stabilizer
import Jordan.Mathlib.Set
import Jordan.Mathlib.GroupTheory.Subgroup.Basic
import Jordan.Mathlib.Alternating
import Jordan.IndexNormal
import Jordan.Primitive
import Jordan.MultipleTransitivity
-- import Jordan.MulActionFinset

-- import group_theory.specific_groups.alternating
-- import group_theory.specific_groups.alternating
open scoped Pointwise Classical

variable {α : Type _} [Fintype α] [DecidableEq α]

open MulAction

namespace Equiv.Perm

theorem ofSubtype_mem_stabilizer (s : Set α) (g : Equiv.Perm s) :
    Equiv.Perm.ofSubtype g ∈ stabilizer (Equiv.Perm α) s := by
  rw [mem_stabilizer_of_finite_iff_smul_le]
  intro x
  rw [Set.mem_smul_set]
  rintro ⟨y, hy, rfl⟩
  simp only [Equiv.Perm.smul_def]
  rw [Equiv.Perm.ofSubtype_apply_of_mem g hy]
  refine' Subtype.mem _
  exact s.toFinite
#align equiv.perm.of_subtype_mem_stabilizer Equiv.Perm.ofSubtype_mem_stabilizer

theorem ofSubtype_mem_stabilizer' (s : Set α) (g : Equiv.Perm (sᶜ : Set α)) :
    Equiv.Perm.ofSubtype g ∈ stabilizer (Equiv.Perm α) s := by
  -- stabilizer_compl adds a `classical.prop_decidable` instance, but
  -- the lemma expects `set.compl_decidable`.
  /-
      rw ← stabilizer_compl,
      let hz := @equiv.perm.of_subtype.mem_stabilizer α _ _ (sᶜ : set α) g,
  -/
  rw [mem_stabilizer_of_finite_iff_smul_le]
  · intro x
    rw [Set.mem_smul_set]
    rintro ⟨y, hy, rfl⟩
    simp only [Equiv.Perm.smul_def]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem g (Set.not_mem_compl_iff.mpr hy)]
    exact hy
  exact s.toFinite
#align equiv.perm.of_subtype_mem_stabilizer' Equiv.Perm.ofSubtype_mem_stabilizer'

theorem stabilizer_isPreprimitive (s : Set α) : IsPreprimitive (stabilizer (Equiv.Perm α) s) s :=
  by
  let φ : stabilizer (Equiv.Perm α) s → Equiv.Perm s := MulAction.toPerm
  let f : s →ₑ[φ] s :=
    { toFun := id
      map_smul' := fun g x => by simp only [id.def, Equiv.Perm.smul_def, toPerm_apply] }
  have hf : Function.Bijective f := Function.bijective_id
  rw [isPreprimitive_of_bijective_map_iff _ hf]
  exact Equiv.Perm.isPreprimitive s
  -- function.surjective φ,
  intro g
  use! Equiv.Perm.ofSubtype g
  ·-- ⇑equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) s
    apply ofSubtype_mem_stabilizer
  · -- φ ⟨⇑equiv.perm.of_subtype g, _⟩ = g
    ext ⟨x, hx⟩
    change Equiv.Perm.ofSubtype g • x = _
    simp only [Equiv.Perm.smul_def]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
#align equiv.perm.stabilizer_is_preprimitive Equiv.Perm.stabilizer_isPreprimitive

theorem Equiv.Perm.Stabilizer.is_preprimitive' (s : Set α) (G : Subgroup (Equiv.Perm α))
    (hG : stabilizer (Equiv.Perm α) s ≤ G) : IsPreprimitive (stabilizer G s) s :=
  by
  let φ : stabilizer (Equiv.Perm α) s → stabilizer G s := fun g =>
    ⟨⟨g, hG g.prop⟩, mem_stabilizer_iff.mp g.prop⟩
  let f : s →ₑ[φ] s :=
    { toFun := id
      map_smul' := fun ⟨m, hm⟩ x => by
        simp only [id_eq, ← Subtype.coe_inj, HasSmul.smul_stabilizer_def, Perm.smul_def]
        rfl }
  have : Function.Surjective f := Function.surjective_id
  apply isPreprimitive_of_surjective_map this
  apply stabilizer_isPreprimitive
#align equiv.perm.equiv.perm.stabilizer.is_preprimitive' Equiv.Perm.Equiv.Perm.Stabilizer.is_preprimitive'

end Equiv.Perm

namespace alternatingGroup

theorem stabilizer.isPreprimitive (s : Set α) (hs : (sᶜ : Set α).Nontrivial) :
    IsPreprimitive (stabilizer (alternatingGroup α) s) s := by
  let φ : stabilizer (alternatingGroup α) s → Equiv.Perm s := MulAction.toPerm
  suffices hφ : Function.Surjective φ
  let f : s →ₑ[φ] s :=
    { toFun := id
      map_smul' := fun ⟨g, hg⟩ ⟨x, hx⟩ => by
        simp only [id.def, Equiv.Perm.smul_def, toPerm_apply] }
  have hf : Function.Bijective f := Function.bijective_id
  rw [isPreprimitive_of_bijective_map_iff hφ hf]
  exact Equiv.Perm.isPreprimitive s
  suffices : ∃ k : Equiv.Perm (sᶜ : Set α), Equiv.Perm.sign k = -1
  obtain ⟨k, hk_sign⟩ := this
  have hks : Equiv.Perm.ofSubtype k • s = s := by
    rw [← mem_stabilizer_iff]
    exact Equiv.Perm.ofSubtype_mem_stabilizer' s k
  -- function.surjective φ
  have hφ : Function.Surjective φ := by
    have hminus_one_ne_one : (-1 : Units ℤ) ≠ 1 := Int.neg_units_ne_self 1
    intro g
    let g' := if Equiv.Perm.sign g = 1
      then Equiv.Perm.ofSubtype g
      else Equiv.Perm.ofSubtype g * Equiv.Perm.ofSubtype k
    use! g'
    rw [Equiv.Perm.mem_alternatingGroup]
    cases' Int.units_eq_one_or (Equiv.Perm.sign g) with hsg hsg <;>
      · -- dsimp [g']
        simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false,
          Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_mul, mul_neg, mul_one,
          neg_neg, hsg, hk_sign]
    rw [mem_stabilizer_iff]
    change g' • s = s
    cases' Int.units_eq_one_or (Equiv.Perm.sign g) with hsg hsg
    · simp only [hsg, eq_self_iff_true, if_true]
      exact Equiv.Perm.ofSubtype_mem_stabilizer s g
    · simp only [hsg, hminus_one_ne_one, if_false, mul_smul, hks]
      exact Equiv.Perm.ofSubtype_mem_stabilizer s g
    dsimp [φ]
    cases' Int.units_eq_one_or (Equiv.Perm.sign g) with hsg hsg
    · -- dsimp [g']
      simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false]
      ext x
      change Equiv.Perm.ofSubtype g ↑x = ↑(g x)
      exact Equiv.Perm.ofSubtype_apply_coe g x
    · -- dsimp [g'];
      simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false]
      ext x
      change (Equiv.Perm.ofSubtype g * Equiv.Perm.ofSubtype k) ↑x = ↑(g x)
      rw [Equiv.Perm.mul_apply]
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem k _]
      exact Equiv.Perm.ofSubtype_apply_coe g x
      rw [Set.not_mem_compl_iff]; exact x.prop
  exact hφ
  -- ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  use Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩
  rw [Equiv.Perm.sign_swap _]
  rw [← Function.Injective.ne_iff Subtype.coe_injective]
  simp only [Subtype.coe_mk]; exact hab
#align alternating_group.stabilizer.is_preprimitive alternatingGroup.stabilizer.isPreprimitive

theorem stabilizer.isPreprimitive' (s : Set α) (hsc : sᶜ.Nontrivial)
    (G : Subgroup (Equiv.Perm α))
    (hG : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α ≤ G) :
    IsPreprimitive (stabilizer G s) s := by
  let φ : stabilizer (alternatingGroup α) s → stabilizer G s := fun g => by
    use! (g : alternatingGroup α)
    apply hG
    rw [Subgroup.mem_inf]
    constructor
    · let h := g.prop; rw [mem_stabilizer_iff] at h ⊢; exact h
    · exact SetLike.coe_mem _
    exact g.prop
  let f : s →ₑ[φ] s :=
    { toFun := id
      map_smul' := fun ⟨⟨m, hm'⟩, hm⟩ ⟨a, ha⟩ => rfl }
  have hf : Function.Surjective f := Function.surjective_id
  apply isPreprimitive_of_surjective_map hf
  apply stabilizer.isPreprimitive
  exact hsc
#align alternating_group.stabilizer.is_preprimitive' alternatingGroup.stabilizer.isPreprimitive'

end alternatingGroup

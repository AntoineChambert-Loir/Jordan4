/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.commutators
-/
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Abelianization

variable {G : Type _} [Group G]

open Subgroup

theorem mem_commutatorSet_of_isConj_sq {G : Type _} [Group G] {g : G} (hg : IsConj g (g ^ 2)) :
    g ∈ commutatorSet G := by
  obtain ⟨h, hg⟩ := hg; rw [SemiconjBy] at hg 
  use ↑h; use g
  rw [commutatorElement_def, hg]
  simp only [IsUnit.mul_inv_cancel_right, Units.isUnit, mul_inv_eq_iff_eq_mul, pow_two]
#align mem_commutator_set_of_is_conj_sq mem_commutatorSet_of_isConj_sq

theorem Subgroup.map_top_eq_range {G H : Type _} [Group H] [Group G] (f : H →* G) :
    Subgroup.map f ⊤ = f.range :=
  by
  suffices : (map f ⊤ : Set G) = (f.range : Set G)
  refine' SetLike.ext' this
  simp only [coe_map, coe_top, Set.image_univ, MonoidHom.coe_range]
#align subgroup.map_top_eq_range Subgroup.map_top_eq_range

theorem Subgroup.map_commutator_eq {G H : Type _} [Group H] [Group G] (f : H →* G) :
    Subgroup.map f (_root_.commutator H) = ⁅f.range, f.range⁆ := by
  rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_eq_range]
#align subgroup.map_commutator_eq Subgroup.map_commutator_eq

theorem Subgroup.commutator_eq' {G : Type _} [Group G] (H : Subgroup G) :
    Subgroup.map H.subtype (_root_.commutator H) = ⁅H, H⁆ := by
  simp only [map_commutator_eq, subtype_range]
#align subgroup.commutator_eq' Subgroup.commutator_eq'

/-- If G and H have multiplications *
and φ : G → H is a surjective multiplicative map,
and if G is commutative, then H is commutative.

Since I only use it with groups,
I should probably use function.surjective.comm_semigroup
--/
theorem surj_to_comm {G H : Type _} [Mul G] [Mul H] (φ : MulHom G H)
    (is_surj : Function.Surjective φ) (is_comm : IsCommutative G (· * ·)) :
    IsCommutative H (· * ·) := by
  apply IsCommutative.mk
  intro a b
  obtain ⟨a', ha'⟩ := is_surj a
  obtain ⟨b', hb'⟩ := is_surj b
  simp only [← ha', ← hb', ← map_mul]
  rw [is_comm.comm]
#align surj_to_comm surj_to_comm

theorem quotient_comm_contains_commutators_iff {N : Subgroup G} (nN : N.Normal) :
    IsCommutative (G ⧸ N) (· * ·) ↔ commutator G ≤ N := by
  skip
  constructor
  · intro hcomm
    rw [commutator_eq_normalClosure]
    rw [← Subgroup.normalClosure_subset_iff]
    intro x hx
    obtain ⟨p, q, rfl⟩ := hx
    simp only [SetLike.mem_coe]
    rw [← QuotientGroup.eq_one_iff]
    rw [commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← commutatorElement_def]
    rw [commutatorElement_eq_one_iff_mul_comm]
    apply hcomm.comm
  · intro hGN; refine' IsCommutative.mk _
    intro x'; obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N x'
    intro y'; obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N y'
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    simp only [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff]
    apply hGN
    rw [commutator_eq_closure]
    apply Subgroup.subset_closure
    exact commutator_mem_commutatorSet x y
#align quotient_comm_contains_commutators_iff quotient_comm_contains_commutators_iff

/-- If N is a normal subgroup, H a commutative subgroup such that H ⊔ N = ⊤,
then N contains the derived subgroup. -/
theorem contains_commutators_of (N : Subgroup G) (nN : N.Normal) (H : Subgroup G) (hHN : N ⊔ H = ⊤)
    (hH : Subgroup.IsCommutative H) : commutator G ≤ N := by
  -- Il suffit de prouver que Q = G ⧸ N est commutatif
  -- let Q := quotient_group.quotient N,
  rw [← quotient_comm_contains_commutators_iff nN]
  -- Q is a quotient of H
  let φ : H →* G ⧸ N := MonoidHom.comp (QuotientGroup.mk' N) (Subgroup.subtype H)
  -- Il suffit de prouver que φ est surjective
  refine' surj_to_comm φ.toMulHom _ hH.is_comm
  suffices hφ : Function.Surjective φ; exact hφ
  -- On prouve que l'image de φ est égale à ⊤
  rw [← MonoidHom.range_top_iff_surjective]
  -- let R := monoid_hom.range φ,
  /-  j : H → G, p : G → G/N,  φ = p o j, on veut prouver que φ est surjective.
      R = im(φ), S = p⁻¹(R) ⊆ G -/
  -- Il va suffire de prouver que S = ⊤, car p est surjective 
  -- let S := φ.range.comap (quotient_group.mk' N),
  suffices S_top : φ.range.comap (QuotientGroup.mk' N) = ⊤
  · rw [eq_top_iff]
    intro x _
    let y := Quotient.out' x
    have hy : y ∈ φ.range.comap (QuotientGroup.mk' N) := by rw [S_top]; exact Subgroup.mem_top y
    rw [← QuotientGroup.out_eq' x]
    exact Subgroup.mem_comap.mp hy
  rw [eq_top_iff, ← hHN, sup_le_iff]
  constructor
  -- have lN : N ≤ φ.range.comap (quotient_group.mk' N),
  · intro g hg
    rw [Subgroup.mem_comap]
    suffices : QuotientGroup.mk' N g = 1
    simp only [this, (MonoidHom.range φ).one_mem]
    simp only [hg, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  -- S contient H = j(H)
  -- have lH : H ≤ φ.range.comap (quotient_group.mk' N),
  · intro h hh
    simp only [Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.coe_comp, QuotientGroup.coe_mk',
      Subgroup.coeSubtype, Function.comp_apply]
    use ⟨h, hh⟩
#align contains_commutators_of contains_commutators_of



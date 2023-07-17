/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module blocks
-/
import Jordan.ForMathlib.Stabilizer
import Jordan.EquivariantMap
import Jordan.SubMulActions
import Mathlib.Data.Setoid.Partition
import Mathlib.Algebra.BigOperators.Finprod

/-! # Blocks

Given `has_smul G X`, an action of a group `G` on a type `X`, we define

- the predicate `is_block G B` states that `B : set X` is a block,
which means that the sets `g • B`, for `g ∈ G` form a partition of `X`.

- a bunch of lemmas that gives example of “trivial” blocks : ⊥, ⊤, singletons, orbits…

-/


-- import .for_mathlib.pretransitive
-- import .for_mathlib.pretransitive
-- import .for_mathlib.set
-- import .for_mathlib.set
-- import .maximal_subgroups
-- import .maximal_subgroups
-- import algebra.big_operators.basic
-- import algebra.big_operators.basic
-- import group_theory.group_action.quotient
-- import group_theory.group_action.quotient
-- import data.finite.card
-- import data.finite.card
open scoped BigOperators Pointwise

namespace MulAction

section SMul

variable (G : Type _) {X : Type _} [SMul G X]

-- Change terminology : is_fully_invariant ?
/-- A fixed block is a fully invariant subset -/
def IsFixedBlock (B : Set X) :=
  ∀ g : G, g • B = B
#align mul_action.is_fixed_block MulAction.IsFixedBlock

/-- An invariant block is a set which is stable under has_smul -/
def IsInvariantBlock (B : Set X) :=
  ∀ g : G, g • B ≤ B
#align mul_action.is_invariant_block MulAction.IsInvariantBlock

/-- A trivial block is a subsingleton or ⊤ (it is not necessarily a block…)-/
def IsTrivialBlock (B : Set X) :=
  B.Subsingleton ∨ B = ⊤
#align mul_action.is_trivial_block MulAction.IsTrivialBlock

/-- A block is a set which is either fixed or moved to a disjoint subset -/
def IsBlock (B : Set X) :=
  (Set.range fun g : G => g • B).PairwiseDisjoint id
#align mul_action.is_block MulAction.IsBlock

variable {G X}

/-- A set B is a block iff for all g, g',
the sets g • B and g' • B are either equal or disjoint -/
theorem IsBlock.def {B : Set X} :
    IsBlock G B ↔ ∀ g g' : G, g • B = g' • B ∨ Disjoint (g • B) (g' • B) :=
  by
  constructor
  · intro hB g g'
    cases em (g • B = g' • B)
    refine' Or.intro_left _ h
    apply Or.intro_right
    exact hB (Set.mem_range_self g) (Set.mem_range_self g') h
  · intro hB
    unfold is_block
    intro C hC C' hC'
    obtain ⟨g, rfl⟩ := hC
    obtain ⟨g', rfl⟩ := hC'
    intro hgg'
    cases hB g g'
    · exfalso; exact hgg' h
    exact h
#align mul_action.is_block.def MulAction.IsBlock.def

/-- Alternate definition of a block -/
theorem IsBlock.mk_notempty {B : Set X} :
    IsBlock G B ↔ ∀ g g' : G, g • B ∩ g' • B ≠ ∅ → g • B = g' • B :=
  by
  rw [is_block.def]
  apply forall_congr'; intro g
  apply forall_congr'; intro g'
  rw [Set.disjoint_iff_inter_eq_empty]
  exact or_iff_not_imp_right
#align mul_action.is_block.mk_notempty MulAction.IsBlock.mk_notempty

/-- A fixed block is a block -/
theorem isBlock_of_fixed {B : Set X} (hfB : IsFixedBlock G B) : IsBlock G B :=
  by
  rw [is_block.def]
  intro g g'
  apply Or.intro_left
  rw [hfB g, hfB g']
#align mul_action.is_block_of_fixed MulAction.isBlock_of_fixed

variable (X)

/-- The empty set is a block -/
theorem bot_isBlock : IsBlock G (⊥ : Set X) :=
  by
  rw [is_block.def]
  intro g g'; apply Or.intro_left
  simp only [Set.bot_eq_empty, Set.smul_set_empty]
#align mul_action.bot_is_block MulAction.bot_isBlock

variable {X}

theorem singleton_isBlock (a : X) : IsBlock G ({a} : Set X) :=
  by
  rw [is_block.def]
  intro g g'
  simp only [Set.smul_set_singleton, Set.singleton_eq_singleton_iff, Set.disjoint_singleton, Ne.def]
  apply em
#align mul_action.singleton_is_block MulAction.singleton_isBlock

/-- Subsingletons are (trivial) blocks -/
theorem subsingleton_isBlock {B : Set X} (hB : B.Subsingleton) : IsBlock G B :=
  by
  cases Set.Subsingleton.eq_empty_or_singleton hB
  · rw [h]; apply bot_is_block
  · obtain ⟨a, ha⟩ := h; rw [ha]; apply singleton_is_block
#align mul_action.subsingleton_is_block MulAction.subsingleton_isBlock

end SMul

section Group

variable {G : Type _} [Group G] {X : Type _} [MulAction G X]

theorem IsBlock.def_one {B : Set X} : IsBlock G B ↔ ∀ g : G, g • B = B ∨ Disjoint (g • B) B :=
  by
  rw [is_block.def]; constructor
  · intro hB g
    simpa only [one_smul] using hB g 1
  · intro hB
    intro g g'
    cases hB (g'⁻¹ * g)
    · apply Or.intro_left
      rw [← inv_inv g', eq_inv_smul_iff, smul_smul]
      exact h
    · apply Or.intro_right
      rw [Set.disjoint_iff] at h ⊢
      rintro x ⟨hx, hx'⟩
      simp only [Set.mem_empty_iff_false]
      suffices : g'⁻¹ • x ∈ (g'⁻¹ * g) • B ⊓ B
      apply h this
      simp only [Set.inf_eq_inter, Set.mem_inter_iff]
      simp only [← Set.mem_smul_set_iff_inv_smul_mem]
      rw [← smul_smul]; rw [smul_inv_smul]
      exact ⟨hx, hx'⟩
#align mul_action.is_block.def_one MulAction.IsBlock.def_one

theorem IsBlock.mk_notempty_one {B : Set X} : IsBlock G B ↔ ∀ g : G, g • B ∩ B ≠ ∅ → g • B = B :=
  by
  rw [is_block.def_one]
  apply forall_congr'
  intro g
  rw [Set.disjoint_iff_inter_eq_empty]
  exact or_iff_not_imp_right
#align mul_action.is_block.mk_notempty_one MulAction.IsBlock.mk_notempty_one

theorem IsBlock.mk_mem {B : Set X} :
    IsBlock G B ↔ ∀ (g : G) (a : X) (ha : a ∈ B) (hga : g • a ∈ B), g • B = B :=
  by
  rw [is_block.mk_notempty_one]
  simp_rw [← Set.nonempty_iff_ne_empty, Set.nonempty_def]
  simp_rw [Set.mem_inter_iff]
  simp_rw [exists_imp]
  simp_rw [and_imp]
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp_rw [Imp.swap]
  constructor
  · intro H g a ha hga
    rw [← eq_inv_smul_iff]; apply symm
    refine' H g⁻¹ a ha _; rw [inv_inv]; exact hga
  · intro H g a ha hga
    rw [← eq_inv_smul_iff]; apply symm
    exact H g⁻¹ a ha hga
#align mul_action.is_block.mk_mem MulAction.IsBlock.mk_mem

-- was : is_block_def'
theorem IsBlock.def_mem {B : Set X} (hB : IsBlock G B) (a : X) (g : G) :
    a ∈ B → g • a ∈ B → g • B = B :=
  IsBlock.mk_mem.mp hB g a
#align mul_action.is_block.def_mem MulAction.IsBlock.def_mem

theorem IsBlock.mk_subset {B : Set X} :
    IsBlock G B ↔ ∀ (g : G) (b : X) (hb : b ∈ B) (hb' : b ∈ g • B), g • B ≤ B :=
  by
  constructor
  · intro hB g b hb hgb
    rw [Set.le_eq_subset, Set.set_smul_subset_iff,
      is_block.def_mem hB b g⁻¹ hb (set.mem_smul_set_iff_inv_smul_mem.mp hgb)]
  · rw [is_block.mk_notempty_one]
    intro hB g hg
    rw [← Set.nonempty_iff_ne_empty] at hg 
    obtain ⟨b : X, hb' : b ∈ g • B, hb : b ∈ B⟩ := set.nonempty_def.mp hg
    apply le_antisymm
    · exact hB g b hb hb'
    suffices g⁻¹ • B ≤ B by
      rw [Set.le_eq_subset] at this ⊢
      rw [← inv_inv g, ← Set.set_smul_subset_iff]; exact this
    exact
      hB g⁻¹ (g⁻¹ • b) (set.mem_smul_set_iff_inv_smul_mem.mp hb') (set.smul_mem_smul_set_iff.mpr hb)
#align mul_action.is_block.mk_subset MulAction.IsBlock.mk_subset

/-- An invariant block is a block -/
theorem isBlock_of_invariant (B : Set X) (hfB : IsInvariantBlock G B) : IsBlock G B :=
  by
  rw [is_block.def_one]
  intro g; apply Or.intro_left
  apply le_antisymm
  exact hfB g
  · intro x hx
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    apply hfB g⁻¹
    rw [Set.smul_mem_smul_set_iff]; exact hx
#align mul_action.is_block_of_invariant MulAction.isBlock_of_invariant

/-- An orbit is a block -/
theorem isBlock_of_orbit (a : X) : IsBlock G (orbit G a) :=
  by
  apply is_block_of_fixed
  intro g; apply smul_orbit
#align mul_action.is_block_of_orbit MulAction.isBlock_of_orbit

variable (X)

/-- The full set is a (trivial) block -/
theorem top_isBlock : IsBlock G (⊤ : Set X) :=
  by
  apply is_block_of_fixed
  intro g
  simp only [Set.top_eq_univ, Set.smul_set_univ]
#align mul_action.top_is_block MulAction.top_isBlock

variable {G X}

/-- Is B is a block for an action G, it is a block for the action of any subgroup of G -/
theorem Subgroup.isBlock {H : Subgroup G} {B : Set X} (hfB : IsBlock G B) : IsBlock H B :=
  by
  rw [is_block.def_one]; rintro ⟨g, hg⟩
  simpa only using is_block.def_one.mp hfB g
#align mul_action.subgroup.is_block MulAction.Subgroup.isBlock

theorem isBlock_preimage {H Y : Type _} [Group H] [MulAction H Y] {φ : H → G} (j : Y →ₑ[φ] X)
    {B : Set X} (hB : IsBlock G B) : IsBlock H (j ⁻¹' B) :=
  by
  rw [is_block.def_one]
  intro g
  cases' is_block.def_one.mp hB (φ g) with heq hdis
  · apply Or.intro_left
    rw [← EquivariantMap.preimage_smul_setₑ, HEq]
  · apply Or.intro_right
    rw [← EquivariantMap.preimage_smul_setₑ]
    apply Disjoint.preimage; exact hdis
#align mul_action.is_block_preimage MulAction.isBlock_preimage

theorem isBlock_image {H Y : Type _} [Group H] [MulAction H Y] {φ : G → H} (j : X →ₑ[φ] Y)
    (hφ : Function.Surjective φ) (hj : Function.Injective j) {B : Set X} (hB : IsBlock G B) :
    IsBlock H (j '' B) := by
  rw [is_block.def]
  intro h h'
  obtain ⟨g, rfl⟩ := hφ h
  obtain ⟨g', rfl⟩ := hφ h'
  simp only [← EquivariantMap.image_smul_setₑ]
  cases' is_block.def.mp hB g g' with h h
  · apply Or.intro_left; rw [h]
  · apply Or.intro_right
    exact Set.disjoint_image_of_injective hj h
#align mul_action.is_block_image MulAction.isBlock_image

theorem SubMulAction.isBlock {C : SubMulAction G X} {B : Set X} (hB : IsBlock G B) :
    IsBlock G (coe ⁻¹' B : Set C) :=
  by
  rw [← SubMulAction.inclusion.toFun_eq_coe]
  change is_block G (C.inclusion ⁻¹' B)
  exact @is_block_preimage G _ X _ G C _ _ (MonoidHom.id G) C.inclusion B hB
#align mul_action.sub_mul_action.is_block MulAction.SubMulAction.isBlock

theorem SubMulAction.smul_coe_eq_coe_smul {C : SubMulAction G X} {B : Set C} {g : G} :
    g • (coe '' B : Set X) = coe '' (g • B) := by
  ext; constructor
  · intro hx; obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hy
    use g • z
    constructor
    exact ⟨z, hz, rfl⟩
    rw [SubMulAction.val_smul_of_tower]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hy
    rw [SubMulAction.val_smul_of_tower]
    use ↑z; constructor
    exact ⟨z, hz, rfl⟩; rfl
#align mul_action.sub_mul_action.smul_coe_eq_coe_smul MulAction.SubMulAction.smul_coe_eq_coe_smul

theorem SubMulAction.isBlock_coe {C : SubMulAction G X} {B : Set C} :
    IsBlock G B ↔ IsBlock G (coe '' B : Set X) :=
  by
  simp only [is_block.def_one]
  apply forall_congr'
  intro g
  rw [sub_mul_action.smul_coe_eq_coe_smul]
  apply or_congr (Set.image_eq_image Subtype.coe_injective).symm
  simp only [Set.disjoint_iff, Set.subset_empty_iff]
  rw [←
    Set.InjOn.image_inter (Set.injOn_of_injective Subtype.coe_injective _) (Set.subset_univ _)
      (Set.subset_univ _)]
  simp only [Set.image_eq_empty]
#align mul_action.sub_mul_action.is_block_coe MulAction.SubMulAction.isBlock_coe

theorem IsBlock.of_top_iff (B : Set X) : IsBlock G B ↔ IsBlock (⊤ : Subgroup G) B :=
  by
  simp only [is_block.def_one]
  constructor
  intro h g; exact h g
  intro h g; exact h ⟨g, Subgroup.mem_top g⟩
#align mul_action.is_block.of_top_iff MulAction.IsBlock.of_top_iff

theorem orbit.equal_or_disjoint (a b : X) :
    orbit G a = orbit G b ∨ Disjoint (orbit G a) (orbit G b) :=
  by
  cases' em (Disjoint (orbit G a) (orbit G b)) with h h
  · apply Or.intro_right; exact h
  apply Or.intro_left
  rw [Set.not_disjoint_iff] at h 
  obtain ⟨x, hxa, hxb⟩ := h
  rw [← orbit_eq_iff] at hxa hxb 
  rw [← hxa, ← hxb]
#align mul_action.orbit.equal_or_disjoint MulAction.orbit.equal_or_disjoint

/-- The intersection of two blocks is a block -/
theorem IsBlock.inter {B₁ B₂ : Set X} (h₁ : IsBlock G B₁) (h₂ : IsBlock G B₂) :
    IsBlock G (B₁ ∩ B₂) := by
  rw [is_block.def_one]
  intro g
  rw [Set.smul_set_inter]
  cases' is_block.def_one.mp h₁ g with h₁ h₁
  -- em (disjoint (g • B₁) B₁) with h h,
  · cases' is_block.def_one.mp h₂ g with h₂ h₂
    · apply Or.intro_left; rw [h₁, h₂]
    apply Or.intro_right
    apply Disjoint.inter_left'; apply Disjoint.inter_right'
    exact h₂
  · apply Or.intro_right
    apply Disjoint.inter_left; apply Disjoint.inter_right
    exact h₁
#align mul_action.is_block.inter MulAction.IsBlock.inter

/-- An intersection of blocks is a block -/
theorem IsBlock.iInter {ι : Type _} {B : ι → Set X} (hB : ∀ i : ι, IsBlock G (B i)) :
    IsBlock G (⋂ i, B i) := by
  rw [is_block.def_one]
  cases' em (IsEmpty ι) with hι hι
  · -- ι = ∅, block = ⊤
    suffices (⋂ i : ι, B i) = Set.univ by rw [this]; exact is_block.def_one.mp (top_is_block X)
    simp only [Set.top_eq_univ, Set.iInter_eq_univ]
    intro i; exfalso; apply hι.false; exact i
  intro g; rw [smul_set_Inter]
  cases' em (∃ i : ι, Disjoint (g • B i) (B i)) with h h
  · obtain ⟨j, hj⟩ := h
    apply Or.intro_right
    -- rw set.smul_Inter h,
    refine' Disjoint.mono _ _ hj
    apply Set.iInter_subset
    apply Set.iInter_subset
  simp only [not_exists] at h 
  apply Or.intro_left
  have : ∀ i : ι, g • B i = B i := fun i => Or.resolve_right (is_block.def_one.mp (hB i) g) (h i)
  rw [Set.iInter_congr this]
#align mul_action.is_block.Inter MulAction.IsBlock.iInter

theorem IsBlock.of_subgroup_of_conjugate {B : Set X} {H : Subgroup G} (hB : IsBlock H B) (g : G) :
    IsBlock (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) H) (g • B) :=
  by
  rw [is_block.def_one]
  intro h'
  obtain ⟨h, hH, hh⟩ := subgroup.mem_map.mp (SetLike.coe_mem h')
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hh 
  suffices : h' • g • B = g • h • B
  simp only [this]
  cases' is_block.def_one.mp hB ⟨h, hH⟩ with heq hdis
  · apply Or.intro_left
    apply congr_arg
    exact HEq
  · apply Or.intro_right
    apply Set.disjoint_image_of_injective (MulAction.injective g)
    exact hdis
  suffices : (h' : G) • g • B = g • h • B
  rw [← this]; rfl
  rw [← hh]
  rw [smul_smul (g * h * g⁻¹) g B]
  rw [smul_smul g h B]
  simp only [inv_mul_cancel_right]
#align mul_action.is_block.of_subgroup_of_conjugate MulAction.IsBlock.of_subgroup_of_conjugate

/-- A translate of a block is a block -/
theorem isBlock_of_block {B : Set X} (g : G) (hB : IsBlock G B) : IsBlock G (g • B) :=
  by
  rw [is_block.of_top_iff] at hB ⊢
  suffices : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) ⊤ = ⊤
  rw [← this]
  refine' is_block.of_subgroup_of_conjugate hB g
  suffices ⊤ = Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj g)) ⊤
    by
    rw [this]
    refine' Subgroup.map_comap_eq_self_of_surjective _ _
    exact MulEquiv.surjective (MulAut.conj g)
  rw [Subgroup.comap_top]
#align mul_action.is_block_of_block MulAction.isBlock_of_block

variable (G)

/-- A block_system of X is a partition of X into blocks -/
def IsBlockSystem (B : Set (Set X)) :=
  Setoid.IsPartition B ∧ ∀ b : Set X, b ∈ B → IsBlock G b
#align mul_action.is_block_system MulAction.IsBlockSystem

variable {G}

-- The following proof is absurdly complicated !
/-- Translates of a block form a `block_system` -/
theorem IsBlockSystem.of_block [hGX : MulAction.IsPretransitive G X] {B : Set X} (hB : IsBlock G B)
    (hBe : B.Nonempty) : IsBlockSystem G (Set.range fun g : G => g • B) :=
  by
  constructor
  constructor
  · simp only [Set.mem_range, not_exists]
    intro x hx; apply Set.Nonempty.ne_empty hBe
    rw [← Set.image_eq_empty]
    exact hx
  · intro a
    obtain ⟨b : X, hb : b ∈ B⟩ := hBe
    obtain ⟨g, hab⟩ := exists_smul_eq G b a
    have hg : a ∈ g • B := by
      change a ∈ (fun b => g • b) '' B
      rw [Set.mem_image]; use b; exact ⟨hb, hab⟩
    use g • B
    constructor
    · simp only [Set.mem_range, exists_apply_eq_apply, exists_unique_iff_exists, exists_true_left]
      exact hg
    · simp only [Set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index,
        forall_apply_eq_imp_iff']
      intro g' hg'
      apply symm
      apply Or.resolve_right (is_block.def.mp hB g g')
      rw [Set.not_disjoint_iff]
      use a; exact ⟨hg, hg'⟩
  intro b; rintro ⟨g, hg : g • B = b⟩
  rw [← hg]; exact is_block_of_block g hB
#align mul_action.is_block_system.of_block MulAction.IsBlockSystem.of_block

/-- Orbits of an element form a partition -/
theorem IsPartition.of_orbits : Setoid.IsPartition (Set.range fun a : X => orbit G a) :=
  by
  constructor
  · rintro ⟨a, ha : orbit G a = ∅⟩
    apply Set.Nonempty.ne_empty (MulAction.orbit_nonempty a)
    exact ha
  intro a; use orbit G a
  constructor
  · simp only [Set.mem_range_self, mem_orbit_self, exists_unique_iff_exists, exists_true_left]
  · simp only [Set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index,
      forall_apply_eq_imp_iff']
    intro b hb
    rw [orbit_eq_iff]
    obtain ⟨g, rfl⟩ := mul_action.mem_orbit_iff.mp hb
    use g⁻¹; simp only [inv_smul_smul]
#align mul_action.is_partition.of_orbits MulAction.IsPartition.of_orbits

section Normal

/-- An orbit of a normal subgroup is a block -/
theorem orbit.isBlock_of_normal {N : Subgroup G} (nN : Subgroup.Normal N) (a : X) :
    IsBlock G (orbit N a) := by
  rw [is_block.def_one]
  intro g
  suffices g • orbit N a = orbit N (g • a) by rw [this]; apply orbit.equal_or_disjoint
  change ((fun x : X => g • x) '' Set.range fun k : N => k • a) = Set.range fun k : N => k • g • a
  simp only [Set.image_smul, Set.smul_set_range]
  ext
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use g * k * g⁻¹
    apply nN.conj_mem; exact hk
    change (g * k * g⁻¹) • g • a = g • k • a
    rw [smul_smul, inv_mul_cancel_right, ← smul_smul]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use g⁻¹ * k * g⁻¹⁻¹
    apply nN.conj_mem; exact hk
    change g • (g⁻¹ * k * g⁻¹⁻¹) • a = k • g • a
    simp only [← mul_assoc, ← smul_smul, smul_inv_smul, inv_inv]
#align mul_action.orbit.is_block_of_normal MulAction.orbit.isBlock_of_normal

/-- The orbits of a normal subgroup form a block system -/
theorem IsBlockSystem.of_normal {N : Subgroup G} (nN : Subgroup.Normal N) :
    IsBlockSystem G (Set.range fun a : X => orbit N a) :=
  by
  constructor
  · apply is_partition.of_orbits
  · intro b; rintro ⟨a, rfl⟩
    exact orbit.is_block_of_normal nN a
#align mul_action.is_block_system.of_normal MulAction.IsBlockSystem.of_normal

end Normal

section Stabilizer

/- For transitive actions, construction of the lattice equivalence
  `stabilizer_block_equiv` between
  - blocks of `mul_action G X` containing a point a ∈ X,
  and
  - subgroups of G containing `stabilizer G a`.
  (Wielandt, th. 7.5) -/
/-- The orbit of a under a subgroup containing the stabilizer of a
 is a block -/
theorem isBlock_of_suborbit {H : Subgroup G} {a : X} (hH : stabilizer G a ≤ H) :
    IsBlock G (MulAction.orbit H a) :=
  by
  rw [is_block.mk_subset]; intro g b
  rintro ⟨h, rfl⟩
  simp
  intro hb'
  suffices g ∈ H by
    rw [← Subgroup.coe_mk H g this, ← Subgroup.smul_def]
    apply smul_orbit_subset
  rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, ← MulAction.mul_smul] at hb' 
  obtain ⟨k : ↥H, hk⟩ := hb'
  simp only at hk 
  rw [MulAction.mul_smul, ← smul_eq_iff_eq_inv_smul, ← inv_inv (h : G), ← smul_eq_iff_eq_inv_smul, ←
    MulAction.mul_smul, Subgroup.smul_def, ← MulAction.mul_smul] at hk 
  rw [← mem_stabilizer_iff] at hk 
  let hk' := hH hk
  rw [Subgroup.mul_mem_cancel_right, Subgroup.mul_mem_cancel_left] at hk' 
  exact hk'
  apply Subgroup.inv_mem; exact SetLike.coe_mem h
  exact SetLike.coe_mem k
#align mul_action.is_block_of_suborbit MulAction.isBlock_of_suborbit

/-- If B is a block containing a , then the stabilizer of B contains the stabilizer of a -/
theorem stabilizer_of_block {B : Set X} (hB : IsBlock G B) {a : X} (ha : a ∈ B) :
    stabilizer G a ≤ stabilizer G B := by
  intro g hg
  rw [mem_stabilizer_iff] at hg ⊢
  cases' is_block.def_one.mp hB g with h h'
  exact h
  exfalso; rw [← Set.mem_empty_iff_false a]
  rw [disjoint_iff, Set.inf_eq_inter, Set.bot_eq_empty] at h' 
  rw [← h', Set.mem_inter_iff]
  constructor
  rw [← hg]; rw [Set.smul_mem_smul_set_iff]; exact ha
  exact ha
#align mul_action.stabilizer_of_block MulAction.stabilizer_of_block

/-- A block is the orbit of a under its stabilizer -/
theorem block_of_stabilizer_of_block [htGX : IsPretransitive G X] {B : Set X} (hB : IsBlock G B)
    {a : X} (ha : a ∈ B) : MulAction.orbit (stabilizer G B) a = B :=
  by
  ext; constructor
  · -- rw mul_action.mem_orbit_iff, intro h,
    rintro ⟨k, rfl⟩
    let z := mem_stabilizer_iff.mp (SetLike.coe_mem k)
    rw [← Subgroup.smul_def] at z 
    let zk : k • a ∈ k • B := set.smul_mem_smul_set_iff.mpr ha
    rw [z] at zk ; exact zk
  intro hx
  obtain ⟨k, rfl⟩ := exists_smul_eq G a x
  use k
  · rw [mem_stabilizer_iff]
    exact is_block.def_mem hB a k ha hx
  rfl
#align mul_action.block_of_stabilizer_of_block MulAction.block_of_stabilizer_of_block

/--
A subgroup containing the stabilizer of a is the stabilizer of the orbit of a under that subgroup -/
theorem stabilizer_of_block_of_stabilizer {a : X} {H : Subgroup G} (hH : stabilizer G a ≤ H) :
    stabilizer G (orbit H a) = H := by
  ext g; constructor
  · intro hg; rw [mem_stabilizer_iff] at hg 
    suffices g • a ∈ orbit H a by
      rw [mem_orbit_iff] at this 
      obtain ⟨k, hk⟩ := this
      rw [← Subgroup.mul_mem_cancel_left H (SetLike.coe_mem k⁻¹)]
      rw [smul_eq_iff_eq_inv_smul] at hk 
      apply hH
      rw [mem_stabilizer_iff]; rw [MulAction.mul_smul]
      rw [← Subgroup.smul_def]; exact hk.symm
    rw [← hg]
    simp only [Set.smul_mem_smul_set_iff, mem_orbit_self]
  intro hg
  rw [mem_stabilizer_iff]
  rw [← Subgroup.coe_mk H g hg, ← Subgroup.smul_def]
  apply smul_orbit
#align mul_action.stabilizer_of_block_of_stabilizer MulAction.stabilizer_of_block_of_stabilizer

variable (G)

/-- Order equivalence between blocks in X containing a point a
 and subgroups of G containing the stabilizer of a (Wielandt, th. 7.5)-/
def stabilizerBlockEquiv [htGX : IsPretransitive G X] (a : X) :
    { B : Set X // a ∈ B ∧ IsBlock G B } ≃o Set.Ici (stabilizer G a)
    where
  toFun := fun ⟨B, ha, hB⟩ => ⟨stabilizer G B, stabilizer_of_block hB ha⟩
  invFun := fun ⟨H, hH⟩ => ⟨MulAction.orbit H a, MulAction.mem_orbit_self a, isBlock_of_suborbit hH⟩
  left_inv := fun ⟨B, ha, hB⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (block_of_stabilizer_of_block hB ha)
  right_inv := fun ⟨H, hH⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (stabilizer_of_block_of_stabilizer hH)
  map_rel_iff' := by
    rintro ⟨B, ha, hB⟩; rintro ⟨B', ha', hB'⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Set.le_eq_subset]
    constructor
    · intro hBB'
      rw [← block_of_stabilizer_of_block hB ha]
      rw [← block_of_stabilizer_of_block hB' ha']
      intro x; rintro ⟨k, rfl⟩; use k; apply hBB'; exact SetLike.coe_mem k
      rfl
    · intro hBB'
      intro g
      change g ∈ stabilizer G B → g ∈ stabilizer G B'
      simp only [mem_stabilizer_iff]
      intro hgB
      apply is_block.def_mem hB' a g ha'
      apply hBB'
      rw [← hgB]
      simp_rw [Set.smul_mem_smul_set_iff]; exact ha
#align mul_action.stabilizer_block_equiv MulAction.stabilizerBlockEquiv

end Stabilizer

section Fintype

theorem Setoid.nat_sum {α : Type _} [Finite α] {c : Set (Set α)} (hc : Setoid.IsPartition c) :
    (finsum fun x : c => Nat.card x) = Nat.card α := by
  classical
  letI := Fintype.ofFinite α
  simp only [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma]
  refine' Fintype.card_congr (Equiv.ofBijective (fun x => x.snd : (Σ a : ↥c, ↥a) → α) _)
  /-
    rw function.bijective_iff_exists_unique,
    have := hc.2,
    intro b, specialize this b, -/
  constructor
  -- injectivity
  rintro ⟨⟨x, hx⟩, ⟨a, ha : a ∈ x⟩⟩ ⟨⟨y, hy⟩, ⟨b, hb : b ∈ y⟩⟩ hab
  dsimp at hab 
  rw [hab] at ha 
  rw [Sigma.subtype_ext_iff]
  simp only [Subtype.mk_eq_mk, Subtype.coe_mk]
  apply And.intro _ hab
  refine' ExistsUnique.unique (hc.2 b) _ _
  simp only [exists_unique_iff_exists, exists_prop]
  exact ⟨hx, ha⟩
  simp only [exists_unique_iff_exists, exists_prop]
  exact ⟨hy, hb⟩
  -- surjectivity
  intro a
  obtain ⟨x, ⟨hx, ha : a ∈ x, ha'⟩, hx'⟩ := hc.2 a
  use ⟨⟨x, hx⟩, ⟨a, ha⟩⟩
  rfl
#align mul_action.setoid.nat_sum MulAction.Setoid.nat_sum

/-- The cardinality of the ambient is the product of
  of the cardinality of a block
  by the cardinality of the set of iterates of that block -/
theorem nat_card_block_mul_card_orbit_eq [hfX : Finite X] [hGX : IsPretransitive G X] {B : Set X}
    (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Nat.card B * Nat.card (Set.range fun g : G => g • B) = Nat.card X := by
  classical
  letI := Fintype.ofFinite X
  rw [← setoid.nat_sum (is_block_system.of_block hB hB_ne).1]
  simp only [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  suffices : ∀ x : Set.range fun g : G => g • B, Fintype.card x = Fintype.card B
  simp_rw [this]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul, Nat.cast_id]
  apply mul_comm
  rintro ⟨C, ⟨g, hg : g • B = C⟩⟩
  simp only [coeSort_coeBase, Subtype.coe_mk]
  simp only [← Set.toFinset_card, ← hg, Set.toFinset_smul_set, Finset.card_smul_finset]
#align mul_action.nat_card_block_mul_card_orbit_eq MulAction.nat_card_block_mul_card_orbit_eq

/-- The cardinality of a block divides the cardinality of the ambient type -/
theorem nat_card_of_block_divides [hfX : Finite X] [hGX : IsPretransitive G X] {B : Set X}
    (hB : IsBlock G B) (hB_ne : B.Nonempty) : Nat.card B ∣ Nat.card X :=
  Dvd.intro _ (nat_card_block_mul_card_orbit_eq hB hB_ne)
#align mul_action.nat_card_of_block_divides MulAction.nat_card_of_block_divides

/-- A too large block is equal to ⊤ -/
theorem is_top_of_large_block [hfX : Finite X] [hGX : IsPretransitive G X] {B : Set X}
    (hB : IsBlock G B) (hB' : Nat.card X < 2 * Nat.card B) : B = ⊤ := by
  classical
  letI := Fintype.ofFinite X
  cases' Set.eq_empty_or_nonempty B with hB_e hB_ne
  --  cases nat.eq_zero_or_pos (nat.card B),
  · exfalso; rw [hB_e] at hB' 
    simpa only [Nat.card_eq_fintype_card, Set.empty_card', MulZeroClass.mul_zero,
      Nat.not_lt_zero] using hB'
  rw [Set.top_eq_univ, ← Set.toFinset_inj, Set.toFinset_univ, ← Finset.card_eq_iff_eq_univ,
    Set.toFinset_card]
  obtain ⟨k, h⟩ := nat_card_of_block_divides hB hB_ne
  simp only [← Nat.card_eq_fintype_card]
  rw [h] at hB' ⊢
  suffices : k = 1
  simp only [this, mul_one]
  apply le_antisymm
  · apply Nat.le_of_lt_succ
    rw [lt_iff_not_le]; intro hk
    rw [lt_iff_not_le] at hB' ; apply hB'
    rw [mul_comm]
    refine' Nat.mul_le_mul_left _ hk
  · rw [Nat.one_le_iff_ne_zero]; intro hk
    rw [hk, MulZeroClass.mul_zero, Nat.card_eq_fintype_card] at h 
    apply (lt_iff_not_le.mp hB') (Eq.le _)
    suffices : Nat.card B = 0; rw [this, MulZeroClass.mul_zero, MulZeroClass.zero_mul]
    rw [← le_zero_iff, ← h, Nat.card_eq_fintype_card]
    exact set_fintype_card_le_univ B
#align mul_action.is_top_of_large_block MulAction.is_top_of_large_block

/-- If a block has too many translates, then it is a singleton  -/
theorem is_top_of_small_block [hfX : Finite X] [hGX : IsPretransitive G X] {B : Set X}
    (hB : IsBlock G B) (hX : Nontrivial X)
    (hB' : Nat.card X < 2 * Nat.card (Set.range fun g : G => (g • B : Set X))) : B.Subsingleton :=
  by
  classical
  letI := Fintype.ofFinite X
  rw [← Set.subsingleton_coe, ← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]
  cases Set.eq_empty_or_nonempty B
  · exfalso
    rw [← Fintype.one_lt_card_iff_nontrivial, lt_iff_not_le] at hX 
    apply hX
    rw [← Nat.lt_succ_iff, ← mul_one (1 : ℕ).succ, ← Nat.card_eq_fintype_card]
    apply lt_of_lt_of_le hB'
    apply mul_le_mul_left'
    rw [Nat.card_eq_fintype_card, Fintype.card_le_one_iff]
    have : ∀ x : Set.range fun g : G => g • B, ↑x = (∅ : Set X) :=
      by
      rintro ⟨x, hx⟩
      simp_rw [h, Set.smul_set_empty] at hx 
      simp only [Subtype.coe_mk]
      apply Set.range_const_subset hx
    intro s t; rw [← Subtype.coe_inj]
    simp only [this]
  let hk := nat_card_block_mul_card_orbit_eq hB h
  cases' Nat.lt_or_ge (Nat.card B) 2 with hb hb
  rwa [Nat.lt_succ_iff] at hb 
  exfalso
  rw [← hk, lt_iff_not_ge] at hB' 
  apply hB'
  refine' Nat.mul_le_mul_right _ hb
#align mul_action.is_top_of_small_block MulAction.is_top_of_small_block

example {α : Type _} (B B' : Set α) (hB : B.Finite) (hB' : B'.Finite) (h : B ⊆ B')
    (hc : Nat.card B = Nat.card B') : B = B' :=
  by
  rw [← Set.Finite.toFinset_inj]
  refine' Finset.eq_of_subset_of_card_le _ _
  -- The two finiteness instances
  exact hB;
  exact hB'
  rw [Set.Finite.toFinset_subset, Set.Finite.coe_toFinset]; exact h
  apply Eq.ge
  suffices : ∀ (B : Set α) (hB : B.Finite), hB.to_finset.card = Nat.card B
  simp only [this]; exact hc
  intro B hB
  haveI : Fintype B := Set.Finite.fintype hB
  rw [Set.Finite.card_toFinset hB]; rw [Nat.card_eq_fintype_card]

-- TODO : Is the assumption B.finite necessary ?
/-- The intersection of the translates of a *finite* subset which contain a given point
is a block (Wielandt, th. 7.3 )-/
theorem IsBlock.of_subset [hGX : IsPretransitive G X] (a : X) (B : Set X) (hfB : B.Finite) :
    IsBlock G (⋂ (k : G) (hg : a ∈ k • B), k • B) :=
  by
  let B' := ⋂ (k : G) (hg : a ∈ k • B), k • B
  cases' Set.eq_empty_or_nonempty B with hfB_e hfB_ne
  · suffices : (⋂ (k : G) (hg : a ∈ k • B), k • B) = Set.univ
    rw [this]; apply top_is_block
    simp only [Set.iInter_eq_univ]
    intro k hk; exfalso
    rw [hfB_e] at hk ; simpa only [Set.smul_set_empty] using hk
  have hB'₀ : ∀ (k : G) (hk : a ∈ k • B), B' ≤ k • B := by intro k hk;
    apply Set.biInter_subset_of_mem; exact hk
  have hfB' : B'.finite := by
    obtain ⟨b, hb : b ∈ B⟩ := hfB_ne
    obtain ⟨k, hk : k • b = a⟩ := exists_smul_eq G b a
    have hk' : a ∈ k • B; use b; exact ⟨hb, hk⟩
    apply Set.Finite.subset _ (hB'₀ k hk')
    apply Set.Finite.map
    exact hfB
  have ha : a ∈ B' := by apply Set.mem_biInter; intro g; intro h; exact h
  have hag : ∀ g : G, a ∈ g • B' → B' ≤ g • B' :=
    by
    intro g; intro hg
    -- a = g • b ; b ∈ B' ; a ∈ k • B → b ∈ k • B
    intro x;
    intro hx
    use g⁻¹ • x; constructor
    · apply Set.mem_biInter; intro k; rintro (hk : a ∈ k • B)
      rw [← Set.mem_smul_set_iff_inv_smul_mem, smul_smul]
      apply hB'₀
      --  x hx,
      rw [← smul_smul, Set.mem_smul_set_iff_inv_smul_mem]
      apply hB'₀ k hk
      -- (g⁻¹ • a) (),
      exact set.mem_smul_set_iff_inv_smul_mem.mp hg
      exact hx
    simp only [smul_inv_smul]
  have hag' : ∀ g : G, a ∈ g • B' → B' = g • B' :=
    by
    intro g hg
    apply symm
    rw [← mem_stabilizer_iff]
    rw [← Subgroup.inv_mem_iff (stabilizer G B')]
    rw [mem_stabilizer_of_finite_iff G B' hfB' g⁻¹]
    rw [← Set.subset_set_smul_iff]
    exact hag g hg
  rw [is_block.mk_notempty_one]
  intro g hg
  rw [← Set.nonempty_iff_ne_empty] at hg 
  obtain ⟨b : X, hb' : b ∈ g • B', hb : b ∈ B'⟩ := set.nonempty_def.mp hg
  obtain ⟨k : G, hk : k • a = b⟩ := exists_smul_eq G a b
  have hak : a ∈ k⁻¹ • B' := by use b; apply And.intro hb; rw [← hk, inv_smul_smul]
  have hagk : a ∈ (k⁻¹ * g) • B' :=
    by
    rw [mul_smul, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, hk]
    exact hb'
  have hkB' : B' = k⁻¹ • B' := hag' k⁻¹ hak
  have hgkB' : B' = (k⁻¹ * g) • B' := hag' (k⁻¹ * g) hagk
  rw [mul_smul] at hgkB' 
  rw [← smul_eq_iff_eq_inv_smul] at hkB' hgkB' 
  rw [← hgkB', hkB']
#align mul_action.is_block.of_subset MulAction.IsBlock.of_subset

end Fintype

end Group

end MulAction

#lint


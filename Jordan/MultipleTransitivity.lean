/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module multiple_transitivity
-/
import Jordan.Primitive
import Jordan.IndexNormal
import Jordan.SubMulActions

import Jordan.Mathlib.Stabilizer
import Jordan.Mathlib.Pretransitive
import Jordan.Mathlib.Partitions
import Jordan.Mathlib.Set
-- import Jordan.Mathlib.Cardinal
import Jordan.Mathlib.Extensions

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.Perm.Cycle.Concrete


open scoped BigOperators Pointwise Cardinal

-- open scoped Classical

namespace MulAction

section Transitivity

section Monoid

/- It would be better do have it for has_smul
but the instance does not automatically transfer to subtypes -/
variable {M α : Type _} [DecidableEq α] [Monoid M] [MulAction M α]

theorem isPretransitive_of_submonoid {K : Submonoid M} (h : IsPretransitive K α) :
    IsPretransitive M α := by
  let h_eq := h.exists_smul_eq
  apply IsPretransitive.mk
  intro x y
  obtain ⟨⟨k, hk⟩, hk'⟩ := h_eq x y
  exact ⟨k, hk'⟩
#align mul_action.is_pretransitive_of_submonoid MulAction.isPretransitive_of_submonoid

theorem isPretransitive_of_submonoid_le {G K : Submonoid M} (hKG : K ≤ G)
    (h : IsPretransitive K α) : IsPretransitive G α :=
  by
  let h_eq := h.exists_smul_eq
  apply IsPretransitive.mk
  intro x y
  obtain ⟨⟨k, hk⟩, hk'⟩ := h_eq x y
  use ⟨k, hKG hk⟩
  exact hk'
#align mul_action.is_pretransitive_of_submonoid_le MulAction.isPretransitive_of_submonoid_le

end Monoid

section Group

variable (M α : Type _) [Group M] [MulAction M α]

/-- Cardinal of an orbit vs index of stabilizers, in nat.card -/
theorem card_orbit_eq_stabilizer_index {a : α} : 
  Set.ncard (orbit M a) = (stabilizer M a).index := by
  rw [← Set.Nat.card_coe_set_eq]
  apply Nat.card_congr
  exact orbitEquivQuotientStabilizer M a
#align mul_action.card_orbit_eq_stabilizer_index MulAction.card_orbit_eq_stabilizer_index

variable {α}
/-- Cardinal vs index of stabilizers, for a pretransitive action, in nat.card -/
theorem stabilizer_index_of_pretransitive (h : IsPretransitive M α) (a : α) :
    (stabilizer M a).index = Nat.card α := by
  rw [← card_orbit_eq_stabilizer_index]
  convert Set.ncard_univ α
  exact orbit_eq_univ M a
#align mul_action.stabilizer_index_of_pretransitive MulAction.stabilizer_index_of_pretransitive

variable {M}

theorem isPretransitive_of_subgroup {K : Subgroup M} (h : IsPretransitive K α) :
    IsPretransitive M α := by
  apply isPretransitive_of_submonoid
  swap; exact K.toSubmonoid
  exact h
#align mul_action.is_pretransitive_of_subgroup MulAction.isPretransitive_of_subgroup

theorem isPretransitive_of_subgroup_le {G K : Subgroup M} (hKG : K ≤ G) (h : IsPretransitive K α) :
    IsPretransitive G α := by
  let h_eq := h.exists_smul_eq
  apply IsPretransitive.mk
  intro x y
  obtain ⟨⟨k, hk⟩, hk'⟩ := h_eq x y
  use ⟨k, hKG hk⟩
  exact hk'
#align mul_action.is_pretransitive_of_subgroup_le MulAction.isPretransitive_of_subgroup_le

end Group

end Transitivity

section MultipleTransitivity

open Function.Embedding Nat MulAction

variable (M α : Type _) [Group M] [MulAction M α]

/-- An action of a group on a type α is n-pretransitive if the associated
action on (fin n ↪ α) is pretransitive -/
def IsMultiplyPretransitive (n : ℕ) := IsPretransitive M (Fin n ↪ α)
#align mul_action.is_multiply_pretransitive MulAction.IsMultiplyPretransitive

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The equivariant map from (fin 1 ↪ α) to α -/
def finOneToMap : (Fin 1 ↪ α) →ₑ[@id M] α
    where
  toFun x := x ⟨0, Nat.one_pos⟩
  map_smul' _ _ := rfl
#align mul_action.fin_one_to_map MulAction.finOneToMap

theorem finOneToMap_bijective : Function.Bijective (finOneToMap M α) := by
  constructor
  · intro x y hxy
    ext i
    rw [Fin.eq_zero i]
    exact hxy
  · intro a
    use {
      toFun := fun _ => a
      inj' := fun i j _ => by 
        rw [Fin.eq_zero i, Fin.eq_zero j] }
    rfl 
#align mul_action.fin_one_to_map_bijective MulAction.finOneToMap_bijective

variable {M α}

theorem isMultiplyPretransitive_of_subgroup {n : ℕ} {K : Subgroup M}
    (h : IsMultiplyPretransitive K α n) : IsMultiplyPretransitive M α n :=
  by
  unfold IsMultiplyPretransitive at *
  exact isPretransitive_of_subgroup h
#align mul_action.is_multiply_pretransitive_of_subgroup MulAction.isMultiplyPretransitive_of_subgroup

theorem isMultiplyPretransitive_of_le {n : ℕ} {H K : Subgroup M} (hHK : K ≤ H)
    (h : IsMultiplyPretransitive K α n) : IsMultiplyPretransitive H α n := by
  unfold IsMultiplyPretransitive at *
  refine' isPretransitive_of_subgroup_le hHK h
#align mul_action.is_multiply_pretransitive_of_le MulAction.isMultiplyPretransitive_of_le


/-- Given an equivariant map α → β, get an equivariant map on function types (ι ↪ α) → (ι ↪ β)-/
def EquivariantMap.embeddingOfEquivariantMap {N β : Type _} [Group N] [MulAction N β] 
    {σ : M → N} 
    {f : α →ₑ[σ] β} (hf : Function.Injective f) (ι : Type _) : 
    (ι ↪ α) →ₑ[σ] (ι ↪ β) where
  toFun x := ⟨f.toFun ∘ x.toFun, hf.comp x.inj'⟩
  map_smul' m x := by
    ext i
    simp only [smul_apply, coeFn_mk, Function.comp_apply, toFun_eq_coe, smul_apply]
    rw [f.map_smul']
#align mul_action.equivariant_map.embedding_of_equivariant_map MulAction.EquivariantMap.embeddingOfEquivariantMap

theorem EquivariantMap.embeddingOfEquivariantMap_apply {N β : Type _} [Group N] [MulAction N β]
    {σ : M → N} {f : α →ₑ[σ] β} (hf : Function.Injective f) {ι : Type _} {x : ι ↪ α} {i : ι} :
    (EquivariantMap.embeddingOfEquivariantMap hf ι) x i = f (x i) :=
  rfl
#align mul_action.equivariant_map.embedding_of_equivariant_map_apply MulAction.EquivariantMap.embeddingOfEquivariantMap_apply

theorem EquivariantMap.embeddingOfEquivariantMap_is_injective {N β : Type _} [Group N]
    [MulAction N β] {σ : M → N} {f : α →ₑ[σ] β} (hf : Function.Injective f) {ι : Type _} :
    Function.Injective (EquivariantMap.embeddingOfEquivariantMap hf ι) :=
  by
  intro x y hxy
  ext i
  apply hf
  simp only [← EquivariantMap.embeddingOfEquivariantMap_apply hf]
  rw [hxy]
#align mul_action.equivariant_map.embedding_of_equivariant_map_is_injective MulAction.EquivariantMap.embeddingOfEquivariantMap_is_injective

theorem EquivariantMap.embeddingOfEquivariantMap_is_bijective {N β : Type _} [Group N]
    [MulAction N β] {σ : M → N} (f : α →ₑ[σ] β) (hf : Function.Bijective f) {ι : Type _} :
    Function.Bijective (EquivariantMap.embeddingOfEquivariantMap hf.injective ι) :=
  by
  constructor
  exact EquivariantMap.embeddingOfEquivariantMap_is_injective hf.injective
  intro y
  obtain ⟨g, _, hfg⟩ := Function.bijective_iff_has_inverse.mp hf
  use ⟨g ∘ y, Function.Injective.comp hfg.injective (EmbeddingLike.injective y)⟩
  ext i
  rw [EquivariantMap.embeddingOfEquivariantMap_apply]
  simp only [coeFn_mk, Function.comp_apply]
  rw [hfg]
#align mul_action.equivariant_map.embedding_of_equivariant_map_is_bijective MulAction.EquivariantMap.embeddingOfEquivariantMap_is_bijective

example (α β : Type) (f g : α ↪ β) : 
    f = g ↔ ∀ a, f a = g a := by
  exact FunLike.ext_iff

/-- Multiple transitivity of an image by an equivariant map of a multiply transitive action -/
theorem isMultiplyPretransitive_of_surjective_map 
    {N β : Type _} [Group N] [MulAction N β] {n : ℕ}
    {σ : M → N} {f : α →ₑ[σ] β} (hf : Function.Surjective f) 
    (h : IsMultiplyPretransitive M α n) :
    IsMultiplyPretransitive N β n :=
  by
  let h_eq := h.exists_smul_eq
  apply IsPretransitive.mk
  let aux : (Fin n ↪ β) → (Fin n ↪ α) := fun x =>
    { toFun := (Function.surjInv hf) ∘ x.toFun
      inj' := fun u v huv => by
        let huv' :=congr_arg f huv
        simp only [Function.comp_apply, Function.surjInv_eq] at huv'
        exact x.inj' huv' }
  have aux_apply : ∀ (x : Fin n ↪ β) (i : Fin n), f.toFun (aux x i) = x i := fun x i => by
    simp only [toFun_eq_coe, coeFn_mk, Function.comp_apply, Function.surjInv_eq]
  intro x y
  obtain ⟨g, hg⟩ := h_eq (aux x) (aux y)
  use σ g
  ext i
  simp only [smul_apply]
  simp only [← aux_apply]
  dsimp
  rw [ FunLike.ext_iff] at hg
  specialize hg i
  dsimp at hg
  rw [← hg]
  rw [EquivariantMap.map_smul]
#align mul_action.is_multiply_pretransitive_of_surjective_map MulAction.isMultiplyPretransitive_of_surjective_map

theorem isMultiplyPretransitive_of_bijective_map_iff 
    {N β : Type _} [Group N] [MulAction N β]
    {n : ℕ} {σ : M → N} {f : α →ₑ[σ] β} (hσ : Function.Surjective σ) 
    (hf : Function.Bijective f) :
    IsMultiplyPretransitive M α n ↔ IsMultiplyPretransitive N β n :=
  by
  constructor
  · apply isMultiplyPretransitive_of_surjective_map hf.surjective
  intro hN; let hN_heq := hN.exists_smul_eq
  apply IsPretransitive.mk
  intro x y
  let x' : Fin n ↪ β := ⟨f ∘ x, hf.injective.comp x.inj'⟩
  let y' : Fin n ↪ β := ⟨f ∘ y, hf.injective.comp y.inj'⟩
  obtain ⟨g', hg'⟩ := hN_heq x' y'
  obtain ⟨g, hg⟩ := hσ g'
  use g
  ext i
  apply hf.injective
  simp only [smul_apply] -- ; simp only [← EquivariantMap.toFun_eq_coe]
  rw [f.map_smul']
  rw [hg]
  suffices : f.toFun (x i) = x' i; rw [this]
  suffices : f.toFun (y i) = y' i; rw [this]
  simp only [← hg, coeFn_mk, Function.comp_apply, ← hg', smul_apply]
  rfl; rfl
#align mul_action.is_multiply_pretransitive_of_bijective_map_iff MulAction.isMultiplyPretransitive_of_bijective_map_iff

/-
lemma subgroup_is_multiply_pretransitive_via_bijective_bihom_iff {N β : Type*} [group N] [mul_action N β] {n : ℕ}
  {j : mul_action_bihom M α N β} (hj : function.bijective j.to_fun)
  (hj' : function.surjective j.to_monoid_hom.to_fun)
  {M' : subgroup M}:
  is_multiply_pretransitive M' α n ↔ is_multiply_pretransitive (subgroup.map j.to_monoid_hom M') β n :=
begin
  let N' := subgroup.map j.to_monoid_hom M',
  let k : mul_action_bihom M' α (subgroup.map j.to_monoid_hom M') β := {
  to_fun := j.to_fun,
  to_monoid_hom := (j.to_monoid_hom.restrict M').cod_restrict N' (λ ⟨x, hx⟩,
  begin
    rw monoid_hom.restrict_apply,
    exact subgroup.apply_coe_mem_map j.to_monoid_hom M' ⟨x, hx⟩
  end),
  map_smul' := λ ⟨m, hm⟩ x,
  begin
    simp only [monoid_hom.restrict_apply, subgroup.coe_mk, monoid_hom.cod_restrict_apply],
    change (j.to_monoid_hom m) • (j.to_fun x) = _,
    simp only [j.map_smul'],
    refl
  end },
  have hk : function.bijective k.to_fun := hj,
  have hk' : function.surjective k.to_monoid_hom.to_fun,
  { rintro ⟨n, m, hm, hmn⟩,
    use ⟨m, hm⟩,
    -- rw ← set_like.coe_eq_coe,
    simp only [monoid_hom.restrict_apply, subgroup.coe_mk, monoid_hom.to_fun_eq_coe,
      monoid_hom.cod_restrict_apply, subtype.mk_eq_mk],
    exact hmn },
  apply is_multiply_pretransitive_via_bijective_bihom_iff hk hk',
end -/
/-
lemma subgroup'_is_multiply_pretransitive_via_bijective_bihom_iff {N β : Type*} [group N] [mul_action N β] {n : ℕ}
  {j : mul_action_bihom M α N β} (hj : function.bijective j.to_fun)
  (hj' : function.surjective j.to_monoid_hom.to_fun)
  {N' : subgroup N}:
  is_multiply_pretransitive (subgroup.comap j.to_monoid_hom N') α n ↔ is_multiply_pretransitive N' β n :=
begin
  let M' := subgroup.comap j.to_monoid_hom N',
  suffices : N' = subgroup.map j.to_monoid_hom (subgroup.comap j.to_monoid_hom N'),
  conv_rhs { rw this },
  exact subgroup_is_multiply_pretransitive_via_bijective_bihom_iff hj hj',
  rw subgroup.map_comap_eq_self_of_surjective hj'
end

lemma is_pretransitive_iff_image :
  is_pretransitive M α
  ↔ is_pretransitive
    (monoid_hom.range (mul_action.to_perm_hom M α)) α :=
is_pretransitive_via_bijective_bihom
  (canonical_bihom_bijective M α) (canonical_bihom_monoid_hom_surjective M α)


begin
   let j : mul_action_bihom M α (monoid_hom.range (mul_action.to_perm_hom M α)) α := {
  to_fun := λ x, x,
  to_monoid_hom := {
    to_fun := λ m, ⟨mul_action.to_perm m,
    (by simp only [monoid_hom.mem_range, to_perm_hom_apply, exists_apply_eq_apply])⟩,
    map_one' := begin
      ext, simp only [subgroup.coe_mk, to_perm_apply,
        one_smul, subgroup.coe_one, equiv.perm.coe_one, id.def],
    end,
    map_mul' := λ m n, begin
      ext, simp, rw mul_smul, end },
  map_smul' := λ m x,  begin simp, refl end },

  have hj : function.bijective j.to_fun := function.bijective_id,
  suffices hj' : function.surjective (canonical_bihom).to_monoid_hom.to_fun,
  --  rintro ⟨f, m, rfl⟩, use m, refl,
-/
/-
lemma is_multiply_pretransitive_iff_image {n : ℕ} :
  is_multiply_pretransitive M α n
  ↔ is_multiply_pretransitive
    (monoid_hom.range (mul_action.to_perm_hom M α)) α n :=
begin
  unfold is_multiply_pretransitive is_multiply_pretransitive,

  apply is_pretransitive_via_bijective_bihom
  (embedding_bihom_of_bihom_of_bijective_bijective
    (canonical_bihom M α)
    (canonical_bihom_bijective M α)
    (fin n)) ,
  rw embedding_bihom_of_bihom_of_injective.to_monoid_hom.def,
  apply canonical_bihom_monoid_hom_surjective,
end
 -/
variable (M α)

/-- Any action is 0-pretransitive -/
theorem is_zero_pretransitive : IsMultiplyPretransitive M α 0 :=
  by
  apply IsPretransitive.mk
  intro x y; use 1; rw [one_smul]
  ext i; exfalso
  exact IsEmpty.false i
#align mul_action.is_zero_pretransitive MulAction.is_zero_pretransitive

/-- An action is 1-pretransitive iff it is pretransitive -/
theorem isPretransitive_iff_is_one_pretransitive :
    IsPretransitive M α ↔ IsMultiplyPretransitive M α 1 :=
  by
  unfold IsMultiplyPretransitive
  rw [isPretransitive.of_bijective_map_iff Function.surjective_id (finOneToMap_bijective M α)]
#align mul_action.is_pretransitive_iff_is_one_pretransitive MulAction.isPretransitive_iff_is_one_pretransitive

/-- An action is 2-pretransitive iff it is two_pretransitive… -/
theorem is_two_pretransitive_iff :
    IsMultiplyPretransitive M α 2 ↔
      ∀ (a b c d : α) (_ : a ≠ b) (_ : c ≠ d), ∃ m : M, m • a = c ∧ m • b = d :=
  by
  have : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
    rintro ⟨i, hi⟩
    by_cases hi' : i = 0
    apply Or.intro_left
    apply Fin.eq_of_veq
    simp only [Fin.val_zero, hi']
    apply Or.intro_right
    apply Fin.eq_of_veq
    simp only [Fin.val_one]
    apply Nat.eq_of_lt_succ_of_not_lt
    exact hi; simp only [lt_one_iff]; exact hi'
  let f : ∀ (a b : α) (_ : a ≠ b), Fin 2 ↪ α := fun a b hab =>
    ⟨fun i => ite (i = 0) a b, by
      intro i j hij
      by_cases hi : i = 0
      by_cases hj : j = 0
      rw [hi, hj]
      simp only [if_pos hi, if_neg hj] at hij ; exfalso; exact hab hij
      by_cases hj : j = 0
      simp only [if_neg hi, if_pos hj] at hij ; exfalso; exact hab hij.symm
      rw [Or.resolve_left (this i) hi, Or.resolve_left (this j) hj]⟩
  constructor
  · intro h
    let h' := h.exists_smul_eq
    intro a b c d hab hcd
    obtain ⟨m, hm⟩ := h' (f a b hab) (f c d hcd)
    rw [← Function.Embedding.ext_iff] at hm 
    use m
    constructor
    simpa only [smul_apply, coeFn_mk, eq_self_iff_true, if_true] using hm 0
    simpa only [smul_apply, coeFn_mk, eq_self_iff_true, if_true] using hm 1
  · intro h
    apply IsPretransitive.mk
    intro u v
    specialize h (u 0) (u 1) (v 0) (v 1)
    obtain ⟨m, hm⟩ := h 
      (by rw [Ne.def, Function.Embedding.apply_eq_iff_eq]; exact zero_ne_one) 
      (by rw [Ne.def, Function.Embedding.apply_eq_iff_eq]; exact zero_ne_one)
    use m
    ext x
    cases' this x with hx hx
    simpa only [hx] using hm.left
    simpa only [hx] using hm.right
#align mul_action.is_two_pretransitive_iff MulAction.is_two_pretransitive_iff

/-- An n-pretransitive action is m-pretransitive for any m ≤ n -/
theorem isMultiplyPretransitive_of_higher {n : ℕ} (hn : IsMultiplyPretransitive M α n) {m : ℕ}
    (hmn : m ≤ n) (hα : ↑n ≤ PartENat.card α) : IsMultiplyPretransitive M α m :=
  by
  unfold IsMultiplyPretransitive
  let hn_eq := hn.exists_smul_eq
  apply IsPretransitive.mk
  intro x y
  obtain ⟨x', hx'⟩ := may_extend hmn hα x
  obtain ⟨y', hy'⟩ := may_extend hmn hα y
  obtain ⟨g, hg⟩ := hn_eq x' y'
  use g
  ext; rw [← hy', ← hx', ← hg]; rfl
#align mul_action.is_multiply_pretransitive_of_higher MulAction.isMultiplyPretransitive_of_higher

variable {α}
lemma exists_extends_with_last_eq (a : α) {n : ℕ} (x : Fin n ↪ SubMulAction.ofStabilizer M a) : 
    let j : SubMulAction.ofStabilizer M a ↪ α :=
      { toFun := fun u => id u
        inj' := fun x y hxy => by simpa using hxy }
    ∃ x' : Fin n.succ ↪ α,
      (Fin.castLEEmb (Nat.le_succ n)).toEmbedding.trans x' = x.trans j ∧
        x' ⟨n, Nat.lt_succ_self n⟩ = a := by
  intro _
  refine' may_extend_with (x.trans (subtype _)) a _
  rintro ⟨u, hu⟩
  simp only [toFun_eq_coe, trans_apply, Function.Embedding.coe_subtype] at hu 
  apply SubMulAction.neq_of_mem_ofStabilizer M a
  exact hu

lemma exists_smul_of_last_eq [hα' : IsPretransitive M α] {n : ℕ} (a : α) (x : Fin n.succ ↪ α) :
    ∃ (g : M) (x1 : Fin n ↪ ↥(SubMulAction.ofStabilizer M a)),
      (Fin.castLEEmb (Nat.le_succ n)).toEmbedding.trans (g • x) =
          Function.Embedding.trans x1 (subtype _) ∧ g • x (Fin.last n) = a := by
  let hα'eq := hα'.exists_smul_eq
  obtain ⟨g, hgx⟩ := hα'eq (x (Fin.last n)) a
  use g
  have zgx : ∀ (i : Fin n), g • x (Fin.castSucc i) ∈ SubMulAction.ofStabilizer M a := by
    rintro ⟨i, hi⟩
    rw [SubMulAction.mem_ofStabilizer_iff]
    rw [← hgx]
    simp only [Fin.castSucc_mk, ne_eq, smul_left_cancel_iff, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq]
    exact Fin.ne_of_lt hi
  use {
    toFun := fun i => ⟨g • x i, (by 
      simp
      exact zgx i)⟩
    inj' := fun i j ↦ by
      simp only [Fin.coe_eq_castSucc, Subtype.mk.injEq, smul_left_cancel_iff, 
        EmbeddingLike.apply_eq_iff_eq, Fin.castSucc_inj, imp_self] }
  constructor
  · ext i 
    simp
    rfl
  · exact hgx

variable (α)
/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)-/
theorem stabilizer.isMultiplyPretransitive' (hα' : IsPretransitive M α) {n : ℕ} :
    IsMultiplyPretransitive M α n.succ ↔
      ∀ a : α, IsMultiplyPretransitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n := by
  -- let hα'eq := hα'.exists_smul_eq
  constructor
  · -- if the action is n.succ-multiply transitive,
    -- then the action of sub_mul_action_of_stabilizer is n-multiply transitive
    intro hn a; let hn_eq := hn.exists_smul_eq
    apply IsPretransitive.mk
    /- let j := (SubMulAction.ofStabilizer M a).inclusion
    -- let j : SubMulAction.ofStabilizer M a ↪ α :=
    --   { toFun := fun u => id u
    --     inj' := fun x y hxy => by simpa using hxy }
    have :
      ∀ x : Fin n ↪ SubMulAction.ofStabilizer M a,
        ∃ x' : Fin n.succ ↪ α,
          (Fin.castLEEmb (Nat.le_succ n)).toEmbedding.trans x' = x.trans j ∧
            x' ⟨n, Nat.lt_succ_self n⟩ = a := by
      intro x
      refine' may_extend_with (x.trans (subtype _)) a _
      rintro ⟨u, hu⟩
      simp only [toFun_eq_coe, trans_apply, Function.Embedding.coe_subtype] at hu 
      apply SubMulAction.ofStabilizer_neq M a
      exact hu -/
    intro x y
    obtain ⟨x', hx', hx'a⟩ := exists_extends_with_last_eq M a x
    obtain ⟨y', hy', hy'a⟩ := exists_extends_with_last_eq M a y
    obtain ⟨g, hg'⟩ := hn_eq x' y'
    have hg : g ∈ stabilizer M a := by
      rw [mem_stabilizer_iff]
      conv_lhs => rw [← hx'a]
      rw [← hy'a, ← hg', smul_apply]
    use ⟨g, hg⟩
    ext ⟨i, hi⟩
    simp only [smul_apply, SubMulAction.val_smul_of_tower]
    rw [← Function.Embedding.ext_iff] at hx' hy' 
    specialize hx' ⟨i, hi⟩; specialize hy' ⟨i, hi⟩
    simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, id.def, coeFn_mk] 
      at hx' hy' 
    rw [← hx', ← hy', ← hg']; rfl
  · -- if the action of sub_mul_action.of_stabilizer is n-multiply transitive,
    -- then the action is n.succ-multiply transitive.
    intro hn
    /- have aux_fun : ∀ (a : α) (x : Fin n.succ ↪ α),
        ∃ (g : M) (x1 : Fin n ↪ ↥(SubMulAction.ofStabilizer M a)),
          (Fin.castLEEmb (Nat.le_succ n)).toEmbedding.trans (g • x) =
              Function.Embedding.trans x1 (subtype _) ∧
                g • x ⟨n, Nat.lt_succ_self n⟩ = a := by
      intro a x
      obtain ⟨g, hgx⟩ := hα'eq (x ⟨n, Nat.lt_succ_self n⟩) a
      use g
      have zgx : ∀ (i : Fin n), g • x (Fin.castSucc i) ∈ SubMulAction.ofStabilizer M a := by
        rintro ⟨i, hi⟩
        rw [mem_SubMulAction.ofStabilizer_iff]
        rw [← hgx]
        simp only [Fin.castSucc_mk, ne_eq, smul_left_cancel_iff, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq]
        exact Nat.ne_of_lt hi 
      use {
        toFun := fun i => ⟨g • x i, (by 
          simp
          exact zgx i)⟩
        inj' := fun i j ↦ by
          simp only [Fin.coe_eq_castSucc, Subtype.mk.injEq, smul_left_cancel_iff, 
            EmbeddingLike.apply_eq_iff_eq, Fin.castSucc_inj, imp_self] }
      constructor
      · ext i 
        simp
        rfl
      · exact hgx -/
    apply IsPretransitive.mk
    intro x
    -- gx • x = x1 :: a
    let a := x ⟨n, lt_add_one n⟩
    obtain ⟨gx, x1, hgx, hga⟩ := exists_smul_of_last_eq M a x
    intro y
    -- gy • y = y1 :: a
    obtain ⟨gy, y1, hgy, hgb⟩ := exists_smul_of_last_eq M a y
    -- g • x1 = y1,
    let hna_eq := (hn a).exists_smul_eq
    obtain ⟨g, hg⟩ := hna_eq x1 y1
    use gy⁻¹ * g * gx
    ext ⟨i, hi⟩
    rw [mul_smul]; simp only [smul_apply]
    cases' lt_or_eq_of_le (le_of_lt_succ hi) with hi' hi'
    · rw [← Function.Embedding.ext_iff] at hgx hgy hg 
      specialize hgx ⟨i, hi'⟩; specialize hgy ⟨i, hi'⟩; specialize hg ⟨i, hi'⟩
      simp only [Fin.castLEEmb_toEmbedding, trans_apply, coeFn_mk, Fin.castLE_mk, 
        smul_apply, zero_eq, coe_subtype] at hgx hgy hg 
      rw [hgx, mul_smul, inv_smul_eq_iff, hgy, ← hg]; rfl
    · simp only [hi']
      dsimp [Fin.last] at  hga hgb
      rw [hga, mul_smul, inv_smul_eq_iff, hgb]
      rw [← mem_stabilizer_iff]; exact SetLike.coe_mem g
#align mul_action.stabilizer.is_multiply_pretransitive' MulAction.stabilizer.isMultiplyPretransitive'

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)-/
theorem stabilizer.isMultiplyPretransitive (hα' : IsPretransitive M α) {n : ℕ}
    {a : α} :-- (hα0 : ↑n ≤ #α) /- (hα : card_ge α n.succ) -/  :
    IsMultiplyPretransitive M α n.succ ↔
      IsMultiplyPretransitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n :=
  by
  -- let hα'eq := hα'.exists_smul_eq
  constructor
  · -- if the action is n.succ-multiply transitive,
    -- then the action of sub_mul_action_of_stabilizer is n-multiply transitive
    intro hn; let hn_eq := hn.exists_smul_eq
    apply IsPretransitive.mk
    /- let j : SubMulAction.ofStabilizer M a ↪ α :=
      { toFun := fun u => id u
        inj' := fun x y hxy => by simpa using hxy }
    have :
      ∀ x : Fin n ↪ SubMulAction.ofStabilizer M a,
        ∃ x' : Fin n.succ ↪ α,
          (Fin.castLEEmb (Nat.le_succ n)).toEmbedding.trans x' = x.trans j ∧
            x' ⟨n, Nat.lt_succ_self n⟩ = a :=
      by
      intro x
      refine' may_extend_with (x.trans (subtype _)) a _
      rintro ⟨u, hu⟩
      simp only [toFun_eq_coe, trans_apply, Function.Embedding.coe_subtype] at hu 
      apply (SubMulAction.ofStabilizer_neq M a) 
      exact hu -/
    intro x y
    obtain ⟨x', hx', hx'a⟩ := exists_extends_with_last_eq M a x
    obtain ⟨y', hy', hy'a⟩ := exists_extends_with_last_eq M a y
    obtain ⟨g, hg'⟩ := hn_eq x' y'
    have hg : g ∈ stabilizer M a := by
      rw [mem_stabilizer_iff]
      conv_lhs => rw [← hx'a]
      rw [← hy'a, ← hg', smul_apply]
    use ⟨g, hg⟩
    ext ⟨i, hi⟩
    simp only [smul_apply, SubMulAction.val_smul_of_tower]
    rw [← Function.Embedding.ext_iff] at hx' hy' 
    specialize hx' ⟨i, hi⟩; specialize hy' ⟨i, hi⟩
    simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, id.def, coeFn_mk] at hx' hy' 
    rw [← hx', ← hy', ← hg']; rfl
  · -- if the action of sub_mul_action.of_stabilizer is n-multiply transitive,
    -- then the action is n.succ-multiply transitive.
    intro hn
    apply IsPretransitive.mk
    intro x
    -- obtain gx : gx • x = x1 :: a
    obtain ⟨gx, x1, hgx, hga⟩ := exists_smul_of_last_eq M a x
    intro y
    -- obtain gy : gy • y = y1 :: a
    obtain ⟨gy, y1, hgy, hgb⟩ := exists_smul_of_last_eq M a y
    -- g • x1 = y1,
    let hna_eq := hn.exists_smul_eq
    obtain ⟨g, hg⟩ := hna_eq x1 y1
    use gy⁻¹ * g * gx
    ext ⟨i, hi⟩
    rw [mul_smul]; simp only [smul_apply]
    cases' lt_or_eq_of_le (le_of_lt_succ hi) with hi' hi'
    · rw [← Function.Embedding.ext_iff] at hgx hgy hg 
      specialize hgx ⟨i, hi'⟩; specialize hgy ⟨i, hi'⟩; specialize hg ⟨i, hi'⟩
      simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, smul_apply,
        Function.Embedding.coe_subtype] at hgx hgy hg 
      dsimp only [Fin.castLEEmb_apply, Fin.castLE_mk] at hgx hgy
      rw [hgx, mul_smul, inv_smul_eq_iff, hgy, ← hg]; rfl
    · simp only [hi']
      dsimp only [Fin.last] at hga hgb
      rw [hga, mul_smul, inv_smul_eq_iff, hgb]
      rw [← mem_stabilizer_iff]; exact SetLike.coe_mem g
#align mul_action.stabilizer.is_multiply_pretransitive MulAction.stabilizer.isMultiplyPretransitive

/-- The fixator of a subset of cardinal d in a k-transitive action
acts (k-d) transitively on the remaining -/
theorem remaining_transitivity 
    {m n : ℕ} (s : Set α) [Finite s]
    (h : IsMultiplyPretransitive M α n) 
    (hmn : n = m + s.ncard) :
    IsMultiplyPretransitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) m := by

  have hs : PartENat.card s = s.ncard := by
    rw [s.ncard_eq_toFinset_card, PartENat.card_eq_coe_nat_card, Set.Nat.card_coe_set_eq, PartENat.natCast_inj, s.ncard_eq_toFinset_card]

  -- have hdn : s.ncard ≤ n := by
  --   rw [hmn]
  --   simp only [le_add_iff_nonneg_left, _root_.zero_le]

  -- cases' le_total s.ncard n with hdn hnd
  -- case where s.ncard ≤ n
  apply IsPretransitive.mk
  intro x y
  obtain ⟨z⟩ := equiv_fin_of_partENat_card_eq hs
  obtain ⟨x', hx'1, hx'2⟩ := may_extend_with' z.toEmbedding hmn x
  obtain ⟨y' : Fin n ↪ α, hy'1, hy'2⟩ := may_extend_with' z.toEmbedding hmn y
  obtain ⟨g, hg⟩ := h.exists_smul_eq x' y'
  suffices : g ∈ fixingSubgroup M s 
  use ⟨g, this⟩
  · ext i
    simp only [smul_apply, SubMulAction.val_smul_of_tower]
    have : (y i : α) = (y.trans (subtype (sᶜ)) i : α) := by
      simp only [trans_apply, Function.Embedding.coe_subtype]
    rw [this]
    have : (x i : α) = (x.trans (subtype (sᶜ)) i : α) := by
      simp only [trans_apply, Function.Embedding.coe_subtype]
    rw [this]
    rw [← Function.Embedding.ext_iff] at hx'1 hy'1 
    simp_rw [← hy'1 i, ← hx'1 i, ← hg]
    simp only [trans_apply, smul_apply, RelEmbedding.coe_toEmbedding]
    rfl
  · intro a
    let i := z.symm a
    have : z.toEmbedding.trans (subtype (s : Set α)) i = a := by
      simp only [trans_apply, Equiv.toEmbedding_apply, Equiv.apply_symm_apply,
        Function.Embedding.coe_subtype]
    simp only [← this]
    conv_lhs => rw [← hx'2]
    rw [← hy'2, ← hg]
    simp only [trans_apply, smul_apply]
  -- -- case where n ≤ Set.ncard s, vacuously true because m = 0
  -- · simp only [hmn, add_le_iff_nonpos_left, nonpos_iff_eq_zero] at hnd 
  --   rw [hnd]
  --   apply is_zero_pretransitive
#align mul_action.remaining_transitivity MulAction.remaining_transitivity

theorem remaining_transitivity' {m n : ℕ} (s : Set α) [Finite s]
    (h : IsMultiplyPretransitive M α n) 
    (hmn : m + s.ncard ≤ n) (hn : (n : PartENat) ≤ PartENat.card α) :
    IsMultiplyPretransitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) m := by

  -- have hs : PartENat.card s = s.ncard := by
  --   rw [s.ncard_eq_toFinset_card, PartENat.card_eq_coe_nat_card, Set.Nat.card_coe_set_eq, PartENat.natCast_inj, s.ncard_eq_toFinset_card]

  apply remaining_transitivity
  -- exact PartENat.card_eq_coe_fintype_card
  exact isMultiplyPretransitive_of_higher M α h hmn hn
  rfl
#align mul_action.remaining_transitivity' MulAction.remaining_transitivity'

/- -- TODO : can one do an induction on s
private theorem IsMultiplyPretransitive.index_of_fixing_subgroup_aux 
    [Fintype α] [DecidableEq α]
    (k : ℕ) (hmk : IsMultiplyPretransitive M α k) 
    {s : Finset α} (hs : s.card = k) :
    (fixingSubgroup M (s : Set α)).index * (Fintype.card α - s.card).factorial =
      (Fintype.card α).factorial := by
  classical
  revert M α
  induction' k with k hrec
  -- k = 0
  · intro M α _ _ _ _ _ s hs
    rw [Finset.card_eq_zero] at hs 
    simp only [hs, Finset.coe_empty, Finset.card_empty, tsub_zero]
    suffices fixingSubgroup M ∅ = ⊤ by rw [this, Subgroup.index_top, one_mul]
    exact GaloisConnection.l_bot (fixingSubgroup_fixedPoints_gc M α)
  -- induction step
  intro M α _ _ _ _ hmk s hs
  have hGX : IsPretransitive M α := by
    rw [isPretransitive_iff_is_one_pretransitive]
    apply isMultiplyPretransitive_of_higher M α hmk
    · rw [Nat.succ_le_succ_iff]; apply Nat.zero_le
    · rw [← hs]
      simp only [PartENat.card_eq_coe_fintype_card, Fintype.card_coe, PartENat.coe_le_coe]
      exact Finset.card_le_univ s
  suffices : s.Nonempty
  obtain ⟨a, has⟩ := Finset.Nonempty.bex this
  let t' : Set (SubMulAction.ofStabilizer M a) := 
    Subtype.val ⁻¹' ((s.erase a) : Set α)
  have hat' : (Subtype.val '' t' : Set α) = s.erase a := by
    ext x
    simp only [Finset.coe_erase, Finset.mem_coe, Set.preimage_diff, Set.mem_image, Set.mem_diff, Set.mem_preimage,
      Set.mem_singleton_iff, Subtype.exists, exists_and_left, exists_prop]
    constructor
    · rintro ⟨b, ⟨hb, hb'⟩, ⟨_, rfl⟩⟩
      exact ⟨hb, hb'⟩
    · rintro ⟨hxs, hxa⟩
      use x
      exact ⟨⟨hxs, hxa⟩, ⟨hxa, rfl⟩⟩
  rw [← Finset.insert_erase has]
  rw [Finset.card_insert_of_not_mem (Finset.not_mem_erase a s)]
  rw [Finset.coe_insert]
  rw [Nat.add_comm, ← Nat.sub_sub]
  -- change (fixing_subgroup M ↑(insert a t)).index * _ = _,
  rw [← hat']
  -- have : insert a (coe '' t') = set.insert a (coe '' t'),
  -- refl, rw this,
  rw [fixingSubgroup_of_insert]
  --   H.relindex K = (H.subgroup_of K).index = (K : H ⊓ K)
  -- si H ≤ K, H.relindex K * K.index = H.index
  -- (K : H) (G : K) = (G : H)
  -- (G : Gat) = (G : Ga) (Ga : Gat)
  -- prendre K = Ga, H = Gat
  rw [Subgroup.index_map]
  rw [(MonoidHom.ker_eq_bot_iff (stabilizer M a).subtype).mpr
      (by simp only [Subgroup.coeSubtype, Subtype.coe_injective])]
  simp only [sup_bot_eq, Subgroup.subtype_range]
  suffices (fixingSubgroup (stabilizer M a) t').index *
    (Fintype.card α - 1 - Fintype.card t').factorial =
      (Fintype.card α - 1).factorial by
    suffices ht' : Fintype.card t' = (s.erase a).card
    rw [mul_comm] at this 
    rw [← ht', mul_comm, ← mul_assoc, mul_comm, this]
    suffices hX : 0 < Fintype.card α
    conv_rhs => rw [← Nat.mul_factorial_pred hX]
    apply congr_arg₂ (· * ·) _ rfl
    · -- (stabilizer G a).index = fintype.card α,
      rw [← Nat.card_eq_fintype_card]
      apply stabilizer_index_of_pretransitive M α hGX
    ·-- 0 < fintype.card α,
      rw [Fintype.card_pos_iff];
      use a
    · -- fintype.card α = (s.erase a).card
      rw [← Set.toFinset_card]
      rw [← Finset.card_image_of_injective t'.toFinset Subtype.coe_injective]
      apply congr_arg
      rw [← Finset.coe_inj]
      rw [Finset.coe_image]
      rw [Set.coe_toFinset]
      exact hat'
  · specialize hrec (stabilizer M a) (SubMulAction.ofStabilizer M a)
      ((stabilizer.isMultiplyPretransitive M α hGX).mp hmk) ?_
    /- let hz := hrec (stabilizer M a) (SubMulAction.ofStabilizer M a)
        ((stabilizer.isMultiplyPretransitive M α hGX).mp hmk) ?_ -/
    exact t'.toFinset
--    swap
    · rw [← Finset.card_image_of_injective t'.toFinset Subtype.coe_injective]
      rw [← Set.coe_toFinset t', ← Finset.coe_image, Finset.coe_inj] at hat' 
      rw [hat']
      rw [Finset.card_erase_of_mem has, hs, Nat.sub_one k.succ, Nat.pred_succ]
    suffices : Fintype.card (SubMulAction.ofStabilizer M a) = Fintype.card α - 1
    rw [this, Set.coe_toFinset t', Set.toFinset_card t'] at hrec
    exact hrec
    suffices : ∀ x,  x ∈ (SubMulAction.ofStabilizer M a) ↔  x ∈ (SubMulAction.ofStabilizer M a).carrier
    simp_rw [this, SubMulAction.ofStabilizer_carrier]
    convert Fintype.card_compl_set _
    intro x; rfl
  ·-- s.nonempty
    rw [← Finset.card_pos, hs];
    exact succ_pos k
 -/

lemma _root_.Set.ncard_le_fintype_card [Fintype α] (s : Set α) : 
    s.ncard ≤ Fintype.card α := by
  rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
  apply Set.ncard_le_of_subset
  exact Set.subset_univ s
  exact Set.finite_univ

 /-- For a multiply pretransitive action, 
  computes the index of the fixing_subgroup of a subset of adequate cardinality -/
private theorem IsMultiplyPretransitive.index_of_fixing_subgroup_aux
    [Fintype α] 
    (k : ℕ) (hmk : IsMultiplyPretransitive M α k) 
    {s : Set α} (hs : s.ncard = k) :
    (fixingSubgroup M s).index * (Fintype.card α - s.ncard).factorial =
      (Fintype.card α).factorial := by
  classical
  revert M α
  induction' k with k hrec
  -- k = 0
  · intro M α _ _ _ _ s hs
    simp only [hs, zero_eq, ge_iff_le, nonpos_iff_eq_zero, tsub_zero, ne_eq]
    rw [Set.ncard_eq_zero] at hs 
    simp only [hs]
    suffices fixingSubgroup M ∅ = ⊤ by 
      rw [this, Subgroup.index_top, one_mul]
    exact GaloisConnection.l_bot (fixingSubgroup_fixedPoints_gc M α)
  -- induction step
  intro M α _ _ _ hmk s hs
  have hGX : IsPretransitive M α := by
    rw [isPretransitive_iff_is_one_pretransitive]
    apply isMultiplyPretransitive_of_higher M α hmk
    · rw [Nat.succ_le_succ_iff]; apply Nat.zero_le
    · rw [← hs]
      simp only [PartENat.card_eq_coe_fintype_card, Fintype.card_coe, PartENat.coe_le_coe]
      apply Set.ncard_le_fintype_card
  
  have : s.Nonempty := by 
    rw [← Set.ncard_pos, hs]
    exact succ_pos k
  obtain ⟨a, has⟩ := this 
  let t : Set (SubMulAction.ofStabilizer M a) := Subtype.val ⁻¹' s
  have hat : Subtype.val '' t = s \ {a} := by 
    rw [Set.image_preimage_eq_inter_range]
    simp only [Subtype.range_coe_subtype]
    rw [Set.diff_eq_compl_inter, Set.inter_comm]
    congr
  have hat' : s = Set.insert a (Subtype.val '' t) := by
    rw [hat]
    change s = {a} ∪ (s \ {a})
    simp only [Set.union_diff_self]
    apply symm
    rw [Set.union_eq_right_iff_subset, Set.singleton_subset_iff]
    exact has
  have hfs : fixingSubgroup M s = ?_ := by
    rw [hat']
    exact fixingSubgroup_of_insert M a t
  rw [hfs]
  rw [Subgroup.index_map]
  rw [(MonoidHom.ker_eq_bot_iff (stabilizer M a).subtype).mpr
      (by simp only [Subgroup.coeSubtype, Subtype.coe_injective])]
  simp only [sup_bot_eq, Subgroup.subtype_range]
  have hscard : s.ncard = 1 + t.ncard := by
    rw [hat']
    suffices : ¬ a ∈ (Subtype.val '' t)
    · rw [add_comm]
      convert Set.ncard_insert_of_not_mem this ?_
      rw [Set.ncard_image_of_injective _ Subtype.coe_injective]
      apply Set.toFinite
    · intro h
      obtain ⟨⟨b, hb⟩, _, hb'⟩ := h
      apply hb
      simp only [Set.mem_singleton_iff]
      rw [← hb']
  have htcard : t.ncard = k := by
    rw [← Nat.succ_inj', ← hs, hscard, add_comm]

  suffices (fixingSubgroup (stabilizer M a) t).index *
    (Fintype.card α - 1 - t.ncard).factorial =
      (Fintype.card α - 1).factorial by
    · rw [mul_comm] at this 
      rw [hscard, mul_comm, ← mul_assoc, mul_comm, Nat.sub_add_eq, this]
      rw [stabilizer_index_of_pretransitive M hGX a]
      rw [Nat.card_eq_fintype_card]
      apply Nat.mul_factorial_pred
      rw [Fintype.card_pos_iff]
      use a 
  · rw [add_comm] at hscard
    have := Nat.sub_eq_of_eq_add hscard
    simp only [hs, Nat.pred_succ] at this
    convert hrec (stabilizer M a) (SubMulAction.ofStabilizer M a)
      ((stabilizer.isMultiplyPretransitive M α hGX).mp hmk) htcard
    all_goals {
      apply symm
      convert Fintype.card_compl_set _
      exact setFintype {a}ᶜ }


 /-- For a multiply pretransitive action, 
  computes the index of the fixing_subgroup of a subset of adequate cardinality -/
theorem IsMultiplyPretransitive.index_of_fixingSubgroup
    [Fintype α] (s : Set α)
    (hMk : IsMultiplyPretransitive M α s.ncard) :
    (fixingSubgroup M s).index * (Fintype.card α - s.ncard).factorial =
      (Fintype.card α).factorial := 
  hMk.index_of_fixing_subgroup_aux M α s.ncard rfl
#align mul_action.index_of_fixing_subgroup_of_multiply_pretransitive MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup

 /-- For a multiply pretransitive action, 
  computes the index of the fixing_subgroup of a subset of adequate cardinality -/
theorem IsMultiplyPretransitive.index_of_fixingSubgroup'
    [Fintype α] (s : Set α)
    (hMk : IsMultiplyPretransitive M α s.ncard) :
    (fixingSubgroup M s).index =
      Nat.choose (Fintype.card α) s.ncard * s.ncard.factorial := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _)
  rw [IsMultiplyPretransitive.index_of_fixingSubgroup M α s hMk]
  rw [Nat.choose_mul_factorial_mul_factorial]
  apply Set.ncard_le_fintype_card

lemma _root_.PartENat.lt_coe_succ_iff_le' {x : PartENat} {n : ℕ} : 
    x < n.succ ↔ x ≤ n := by
  by_cases hx : x = ⊤
  · rw [hx]
    simp only [cast_succ, not_top_lt, top_le_iff, PartENat.natCast_ne_top]
  · rw [Nat.succ_eq_add_one n, Nat.cast_add, Nat.cast_one, PartENat.lt_add_one_iff_lt hx]

/-- A 2-transitive action is primitive -/
theorem IsMultiplyPretransitive.isPreprimitive_of_two
    (h2 : IsMultiplyPretransitive M α 2) : IsPreprimitive M α := by
  by_cases hα : Subsingleton α
  -- when α is a subsingleton, two-transitivity is vacuous, 
  -- but preprimitivity holds trivially
  · apply IsPreprimitive.on_subsingleton
  -- The (important) case where α has at least 2 elements
  have hα' : 2 ≤ PartENat.card α := by
    rw [← PartENat.card_le_one_iff_subsingleton, not_le] at hα
    exact PartENat.coe_succ_le_iff.mpr hα
  have : IsPretransitive M α := by
    rw [isPretransitive_iff_is_one_pretransitive]
    apply isMultiplyPretransitive_of_higher M α h2
    norm_num
    exact hα'
  apply IsPreprimitive.mk
  intro B hB
  cases' B.subsingleton_or_nontrivial with h h
  · left
    exact h
  · right
    obtain ⟨a, ha, b, hb, h⟩ := h
    rw [eq_top_iff]
    intro c _
    by_cases h' : a = c
    · rw [← h']; exact ha
    · rw [IsBlock.mk_subset] at hB
      rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, hga, hgb⟩ := h2 a b a c h h'
      apply hB ha 
      · rw [← hga]
        exact Set.smul_mem_smul_set ha
      · rw [← hgb]
        exact Set.smul_mem_smul_set hb
#align mul_action.is_preprimitive_of_two_pretransitive MulAction.IsMultiplyPretransitive.isPreprimitive_of_two

section Finite

/-- The permutation group on α is pretransitive -/
theorem _root_.Equiv.Perm.isPretransitive [DecidableEq α] : 
  MulAction.IsPretransitive (Equiv.Perm α) α := by
  apply IsPretransitive.mk
  intro x y
  use Equiv.swap x y
  simp only [Equiv.Perm.smul_def]
  rw [Equiv.swap_apply_left x y]
#align mul_action.equiv.perm.is_pretransitive Equiv.Perm.isPretransitive

variable [Fintype α]

/-- The permutation group on α is multiply pretransitive -/
theorem _root_.Equiv.Perm.isMultiplyPretransitive (n : ℕ) :
    MulAction.IsMultiplyPretransitive (Equiv.Perm α) α n := by
  cases' le_or_gt n (Fintype.card α) with hn hn
  · apply isMultiplyPretransitive_of_higher (Equiv.Perm α) α _ hn
    apply le_of_eq
    rw [PartENat.card_eq_coe_fintype_card]
    apply IsPretransitive.mk
    intro x y
    let x' := Equiv.ofBijective x.toFun ?_
    let y' := Equiv.ofBijective y.toFun ?_
    use x'.symm.trans y'
    ext i
    simp only [Function.Embedding.smul_apply, Equiv.Perm.smul_def, Equiv.coe_trans,
      Function.comp_apply, Equiv.ofBijective_apply, Function.Embedding.toFun_eq_coe,
      EmbeddingLike.apply_eq_iff_eq]
    exact x'.left_inv i
    all_goals rw [Fintype.bijective_iff_injective_and_card]; constructor
    any_goals try exact Fintype.card_fin (Fintype.card α)
    exact EmbeddingLike.injective y
    exact EmbeddingLike.injective x
  -- hn : n > Fintype.card α
  suffices IsEmpty (Fin n ↪ α) by
    apply IsPretransitive.mk
    intro x
    exfalso
    exact this.false  x
  apply Function.Embedding.isEmpty_of_card_lt
  simp only [Fintype.card_fin]
  exact hn
#align mul_action.equiv_perm_is_multiply_pretransitive Equiv.Perm.isMultiplyPretransitive

/-- The action of the permutation group of α on α is preprimitive -/
theorem _root_.Equiv.Perm.isPreprimitive : IsPreprimitive (Equiv.Perm α) α := by
  cases subsingleton_or_nontrivial α
  · exact IsPreprimitive.on_subsingleton
  apply IsMultiplyPretransitive.isPreprimitive_of_two
  apply Equiv.Perm.isMultiplyPretransitive
#align mul_action.equiv.perm.is_preprimitive Equiv.Perm.isPreprimitive

variable {α}

theorem aux_lt_iff_lt_or_eq {m n : ℕ} (hmn : m < n) : m < n - 1 ∨ m = n - 1 :=
  by
  rw [Nat.lt_iff_le_not_le]
  cases' dec_em (m = n - 1) with h h'
  · exact Or.intro_right _ h
  · apply Or.intro_left; apply And.intro
    · exact Nat.le_pred_of_lt hmn
    · intro h; apply h'
      exact Nat.le_antisymm (Nat.le_pred_of_lt hmn) h
#align mul_action.aux_lt_iff_lt_or_eq MulAction.aux_lt_iff_lt_or_eq

/-- A subgroup of equiv.perm α is ⊤ iff it is (fintype.card α - 1)-pretransitive -/
theorem IsMultiplyPretransitive.eq_top_of_is_full_minus_one_pretransitive 
    {G : Subgroup (Equiv.Perm α)}
    (hmt : IsMultiplyPretransitive (↥G) α (Fintype.card α - 1)) : 
    G = ⊤ := by
  let j : Fin (Fintype.card α - 1) ↪ Fin (Fintype.card α) :=
    (Fin.castLEEmb ((Fintype.card α).sub_le 1)).toEmbedding
  rw [eq_top_iff]; intro k _
  let x : Fin (Fintype.card α) ↪ α := (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  let hmt_eq := hmt.exists_smul_eq
  let x' := j.trans x
  obtain ⟨g, hg'⟩ := hmt_eq x' (k • x')
  suffices k = g by rw [this]; exact SetLike.coe_mem g
  have hx : ∀ x : Fin (Fintype.card α) ↪ α, Function.Surjective x.toFun := by
    intro x
    apply Function.Bijective.surjective
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨EmbeddingLike.injective x, Fintype.card_fin (Fintype.card α)⟩
  have hgk' : ∀ (i : Fin (Fintype.card α)) (_ : i.val < Fintype.card α - 1), 
    (g • x) i = (k • x) i := by
    intro i hi
    exact Function.Embedding.ext_iff.mpr hg' ⟨i.val, hi⟩
  have hgk : ∀ i : Fin (Fintype.card α), (g • x) i = (k • x) i := by
    intro i
    cases' aux_lt_iff_lt_or_eq i.prop with hi hi
    · exact hgk' i hi
    · obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i)
      cases' aux_lt_iff_lt_or_eq j.prop with hj hj
      · exfalso
        suffices i = j by rw [← this, ← hi] at hj ; refine' lt_irrefl _ hj
        apply EmbeddingLike.injective (g • x)
        rw [hgk' j hj]; rw [hxj]
      · rw [← hxj]
        apply congr_arg
        rw [Fin.eq_iff_veq, hi, hj]
  apply Equiv.Perm.ext; intro a
  obtain ⟨i, rfl⟩ := (hx x) a
  let zi := hgk i
  simp only [Function.Embedding.smul_apply, Equiv.Perm.smul_def] at zi 
  simp only [Function.Embedding.toFun_eq_coe]
  rw [← zi]
  rfl
#align mul_action.eq_top_of_is_full_minus_one_pretransitive MulAction.IsMultiplyPretransitive.eq_top_of_is_full_minus_one_pretransitive

variable (α)

-- Cette instance n'était pas nécessaire,
-- mais sans elle, Lean utilise des classical dont il ne se dépêtre plus après !
-- (cf alternating_iwasawa)

/-- The alternating group on α is (fintype.card α - 2)-pretransitive -/
theorem IsMultiplyPretransitive.alternatingGroup_of_sub_two [DecidableEq α] :
    IsMultiplyPretransitive (alternatingGroup α) α (Fintype.card α - 2) := by
  cases' lt_or_ge (Fintype.card α) 2 with h2 h2
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h2)]
    apply is_zero_pretransitive
  -- fintype.card α ≥ 2
  obtain ⟨n, hn⟩ := Nat.le.dest h2
  have hn' : Fintype.card α - 2 = n := tsub_eq_of_eq_add_rev hn.symm
  rw [add_comm] at hn 
  have hn_le : n ≤ Fintype.card α := by rw [← hn]; exact le_self_add
  apply IsPretransitive.mk
  rw [hn']
  intro x y
  obtain ⟨x', hx'⟩ := may_extend hn_le (le_of_eq PartENat.card_eq_coe_fintype_card.symm) x
  obtain ⟨y', hy'⟩ := may_extend hn_le (le_of_eq PartENat.card_eq_coe_fintype_card.symm) y
  let heq := (Equiv.Perm.isMultiplyPretransitive α (Fintype.card α)).exists_smul_eq
  obtain ⟨g, hg⟩ := heq x' y'
  cases' Int.units_eq_one_or (Equiv.Perm.sign g) with h h
  · use ⟨g, Equiv.Perm.mem_alternatingGroup.mpr h⟩
    ext i
    simp only [Function.Embedding.smul_apply]
    rw [← hx', ← hy', ← hg]
    rfl
  · have hg'1 : n + 1 < Fintype.card α := by 
      rw [← hn]; exact Nat.lt.base (n + 1)
    have hg'2 : n < Fintype.card α := by 
        apply lt_trans _ hg'1; exact lt_add_one n
    let g' := Equiv.swap (y'.toFun ⟨n + 1, hg'1⟩) (y'.toFun ⟨n, hg'2⟩)
    have hg' : Equiv.Perm.sign g' = -1 := by
      rw [Equiv.Perm.IsSwap.sign_eq]
      use y'.toFun ⟨n + 1, hg'1⟩; use y'.toFun ⟨n, hg'2⟩
      simp only [toFun_eq_coe, Ne.def, EmbeddingLike.apply_eq_iff_eq, Fin.mk_eq_mk,
        Nat.succ_ne_self, not_false_iff, true_and_iff]
    use ⟨g' * g, ?_⟩
    swap
    · rw [Equiv.Perm.mem_alternatingGroup]
      simp only [Equiv.Perm.sign_mul, h, hg']
      norm_num
    ext i
    suffices (g' * g) • x i = y i by exact this
    simp only [toFun_eq_coe, Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [← hx', ← hy', ← hg]
    simp only [smul_apply, Equiv.Perm.smul_def, Fin.castLEEmb_toEmbedding, trans_apply, coeFn_mk]
    have : ∀ i, g (x' i) = y' i
    · intro i
      rw [← hg]
      rfl
    simp only [this]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      simp only [EmbeddingLike.apply_eq_iff_eq, ← Fin.val_inj, Fin.coe_castLE] at h 
      apply not_lt.mpr (le_succ n)
      convert i.prop
      rw [h]
    · intro h
      simp only [EmbeddingLike.apply_eq_iff_eq, ← Fin.val_inj, Fin.coe_castLE] at h 
      apply lt_irrefl n
      convert i.prop
      rw [h]
#align mul_action.alternating_group_is_fully_minus_two_pretransitive MulAction.IsMultiplyPretransitive.alternatingGroup_of_sub_two

variable {α}

/-- A subgroup of equiv.perm α which is (fintype.card α - 2)-pretransitive
  contains the alternating group  -/
theorem IsMultiplyPretransitive.alternatingGroup_le_of_sub_two [DecidableEq α]
    {G : Subgroup (Equiv.Perm α)}
    (hmt : IsMultiplyPretransitive G α (Fintype.card α - 2)) : 
    alternatingGroup α ≤ G := by
  classical
  cases' Nat.lt_or_ge (Fintype.card α) 2 with hα1 hα
  · -- fintype.card α  < 2
    rw [Nat.lt_succ_iff] at hα1 
    suffices : alternatingGroup α = ⊥
    · rw [this]; exact bot_le
    rw [← Subgroup.card_le_one_iff_eq_bot]
    suffices Fintype.card (alternatingGroup α) ≤ Fintype.card (Equiv.Perm α) by
      apply le_trans this
      rw [Fintype.card_perm]
      exact Nat.factorial_le hα1
    convert Fintype.card_subtype_le (fun x ↦ x ∈ alternatingGroup α)
  suffices : ∃ s : Set α, Nat.card s = Fintype.card α - 2
  obtain ⟨s, hs⟩ := this
  rw [← hs] at hmt 
  let hyp := hmt.index_of_fixingSubgroup G α s
  rw [hs, Nat.sub_sub_self hα, Nat.factorial_two] at hyp 
  have hyp' : (fixingSubgroup G s).index * 2 ≤ Fintype.card G * 2
  · apply Nat.mul_le_mul_right
    apply Nat.le_of_dvd
    exact Fintype.card_pos
    apply Subgroup.index_dvd_card 
  rw [hyp, mul_comm] at hyp' 
  apply large_subgroup_of_perm_contains_alternating
  rw [Fintype.card_equiv (Equiv.refl _)]; exact hyp'
  obtain ⟨s, hs⟩ := Finset.exists_smaller_set (⊤ : Finset α) (Fintype.card α - 2) (Nat.sub_le _ _)
  use ↑s
  simp only [Finset.coe_sort_coe, card_eq_fintype_card, Fintype.card_coe, ge_iff_le, hs.right]
#align mul_action.alternating_group_le_of_full_minus_two_pretransitive MulAction.IsMultiplyPretransitive.alternatingGroup_le_of_sub_two

/-- The alternating group on 3 letters or more acts transitively -/
theorem alternatingGroup.isPretransitive [DecidableEq α] (h : 3 ≤ Fintype.card α) :
    IsPretransitive (alternatingGroup α) α :=
  by
  rw [isPretransitive_iff_is_one_pretransitive]
  apply isMultiplyPretransitive_of_higher
  apply IsMultiplyPretransitive.alternatingGroup_of_sub_two
  apply le_trans _ (Nat.sub_le_sub_right h 2)
  norm_num
  simp only [ge_iff_le, PartENat.card_eq_coe_fintype_card, PartENat.coe_le_coe,
    tsub_le_iff_right, le_add_iff_nonneg_right]
#align mul_action.alternating_group.is_pretransitive MulAction.alternatingGroup.isPretransitive

/- This lemma proves the trivial blocks property even if the action is not preprimitive
because it is not pretransitive (for fintype.card α ≤ 2)-/
theorem alternatingGroup.has_trivial_blocks [DecidableEq α]
    (B : Set α) (hB : IsBlock (alternatingGroup α) B) :
    IsTrivialBlock B := by
  classical
  cases' le_or_lt (Fintype.card α) 2 with h2 h2
  · exact IsTrivialBlock.of_card_le_2 h2 B
  cases' le_or_lt (Fintype.card α) 3 with h3 h4
  · have h3' : Fintype.card α = 3 := le_antisymm h3 h2
    cases' le_or_lt (Fintype.card B) 1 with h1 h2
    · apply Or.intro_left
      rw [← Set.subsingleton_coe, ← Fintype.card_le_one_iff_subsingleton]
      exact h1
    · apply Or.intro_right
      rw [Fintype.one_lt_card_iff] at h2 
      -- using h2, get a ≠ b in B
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := h2
      simp only [Ne.def, Subtype.mk_eq_mk] at hab 
      -- using h3', get c ≠ a, b
      have : ∃ c : α, c ∉ ({a, b}  : Finset α) := by
        by_contra h
        push_neg at h 
        have : ({a, b} : Finset α) = Finset.univ := by
          ext c
          constructor
          · intro _; exact Finset.mem_univ c
          · intro _; exact h c
        rw [lt_iff_not_ge] at h2 ; apply h2; rw [ge_iff_le]
        rw [← Finset.card_eq_iff_eq_univ] at this 
        rw [← this]
        rw [Finset.card_doubleton hab]
      obtain ⟨c, hc⟩ := this
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc 
      suffices : ({a, b, c} : Finset α) = Finset.univ
      rw [eq_top_iff]
      rw [Set.top_eq_univ, ← Finset.coe_univ, ← this]
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx 
      cases' hx with hxa hx
      rw [hxa]; exact ha
      cases' hx with hxb hxc
      rw [hxb]; exact hb
      rw [hxc]
      -- get a three_cycle g = c[a,b,c]
      let g : alternatingGroup α :=
        ⟨Equiv.swap a b * Equiv.swap c b,-- cycle [a,b,c]
        by
          rw [Equiv.Perm.mem_alternatingGroup]
          rw [Equiv.Perm.sign_mul]
          rw [Equiv.Perm.sign_swap hab]
          rw [Equiv.Perm.sign_swap hc.right]
          simp only [Int.units_mul_self]⟩
      suffices : g • B = B
      rw [← this]
      use b
      apply And.intro hb
      change (Equiv.swap a b * Equiv.swap c b) • b = c
      simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [Equiv.swap_apply_right]
      rw [Equiv.swap_apply_of_ne_of_ne hc.left hc.right]
      -- g • B = B
      apply hB.def_mem ha
      change (Equiv.swap a b * Equiv.swap c b) • a ∈ B
      simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (ne_comm.mp hc.left) hab]
      rw [Equiv.swap_apply_left]
      exact hb
      -- {a, b, c} = finset.univ
      rw [← Finset.card_eq_iff_eq_univ, h3']
      rw [Finset.card_insert_of_not_mem]
      rw [Finset.card_doubleton (ne_comm.mp hc.right)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      apply And.intro hab
      exact ne_comm.mp hc.left
  -- 4 ≤ fintype.card α
  change 4 ≤ Fintype.card α at h4 
  suffices : IsPreprimitive (alternatingGroup α) α
  exact this.has_trivial_blocks hB
  apply IsMultiplyPretransitive.isPreprimitive_of_two
  apply isMultiplyPretransitive_of_higher
  apply IsMultiplyPretransitive.alternatingGroup_of_sub_two
  apply le_trans _ (Nat.sub_le_sub_right h4 2); norm_num
  simp only [ge_iff_le, PartENat.card_eq_coe_fintype_card, PartENat.coe_le_coe,
    tsub_le_iff_right, le_add_iff_nonneg_right]
#align mul_action.alternating_group.has_trivial_blocks MulAction.alternatingGroup.has_trivial_blocks

/-- The alternating group on 3 letters or more acts primitively -/
theorem AlternatingGroup.isPreprimitive [DecidableEq α] (h : 3 ≤ Fintype.card α) :
    IsPreprimitive (alternatingGroup α) α := by
  have := alternatingGroup.isPretransitive h
  apply IsPreprimitive.mk
  apply alternatingGroup.has_trivial_blocks
#align mul_action.alternating_group.is_preprimitive MulAction.AlternatingGroup.isPreprimitive

end Finite

end MultipleTransitivity

end MulAction



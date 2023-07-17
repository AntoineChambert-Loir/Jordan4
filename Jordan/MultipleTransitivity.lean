/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module multiple_transitivity
-/
import Oneshot.SubMulActions
import Oneshot.ForMathlib.Stabilizer
import Oneshot.ForMathlib.Pretransitive
import Oneshot.ForMathlib.Partitions
import Oneshot.ForMathlib.Set
import Oneshot.ForMathlib.Cardinal
import Oneshot.Primitive
import Oneshot.ForMathlib.Extensions
import Mathbin.SetTheory.Cardinal.Finite
import Mathbin.GroupTheory.Index
import Mathbin.GroupTheory.GroupAction.Embedding
import Mathbin.GroupTheory.SpecificGroups.Alternating
import Mathbin.GroupTheory.Perm.List
import Mathbin.GroupTheory.Perm.Cycle.Concrete
import Oneshot.IndexNormal

/-


import order.hom.basic
import order.bounded_order

-- import group_theory.group_action.fixing_subgroup
-- import field_theory.galois

-- import group_theory.specific_groups.alternating

-- import group_theory.subgroup.pointwise
-- import group_theory.coset
-- import group_theory.quotient_group
-- import group_theory.abelianization
-- import group_theory.group_action.defs
-- import group_theory.group_action.basic
-- import group_theory.group_action.group
-- import group_theory.group_action.conj_act
-- import group_theory.group_action.sub_mul_action

-- import order.partition.finpartition
-- import data.finset.lattice

-- import data.setoid.partition
-- import data.set.basic
-- import data.fintype.basic
-- import order.rel_classes
-- import algebra.big_operators.order
-/
/-


import order.hom.basic
import order.bounded_order

-- import group_theory.group_action.fixing_subgroup
-- import field_theory.galois

-- import group_theory.specific_groups.alternating

-- import group_theory.subgroup.pointwise
-- import group_theory.coset
-- import group_theory.quotient_group
-- import group_theory.abelianization
-- import group_theory.group_action.defs
-- import group_theory.group_action.basic
-- import group_theory.group_action.group
-- import group_theory.group_action.conj_act
-- import group_theory.group_action.sub_mul_action

-- import order.partition.finpartition
-- import data.finset.lattice

-- import data.setoid.partition
-- import data.set.basic
-- import data.fintype.basic
-- import order.rel_classes
-- import algebra.big_operators.order
-/
open scoped BigOperators Pointwise Cardinal

open scoped Classical

namespace MulAction

section Transitivity

section Monoid

/- It would be better do have it for has_smul
but the instance does not automatically transfer to subtypes -/
variable {M α : Type _} [Monoid M] [MulAction M α]

theorem isPretransitive_of_submonoid {K : Submonoid M} (h : IsPretransitive K α) :
    IsPretransitive M α := by
  let h_eq := h.exists_smul_eq
  apply is_pretransitive.mk
  intro x y
  obtain ⟨⟨k, hk⟩, hk'⟩ := h_eq x y
  exact ⟨k, hk'⟩
#align mul_action.is_pretransitive_of_submonoid MulAction.isPretransitive_of_submonoid

theorem isPretransitive_of_submonoid_le {G K : Submonoid M} (hKG : K ≤ G)
    (h : IsPretransitive K α) : IsPretransitive G α :=
  by
  let h_eq := h.exists_smul_eq
  apply is_pretransitive.mk
  intro x y
  obtain ⟨⟨k, hk⟩, hk'⟩ := h_eq x y
  use ⟨k, hKG hk⟩
  exact hk'
#align mul_action.is_pretransitive_of_submonoid_le MulAction.isPretransitive_of_submonoid_le

end Monoid

section Group

variable (M α : Type _) [Group M] [MulAction M α]

/-- Cardinal of an orbit vs index of stabilizers, in nat.card -/
theorem card_orbit_eq_stabilizer_index {a : α} : Nat.card (orbit M a) = (stabilizer M a).index :=
  by
  change _ = Nat.card (M ⧸ stabilizer M a)
  unfold Nat.card
  apply Cardinal.toNat_congr
  exact orbit_equiv_quotient_stabilizer M a
#align mul_action.card_orbit_eq_stabilizer_index MulAction.card_orbit_eq_stabilizer_index

/-- Cardinal vs index of stabilizers, for a pretransitive action, in nat.card -/
theorem stabilizer_index_of_pretransitive (h : IsPretransitive M α) {a : α} :
    (stabilizer M a).index = Nat.card α :=
  by
  let heq := h.exists_smul_eq
  rw [← card_orbit_eq_stabilizer_index]
  apply Cardinal.toNat_congr
  refine'
    Equiv.mk (fun x => x)
      (fun y =>
        ⟨y, by
          obtain ⟨g, hg⟩ := HEq a y
          use g; rw [← hg]⟩)
      _ _
  · intro y; simp only [Subtype.coe_eta]
  · intro x; rfl
#align mul_action.stabilizer_index_of_pretransitive MulAction.stabilizer_index_of_pretransitive

variable {M α}

theorem isPretransitive_of_subgroup {K : Subgroup M} (h : IsPretransitive K α) :
    IsPretransitive M α := by
  apply is_pretransitive_of_submonoid
  swap; exact K.to_submonoid
  exact h
#align mul_action.is_pretransitive_of_subgroup MulAction.isPretransitive_of_subgroup

theorem isPretransitive_of_subgroup_le {G K : Subgroup M} (hKG : K ≤ G) (h : IsPretransitive K α) :
    IsPretransitive G α := by
  let h_eq := h.exists_smul_eq
  apply is_pretransitive.mk
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
def IsMultiplyPretransitive (n : ℕ) :=
  IsPretransitive M (Fin n ↪ α)
#align mul_action.is_multiply_pretransitive MulAction.IsMultiplyPretransitive

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The equivariant map from (fin 1 ↪ α) to α -/
def finOneToMap : (Fin 1 ↪ α) →[M] α
    where
  toFun x := x ⟨0, Nat.one_pos⟩
  map_smul' m x := rfl
#align mul_action.fin_one_to_map MulAction.finOneToMap

theorem finOneToMap_bijective : Function.Bijective (finOneToMap M α) :=
  by
  constructor
  · intro x y hxy
    ext i
    rw [Fin.eq_zero i]; exact hxy
  · intro a; use fun _ => a
    · intro i j hij
      rw [Fin.eq_zero i, Fin.eq_zero j]
    rfl
#align mul_action.fin_one_to_map_bijective MulAction.finOneToMap_bijective

variable {M α}

theorem isMultiplyPretransitive_of_subgroup {n : ℕ} {K : Subgroup M}
    (h : IsMultiplyPretransitive K α n) : IsMultiplyPretransitive M α n :=
  by
  unfold is_multiply_pretransitive at *
  exact is_pretransitive_of_subgroup h
#align mul_action.is_multiply_pretransitive_of_subgroup MulAction.isMultiplyPretransitive_of_subgroup

theorem isMultiplyPretransitive_of_le {n : ℕ} {H K : Subgroup M} (hHK : K ≤ H)
    (h : IsMultiplyPretransitive K α n) : IsMultiplyPretransitive H α n :=
  by
  unfold is_multiply_pretransitive at *
  refine' is_pretransitive_of_subgroup_le hHK h
#align mul_action.is_multiply_pretransitive_of_le MulAction.isMultiplyPretransitive_of_le

/-- Given an equivariant map α → β, get an equivariant map on function types (ι ↪ α) → (ι ↪ β)-/
def EquivariantMap.embeddingOfEquivariantMap {N β : Type _} [Group N] [MulAction N β] {φ : M → N}
    {f : α →ₑ[φ] β} (hf : Function.Injective f) (ι : Type _) : (ι ↪ α) →ₑ[φ] ι ↪ β
    where
  toFun x := ⟨f.toFun ∘ x.toFun, hf.comp x.inj'⟩
  map_smul' m x := by
    ext i
    simp only [smul_apply, coe_fn_mk, Function.comp_apply, to_fun_eq_coe, smul_apply]
    rw [f.map_smul']
#align mul_action.equivariant_map.embedding_of_equivariant_map MulAction.EquivariantMap.embeddingOfEquivariantMap

theorem EquivariantMap.embeddingOfEquivariantMap_apply {N β : Type _} [Group N] [MulAction N β]
    {φ : M → N} {f : α →ₑ[φ] β} (hf : Function.Injective f) {ι : Type _} {x : ι ↪ α} {i : ι} :
    (EquivariantMap.embeddingOfEquivariantMap hf ι) x i = f (x i) :=
  rfl
#align mul_action.equivariant_map.embedding_of_equivariant_map_apply MulAction.EquivariantMap.embeddingOfEquivariantMap_apply

theorem EquivariantMap.embeddingOfEquivariantMap_is_injective {N β : Type _} [Group N]
    [MulAction N β] {φ : M → N} {f : α →ₑ[φ] β} (hf : Function.Injective f) {ι : Type _} :
    Function.Injective (EquivariantMap.embeddingOfEquivariantMap hf ι) :=
  by
  intro x y hxy
  ext i
  apply hf
  simp only [← equivariant_map.embedding_of_equivariant_map_apply hf]
  rw [hxy]
#align mul_action.equivariant_map.embedding_of_equivariant_map_is_injective MulAction.EquivariantMap.embeddingOfEquivariantMap_is_injective

theorem EquivariantMap.embeddingOfEquivariantMap_is_bijective {N β : Type _} [Group N]
    [MulAction N β] {φ : M → N} (f : α →ₑ[φ] β) (hf : Function.Bijective f) {ι : Type _} :
    Function.Bijective (EquivariantMap.embeddingOfEquivariantMap hf.Injective ι) :=
  by
  constructor
  exact equivariant_map.embedding_of_equivariant_map_is_injective hf.injective
  intro y
  obtain ⟨g, hgf, hfg⟩ := function.bijective_iff_has_inverse.mp hf
  let hg := Function.RightInverse.injective hfg
  use ⟨g ∘ y, Function.Injective.comp hfg.injective (EmbeddingLike.injective y)⟩
  ext i
  rw [equivariant_map.embedding_of_equivariant_map_apply]
  simp only [coe_fn_mk, Function.comp_apply]
  rw [hfg]
#align mul_action.equivariant_map.embedding_of_equivariant_map_is_bijective MulAction.EquivariantMap.embeddingOfEquivariantMap_is_bijective

/-- Multiple transitivity of an image by an equivariant map of a multiply transitive action -/
theorem isMultiplyPretransitive_of_surjective_map {N β : Type _} [Group N] [MulAction N β] {n : ℕ}
    {φ : M → N} {f : α →ₑ[φ] β} (hf : Function.Surjective f) (h : IsMultiplyPretransitive M α n) :
    IsMultiplyPretransitive N β n :=
  by
  let h_eq := h.exists_smul_eq
  apply is_pretransitive.mk
  --  intros x y,
  have aux : ∀ x : Fin n ↪ β, ∃ x' : Fin n ↪ α, f ∘ x' = x := fun x =>
    by
    let x' : Fin n → α := fun i => (hf (x i)).some
    suffices hx' : Function.Injective x'
    · use ⟨x', hx'⟩
      ext i
      simp only [Function.comp_apply, to_fun_eq_coe]
      rw [← Classical.choose_spec (hf (x i))]
      simp only [coe_fn_mk]
    · intro i i' hi
      let hi' := congr_arg f hi
      simp only [Classical.choose_spec (hf (x _))] at hi' 
      exact x.inj' hi'
  intro x y
  obtain ⟨x', hx'⟩ := aux x
  obtain ⟨y', hy'⟩ := aux y
  obtain ⟨g, hg'⟩ := h_eq x' y'
  use φ g
  ext i
  change _ • x i = y i
  rw [← hx', ← hy']; simp only [Function.comp_apply]
  simp only [← EquivariantMap.toFun_eq_coe]
  simp_rw [← f.map_smul']
  apply congr_arg
  rw [← hg']
  simp only [to_fun_eq_coe, smul_apply]
#align mul_action.is_multiply_pretransitive_of_surjective_map MulAction.isMultiplyPretransitive_of_surjective_map

theorem isMultiplyPretransitive_of_bijective_map_iff {N β : Type _} [Group N] [MulAction N β]
    {n : ℕ} {φ : M → N} {f : α →ₑ[φ] β} (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsMultiplyPretransitive M α n ↔ IsMultiplyPretransitive N β n :=
  by
  constructor
  apply is_multiply_pretransitive_of_surjective_map hf.surjective
  intro hN; let hN_heq := hN.exists_smul_eq
  apply is_pretransitive.mk
  intro x y
  let x' : Fin n ↪ β := ⟨f ∘ x, hf.injective.comp x.inj'⟩
  let y' : Fin n ↪ β := ⟨f ∘ y, hf.injective.comp y.inj'⟩
  obtain ⟨g', hg'⟩ := hN_heq x' y'
  obtain ⟨g, hg⟩ := hφ g'
  use g
  ext i
  apply hf.injective
  simp only [smul_apply]; simp only [← EquivariantMap.toFun_eq_coe]
  rw [f.map_smul']
  rw [hg]
  suffices : f.to_fun (x i) = x' i; rw [this]
  suffices : f.to_fun (y i) = y' i; rw [this]
  rw [← hg']; rw [← hg]
  simp only [MonoidHom.toFun_eq_coe, smul_apply]
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
  apply is_pretransitive.mk
  intro x y; use 1; rw [one_smul]
  ext i; exfalso
  exact IsEmpty.false i
#align mul_action.is_zero_pretransitive MulAction.is_zero_pretransitive

/-- An action is 1-pretransitive iff it is pretransitive -/
theorem isPretransitive_iff_is_one_pretransitive :
    IsPretransitive M α ↔ IsMultiplyPretransitive M α 1 :=
  by
  unfold is_multiply_pretransitive
  rw [isPretransitive_of_bijective_map_iff Function.surjective_id (fin_one_to_map_bijective M α)]
#align mul_action.is_pretransitive_iff_is_one_pretransitive MulAction.isPretransitive_iff_is_one_pretransitive

/-- An action is 2-pretransitive iff it is two_pretransitive… -/
theorem is_two_pretransitive_iff :
    IsMultiplyPretransitive M α 2 ↔
      ∀ (a b c d : α) (hab : a ≠ b) (hcd : c ≠ d), ∃ m : M, m • a = c ∧ m • b = d :=
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
  let f : ∀ (a b : α) (hab : a ≠ b), Fin 2 ↪ α := fun a b hab =>
    ⟨fun i => ite (i = 0) a b, by
      intro i j hij
      by_cases hi : i = 0
      by_cases hj : j = 0
      rw [hi, hj]
      simp only [if_pos hi, if_neg hj] at hij ; exfalso; exact hab hij
      by_cases hj : j = 0
      simp only [if_neg hi, if_pos hj] at hij ; exfalso; exact hab hij.symm
      rw [Or.resolve_left (this i) hi, Or.resolve_left (this j) hj]⟩
  have hf0 : ∀ (a b : α) (hab : a ≠ b), (f a b hab) 0 = a := by intro a b hab; rfl
  have hf1 : ∀ (a b : α) (hab : a ≠ b), (f a b hab) 1 = b := by intro a b hab; rfl
  constructor
  · intro h
    let h' := h.exists_smul_eq
    intro a b c d hab hcd
    obtain ⟨m, hm⟩ := h' (f a b hab) (f c d hcd)
    rw [← Function.Embedding.ext_iff] at hm 
    use m
    constructor
    simpa only [smul_apply, coe_fn_mk, eq_self_iff_true, if_true] using hm 0
    simpa only [smul_apply, coe_fn_mk, eq_self_iff_true, if_true] using hm 1
  · intro h
    apply is_pretransitive.mk
    intro u v
    obtain ⟨m, hm⟩ := h (u 0) (u 1) (v 0) (v 1) _ _
    use m
    ext
    cases' this x with hx hx
    simpa only [hx] using hm.left
    simpa only [hx] using hm.right
    rw [Ne.def, Function.Embedding.apply_eq_iff_eq]; exact zero_ne_one
    rw [Ne.def, Function.Embedding.apply_eq_iff_eq]; exact zero_ne_one
#align mul_action.is_two_pretransitive_iff MulAction.is_two_pretransitive_iff

/-- An n-pretransitive action is m-pretransitive for any m ≤ n -/
theorem isMultiplyPretransitive_of_higher {n : ℕ} (hn : IsMultiplyPretransitive M α n) {m : ℕ}
    (hmn : m ≤ n) (hα : ↑n ≤ PartENat.card α) : IsMultiplyPretransitive M α m :=
  by
  unfold is_multiply_pretransitive
  let hn_eq := hn.exists_smul_eq
  apply is_pretransitive.mk
  intro x y
  obtain ⟨x', hx'⟩ := may_extend hmn hα x
  obtain ⟨y', hy'⟩ := may_extend hmn hα y
  obtain ⟨g, hg⟩ := hn_eq x' y'
  use g
  ext; rw [← hy', ← hx', ← hg]; rfl
#align mul_action.is_multiply_pretransitive_of_higher MulAction.isMultiplyPretransitive_of_higher

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)-/
theorem stabilizer.is_multiply_pretransitive' (hα' : IsPretransitive M α) {n : ℕ} :
    IsMultiplyPretransitive M α n.succ ↔
      ∀ a : α, IsMultiplyPretransitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n :=
  by
  let hα'eq := hα'.exists_smul_eq
  constructor
  · -- if the action is n.succ-multiply transitive,
    -- then the action of sub_mul_action_of_stabilizer is n-multiply transitive
    intro hn a; let hn_eq := hn.exists_smul_eq
    apply is_pretransitive.mk
    let j : SubMulAction.ofStabilizer M a ↪ α :=
      { toFun := fun u => id u
        inj' := fun x y hxy => by simpa using hxy }
    have :
      ∀ x : Fin n ↪ SubMulAction.ofStabilizer M a,
        ∃ x' : Fin n.succ ↪ α,
          (Fin.castLE (Nat.le_succ n)).toEmbedding.trans x' = x.trans j ∧
            x' ⟨n, Nat.lt_succ_self n⟩ = a :=
      by
      intro x
      refine' may_extend_with (x.trans (Subtype _)) a _
      rintro ⟨u, hu⟩
      simp only [to_fun_eq_coe, trans_apply, Function.Embedding.coe_subtype] at hu 
      exact (SubMulAction.ofStabilizer.neq M a) hu
    intro x y
    obtain ⟨x', hx', hx'a⟩ := this x
    obtain ⟨y', hy', hy'a⟩ := this y
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
    simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, id.def, coe_fn_mk] at hx'
      hy' 
    rw [← hx', ← hy', ← hg']; rfl
  · -- if the action of sub_mul_action.of_stabilizer is n-multiply transitive,
    -- then the action is n.succ-multiply transitive.
    intro hn
    have aux_fun :
      ∀ (a : α) (x : Fin n.succ ↪ α),
        ∃ (g : M) (x1 : Fin n ↪ ↥(SubMulAction.ofStabilizer M a)),
          (Fin.castLE (Nat.le_succ n)).toEmbedding.trans (g • x) =
              Function.Embedding.trans x1 (Subtype _) ∧
            g • x ⟨n, Nat.lt_succ_self n⟩ = a :=
      by
      intro a x
      obtain ⟨g, hgx⟩ := hα'eq (x ⟨n, Nat.lt_succ_self n⟩) a
      use g
      have zgx : ∀ i : Fin n, g • x i ∈ SubMulAction.ofStabilizer M a :=
        by
        rintro ⟨i, hi⟩
        rw [SubMulAction.ofStabilizer.mem_iff]
        rw [← hgx]
        simp only [Fin.coe_eq_castSuccEmb, Fin.castSuccEmb_mk, Ne.def, smul_left_cancel_iff,
          EmbeddingLike.apply_eq_iff_eq]
        exact ne_of_lt hi
      let x1 : Fin n → SubMulAction.ofStabilizer M a := fun i => ⟨g • x i, zgx i⟩
      use x1
      · intro i j
        simp only [Subtype.mk_eq_mk, Fin.coe_eq_castSuccEmb, smul_left_cancel_iff,
          EmbeddingLike.apply_eq_iff_eq, OrderEmbedding.eq_iff_eq, imp_self]
      refine' And.intro _ hgx
      · ext i; simp; rfl
    apply is_pretransitive.mk
    intro x
    -- gx • x = x1 :: a
    let a := x ⟨n, lt_add_one n⟩
    obtain ⟨gx, x1, hgx, hga⟩ := aux_fun a x
    intro y
    -- gy • y = y1 :: a
    obtain ⟨gy, y1, hgy, hgb⟩ := aux_fun a y
    -- g • x1 = y1,
    let hna_eq := (hn a).exists_smul_eq
    obtain ⟨g, hg⟩ := hna_eq x1 y1
    use gy⁻¹ * g * gx
    ext ⟨i, hi⟩
    rw [mul_smul]; simp only [smul_apply]
    cases' lt_or_eq_of_le (le_of_lt_succ hi) with hi' hi'
    · rw [← Function.Embedding.ext_iff] at hgx hgy hg 
      specialize hgx ⟨i, hi'⟩; specialize hgy ⟨i, hi'⟩; specialize hg ⟨i, hi'⟩
      simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, smul_apply,
        Function.Embedding.coe_subtype] at hgx hgy hg 
      rw [hgx, mul_smul, inv_smul_eq_iff, hgy, ← hg]; rfl
    · simp only [hi']
      rw [hga, mul_smul, inv_smul_eq_iff, hgb]
      rw [← mem_stabilizer_iff]; exact SetLike.coe_mem g
#align mul_action.stabilizer.is_multiply_pretransitive' MulAction.stabilizer.is_multiply_pretransitive'

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)-/
theorem stabilizer.isMultiplyPretransitive (hα' : IsPretransitive M α) {n : ℕ}
    {a : α} :-- (hα0 : ↑n ≤ #α) /- (hα : card_ge α n.succ) -/  :
        IsMultiplyPretransitive
        M α n.succ ↔
      IsMultiplyPretransitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n :=
  by
  let hα'eq := hα'.exists_smul_eq
  constructor
  · -- if the action is n.succ-multiply transitive,
    -- then the action of sub_mul_action_of_stabilizer is n-multiply transitive
    intro hn; let hn_eq := hn.exists_smul_eq
    apply is_pretransitive.mk
    let j : SubMulAction.ofStabilizer M a ↪ α :=
      { toFun := fun u => id u
        inj' := fun x y hxy => by simpa using hxy }
    have :
      ∀ x : Fin n ↪ SubMulAction.ofStabilizer M a,
        ∃ x' : Fin n.succ ↪ α,
          (Fin.castLE (Nat.le_succ n)).toEmbedding.trans x' = x.trans j ∧
            x' ⟨n, Nat.lt_succ_self n⟩ = a :=
      by
      intro x
      refine' may_extend_with (x.trans (Subtype _)) a _
      rintro ⟨u, hu⟩
      simp only [to_fun_eq_coe, trans_apply, Function.Embedding.coe_subtype] at hu 
      exact (SubMulAction.ofStabilizer.neq M a) hu
    intro x y
    obtain ⟨x', hx', hx'a⟩ := this x
    obtain ⟨y', hy', hy'a⟩ := this y
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
    simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, id.def, coe_fn_mk] at hx'
      hy' 
    rw [← hx', ← hy', ← hg']; rfl
  · -- if the action of sub_mul_action.of_stabilizer is n-multiply transitive,
    -- then the action is n.succ-multiply transitive.
    intro hn
    have aux_fun :
      ∀ (a : α) (x : Fin n.succ ↪ α),
        ∃ (g : M) (x1 : Fin n ↪ ↥(SubMulAction.ofStabilizer M a)),
          (Fin.castLE (Nat.le_succ n)).toEmbedding.trans (g • x) =
              Function.Embedding.trans x1 (Subtype _) ∧
            g • x ⟨n, Nat.lt_succ_self n⟩ = a :=
      by
      intro a x
      obtain ⟨g, hgx⟩ := hα'eq (x ⟨n, Nat.lt_succ_self n⟩) a
      use g
      have zgx : ∀ i : Fin n, g • x i ∈ SubMulAction.ofStabilizer M a :=
        by
        rintro ⟨i, hi⟩
        rw [SubMulAction.ofStabilizer.mem_iff]
        rw [← hgx]
        simp only [Fin.coe_eq_castSuccEmb, Fin.castSuccEmb_mk, Ne.def, smul_left_cancel_iff,
          EmbeddingLike.apply_eq_iff_eq]
        exact ne_of_lt hi
      let x1 : Fin n → SubMulAction.ofStabilizer M a := fun i => ⟨g • x i, zgx i⟩
      use x1
      · intro i j
        simp only [Subtype.mk_eq_mk, Fin.coe_eq_castSuccEmb, smul_left_cancel_iff,
          EmbeddingLike.apply_eq_iff_eq, OrderEmbedding.eq_iff_eq, imp_self]
      refine' And.intro _ hgx
      · ext i; simp; rfl
    apply is_pretransitive.mk
    intro x
    -- obtain gx : gx • x = x1 :: a
    obtain ⟨gx, x1, hgx, hga⟩ := aux_fun a x
    intro y
    -- obtain gy : gy • y = y1 :: a
    obtain ⟨gy, y1, hgy, hgb⟩ := aux_fun a y
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
      rw [hgx, mul_smul, inv_smul_eq_iff, hgy, ← hg]; rfl
    · simp only [hi']
      rw [hga, mul_smul, inv_smul_eq_iff, hgb]
      rw [← mem_stabilizer_iff]; exact SetLike.coe_mem g
#align mul_action.stabilizer.is_multiply_pretransitive MulAction.stabilizer.isMultiplyPretransitive

/-- The fixator of a subset of cardinal d in a k-transitive action
acts (k-d) transitively on the remaining -/
theorem remaining_transitivity (d : ℕ) (s : Set α) (hs : PartENat.card s = d) (n : ℕ)
    (h : IsMultiplyPretransitive M α n) :
    IsMultiplyPretransitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) (n - d) :=
  by
  cases' le_total d n with hdn hnd
  · apply is_pretransitive.mk
    intro x y
    let h_eq := h.exists_smul_eq
    obtain ⟨z'⟩ := equiv_fin_of_partENat_card_eq hs
    let z := z'.symm
    have hd' : n = n - d + d := (Nat.sub_add_cancel hdn).symm
    obtain ⟨x' : Fin n ↪ α, hx'1, hx'2⟩ := may_extend_with' z.to_embedding hd' x
    obtain ⟨y' : Fin n ↪ α, hy'1, hy'2⟩ := may_extend_with' z.to_embedding hd' y
    obtain ⟨g, hg⟩ := h_eq x' y'
    use g
    · intro a
      let i := z.symm a
      have : z.to_embedding.trans (Subtype (s : Set α)) i = a := by
        simp only [trans_apply, Equiv.toEmbedding_apply, Equiv.apply_symm_apply,
          Function.Embedding.coe_subtype]
      simp only [← this]
      conv_lhs => rw [← hx'2]; rw [← hy'2]; rw [← hg]
      simp only [trans_apply, smul_apply]
    · ext i
      simp only [smul_apply, SubMulAction.val_smul_of_tower]
      have : (y i : α) = (y.trans (Subtype (sᶜ)) i : α) := by
        simp only [trans_apply, Function.Embedding.coe_subtype]
      rw [this]
      have : (x i : α) = (x.trans (Subtype (sᶜ)) i : α) := by
        simp only [trans_apply, Function.Embedding.coe_subtype]
      rw [this]
      rw [← Function.Embedding.ext_iff] at hx'1 hy'1 
      simp_rw [← hy'1 i, ← hx'1 i, ← hg]
      simp only [trans_apply, smul_apply, RelEmbedding.coe_toEmbedding]
      rfl
  · rw [Nat.sub_eq_zero_of_le hnd]
    apply is_zero_pretransitive
#align mul_action.remaining_transitivity MulAction.remaining_transitivity

theorem remaining_transitivity' (s : Set α) [Fintype s] (m n : ℕ)
    (hn : (n : PartENat) ≤ PartENat.card α) (hmn : m + Fintype.card s ≤ n)
    (h : IsMultiplyPretransitive M α n) :
    IsMultiplyPretransitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) m :=
  by
  let d := Fintype.card s
  rw [← Nat.add_sub_cancel m d]
  apply remaining_transitivity
  exact part_enat.of_fintype ↥s
  apply is_multiply_pretransitive_of_higher
  exact h
  exact hmn
  exact hn
#align mul_action.remaining_transitivity' MulAction.remaining_transitivity'

private theorem index_of_fixing_subgroup_of_multiply_pretransitive_aux (k : ℕ) [Fintype α]
    (hmk : IsMultiplyPretransitive M α k) {s : Finset α} (hs : s.card = k) :
    (fixingSubgroup M (s : Set α)).index * (Fintype.card α - s.card).factorial =
      (Fintype.card α).factorial :=
  by
  revert M α
  induction' k with k hrec
  -- k = 0
  · intro M α _ _ _ hmk s hs
    rw [Finset.card_eq_zero] at hs 
    simp only [hs, Finset.coe_empty, Finset.card_empty, tsub_zero]
    suffices fixingSubgroup M ∅ = ⊤ by rw [this, Subgroup.index_top, one_mul]
    exact GaloisConnection.l_bot (fixingSubgroup_fixedPoints_gc M α)
  -- induction step
  intro M α _ _ _ hmk s hs
  have hGX : is_pretransitive M α :=
    by
    rw [is_pretransitive_iff_is_one_pretransitive]
    apply is_multiply_pretransitive_of_higher M α hmk
    · rw [Nat.succ_le_succ_iff]; apply Nat.zero_le
    · rw [← hs]
      simp only [PartENat.card_eq_coe_fintype_card, Fintype.card_coe, PartENat.coe_le_coe]
      exact Finset.card_le_univ s
  suffices : s.nonempty
  obtain ⟨a, has⟩ := Finset.Nonempty.bex this
  let t' : Set (SubMulAction.ofStabilizer M a) := coe ⁻¹' (↑(s.erase a) : Set α)
  have hat' : (coe '' t' : Set α) = s.erase a :=
    by
    simp only [Subtype.image_preimage_coe, Finset.coe_erase, SetLike.mem_coe,
      Set.inter_eq_left_iff_subset, Set.diff_singleton_subset_iff]
    simp_rw [SubMulAction.ofStabilizer.mem_iff]
    intro x _
    simp only [Set.mem_insert_iff]
    cases' em (x = a) with hx hx
    apply Or.intro_left; exact hx
    apply Or.intro_right; exact hx
  --   have hat : a ∉ s.erase a := finset.not_mem_erase a s,
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
  rw [(MonoidHom.ker_eq_bot_iff (stabilizer M a).Subtype).mpr
      (by simp only [Subgroup.coeSubtype, Subtype.coe_injective])]
  simp only [sup_bot_eq, Subgroup.subtype_range]
  suffices
    (fixingSubgroup (stabilizer M a) t').index * (Fintype.card α - 1 - Fintype.card t').factorial =
      (Fintype.card α - 1).factorial
    by
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
      rw [← Finset.card_image_of_injective t'.to_finset Subtype.coe_injective]
      apply congr_arg
      rw [← Finset.coe_inj]
      rw [Finset.coe_image]
      rw [Set.coe_toFinset]
      exact hat'
  · let hz :=
      hrec (stabilizer M a) (SubMulAction.ofStabilizer M a)
        ((stabilizer.is_multiply_pretransitive M α hGX).mp hmk) _
    swap; exact t'.to_finset
    swap
    · rw [← Finset.card_image_of_injective t'.to_finset Subtype.coe_injective]
      rw [← Set.coe_toFinset t', ← Finset.coe_image, Finset.coe_inj] at hat' 
      rw [hat']
      rw [Finset.card_erase_of_mem has, hs, Nat.sub_one k.succ, Nat.pred_succ]
    suffices : Fintype.card (SubMulAction.ofStabilizer M a) = Fintype.card α - 1
    rw [this, Set.coe_toFinset t', Set.toFinset_card t'] at hz 
    exact hz
    change Fintype.card (SubMulAction.ofStabilizer M a).carrier = _
    rw [SubMulAction.ofStabilizer.def, Fintype.card_compl_set, Set.card_singleton]
  ·-- s.nonempty
    rw [← Finset.card_pos, hs];
    exact succ_pos k

/-- For a multiply pretransitive action, computes the index of the fixing_subgroup of a subset -/
theorem index_of_fixingSubgroup_of_multiply_pretransitive [Fintype α] (s : Set α)
    (hMk : IsMultiplyPretransitive M α (Fintype.card s)) :
    (fixingSubgroup M s).index * (Fintype.card α - Fintype.card s).factorial =
      (Fintype.card α).factorial :=
  by
  rw [← index_of_fixing_subgroup_of_multiply_pretransitive_aux M α _ hMk (Set.toFinset_card s)]
  rw [Set.coe_toFinset s]
  rw [← Set.toFinset_card]
#align mul_action.index_of_fixing_subgroup_of_multiply_pretransitive MulAction.index_of_fixingSubgroup_of_multiply_pretransitive

open scoped Classical

/-- A 2-transitive action is primitive -/
theorem isPreprimitive_of_two_pretransitive (h2 : IsMultiplyPretransitive M α 2) :
    IsPreprimitive M α := by
  cases' le_or_gt (PartENat.card α) 1 with hα hα
  -- Trivial case where subsingleton α
  · rw [PartENat.card_le_one_iff_subsingleton] at hα 
    skip
    apply IsPreprimitive.on_subsingleton
  /-
      haveI : is_pretransitive M α,
      { apply is_pretransitive.mk,
        intros x y, use 1, exact subsingleton_iff.mp hα _ _ },
      apply is_preprimitive.mk,
      { intros B hB,
        apply or.intro_left,
        exact @set.subsingleton_of_subsingleton _ hα B } -/
  -- Important case : 2 ≤ #α
  let hα' := id hα;
  rw [gt_iff_lt] at hα' 
  rw [← cast_one, ← PartENat.succ_le_iff] at hα' 
  have : is_pretransitive M α :=
    by
    rw [is_pretransitive_iff_is_one_pretransitive]
    apply is_multiply_pretransitive_of_higher M α h2 _ hα'
    norm_num
  apply IsPreprimitive.mk
  intro B hB
  cases' le_or_gt (PartENat.card B) 1 with h h
  · -- Case : subsingleton
    apply Or.intro_left
    rw [PartENat.card_le_one_iff_subsingleton, Set.subsingleton_coe] at h 
    exact h
  -- Case : top
  apply Or.intro_right
  unfold PartENat.card at h 
  rw [gt_iff_lt, ← cast_one, ← PartENat.succ_le_iff] at h 
  obtain ⟨x : Fin 2 ↪ ↥B⟩ := gimme_some h
  rw [Set.top_eq_univ]
  apply Set.eq_univ_of_forall
  intro a
  cases' em (a = x 0) with hca hca'
  rw [hca]; exact Subtype.mem (x 0)
  cases' em (a = x 1) with hcb hcb'
  rw [hcb]; exact Subtype.mem (x 1)
  unfold is_multiply_pretransitive at h2 ; let h2_eq := h2.exists_smul_eq
  let y : Fin 2 → α := fun i => if i.val = 0 then x 0 else a
  have hy0 : y 0 = x 0 := by simp
  have hy1 : y 1 = a := by simp
  have : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
    rintro ⟨i, hi⟩
    rw [Nat.lt_succ_iff] at hi 
    cases' Nat.eq_zero_or_pos i with hi_zero hi_pos
    · apply Or.intro_left
      change _ = (⟨0, _⟩ : Fin 2)
      rw [Fin.mk.inj_iff]; exact hi_zero
    · apply Or.intro_right
      change _ = (⟨1, _⟩ : Fin 2)
      rw [Fin.mk.inj_iff]; exact le_antisymm hi hi_pos
  have hy : Function.Injective y := by
    intro i j hij
    cases' this i with hi hi <;> cases' this j with hj hj <;>
        simp only [hi, hj, hy0, hy1] at hij ⊢ <;>
      exfalso
    exact hca' hij.symm
    exact hca' hij
  obtain ⟨g : M, hg : g • x.trans (Subtype _) = ⟨y, hy⟩⟩ := h2_eq _ _
  rw [← Function.Embedding.ext_iff] at hg 
  simp at hg 
  rw [← hy1, ← hg 1, ← inv_inv g, ← Set.mem_smul_set_iff_inv_smul_mem]
  rw [is_block.def_mem hB (x 0) g⁻¹ (Subtype.mem (x 0)) _]
  exact Subtype.mem (x 1)
  · rw [← hy0, ← hg 0, ← mul_smul, inv_mul_self, one_smul]
    exact Subtype.mem (x 0)
#align mul_action.is_preprimitive_of_two_pretransitive MulAction.isPreprimitive_of_two_pretransitive

section Finite

variable (α)

/-- The permutation group on α is pretransitive -/
theorem Equiv.Perm.isPretransitive : MulAction.IsPretransitive (Equiv.Perm α) α :=
  by
  apply is_pretransitive.mk
  intro x y
  use Equiv.swap x y
  simp only [Equiv.Perm.smul_def]
  rw [Equiv.swap_apply_left x y]
#align mul_action.equiv.perm.is_pretransitive MulAction.Equiv.Perm.isPretransitive

variable [Fintype α]

/-- The permutation group on α is fintype.card α-pretransitive -/
theorem equiv_perm_is_fully_pretransitive :
    MulAction.IsMultiplyPretransitive (Equiv.Perm α) α (Fintype.card α) :=
  by
  apply is_pretransitive.mk
  intro x y
  let x' := Equiv.ofBijective x.to_fun _
  let y' := Equiv.ofBijective y.to_fun _
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
#align mul_action.equiv_perm_is_fully_pretransitive MulAction.equiv_perm_is_fully_pretransitive

theorem equiv_perm_isMultiplyPretransitive (n : ℕ) :
    MulAction.IsMultiplyPretransitive (Equiv.Perm α) α n :=
  by
  cases' le_or_gt n (Fintype.card α) with hn hn
  · apply is_multiply_pretransitive_of_higher (Equiv.Perm α) α _ hn
    apply le_of_eq; rw [PartENat.card_eq_coe_fintype_card]
    apply equiv_perm_is_fully_pretransitive
  -- hn : n > fintype.card α
  suffices IsEmpty (Fin n ↪ α) by
    rw [is_multiply_pretransitive]
    apply is_pretransitive.mk
    intro x
    exfalso; apply this.false; exact x
  apply Function.Embedding.is_empty_of_card_lt
  simp only [Fintype.card_fin]
  exact hn
#align mul_action.equiv_perm_is_multiply_pretransitive MulAction.equiv_perm_isMultiplyPretransitive

/-- The action of the permutation group of α on α is preprimitive -/
theorem Equiv.Perm.isPreprimitive : IsPreprimitive (Equiv.Perm α) α :=
  by
  cases subsingleton_or_nontrivial α <;> skip
  exact IsPreprimitive.on_subsingleton
  apply is_preprimitive_of_two_pretransitive
  apply is_multiply_pretransitive_of_higher
  apply equiv_perm_is_fully_pretransitive
  rw [← Fintype.one_lt_card_iff_nontrivial] at h 
  exact h
  apply le_of_eq; rw [part_enat.of_fintype]
#align mul_action.equiv.perm.is_preprimitive MulAction.Equiv.Perm.isPreprimitive

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
theorem eq_top_of_is_full_minus_one_pretransitive {G : Subgroup (Equiv.Perm α)}
    (hmt : IsMultiplyPretransitive (↥G) α (Fintype.card α - 1)) : G = ⊤ :=
  by
  let j : Fin (Fintype.card α - 1) ↪ Fin (Fintype.card α) :=
    (Fin.castLE ((Fintype.card α).sub_le 1)).toEmbedding
  rw [eq_top_iff]; intro k _
  let x : Fin (Fintype.card α) ↪ α := (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  let hmt_eq := hmt.exists_smul_eq
  let x' := j.trans x
  obtain ⟨g, hg'⟩ := hmt_eq x' (k • x')
  suffices k = g by rw [this]; exact SetLike.coe_mem g
  have hx : ∀ x : Fin (Fintype.card α) ↪ α, Function.Surjective x.toFun :=
    by
    intro x
    suffices : Function.Bijective x.to_fun; exact this.right
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨EmbeddingLike.injective x, Fintype.card_fin (Fintype.card α)⟩
  have hgk' :
    ∀ (i : Fin (Fintype.card α)) (hi : i.val < Fintype.card α - 1), (g • x) i = (k • x) i :=
    by
    intro i hi
    simpa using congr_fun (congr_arg coeFn hg') ⟨i.val, hi⟩
  have hgk : ∀ i : Fin (Fintype.card α), (g • x) i = (k • x) i :=
    by
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
#align mul_action.eq_top_of_is_full_minus_one_pretransitive MulAction.eq_top_of_is_full_minus_one_pretransitive

variable (α)

-- Cette instance n'était pas nécessaire,
-- mais sans elle, Lean utilise des classical dont il ne se dépêtre plus après !
-- (cf alternating_iwasawa)
variable [DecidableEq α]

/-- The alternating group on α is (fintype.card α - 2)-pretransitive -/
theorem alternatingGroup_is_fully_minus_two_pretransitive :
    MulAction.IsMultiplyPretransitive (alternatingGroup α) α (Fintype.card α - 2) :=
  by
  cases' lt_or_ge (Fintype.card α) 2 with h2 h2
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h2)]
    apply is_zero_pretransitive
  -- fintype.card α ≥ 2
  obtain ⟨n, hn⟩ := Nat.le.dest h2
  have hn' : Fintype.card α - 2 = n := NormNum.sub_nat_pos (Fintype.card α) 2 n hn
  rw [add_comm] at hn 
  have hn_le : n ≤ Fintype.card α := by rw [← hn]; exact le_self_add
  apply is_pretransitive.mk
  rw [hn']
  intro x y
  obtain ⟨x', hx'⟩ := may_extend hn_le (le_of_eq (part_enat.of_fintype α).symm) x
  obtain ⟨y', hy'⟩ := may_extend hn_le (le_of_eq (part_enat.of_fintype α).symm) y
  let heq := (equiv_perm_is_fully_pretransitive α).exists_smul_eq
  obtain ⟨g, hg⟩ := HEq x' y'
  cases' Int.units_eq_one_or g.sign with h h
  · use ⟨g, equiv.perm.mem_alternating_group.mpr h⟩
    ext i
    simp only [Function.Embedding.smul_apply]
    rw [← hx', ← hy', ← hg]
    rfl
  · have hg'1 : n + 1 < Fintype.card α := by rw [← hn]; exact Nat.lt.base (n + 1)
    have hg'2 : n < Fintype.card α := by apply lt_trans _ hg'1; exact lt_add_one n
    let g' := Equiv.swap (y'.to_fun ⟨n + 1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩)
    have hg' : g'.sign = -1 := by
      rw [Equiv.Perm.IsSwap.sign_eq]
      use y'.to_fun ⟨n + 1, hg'1⟩; use y'.to_fun ⟨n, hg'2⟩
      simp only [to_fun_eq_coe, Ne.def, EmbeddingLike.apply_eq_iff_eq, Fin.mk_eq_mk,
        Nat.succ_ne_self, not_false_iff, true_and_iff]
      rfl
    use g' * g
    · rw [Equiv.Perm.mem_alternatingGroup]
      simp only [Equiv.Perm.sign_mul, h, hg']
      norm_num
    ext i; simp only [Function.Embedding.smul_apply]
    rw [← hx', ← hy', ← hg]
    simp only [Function.Embedding.trans_apply, RelEmbedding.coe_toEmbedding,
      Function.Embedding.smul_apply, Equiv.Perm.smul_def]
    change (g' * g) • _ = _
    rw [← smul_smul]
    simp
    change (Equiv.swap (y'.to_fun ⟨n + 1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩)) _ = _
    refine' Equiv.swap_apply_of_ne_of_ne _ _
    · rw [← hg]
      intro h
      simp only [Function.Embedding.toFun_eq_coe, Function.Embedding.smul_apply,
        Equiv.Perm.smul_def, EmbeddingLike.apply_eq_iff_eq] at h 
      apply (lt_iff_not_ge _ _).mp i.prop
      convert le_succ n
      simpa using Fin.veq_of_eq h
    · rw [← hg]
      intro h
      simp only [Function.Embedding.toFun_eq_coe, Function.Embedding.smul_apply,
        Equiv.Perm.smul_def, EmbeddingLike.apply_eq_iff_eq] at h 
      apply (lt_iff_not_ge _ _).mp i.prop
      apply ge_of_eq
      simpa using Fin.veq_of_eq h
#align mul_action.alternating_group_is_fully_minus_two_pretransitive MulAction.alternatingGroup_is_fully_minus_two_pretransitive

/-

variable {α}
lemma aux_lt_iff_lt_or_eq {m n : ℕ} (hmn : m < n) : (m < n - 1) ∨ (m = n - 1) :=
begin
  rw nat.lt_iff_le_not_le,
  cases dec_em (m = n - 1) with h h',
  { exact or.intro_right _ h },
  { apply or.intro_left, apply and.intro,
    { exact nat.le_pred_of_lt hmn},
    { intro h, apply h',
      exact nat.le_antisymm (nat.le_pred_of_lt hmn) h } },
end


/-- A subgroup of equiv.perm α is ⊤ iff it is (fintype.card α - 1)-pretransitive -/
theorem is_fully_minus_one_pretransitive_iff {G : subgroup (equiv.perm α)}
  (hmt : is_multiply_pretransitive ↥G α (fintype.card α - 1)) :
  G = ⊤ :=
begin
  let j : fin (fintype.card α - 1) ↪ fin (fintype.card α) :=
    (fin.cast_le ((fintype.card α).sub_le 1)).to_embedding,
  rw eq_top_iff, intros k _,
  let x : fin(fintype.card α) ↪ α := (fintype.equiv_fin_of_card_eq rfl).symm.to_embedding,
  let hmt_eq := hmt.exists_smul_eq,
  let x' := j.trans x,
  obtain ⟨g, hg'⟩ := hmt_eq x' (k • x'),
  suffices : k = g, { rw this, exact set_like.coe_mem g },

  have hx : ∀ (x : fin(fintype.card α) ↪ α), function.surjective x.to_fun,
  { intro x,
    suffices : function.bijective x.to_fun, exact this.right,
    rw fintype.bijective_iff_injective_and_card,
    exact ⟨embedding_like.injective x, fintype.card_fin (fintype.card α)⟩ },

  have hgk' : ∀ (i : fin (fintype.card α)) (hi : i.val < fintype.card α - 1), (g • x) i = (k • x) i,
  { intros i hi,
    simpa using congr_fun (congr_arg coe_fn hg') ⟨i.val, hi⟩ },
  have hgk : ∀ (i : fin (fintype.card α)), (g • x) i = (k • x) i,
  { intro i,
    cases aux_lt_iff_lt_or_eq i.prop with hi hi,
    { exact hgk' i hi },
    { obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i),
      cases aux_lt_iff_lt_or_eq j.prop with hj hj,
      { exfalso,
        suffices : i = j,
        { rw [← this, ← hi] at hj, refine lt_irrefl _ hj },
        apply embedding_like.injective (g • x),
        rw hgk' j hj, rw hxj },
      { rw ← hxj,
        apply congr_arg,
        apply fin.ext,
        rw [hi, hj] } } },

  apply equiv.perm.ext, intro a,
  obtain ⟨i, rfl⟩ := (hx x) a,
  let zi := hgk i,
  simp only [function.embedding.smul_apply, equiv.perm.smul_def] at zi,
  simp only [function.embedding.to_fun_eq_coe],
  rw ← zi,
  refl
end

variable (α)
/-- The alternating group on α is (fintype.card α - 2)-pretransitive -/
theorem alternating_group_is_fully_minus_two_pretransitive :
  mul_action.is_multiply_pretransitive (alternating_group α) α (fintype.card α - 2) :=
begin
  cases lt_or_ge (fintype.card α) 2 with h2 h2,
  { rw nat.sub_eq_zero_of_le (le_of_lt h2),
    apply is_zero_pretransitive },
  -- fintype.card α ≥ 2
  obtain ⟨n,hn⟩ := nat.le.dest h2,
  have hn' : fintype.card α - 2 = n := norm_num.sub_nat_pos (fintype.card α) 2 n hn,
  rw add_comm at hn,
  have hn_le : n ≤ fintype.card α, { rw ← hn, exact le_self_add },

  apply is_pretransitive.mk,
  rw hn',
  intros x y,

  obtain ⟨x', hx'⟩ :=
    may_extend hn_le (le_of_eq (part_enat.of_fintype α).symm) x,
  obtain ⟨y', hy'⟩ :=
    may_extend hn_le (le_of_eq (part_enat.of_fintype α).symm) y,
  let heq := (equiv_perm_is_fully_pretransitive α).exists_smul_eq,
  obtain ⟨g, hg⟩ := heq x' y',
  cases int.units_eq_one_or g.sign with h h,
  { use ⟨g, equiv.perm.mem_alternating_group.mpr h⟩,
    ext i,
    simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],
    refl },
  { have hg'1 : n + 1 < fintype.card α,
    { rw ← hn, exact nat.lt.base (n + 1) },
    have hg'2 : n < fintype.card α,
    { apply lt_trans _ hg'1, exact lt_add_one n },

    let g' := equiv.swap (y'.to_fun ⟨n+1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩),

    have hg' : g'.sign = -1,
    { rw equiv.perm.is_swap.sign_eq,
      unfold equiv.perm.is_swap,
      use (y'.to_fun ⟨n+1, hg'1⟩), use (y'.to_fun ⟨n, hg'2⟩),
      split,
      { intro h,
        let h' := function.embedding.injective y' h,
        simp only [subtype.mk_eq_mk] at h',
        exact nat.succ_ne_self _ h' },
      refl },

    use g' * g,
    { rw equiv.perm.mem_alternating_group,
      simp only [equiv.perm.sign_mul, h, hg'],
      norm_num },
    ext i, simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],

      simp only [function.embedding.trans_apply, rel_embedding.coe_fn_to_embedding,
        function.embedding.smul_apply, equiv.perm.smul_def],

    change (g' * g) • _ = _,
    rw ← smul_smul,
    simp,
    change (equiv.swap (y'.to_fun ⟨n+1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩))  _ = _,

    refine equiv.swap_apply_of_ne_of_ne _ _,
    { rw ← hg,
      intro h,
      simp only [function.embedding.to_fun_eq_coe, function.embedding.smul_apply,
        equiv.perm.smul_def, embedding_like.apply_eq_iff_eq] at h,
      let h' := fin.veq_of_eq h,
      simp only [fin.val_eq_coe, fin.coe_cast_le] at h',
      let hi := i.prop,
      rw h' at hi,
      simpa only [add_lt_iff_neg_left, not_lt_zero'] using hi } ,
    { rw ← hg,
      intro h,
      simp only [function.embedding.to_fun_eq_coe, function.embedding.smul_apply,
        equiv.perm.smul_def, embedding_like.apply_eq_iff_eq] at h,
      let h' := fin.veq_of_eq h,
      simp only [fin.val_eq_coe, fin.coe_cast_le] at h',
      let hi := i.prop,
      rw h' at hi,
      simpa only [lt_self_iff_false] using hi} },
end

 -/
variable {α}

/-- A subgroup of equiv.perm α which is (fintype.card α - 2)-pretransitive
  contains the alternating group  -/
theorem alternatingGroup_le_of_full_minus_two_pretransitive {G : Subgroup (Equiv.Perm α)}
    (hmt : IsMultiplyPretransitive (↥G) α (Fintype.card α - 2)) : alternatingGroup α ≤ G :=
  by
  cases' Nat.lt_or_ge (Fintype.card α) 2 with hα1 hα
  · -- fintype.card α  < 2
    rw [Nat.lt_succ_iff] at hα1 
    suffices : alternatingGroup α = ⊥; rw [this]; exact bot_le
    rw [← Subgroup.card_le_one_iff_eq_bot]
    suffices Fintype.card ↥(alternatingGroup α) ≤ Fintype.card (Equiv.Perm α)
      by
      apply le_trans this
      rw [Fintype.card_perm]
      exact Nat.factorial_le hα1
    apply Fintype.card_subtype_le
  suffices : ∃ s : Set α, Fintype.card s = Fintype.card α - 2
  obtain ⟨s, hs⟩ := this
  rw [← hs] at hmt 
  let hyp := index_of_fixing_subgroup_of_multiply_pretransitive G α s hmt
  rw [hs, Nat.sub_sub_self hα, Nat.factorial_two] at hyp 
  let hyp' :=
    Nat.mul_le_mul_right 2
      (Nat.le_of_dvd (by rw [Fintype.card_pos_iff]; use 1)
        (Subgroup.index_dvd_card (fixingSubgroup G s)))
  rw [hyp, mul_comm] at hyp' 
  apply large_subgroup_of_perm_contains_alternating
  rw [Fintype.card_equiv (Equiv.refl _)]; exact hyp'
  obtain ⟨s, hs⟩ := Finset.exists_smaller_set (⊤ : Finset α) (Fintype.card α - 2) (Nat.sub_le _ _)
  use s
  simp only [Finset.coe_sort_coe, Fintype.card_coe]
  exact hs.right
#align mul_action.alternating_group_le_of_full_minus_two_pretransitive MulAction.alternatingGroup_le_of_full_minus_two_pretransitive

/-- The alternating group on 3 letters or more acts primitively -/
theorem AlternatingGroup.isPretransitive (h : 3 ≤ Fintype.card α) :
    IsPretransitive (alternatingGroup α) α :=
  by
  rw [is_pretransitive_iff_is_one_pretransitive]
  apply is_multiply_pretransitive_of_higher
  exact alternating_group_is_fully_minus_two_pretransitive α
  apply le_trans _ (Nat.sub_le_sub_right h 2); norm_num
  simp only [part_enat.of_fintype, PartENat.coe_le_coe, Nat.sub_le]
#align mul_action.alternating_group.is_pretransitive MulAction.AlternatingGroup.isPretransitive

/- This lemma proves the trivial blocks property even if the action is not preprimitive
because it is not pretransitive (for fintype.card α ≤ 2)-/
theorem AlternatingGroup.has_trivial_blocks (B : Set α) (hB : IsBlock (alternatingGroup α) B) :
    IsTrivialBlock B := by
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
      have : ∃ c : α, c ∉ {a, b} := by
        by_contra
        push_neg at h 
        have : ({a, b} : Finset α) = Finset.univ :=
          by
          ext c; constructor
          intro hc; exact Finset.mem_univ c
          intro; exact h c
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
      rw [is_block.mk_mem] at hB 
      apply hB g a ha
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
  apply is_preprimitive_of_two_pretransitive
  apply is_multiply_pretransitive_of_higher
  apply alternating_group_is_fully_minus_two_pretransitive
  apply le_trans _ (Nat.sub_le_sub_right h4 2); norm_num
  simp only [part_enat.of_fintype, PartENat.coe_le_coe, Nat.sub_le]
#align mul_action.alternating_group.has_trivial_blocks MulAction.AlternatingGroup.has_trivial_blocks

/-- The alternating group on 3 letters or more acts primitively -/
theorem AlternatingGroup.isPreprimitive (h : 3 ≤ Fintype.card α) :
    IsPreprimitive (alternatingGroup α) α :=
  by
  haveI := alternating_group.is_pretransitive h
  apply IsPreprimitive.mk
  exact alternating_group.has_trivial_blocks
#align mul_action.alternating_group.is_preprimitive MulAction.AlternatingGroup.isPreprimitive

/- lemma alternating_group.is_pretransitive' (h : 3 ≤ fintype.card α) :
  is_pretransitive (alternating_group α) α :=
begin
  classical,
  apply is_pretransitive.mk,
  intros x y,
  cases em (y = x) with hxy hxy,
  use 1, rw [hxy, one_smul],
  suffices : nonempty(finset.erase (finset.erase finset.univ x) y),
  obtain ⟨z, hz⟩ := this,
  simp only [finset.mem_erase, ne.def, finset.mem_univ, and_true] at hz,
  let g := [x,y,z].form_perm,
  suffices : [x,y,z].nodup,
  use g,
  rw equiv.perm.mem_alternating_group,
  apply equiv.perm.is_three_cycle.sign,
  rw ← card_support_eq_three_iff ,
  rw list.support_form_perm_of_nodup _ this _,
  rw list.to_finset_card_of_nodup this,
  simp only [list.length],
  intros t ht, simpa only [and_false] using ht,
  change g • x = y,
  simp only [equiv.perm.smul_def],
  rw list.form_perm_apply_head x y _ this,
  -- nodup
  simp only [list.nodup_cons, list.mem_cons_iff, list.mem_singleton, list.not_mem_nil,
    not_false_iff, list.nodup_nil, and_true, not_or_distrib],
  split, split,
  exact ne_comm.mp hxy, exact ne_comm.mp hz.right, exact ne_comm.mp hz.left,
  { rw ← fintype.card_pos_iff ,
    simp only [fintype.card_coe],
    rw finset.card_erase_of_mem, rw finset.card_erase_of_mem,
    rw nat.sub_sub,
    refine lt_of_lt_of_le _ (nat.sub_le_sub_right h _),
    norm_num,
    exact finset.mem_univ x,
    simp only [finset.mem_erase, ne.def, finset.mem_univ, and_true],
    exact hxy },
end
 -/
end Finite

end MultipleTransitivity

end MulAction

#lint


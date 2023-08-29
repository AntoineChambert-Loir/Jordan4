/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module mul_action_finset
-/

import Jordan.SubMulActions
-- import Jordan.MultipleTransitivity
-- import Jordan.Mathlib.Extensions
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupAction.Embedding
-- import Mathlib.GroupTheory.GroupAction.Basic

open scoped Pointwise 

open MulAction

variable (α : Type*) [DecidableEq α] 
  (G : Type*) [Group G] [MulAction G α]

def Nat.Combination (n : ℕ) := {s : Finset α | s.card = n}
#align nat.finset Nat.Combination

-- theorem Nat.Combination.def  {n : ℕ} (s : n.Combination α) : 
--     (s : Finset α).card = n :=
--   s.prop
-- #align nat.finset.def Nat.Combination.def

theorem Nat.Combination.mem_iff {n : ℕ} {s : Finset α} :
    s ∈ n.Combination α ↔ s.card = n := by 
  unfold Combination
  simp only [Set.mem_setOf_eq]
#align nat.finset_mem.def Nat.Combination.mem_iff

variable {α G} 

-- theorem Finset.smul_card_eq (s : Finset α) (g : G) : 
--   (g • s).card = s.card := by
--   simp only [card_smul_finset]
-- #align finset.smul_card_eq Finset.smul_card_eq

variable (n : ℕ)

theorem Nat.Combination.eq_iff {n : ℕ} (s t : n.Combination α) : 
    s = t ↔ (s : Finset α) = (t : Finset α) := Subtype.ext_iff
  
theorem Nat.Combination.eq_iff_finset_le {n : ℕ} (s t : n.Combination α) : 
    s = t ↔ (s : Finset α) ≤ (t : Finset α) := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← Subtype.coe_inj]
    apply Finset.eq_of_subset_of_card_le h
    rw [s.prop, t.prop]
#align is_eq_iff_is_le Nat.Combination.eq_iff_finset_le

variable (α G)

instance Nat.Combination.SubMulAction : SubMulAction G (Finset α) where
  carrier := n.Combination α
  smul_mem' g s hs := by
    rw [Nat.Combination.mem_iff] at hs ⊢
    rw [← hs]
    rw [Finset.card_smul_finset]
#align nat.finset.mul_action.finset' Nat.Combination.SubMulAction

instance Nat.Combination.MulAction : MulAction G (n.Combination α) := 
  (Nat.Combination.SubMulAction α G n).mulAction
#align nat.finset.mul_action.finset Nat.Combination.MulAction

variable {α G}

-- Why does `Nat.Combination.mulAction_apply` doesn't work?
@[simp]
theorem Nat.combination_mulAction_apply 
    {n : ℕ} {g : G} {s : Finset α} {hs : s ∈ n.Combination α} :
    g • s = (g • (⟨s, hs⟩ : n.Combination α)) := by
  rfl
#align nat.finset.mul_action.finset_apply Nat.combination_mulAction_apply



@[simp]
theorem Nat.combination_mulAction.coe_apply' (g : G) (s : n.Combination α) : 
    ↑(g • s) = g • (↑s : Finset α) :=
  rfl
#align nat.finset.mul_action.coe_apply' Nat.combination_mulAction.coe_apply'

theorem Nat.combination.smul_ne_iff_hasMem_not_mem {s t : n.Combination α} {g : G} :
    g • s ≠ t ↔ ∃ a  ∈ (s : Finset α), a ∉ g⁻¹ • (t : Finset α) := by
  simp only [ne_eq, exists_prop]
  rw [← Finset.not_subset]
  rw [not_iff_not]
  rw [← Nat.combination_mulAction.coe_apply']
  rw [Nat.Combination.eq_iff_finset_le]
  simp only [Nat.combination_mulAction.coe_apply', Finset.le_eq_subset]
  exact Finset.smul_finset_subset_iff
#align smul_ne_iff_has_mem_not_mem Nat.combination.smul_ne_iff_hasMem_not_mem

theorem Nat.combination.mulAction_faithful (hn : 1 ≤ n) (hα : n.succ ≤ PartENat.card α)
      {g : G}
      (hg : (MulAction.toPerm g : Equiv.Perm α) ≠ 1) : 
      ∃ s : n.Combination α, g • s ≠ s := by
  --  mul_action.fixed_by (perm α) (action_on_pairs_of (perm α) α) g ≠ ⊤ :=
  classical
  have zob : ∃ (a : α), (g • a : α) ≠ a := by
    by_contra h
    push_neg at h 
    apply hg
    ext a
    simpa only using h a
  obtain ⟨a, ha⟩ := zob
  suffices : ∃ (s : Set α), s.encard = n ∧ a ∈ s ∧ g • a ∉ s
  obtain ⟨s, hs, has, has'⟩ := this
  have : Set.Finite s := Set.finite_of_encard_eq_coe hs
  rw [Set.Finite.encard_eq_coe_toFinset_card this, cast_inj] at hs 
  use ⟨Set.Finite.toFinset this, hs⟩
  · -- g • s ≠ s,
    simp only [ne_eq]
    rw [Nat.Combination.eq_iff, ← Finset.coe_inj, combination_mulAction.coe_apply', Finset.coe_smul_finset, Set.Finite.coe_toFinset]
    intro h
    apply has'
    rw [← h]
    exact Set.smul_mem_smul_set has

  -- ∃ (s : Set α), s.encard = n ∧ a ∈ s ∧ g • a ∉ s,
  have : ({a} : Set α) ⊆ {g • a}ᶜ := by
    simp only [Set.subset_compl_singleton_iff, Set.mem_singleton_iff]
    exact ha
  have hα' : n ≤ Set.encard ({g • a}ᶜ) := by
    rw [← not_lt, ← WithTop.add_one_lt_succ_iff, not_lt, add_comm, 
      ← Set.encard_singleton (g • a), Set.encard_add_encard_compl, Set.encard_univ]
    rw [← PartENat.withTopEquiv_natCast, PartENat.withTopEquiv_le]
    exact hα
  obtain ⟨s, has, has', hs⟩ := Set.exists_supset_subset_encard_eq this 
    (by rw [Set.encard_singleton, ← Nat.cast_one, Nat.cast_le]
        exact hn) hα'
  use s
  constructor
  · exact hs
  · simp only [Set.singleton_subset_iff, Set.subset_compl_singleton_iff] at has has' 
    exact ⟨has, has'⟩
#align nat.finset.mul_action_faithful Nat.combination.mulAction_faithful


example {s : Set α} {a : α} {g : G} : a ∉ g⁻¹ • s ↔ g • a ∈ sᶜ := by
  rw [Set.mem_smul_set_iff_inv_smul_mem]; rw [inv_inv]; rw [← Set.mem_compl_iff]

example : MulAction G (Fin n ↪ α) := by infer_instance

example : MulAction G (n.Combination α) := by infer_instance

-- variable (α n)
variable (α)

variable (G)

def EmbeddingToFinset.map : (Fin n ↪ α) →ₑ[@id G] n.Combination α
    where
  toFun := fun f : Fin n ↪ α =>
    ⟨Finset.univ.map f, by rw [Nat.Combination.mem_iff, Finset.card_map, Finset.card_fin]⟩
  map_smul' g f := by
    simp only [id.def]
    rw [← Subtype.coe_inj, Subtype.coe_mk] 
    simp only [Nat.combination_mulAction.coe_apply']
    rw [Function.Embedding.smul_def]; rw [Finset.smul_finset_def]
    rw [← Finset.map_map]
    rw [Finset.map_eq_image]
    rfl
#align embedding_to_finset.map EmbeddingToFinset.map

theorem EmbeddingToFinset.map_def (f : Fin n ↪ α) :
    ↑((EmbeddingToFinset.map α G n).toFun f) = Finset.univ.map f :=
  rfl
#align embedding_to_finset.map_def EmbeddingToFinset.map_def

lemma Finset.exists_fin_enum (s : Finset α) (n : ℕ) (hsn : Finset.card s = n) : 
    ∃ f : Fin n ↪ α, Finset.univ.map f = s := by
  have slc : s.toList.length = n := by rw [← hsn, Finset.length_toList]
  rw [← slc]
  use ⟨s.toList.get, by rw [← List.nodup_iff_injective_get]; exact Finset.nodup_toList s⟩
  ext  a
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  rw [← Finset.mem_toList, List.mem_iff_get]
  rfl
  

  
theorem EmbeddingToFinset.map_surjective : 
    Function.Surjective (EmbeddingToFinset.map α G n) := by
  rintro ⟨s, hs⟩
  -- have : Set.Finite (s : Set α) := Finset.finite_toSet s
  rw [Nat.Combination.mem_iff] at hs
  obtain ⟨f, hf⟩ := s.exists_fin_enum α n hs
  use { toFun := f, inj' := f.injective }
  simp only [Function.Embedding.mk_coe, Nat.Combination.eq_iff]
  exact hf
#align embedding_to_finset.map_surjective EmbeddingToFinset.map_surjective

variable [Fintype α]

theorem Nat.Combination_nontrivial (h1 : 0 < n) (h2 : n < Fintype.card α) :
    Nontrivial (n.Combination α) := by
  suffices : Nonempty (n.Combination α)
  obtain ⟨s, hs⟩ := this
  change s.card = n at hs 
  let h'1 := id h1
  rw [← hs, Finset.card_pos] at h'1 ; obtain ⟨a, ha⟩ := h'1
  let h'2 := id h2
  rw [← hs, Finset.card_lt_iff_ne_univ, Ne.def, ← Finset.coe_eq_univ, ← Ne.def,
    Set.ne_univ_iff_exists_not_mem] at h'2 
  obtain ⟨b, hb⟩ := h'2
  let t : Finset α := insert b (Finset.erase s a)
  rw [nontrivial_iff]
  use ⟨s, hs⟩
  use ⟨t, by 
    rw [Nat.Combination.mem_iff]
    rw [Finset.card_insert_of_not_mem]
    rw [Finset.card_erase_of_mem ha]
    rw [hs]; rw [Nat.sub_add_cancel]; exact h1
    intro h; apply hb; apply Finset.erase_subset; exact h⟩
  intro h
  rw [Subtype.mk_eq_mk] at h
  apply hb
  rw [h]
  exact Finset.mem_insert_self b _

  obtain ⟨s, _, hs'⟩ := Finset.exists_smaller_set (Finset.univ : Finset α) n 
    (le_of_lt h2)
  use s
  exact hs'
#align nat.finset_nontrivial Nat.Combination_nontrivial

theorem Nat.finset_isPretransitive_of_multiply_pretransitive {G : Type _} [Group G] [MulAction G α]
    (h : IsMultiplyPretransitive G α n) : IsPretransitive G (n.Finset α) :=
  by
  refine' isPretransitive_of_surjective_map (EmbeddingToFinset.map_surjective α G n) _
  exact h
#align nat.finset_is_pretransitive_of_multiply_pretransitive Nat.finset_isPretransitive_of_multiply_pretransitive

theorem Nat.finset_isPretransitive : IsPretransitive (Equiv.Perm α) (n.Finset α) :=
  by
  apply Nat.finset_isPretransitive_of_multiply_pretransitive
  apply equiv_perm_is_multiply_pretransitive
#align nat.finset_is_pretransitive Nat.finset_isPretransitive

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def Nat.finsetCompl {m : ℕ} (hm : m + n = Fintype.card α) : Nat.finset α n →[G] Nat.finset α m
    where
  toFun := fun ⟨s, hs⟩ =>
    ⟨(sᶜ : Finset α), by
      change sᶜ.card = m; change s.card = n at hs 
      rw [Finset.card_compl, hs, Nat.sub_eq_iff_eq_add _, hm]
      rw [← hm]; apply Nat.le_add_left⟩
  map_smul' := fun g ⟨s, hs⟩ => by
    apply Subtype.coe_injective
    simp only [id.def, Nat.finset.MulAction.coe_apply']
    change (g • s)ᶜ = g • sᶜ
    ext; simp only [Finset.mem_compl]
    change ¬a ∈ g • s ↔ _
    simp [← Finset.inv_smul_mem_iff]
#align nat.finset_compl Nat.finsetCompl

theorem Nat.finsetCompl_bijective {m : ℕ} (hm : m + n = Fintype.card α) :
    Function.Bijective (Nat.finsetCompl α G n hm) :=
  by
  rw [Nat.finsetCompl]
  constructor
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ h
    rw [← Subtype.coe_inj] at h 
    change sᶜ = tᶜ at h 
    apply Subtype.coe_injective
    change s = t
    rw [← compl_compl s]; rw [h]; rw [compl_compl]
  · rintro ⟨s, hs⟩
    have hn : n + m = Fintype.card α := by rw [add_comm]; exact hm
    use Nat.finsetCompl α G m hn ⟨s, hs⟩
    apply Subtype.coe_injective
    change sᶜᶜ = s; rw [compl_compl]
#align nat.finset_compl_bijective Nat.finsetCompl_bijective

/- example (s t : set α) (g : G) : g • s ⊆ t ↔ s ⊆ g⁻¹ • t :=
begin
exact set.set_smul_subset_iff,
end

example (s t : finset α) (g : G) : g • s ⊆ t ↔ s ⊆ g⁻¹ • t :=
begin
simp only [← finset.coe_subset, finset.coe_smul_finset],
exact set.set_smul_subset_iff,
end

lemma exc (s t : n.finset α) (g : equiv.perm α) :
  g • s ≤ t ↔ g • (s : set α) ≤ t :=
begin
simp only [coe_coe, set.le_eq_subset],
change g • ↑s ≤ ↑t ↔ _,
change ⟨g • ↑↑ s,_⟩ ≤ ↑t ↔ _,

end

lemma exa' (s t : n.finset α) (g : equiv.perm α) :
  g • s ≤ t ↔ s ≤ g⁻¹ • t :=
begin
  rw ← exa, rw ← exa,
  exact smul_eq_iff_eq_inv_smul g,
end

lemma exb {s t : n.finset α} {g : equiv.perm α} :
  g • s ≠ t ↔
  ∃ (a : α) (ha : a ∈ (s : finset α)), a ∉ g⁻¹ • (t : finset α) :=
begin
  rw ← finset.not_subset ,
  rw not_iff_comm, rw not_not,
  rw ← nat.finset.mul_action.finset_apply n,
  rw ← finset.le_eq_subset,
  rw subtype.coe_le_coe,
  simp only [subtype.coe_eta],
  rw ← is_eq_iff_is_le,
  rw smul_eq_iff_eq_inv_smul g,
  exact t.prop,
end

example (s : n.finset α) (g : equiv.perm α) :
  g • s ≠ s ↔
  ∃ (a : α) (ha : a ∈ (s : set α)), a ∉ g⁻¹ • (s : set α) :=
begin
  rw ← set.not_subset,
  split,
  { intros h h', apply h,
    let hs := s.prop, rw set.mem_def at hs,
    change finset.card ↑s = n at hs,
    rw ← subtype.coe_eta s s.prop,
    rw ← subtype.coe_inj,
    rw nat.finset.mul_action.finset_apply,
    rw subtype.coe_mk,
    apply finset.eq_of_subset_of_card_le,
    intros x hx,
    change x ∈ finset.image (λ u, g • u) (s : finset α) at hx,
    rw finset.mem_image at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    rw ← finset.mem_coe,
    rw ← set.mem_inv_smul_set_iff,  apply h', exact hy,
    apply le_of_eq, apply symm,

    rw nat.finset.mul_action.finset_apply' α (equiv.perm α) n
        g s hs,
    rw hs,
    rw subtype.coe_eta,
    exact subtype.mem (g • s) },
  { intros h h', apply h,
    intros x hx, rw set.mem_inv_smul_set_iff,
    rw ← h',
    rw ← subtype.coe_eta s s.prop,
    rw [coe_coe, finset.mem_coe],
    rw nat.finset.mul_action.finset_apply,
    -- simp only [equiv.perm.smul_def, coe_coe, finset.mem_coe],
    change g • x ∈ finset.image (λ u, g • u) (s : finset α),
    rw finset.mem_image,
    use x, use hx }
end
 -/
#lint


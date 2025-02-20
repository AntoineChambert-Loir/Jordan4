/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module mul_action_finset
-/

import Jordan.SubMulActions
import Jordan.MultipleTransitivity
import Jordan.Mathlib.Extensions
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.GroupAction.Basic

variable (G : Type*) [Group G] (α : Type*) [MulAction G α]

open scoped Pointwise

open MulAction

/-- The type of combinations of `n` elements of a type `α` -/
def Nat.Combination (n : ℕ) := {s : Finset α | s.card = n}

-- theorem Nat.Combination.def  {n : ℕ} (s : n.Combination α) :
--     (s : Finset α).card = n :=
--   s.prop
--
theorem Nat.Combination.mem_iff {n : ℕ} {s : Finset α} :
    s ∈ n.Combination α ↔ s.card = n := by
  unfold Combination
  simp only [Set.mem_setOf_eq]

variable {α}

-- theorem Finset.smul_card_eq (s : Finset α) (g : G) :
--   (g • s).card = s.card := by
--   simp only [card_smul_finset]
--
theorem Nat.Combination.eq_iff {n : ℕ} (s t : n.Combination α) :
    s = t ↔ (s : Finset α) = (t : Finset α) := Subtype.ext_iff

theorem Nat.Combination.eq_iff_finset_subset {n : ℕ} (s t : n.Combination α) :
    s = t ↔ (s : Finset α) ⊆ (t : Finset α) := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← Subtype.coe_inj]
    apply Finset.eq_of_subset_of_card_le h
    rw [s.prop, t.prop]

variable (α)

variable (n : ℕ)

/-- `Combination α n` as a `SubMulAction` of `Finset α`-/
def Nat.Combination.SubMulAction [DecidableEq α] : SubMulAction G (Finset α) where
  carrier := n.Combination α
  smul_mem' g s hs := by
    rw [Nat.Combination.mem_iff] at hs ⊢
    rw [← hs]
    rw [Finset.card_smul_finset]

instance Nat.Combination.MulAction [DecidableEq α] : MulAction G (n.Combination α) :=
  (Nat.Combination.SubMulAction G α n).mulAction

variable {α G}

-- Why does `Nat.Combination.mulAction_apply` doesn't work?
@[simp]
theorem Nat.combination_mulAction_apply [DecidableEq α]
    {n : ℕ} {g : G} {s : Finset α} {hs : s ∈ n.Combination α} :
    g • s = (g • (⟨s, hs⟩ : n.Combination α)) := by
  rfl

@[simp]
theorem Nat.combination_mulAction.coe_apply' [DecidableEq α] (g : G) (s : n.Combination α) :
    ↑(g • s) = g • (↑s : Finset α) :=
  rfl

theorem Nat.combination.smul_ne_iff_hasMem_not_mem [DecidableEq α] {s t : n.Combination α} {g : G} :
    g • s ≠ t ↔ ∃ a  ∈ (s : Finset α), a ∉ g⁻¹ • (t : Finset α) := by
  simp only [ne_eq, exists_prop]
  rw [← Finset.not_subset]
  rw [not_iff_not]
  rw [← Nat.combination_mulAction.coe_apply']
  rw [Nat.Combination.eq_iff_finset_subset]
  simp only [Nat.combination_mulAction.coe_apply', Finset.le_eq_subset]
  exact Finset.smul_finset_subset_iff

theorem Nat.combination.mulAction_faithful [DecidableEq α] (hn : 1 ≤ n) (hα : n.succ ≤ PartENat.card α)
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
  suffices ∃ (s : Set α), s.encard = n ∧ a ∈ s ∧ g • a ∉ s by
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
    rw [← not_lt, ← WithTop.add_one_lt_coe_succ_iff, not_lt, add_comm,
      ← Set.encard_singleton (g • a), Set.encard_add_encard_compl, Set.encard_univ]
    rw [← PartENat.withTopEquiv_natCast, PartENat.withTopEquiv_le]
    exact hα
  obtain ⟨s, has, has', hs⟩ := Set.exists_superset_subset_encard_eq this (by
    rw [Set.encard_singleton, ← Nat.cast_one, Nat.cast_le]
    exact hn) hα'
  use s
  constructor
  · exact hs
  · simp only [Set.singleton_subset_iff, Set.subset_compl_singleton_iff] at has has'
    exact ⟨has, has'⟩


example {s : Set α} {a : α} {g : G} : a ∉ g⁻¹ • s ↔ g • a ∈ sᶜ := by
  rw [Set.mem_smul_set_iff_inv_smul_mem]; rw [inv_inv]; rw [← Set.mem_compl_iff]

example : MulAction G (Fin n ↪ α) := by infer_instance

example [DecidableEq α] : MulAction G (n.Combination α) := by infer_instance

variable (α G)

/-- The equivariant map from arrangements to combinations -/
def EmbeddingToFinset.map [DecidableEq α] : (Fin n ↪ α) →[G] n.Combination α where
  toFun := fun f : Fin n ↪ α =>
    ⟨Finset.univ.map f, by rw [Nat.Combination.mem_iff, Finset.card_map, Finset.card_fin]⟩
  map_smul' g f := by
    simp only [id]
    rw [← Subtype.coe_inj, Subtype.coe_mk]
    simp only [Nat.combination_mulAction.coe_apply']
    rw [Function.Embedding.smul_def]; rw [Finset.smul_finset_def]
    rw [← Finset.map_map]
    rw [Finset.map_eq_image]
    rfl

variable {n}

theorem EmbeddingToFinset.map_def [DecidableEq α] (f : Fin n ↪ α) :
    ↑((EmbeddingToFinset.map G α n).toFun f) = Finset.univ.map f :=
  rfl

lemma Finset.exists_fin_enum (s : Finset α) (hsn : Finset.card s = n) :
    ∃ f : Fin n ↪ α, Finset.univ.map f = s := by
  have slc : s.toList.length = n := by rw [← hsn, Finset.length_toList]
  rw [← slc]
  use ⟨s.toList.get, by rw [← List.nodup_iff_injective_get]; exact Finset.nodup_toList s⟩
  ext  a
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  rw [← Finset.mem_toList, List.mem_iff_get]
  rfl

theorem EmbeddingToFinset.map_surjective [DecidableEq α] :
    Function.Surjective (EmbeddingToFinset.map G α n) := by
  rintro ⟨s, hs⟩
  -- have : Set.Finite (s : Set α) := Finset.finite_toSet s
  rw [Nat.Combination.mem_iff] at hs
  obtain ⟨f, hf⟩ := s.exists_fin_enum α hs
  use { toFun := f, inj' := f.injective }
  simp only [Function.Embedding.mk_coe, Nat.Combination.eq_iff]
  exact hf

theorem Nat.Combination_nontrivial [DecidableEq α] [Fintype α] (h1 : 0 < n) (h2 : n < Fintype.card α) :
    Nontrivial (n.Combination α) := by
  suffices Nonempty (n.Combination α) by
    obtain ⟨s, hs⟩ := this
    change s.card = n at hs
    let h'1 := id h1
    rw [← hs, Finset.card_pos] at h'1 ; obtain ⟨a, ha⟩ := h'1
    let h'2 := id h2
    rw [← hs, Finset.card_lt_iff_ne_univ, Ne, ← Finset.coe_eq_univ, ← Ne,
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

  obtain ⟨s, _, hs'⟩ := Finset.exists_subset_card_eq h2.le
  use s
  exact hs'

theorem Nat.Combination_isPretransitive_of_IsMultiplyPretransitive [DecidableEq α]
    (h : IsMultiplyPretransitive G α n) :
    IsPretransitive G (n.Combination α) :=
  isPretransitive.of_surjective_map (EmbeddingToFinset.map_surjective G α) h

theorem Nat.Combination_isPretransitive [DecidableEq α] [Fintype α] :
    IsPretransitive (Equiv.Perm α) (n.Combination α) := by
  apply Nat.Combination_isPretransitive_of_IsMultiplyPretransitive
  apply Equiv.Perm.isMultiplyPretransitive

/-- The complement of a combination -/
def Nat.Combination_compl [DecidableEq α] [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α) :
    n.Combination α →[G] m.Combination α where
  toFun := fun ⟨s, hs⟩ =>
    ⟨(sᶜ : Finset α), by
      change sᶜ.card = m; change s.card = n at hs
      rw [Finset.card_compl, hs, Nat.sub_eq_iff_eq_add _, hm]
      rw [← hm]; apply Nat.le_add_left⟩
  map_smul' := fun g ⟨s, hs⟩ => by
    apply Subtype.coe_injective
    simp only [id_eq, combination_mulAction.coe_apply']
    change (g • s)ᶜ = g • sᶜ
    ext a
    simp only [Finset.mem_compl]
    simp [← Finset.inv_smul_mem_iff]

theorem Nat.Combination_compl_bijective [DecidableEq α] [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α) :
    Function.Bijective (Nat.Combination_compl G α hm) := by
  constructor
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ h
    rw [← Subtype.coe_inj] at h
    change sᶜ = tᶜ at h
    apply Subtype.coe_injective
    change s = t
    rw [← compl_compl s]; rw [h]; rw [compl_compl]
  · rintro ⟨s, hs⟩
    have hn : n + m = Fintype.card α := by rw [add_comm]; exact hm
    use Nat.Combination_compl G α hn ⟨s, hs⟩
    apply Subtype.coe_injective
    change sᶜᶜ = s; rw [compl_compl]

/-- The obvious map from a type to its 1-combinations, as an equivariant map -/
def Nat.toCombination_one_equivariant [DecidableEq α] :
    α →[G] Nat.Combination α 1 where
  toFun := fun x => ⟨{x}, Finset.card_singleton x⟩
  map_smul' _ _ := rfl

theorem Nat.bijective_toCombination_one_equivariant [DecidableEq α] :
    Function.Bijective (Nat.toCombination_one_equivariant G α) := by
  constructor
  · intro a b h
    simp only [toCombination_one_equivariant, Combination.eq_iff] at h
    apply Finset.singleton_injective
    exact h
  · rintro ⟨s, hs⟩
    simp [Nat.Combination.mem_iff, Finset.card_eq_one] at hs
    obtain ⟨a, ha⟩ := hs
    use a
    simp only [toCombination_one_equivariant, ha]
    rfl

#lint

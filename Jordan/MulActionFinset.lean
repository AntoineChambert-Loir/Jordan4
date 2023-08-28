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

def Nat.finset (n : ℕ) := {s : Finset α | s.card = n}
#align nat.finset Nat.finset

theorem Nat.finset.def  {n : ℕ} (s : Nat.finset α n) : 
    (s : Finset α).card = n :=
  s.prop
#align nat.finset.def Nat.finset.def

theorem Nat.finset.mem_iff {n : ℕ} {s : Finset α} :
    s ∈ Nat.finset α n ↔ s.card = n := by 
  unfold Nat.finset
  simp only [Set.mem_setOf_eq]
#align nat.finset_mem.def Nat.finset.mem_iff

variable {α G} 


theorem Finset.smul_card_eq (s : Finset α) (g : G) : 
  (s.map ⟨fun x => g • x, MulAction.injective g⟩).card = s.card := by
  change (Finset.image (fun x => g • x) s).card = _
  rw [Finset.card_image_of_injective]
  exact MulAction.injective g
#align finset.smul_card_eq Finset.smul_card_eq

variable (n : ℕ)

theorem is_eq_iff_is_le (s t : n.finset α) : s = t ↔ s ≤ t :=
  by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← Subtype.coe_inj]
    apply Finset.eq_of_subset_of_card_le h
    rw [s.prop, t.prop]
#align is_eq_iff_is_le is_eq_iff_is_le

variable (α G)

instance Nat.finset.SubMulAction : SubMulAction G (Finset α) where
  carrier := n.finset α
  smul_mem' g s hs := by
    rw [Nat.finset.mem_iff] at hs ⊢
    rw [← hs]
    rw [Finset.smul_card_eq]
#align nat.finset.mul_action.finset' Nat.finset.SubMulAction

instance Nat.finset.MulAction : MulAction G (n.finset α) := 
  (Nat.finset.SubMulAction α G n).mulAction
#align nat.finset.mul_action.finset Nat.finset.MulAction

variable {α G}

@[simp]
theorem Nat.finset.MulAction_apply {g : G} {s : Finset α} {hs : s ∈ n.Finset α} :
    (g • (⟨s, hs⟩ : n.Finset α)) = g • s := by
  rfl

-- #align nat.finset.mul_action.finset_apply Nat.finset.MulAction_apply


@[simp]
theorem Nat.finset.MulAction.coe_apply' (g : G) (s : n.Finset α) : ↑(g • s) = g • (↑s : Finset α) :=
  rfl
#align nat.finset.mul_action.coe_apply' Nat.finset.MulAction.coe_apply'

theorem smul_ne_iff_hasMem_not_mem {s t : n.Finset α} {g : G} :
    g • s ≠ t ↔ ∃ (a : α) (ha : a ∈ (s : Finset α)), a ∉ g⁻¹ • (t : Finset α) :=
  by
  rw [← Finset.not_subset]
  rw [not_iff_comm]; rw [Classical.not_not]
  rw [← Nat.finset.MulAction.finset_apply n]
  rw [← Finset.le_eq_subset]
  rw [Subtype.coe_le_coe]
  simp only [Subtype.coe_eta]
  rw [← is_eq_iff_is_le]
  rw [smul_eq_iff_eq_inv_smul g]
  exact t.prop
#align smul_ne_iff_has_mem_not_mem smul_ne_iff_hasMem_not_mem

theorem Nat.finset.mulAction_faithful [Fintype α] (hn : 1 ≤ n) (hα : n < Fintype.card α)
    -- (g : equiv.perm α)
    {g : G}
    (hg : (MulAction.toPerm g : Equiv.Perm α) ≠ 1) : ∃ s : n.Finset α, g • s ≠ s :=
  by
  --  mul_action.fixed_by (perm α) (action_on_pairs_of (perm α) α) g ≠ ⊤ :=
  have : ∃ a : α, g • a ≠ a := by
    by_contra
    push_neg at h 
    apply hg
    ext a
    simpa only using h a
  obtain ⟨a, ha⟩ := this
  suffices : ∃ s : Finset α, s.card = n ∧ {a} ⊆ s ∧ s ⊆ {g • a}ᶜ
  obtain ⟨s, hs, ha, ha'0⟩ := this
  rw [Finset.singleton_subset_iff] at ha 
  have ha' : g • a ∉ s := by
    intro h
    simpa only [Finset.mem_compl, Finset.mem_singleton, eq_self_iff_true, not_true] using ha'0 h
  use ⟨s, hs⟩
  · -- g • s ≠ s,
    intro h
    rw [← Subtype.coe_inj] at h 
    change g • s = s at h 
    suffices : a ∉ s
    exact this ha
    exfalso; apply ha'
    rw [← h]
    rw [Finset.mem_smul_finset]
    use ⟨a, ha, rfl⟩
  -- ∃ (s : finset α), s.card = n ∧ a ∈ s ∧ g • a ∉ s,
  have hA : ({a} : Finset α) ⊆ {g • a}ᶜ :=
    by
    simp only [Finset.singleton_subset_iff, Finset.mem_compl, Finset.mem_singleton]
    intro h; exact ha h.symm
  obtain ⟨s, ha, ha', hs⟩ := Finset.exists_intermediate_set (n - 1) _ hA
  use s
  constructor
  rw [hs, Finset.card_singleton]
  rw [Nat.sub_add_cancel hn]
  constructor; exact ha; exact ha'
  -- n - 1 + {a}.card ≤ {g • a}ᶜ.card
  simp only [Finset.card_singleton, Nat.sub_add_cancel hn, Finset.card_compl]
  exact Nat.le_pred_of_lt hα
#align nat.finset.mul_action_faithful Nat.finset.mulAction_faithful

example {s : Set α} {a : α} {g : G} : a ∉ g⁻¹ • s ↔ g • a ∈ sᶜ := by
  rw [Set.mem_smul_set_iff_inv_smul_mem]; rw [inv_inv]; rw [← Set.mem_compl_iff]

example : MulAction G (Fin n ↪ α) := by infer_instance

example : MulAction G (n.Finset α) := by infer_instance

-- variable (α n)
variable (α)

variable (G)

variable (n)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def EmbeddingToFinset.map : (Fin n ↪ α) →[G] n.Finset α
    where
  toFun := fun f : Fin n ↪ α =>
    ⟨Finset.univ.map f, by
      change (finset.univ.map f).card = n
      rw [Finset.card_map]
      exact Finset.card_fin n⟩
  map_smul' g f := by
    simp only [id.def]
    rw [← Subtype.coe_inj, Subtype.coe_mk, Nat.finset.MulAction.finset_apply]
    rw [Function.Embedding.smul_def]; rw [Finset.smul_finset_def]
    rw [← Finset.map_map]
    rw [Finset.map_eq_image]
    rfl
#align embedding_to_finset.map EmbeddingToFinset.map

theorem EmbeddingToFinset.map_def (f : Fin n ↪ α) :
    ↑((EmbeddingToFinset.map α G n).toFun f) = Finset.univ.map f :=
  rfl
#align embedding_to_finset.map_def EmbeddingToFinset.map_def

theorem EmbeddingToFinset.map_surjective : Function.Surjective (EmbeddingToFinset.map α G n) :=
  by
  rintro ⟨s, hs⟩
  have slc : s.to_list.length = n := by change s.card = n at hs ; rw [← hs];
    exact Finset.length_toList s
  use fun i => s.to_list.nth_le (↑i) (by rw [slc]; exact i.prop)
  -- function.injective
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only [Fin.mk_eq_mk]
  apply list.nodup_iff_nth_le_inj.mp s.nodup_to_list
  exact hij
  -- image of map = given finset set
  ext
  rw [EmbeddingToFinset.map]
  simp only [EquivariantMap.coe_mk, Subtype.coe_mk, Finset.mem_map, Finset.mem_univ,
    Function.Embedding.coeFn_mk, exists_true_left]
  rw [← Finset.mem_toList, List.mem_iff_nthLe, Fin.exists_iff]
  simp_rw [← slc]
  rfl
#align embedding_to_finset.map_surjective EmbeddingToFinset.map_surjective

variable [Fintype α]

theorem Nat.finset_nontrivial (h1 : 0 < n) (h2 : n < Fintype.card α) : Nontrivial (n.Finset α) :=
  by
  suffices : Nonempty (n.finset α)
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
  use t
  change t.card = n
  rw [Finset.card_insert_of_not_mem]
  rw [Finset.card_erase_of_mem ha]
  rw [hs]; rw [Nat.sub_add_cancel]; exact h1
  intro h; apply hb; apply Finset.erase_subset; exact h
  intro h; rw [Subtype.mk_eq_mk] at h ; apply hb; rw [h]; exact Finset.mem_insert_self b _
  obtain ⟨s, hs, hs'⟩ := Finset.exists_smaller_set Finset.univ n _
  use ⟨s, hs'⟩; infer_instance; exact le_of_lt h2
#align nat.finset_nontrivial Nat.finset_nontrivial

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


/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module perm_maximal
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Order.Minimal
import Jordan.Mathlib.Alternating
import Jordan.Mathlib.GroupTheory.Subgroup.Basic
import Jordan.Mathlib.Stabilizer
import Jordan.Mathlib.Set
import Jordan.Primitive
import Jordan.MultipleTransitivity
import Jordan.Jordan
import Jordan.MulActionCombination
import Jordan.StabilizerPrimitive

/-# Maximal subgroups of the symmetric groups

This file establishes that the stabilizer of `s : set α` is a maximal subgroup of the symmetric group `equiv.perm α` when `α` is finite and the cardinality of `s` is not half of that of `α`.
This is the *intransitive case* of the O'Nan-Scott classification.
As a corollary, the action of `equiv.perm α` on finsets of `α` of given cardinality, not equal to the half of that of `α` is primitive.

* `equiv.perm.is_maximal_stab` : the stabilizer of `s : set α` is a maximal subgroup of the symmetric group `equiv.perm α` when `α` is finite and the cardinality of `s` is not half of that of `α`.


-/
/-# Maximal subgroups of the symmetric groups

This file establishes that the stabilizer of `s : set α` is a maximal subgroup of the symmetric group `equiv.perm α` when `α` is finite and the cardinality of `s` is not half of that of `α`.
This is the *intransitive case* of the O'Nan-Scott classification.
As a corollary, the action of `equiv.perm α` on finsets of `α` of given cardinality, not equal to the half of that of `α` is primitive.

* `equiv.perm.is_maximal_stab` : the stabilizer of `s : set α` is a maximal subgroup of the symmetric group `equiv.perm α` when `α` is finite and the cardinality of `s` is not half of that of `α`.


-/
open scoped Pointwise

theorem Nat.add_lt_of_le_lt (a b c d : ℕ) (hab : a ≤ c) (hbd : b < d) : a + b < c + d :=
  by
  apply Nat.lt_of_lt_of_le
  apply Nat.add_lt_add_left _ a; use d; exact hbd
  apply Nat.add_le_add_right hab d

theorem subgroup_of_group_of_order_two
    {G : Type _} [Group G] [Fintype G] (hG : Fintype.card G = 2)
    (H : Subgroup G) : H = ⊥ ∨ H = ⊤ := by
  classical
  cases le_or_lt (Fintype.card H) 1 with
  | inl h =>
    apply Or.intro_left
    apply Subgroup.eq_bot_of_card_le
    rw [Nat.card_eq_fintype_card]
    exact h
  | inr h =>
    apply Or.intro_right
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply le_antisymm
    · apply Nat.le_of_dvd
      refine Fintype.card_pos
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      refine Subgroup.card_subgroup_dvd_card H
    · rw [hG]; exact h

namespace Equiv.Perm

open MulAction

variable {α : Type _} [DecidableEq α] (G : Type _) [Group G] [MulAction G α]

omit [DecidableEq α] in
theorem IsPretransitive.of_partition (s : Set α) :
    (∀ a ∈ s, ∀ b ∈ s, ∃ g : G, g • a = b) →
      (∀ a ∈ sᶜ, ∀ b ∈ sᶜ, ∃ g : G, g • a = b) →
        stabilizer G s ≠ ⊤ →-- (∃ (a b : α) (g : G), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b) →
            IsPretransitive
            G α := by
  intro hs hs' hG
  suffices hss' : ∃ (a b : α) (g : G), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b by
    obtain ⟨a, b, g, ha, hb, hgab⟩ := hss'
    apply IsPretransitive.mk_base a
    intro x
    by_cases hx : x ∈ s
    · exact hs a ha x hx
    · rw [← Set.mem_compl_iff] at hx
      obtain ⟨k, hk⟩ := hs' b hb x hx
      use k * g
      rw [MulAction.mul_smul, hgab, hk]
  --
  by_contra hyp
  push_neg at hyp
  apply hG
  rw [eq_top_iff, MulAction.le_stabilizer_iff_smul_le]
  intro g _
  rintro b ⟨a, ha, hgab⟩
  by_contra hb
  exact hyp a b g ha (Set.mem_compl hb) hgab

theorem swap_mem_stabilizer {a b : α} {s : Set α} (ha : a ∈ s) (hb : b ∈ s) :
    Equiv.swap a b ∈ stabilizer (Equiv.Perm α) s := by
  suffices Equiv.swap a b • s ⊆ s by
    rw [mem_stabilizer_iff]
    apply Set.Subset.antisymm
    exact this
    exact Set.subset_set_smul_iff.mpr this
  rintro _ ⟨x, hx, rfl⟩
  simp only [Equiv.Perm.smul_def]
  cases' em (x = a) with hxa hxa'
  rw [hxa, Equiv.swap_apply_left]; exact hb
  cases' em (x = b) with hxb hxb'
  rw [hxb, Equiv.swap_apply_right]; exact ha
  rw [Equiv.swap_apply_of_ne_of_ne hxa' hxb']; exact hx

theorem ne_one_of_isSwap {f : Equiv.Perm α} (hf : f.IsSwap) : f ≠ 1 := by
  intro h1
  obtain ⟨x, y, hxy, h⟩ := hf
  rw [h1] at h ; apply hxy
  rw [← Equiv.swap_apply_left x y]; rw [← h]
  simp only [Equiv.Perm.coe_one, id]

theorem swap_isSwap_iff {a b : α} : (Equiv.swap a b).IsSwap ↔ a ≠ b :=
  by
  constructor
  · intro h hab
    suffices Equiv.swap a b ≠ 1 by
      apply this
      rw [← hab, Equiv.swap_self]
      ext x; simp only [Equiv.coe_refl, Equiv.Perm.coe_one]
    exact ne_one_of_isSwap h
  · intro h; use a; use b;

variable [Fintype α]

open scoped Classical

/- -- Avoid in preference of using Set.ncard

theorem _root_.Fintype.card_add_compl (s : Set α) :
    Fintype.card s + Fintype.card (sᶜ : Set α) = Fintype.card α :=
  by
  rw [Fintype.card_compl_set]
  rw [add_comm]
  rw [Nat.sub_add_cancel]
  exact set_fintype_card_le_univ s

theorem card_smul_eq (s : Set α) (g : Equiv.Perm α) :
    Fintype.card (g • s : Set α) = Fintype.card s := by
  rw [← Set.coe_toFinset s]
  simp only [← Set.toFinset_card]

  change ((fun x => g • x) '' ↑s.toFinset).toFinset.card = _
  simp_rw [← Finset.coe_image]
  simp only [Finset.toFinset_coe]
  rw [Finset.card_image_of_injective _ (MulAction.injective g)]
-/

omit [DecidableEq α] [Fintype α] in
theorem moves_in
    (G : Subgroup (Equiv.Perm α)) (t : Set α) (hGt : stabilizer (Equiv.Perm α) t < G) :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g : G, g • a = b :=
  by
  intro a ha b hb
  use ⟨Equiv.swap a b, ?_⟩
  · change Equiv.swap a b • a = b
    simp only [Equiv.Perm.smul_def, Equiv.swap_apply_left]
  · apply le_of_lt hGt
    apply swap_mem_stabilizer ha hb

omit [DecidableEq α] [Fintype α] in
theorem stabilizer_ne_top (s : Set α) (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    stabilizer (Equiv.Perm α) s ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hsc
  intro h
  rw [Set.mem_compl_iff] at hb ; apply hb
  have hg : Equiv.swap a b ∈ stabilizer (Equiv.Perm α) s := by rw [h]; apply Subgroup.mem_top
  rw [mem_stabilizer_iff] at hg
  rw [← hg]
  rw [Set.mem_smul_set]
  use a; use ha; apply Equiv.swap_apply_left

theorem stabilizer_empty_eq_top (G : Type _) [Group G] (α : Type _) [MulAction G α] :
    stabilizer G (∅ : Set α) = ⊤ := by
  rw [eq_top_iff]
  intro g; apply imp_intro
  rw [mem_stabilizer_iff]
  simp only [Set.smul_set_empty]

theorem stabilizer_univ_eq_top (G : Type _) [Group G] (α : Type _) [MulAction G α] :
    stabilizer G (_root_.Set.univ : Set α) = ⊤ := by
  rw [eq_top_iff]
  intro g; apply imp_intro
  rw [mem_stabilizer_iff]
  simp only [Set.smul_set_univ]

example : ↑(Nat.card α) ≤ ENat.card α := by
  simp only [Nat.card_eq_fintype_card, ENat.card_eq_coe_fintype_card, le_refl]
theorem stabilizer_nonempty_ne_top (α : Type _) (s : Set α) (hs : s.Nonempty) (hs' : sᶜ.Nonempty) :
    stabilizer (Equiv.Perm α) s ≠ ⊤ :=
  by
  obtain ⟨a : α, ha : a ∈ s⟩ := hs
  obtain ⟨b : α, hb : b ∈ sᶜ⟩ := hs'
  intro h
  let g := Equiv.swap a b
  have h' : g ∈ ⊤ := Subgroup.mem_top g
  rw [← h, mem_stabilizer_iff] at h'
  rw [Set.mem_compl_iff] at hb
  apply hb
  rw [← h']
  use a
  exact And.intro ha (Equiv.swap_apply_left a b)

theorem has_swap_of_lt_stabilizer (s : Set α) (G : Subgroup (Equiv.Perm α))
    (hG : stabilizer (Equiv.Perm α) s < G) :
    ∃ g : Equiv.Perm α, g.IsSwap ∧ g ∈ G := by
  have : ∀ (t : Set α) (_ : 1 < t.ncard), ∃ (g : Equiv.Perm α),
      g.IsSwap ∧ g ∈ stabilizer (Equiv.Perm α) t := by
    intro t ht
    rw [Set.one_lt_ncard_iff] at ht
    obtain ⟨a, b, ha, hb, h⟩ := ht
    simp only [Ne, Subtype.mk_eq_mk] at h
    use Equiv.swap a b
    constructor
    rw [swap_isSwap_iff]; exact h
    apply swap_mem_stabilizer ha hb
  cases' lt_or_le 1 (s.ncard) with h1 h1'
  · obtain ⟨g, hg, hg'⟩ := this s h1
    use g; apply And.intro hg
    exact le_of_lt hG hg'
  cases' lt_or_le 1 sᶜ.ncard with h1c h1c'
  · obtain ⟨g, hg, hg'⟩ := this sᶜ h1c
    use g; apply And.intro hg
    rw [stabilizer_compl] at hg'
    exact le_of_lt hG hg'
  have hα : Nat.card α = 2 := by
    rw [← Set.ncard_add_ncard_compl s] -- , hs1, hsc1]
    convert Nat.one_add 1
    · apply le_antisymm
      assumption
      rw [Nat.succ_le_iff, Set.ncard_pos, Set.nonempty_iff_ne_empty]
      intro h
      apply ne_top_of_lt hG
      rw [h, stabilizer_empty_eq_top]
    · apply le_antisymm
      assumption
      rw [Nat.succ_le_iff, Set.ncard_pos, Set.nonempty_iff_ne_empty]
      intro h
      apply ne_top_of_lt hG
      rw [← stabilizer_compl, h, stabilizer_empty_eq_top]
  cases subgroup_of_group_of_order_two (by
    rw [Fintype.card_perm, ← Nat.card_eq_fintype_card, hα]
    simp) G with
  | inl h =>
    exfalso; exact ne_bot_of_gt hG h
  | inr h =>
    rw [h]
    rw [← stabilizer_univ_eq_top (Equiv.Perm α) α]
    apply this
    rw [Set.ncard_univ, hα]
    norm_num

theorem Subtype.image_preimage_of_val {α : Type*} {s B : Set α} (h : B ⊆ s) :
    Subtype.val '' (Subtype.val ⁻¹' B : Set s) = B := by
  apply Set.Subset.antisymm (Set.image_preimage_subset Subtype.val B)
  intro x hx
  use ⟨x, h hx⟩
  simp only [hx, Set.mem_preimage, Subtype.coe_mk, eq_self_iff_true, and_self_iff]

-- Move to Blocks.lean
omit [DecidableEq α] in
theorem _root_.MulAction.isTrivialBlock_or_2_mul_ncard_le_card  {G : Type*} [Group G] [MulAction G α] [IsPretransitive G α]
    {B : Set α} (hB : IsBlock G B) :
    IsTrivialBlock B ∨ (2 * Set.ncard B ≤ Nat.card α) := by
  by_cases hBne : Set.Nonempty B
  · obtain ⟨m, hm⟩ := ncard_of_block_divides hB hBne
    match m with
    | 0 =>
      left; left
      simp only [mul_zero, Finite.card_eq_zero_iff] at hm
      exact Set.subsingleton_of_subsingleton
    | 1 =>
      left; right
      simp only [mul_one] at hm
      rw [Set.eq_top_iff_ncard, ← hm, Nat.card_eq_fintype_card]
    | m + 2 =>
      right
      rw [hm, mul_comm, add_comm, mul_add]
      apply Nat.le_add_right
  · simp only [Set.not_nonempty_iff_eq_empty] at hBne
    rw [hBne]
    left; left
    exact Set.subsingleton_empty

theorem isMaximalStab' (s : Set α) (h0 : s.Nonempty) (h1 : sᶜ.Nonempty)
    (hα : s.ncard < sᶜ.ncard) :
    Subgroup.IsMaximal (stabilizer (Equiv.Perm α) s) := by
  constructor; constructor
  -- To prove that `stabilizer (Equiv.Perm α) s` is maximal,
  -- we need to prove that it is `≠ ⊤`
  exact stabilizer_ne_top s h0 h1
  -- … and that every strict over-subgroup `G` is equal to `⊤`
  intro G hG
  -- We need to prove that G = ⊤
  -- We know that `G` contains a swap
  obtain ⟨g, hg_swap, hg⟩ := has_swap_of_lt_stabilizer s G hG
  -- By Jordan's theorem `jordan_swap`,
  -- it suffices to prove that G acts primitively
  apply jordan_swap _ g hg_swap hg
  -- First, we prove that G acts transitively
  have : IsPretransitive G α := by
    apply IsPretransitive.of_partition G s
    · apply moves_in; exact hG
    · apply moves_in; rw [stabilizer_compl]; exact hG
    · intro h
      apply lt_irrefl G; apply lt_of_le_of_lt _ hG
      --  G ≤ stabilizer (equiv.perm α) s,
      intro g hg
      rw [mem_stabilizer_iff]
      rw [← Subgroup.coe_mk G g hg]
      change (⟨g, hg⟩ : ↥G) • s = s
      rw [← mem_stabilizer_iff]
      change _ ∈ stabilizer (↥G) s
      rw [h]
      trivial
  apply IsPreprimitive.mk
  -- We now have to prove that all blocks of `G` are trivial
  -- The proof needs 4 steps

  /- Step 1 : No block is equal to sᶜ
       This uses that Fintype.card s < Fintype.card sᶜ.
       In the equality case, Fintype.card s = Fintype.card sᶜ,
       it would be possible that sᶜ is a block, then G is a wreath product,
       — this is case (b) of the O'Nan-Scott classification
       of maximal subgroups of the symmetric group -/
  have hB_ne_sc : ∀ (B : Set α) (_ : IsBlock G B), ¬B = sᶜ := by
    intro B hB hBsc
    cases MulAction.isTrivialBlock_or_2_mul_ncard_le_card hB with
    | inl hB_triv =>
      cases hB_triv with
      | inl hB_subsingleton =>
        have : Set.ncard B ≤ 1 := by
          rw [Set.ncard_le_one_iff_eq]
          apply Set.Subsingleton.eq_empty_or_singleton
          exact hB_subsingleton
        apply not_lt.mpr this
        rw [hBsc]
        apply lt_of_le_of_lt _ hα
        rw [Nat.succ_le_iff, Set.ncard_pos]
        exact h0
      | inr hB_top =>
        apply Set.not_nonempty_empty
        simp only [hBsc, Set.top_eq_univ, Set.compl_univ_iff] at hB_top
        rw [← hB_top]
        exact h0
    | inr hcard =>
      apply not_lt.mpr hcard
      rw [← Set.ncard_add_ncard_compl B, two_mul, add_lt_add_iff_left,
        hBsc, compl_compl]
      exact hα

  -- Step 2 : A block contained in sᶜ is a subsingleton
  have hB_not_le_sc : ∀ (B : Set α) (_ : IsBlock G B) (_ : B ⊆ sᶜ), B.Subsingleton := by
    intro B hB hBsc
    rw [← Subtype.image_preimage_of_val hBsc]
    -- suffices B = Subtype.val '' (Subtype.val ⁻¹' B : Set (sᶜ : Set α)) by
    -- rw [this]
    apply Set.Subsingleton.image
    suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set (sᶜ : Set α)) by
      apply Or.resolve_right this
      intro hB'
      apply hB_ne_sc B hB
      apply Set.Subset.antisymm hBsc
      intro x hx
      rw [← Subtype.coe_mk x _, ← Set.mem_preimage, hB', Set.top_eq_univ]
      apply Set.mem_univ
      exact hx
    -- IsTrivialBlock (Subtype.val ⁻¹' B : Set (sᶜ : Set α)),
    suffices IsPreprimitive (stabilizer G (sᶜ : Set α)) (sᶜ : Set α) by
      refine IsPreprimitive.has_trivial_blocks this ?_
      -- is_block (coe ⁻¹' B : set (sᶜ : set α))
      let φ' : stabilizer G (sᶜ : Set α) → G := Subtype.val
      let f' : (sᶜ : Set α) →ₑ[φ'] α := {
        toFun := Subtype.val
        map_smul' := fun ⟨m, _⟩ x => by
          simp only [SMul.smul_stabilizer_def] }
      apply MulAction.IsBlock_preimage f' hB
    -- is_preprimitive (stabilizer G (sᶜ : set α)) (sᶜ : set α)
    let φ : stabilizer G (sᶜ : Set α) → Equiv.Perm (sᶜ : Set α) := MulAction.toPerm
    let f : (sᶜ : Set α) →ₑ[φ] (sᶜ : Set α) := {
      toFun := id
      map_smul' := fun g x => by
        simp only [φ, id, Equiv.Perm.smul_def, toPerm_apply] }
    have hf : Function.Bijective f := Function.bijective_id
    rw [isPreprimitive_of_bijective_map_iff _ hf]
    apply Equiv.Perm.isPreprimitive
    -- Function.Surjective φ,
    -- will need to adjust for alternating_group
    intro g
    use! Equiv.Perm.ofSubtype g
    · apply le_of_lt hG
      rw [← stabilizer_compl]
      convert ofSubtype_mem_stabilizer _ g
    · rw [mem_stabilizer_iff]
      change Equiv.Perm.ofSubtype g • sᶜ = sᶜ
      rw [← mem_stabilizer_iff]
      convert ofSubtype_mem_stabilizer _ g
    · ext ⟨x, hx⟩
      change Equiv.Perm.ofSubtype g • x = _
      simp only [Equiv.Perm.smul_def]
      rw [Equiv.Perm.ofSubtype_apply_of_mem]

  -- Step 3 : A block contained in s is a subsingleton
  have hB_not_le_s : ∀ (B : Set α) (_ : IsBlock G B), B ⊆ s → B.Subsingleton := by
    intro B hB hBs
    --  suffices hB_coe : B = Subtype.val '' (Subtype.val ⁻¹' B : Set s) by
    suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set s) by
      cases' this with hB' hB'
      · -- trivial case
        rw [← Subtype.image_preimage_of_val hBs]
        apply Set.Subsingleton.image
        exact hB'
      · -- coe ⁻¹' B = s
        have hBs' : B = s := by
          apply Set.Subset.antisymm hBs
          intro x hx
          rw [← Subtype.coe_mk x _]
          rw [← Set.mem_preimage]
          rw [hB']
          rw [Set.top_eq_univ]
          apply Set.mem_univ
          exact hx
        have : ∃ g' ∈ G, g' • s ≠ s := by
          by_contra h
          apply ne_of_lt hG
          push_neg at h
          apply le_antisymm
          exact le_of_lt hG
          intro g' hg'; rw [mem_stabilizer_iff]; exact h g' hg'
        obtain ⟨g', hg', hg's⟩ := this
        cases' IsBlock.def_one.mp hB ⟨g', hg'⟩ with h h
        · -- case g' • B = B : absurd, since B = s and choice of g'
          exfalso
          apply hg's; rw [← hBs']; exact h
        · -- case g' • B disjoint from B
          suffices (g' • B).Subsingleton by
            apply Set.subsingleton_of_image _ B this
            apply Function.Bijective.injective
            apply MulAction.bijective
          apply hB_not_le_sc ((⟨g', hg'⟩ : G) • B)
          exact IsBlock_of_block _ hB
          rw [← hBs']
          apply Disjoint.subset_compl_right
          exact h
      -- IsTrivialBlock (coe ⁻¹' B : set s),
    suffices IsPreprimitive (stabilizer G s) s by
      apply IsPreprimitive.has_trivial_blocks this
      -- is_block (coe ⁻¹' B : set s)
      let φ' : stabilizer G s → G := Subtype.val
      let f' : s →ₑ[φ'] α := {
        toFun := Subtype.val
        map_smul' := fun ⟨m, _⟩ x => by
          simp only [SMul.smul_stabilizer_def] }
      apply MulAction.IsBlock_preimage f' hB
    -- IsPreprimitive (stabilizer G s) s
    let φ : stabilizer G s → Equiv.Perm s := MulAction.toPerm
    let f : s →ₑ[φ] s := {
        toFun := id
        map_smul' := fun g x => by
          simp only [φ, id, Equiv.Perm.smul_def, toPerm_apply] }
    have hf : Function.Bijective f := Function.bijective_id
    rw [isPreprimitive_of_bijective_map_iff _ hf]
    apply Equiv.Perm.isPreprimitive
    -- Function.Surjective φ,
    -- We will need to adjust this part for the alternating group
    intro g
    use! Equiv.Perm.ofSubtype g
    · apply le_of_lt hG
      apply ofSubtype_mem_stabilizer
    · apply ofSubtype_mem_stabilizer
    · ext ⟨x, hx⟩
      change Equiv.Perm.ofSubtype g • x = _
      simp only [Equiv.Perm.smul_def]
      rw [Equiv.Perm.ofSubtype_apply_of_mem]
  intro B hB
  unfold IsTrivialBlock
  rw [or_iff_not_imp_left]
  intro hB'
  obtain ⟨a, ha, ha'⟩ :=
    Set.not_subset_iff_exists_mem_not_mem.mp fun h => hB' ((hB_not_le_sc B hB) h)
  rw [Set.not_mem_compl_iff] at ha'
  obtain ⟨b, hb, hb'⟩ :=
    Set.not_subset_iff_exists_mem_not_mem.mp fun h => hB' ((hB_not_le_s B hB) h)
  rw [← Set.mem_compl_iff] at hb'
  have hsc_le_B : sᶜ ⊆ B := by
    intro x hx'
    suffices ∃ k : fixingSubgroup (Equiv.Perm α) s, k • b = x by
      obtain ⟨⟨k, hk⟩, hkbx : k • b = x⟩ := this
      suffices k • B = B by
        rw [← hkbx, ← this, Set.smul_mem_smul_set_iff]
        exact hb
      -- k • B = B,
      apply or_iff_not_imp_right.mp (IsBlock.def_one.mp hB ⟨k, _⟩)
      · rw [Set.not_disjoint_iff_nonempty_inter]
        change (k • B ∩ B).Nonempty
        use a
        constructor
        rw [mem_fixingSubgroup_iff] at hk
        rw [← hk a ha']
        exact Set.smul_mem_smul_set ha
        exact ha
        · -- ↑k ∈ G
          apply le_of_lt hG
          exact fixingSubgroup_le_stabilizer (Equiv.Perm α) s hk
    · -- ∃ (k : fixing_subgroup (equiv.perm α) s), k • b = x,
      suffices
        IsPretransitive (fixingSubgroup (Equiv.Perm α) s)
          (SubMulAction.ofFixingSubgroup (Equiv.Perm α) s) by
        obtain ⟨k, hk⟩ :=
          exists_smul_eq (fixingSubgroup (Equiv.Perm α) s)
           (⟨b, hb'⟩ : SubMulAction.ofFixingSubgroup (Equiv.Perm α) s) ⟨x, hx'⟩
        use k
        rw [← Subtype.coe_inj, SubMulAction.val_smul] at hk
        exact hk
      -- IsPretransitive …
      rw [isPretransitive_iff_is_one_pretransitive]
      apply remaining_transitivity'
      · exact Equiv.Perm.isMultiplyPretransitive α (Nat.card α)
      · rw [add_comm]
        rw [← Set.ncard_add_ncard_compl s]
        simp only [add_le_add_iff_left]
        rw [Nat.succ_le_iff, Set.ncard_pos]
        exact h1
      simp only [Nat.card_eq_fintype_card, ENat.card_eq_coe_fintype_card, le_refl]
  -- Conclusion of the proof : B = ⊤
  rw [eq_top_iff]
  intro x _
  obtain ⟨b, hb⟩ := h1
  obtain ⟨⟨g, hg⟩, hgbx : g • b = x⟩ := exists_smul_eq G b x
  suffices g • B = B by
    rw [← hgbx, ← this, Set.smul_mem_smul_set_iff]
    exact hsc_le_B hb
  -- g • B = B,
  apply or_iff_not_imp_right.mp (IsBlock.def_one.mp hB ⟨g, hg⟩)
  rw [Set.not_disjoint_iff_nonempty_inter]
  change (g • B ∩ B).Nonempty
  apply Set.ncard_pigeonhole
  -- card B + card (g • B) = card B + card B
  -- ... ≥ card sᶜ + card sᶜ
  -- ... > card s + card s ᶜ = card α
  rw [← Nat.card_eq_fintype_card, ← Set.ncard_add_ncard_compl s]
--   rw [← Fintype.card_add_compl s]
  apply Nat.lt_of_lt_of_le
  rw [Nat.add_lt_add_iff_right] -- _ _ sᶜ.ncard]
  · exact hα
  · rw [MulAction.smul_set_ncard_eq]
    simp only [← two_mul]
    apply Nat.mul_le_mul_left
    exact Set.ncard_le_ncard hsc_le_B (Set.toFinite B)


/-- stabilizer (equiv.perm α) s is a maximal subgroup of equiv.perm α,
provided s ≠ ⊥, s ≠ ⊤ and fintype.card α ≠ 2 * fintype.card ↥s) -/
theorem isMaximalStab (s : Set α) (h0 : s.Nonempty) (h1 : sᶜ.Nonempty)
    (hα : Fintype.card α ≠ 2 * s.ncard) :
    Subgroup.IsMaximal (stabilizer (Equiv.Perm α) s) := by
  cases' Nat.lt_trichotomy s.ncard sᶜ.ncard with hs hs'
  · exact Equiv.Perm.isMaximalStab' s h0 h1 hs
  cases' hs' with hs hs
  · exfalso; apply hα
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_add_ncard_compl s, two_mul, ← hs]
  · rw [← compl_compl s] at h0
    rw [← stabilizer_compl]
    apply Equiv.Perm.isMaximalStab' (sᶜ) h1 h0
    rw [compl_compl]
    exact hs

end Equiv.Perm

namespace MulAction

open Pointwise

variable {α : Type _} [DecidableEq α] [Fintype α]

omit [Fintype α] in
theorem Nat.Combination.stabilizer_eq
    {G : Type*} [Group G] [MulAction G α] (s : Nat.Combination α n) :
    stabilizer G s = stabilizer G (s : Set α) := by
  ext g
  simp only [mem_stabilizer_iff]
  rw [← Subtype.coe_inj, ← Finset.coe_smul_finset]
  simp only [← Finset.coe_smul_finset, ← Finset.coe_inj]
  simp only [Nat.combination_mulAction.coe_apply', Finset.coe_smul_finset]

/-- The action of `Equiv.Perm α` on `n.Combination α` is preprimitive
provided 1 ≤ n < #α and #α ≠ 2*n -/
theorem Nat.Combination_isPreprimitive
    {n : ℕ} (h_one_le : 1 ≤ n) (hn : n < Fintype.card α)
    (hα : Fintype.card α ≠ 2 * n) :
    IsPreprimitive (Equiv.Perm α) (n.Combination α) := by
--  classical
  cases' Nat.eq_or_lt_of_le h_one_le with h_one h_one_lt
  · -- n = 1 :
    rw [← h_one]
    apply isPreprimitive_of_surjective_map
      (Nat.bijective_toCombination_one_equivariant _ α).surjective
    exact Equiv.Perm.isPreprimitive α
  -- h_one_lt : 1 < n
  have : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    exact lt_trans h_one_lt hn
  haveI ht : IsPretransitive (Equiv.Perm α) (n.Combination α) :=
    n.Combination_isPretransitive α
  have : Nontrivial (n.Combination α) :=
    n.Combination_nontrivial α (lt_trans (Nat.lt_succ_self 0) h_one_lt) hn
  -- have : Nonempty (n.Combination α) := by
  --   exact Nontrivial.to_nonempty
  obtain ⟨sn : n.Combination α⟩ := this.to_nonempty
  -- Nontrivial.to_nonempty
  let s := sn.val
  let hs : s.card = n := sn.prop
  -- have hs : (s : finset α).card = n := s.prop,
  rw [← maximal_stabilizer_iff_preprimitive (Equiv.Perm α) sn]
  have : stabilizer (Equiv.Perm α) sn =
      stabilizer (Equiv.Perm α) (s : Set α) := by
    ext g
    simp only [mem_stabilizer_iff]
    rw [← Subtype.coe_inj]
    change g • s = s ↔ _
    rw [← Finset.coe_smul_finset, ← Finset.coe_inj]
  rw [this]
  apply Equiv.Perm.isMaximalStab (s : Set α)
  · simp only [Finset.coe_nonempty, ← Finset.card_pos, hs]
    apply lt_trans one_pos h_one_lt
  · simp only [← Finset.coe_compl, Finset.coe_nonempty,
      ← Finset.card_compl_lt_iff_nonempty, compl_compl, hs]
    exact hn
  · simp only [Set.ncard_coe_Finset, ne_eq]
    simp only [Finset.coe_sort_coe, Fintype.card_coe, hs]
    exact hα

end MulAction

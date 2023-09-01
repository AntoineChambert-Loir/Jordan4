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
#align nat.add_lt_of_le_lt Nat.add_lt_of_le_lt

theorem subgroup_of_group_of_order_two 
    {G : Type _} [Group G] [Fintype G] (hG : Fintype.card G = 2)
    (H : Subgroup G) : H = ⊥ ∨ H = ⊤ := by
  classical
  cases le_or_lt (Fintype.card H) 1 with 
  | inl h => 
    apply Or.intro_left
    apply Subgroup.eq_bot_of_card_le
    exact h
  | inr h =>
    apply Or.intro_right
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm
    · apply Nat.le_of_dvd
      refine' Fintype.card_pos
      refine' Subgroup.card_subgroup_dvd_card H
    · rw [hG]; exact h
#align subgroup_of_group_of_order_two subgroup_of_group_of_order_two

namespace Equiv.Perm

open MulAction

variable {α : Type _} [DecidableEq α] (G : Type _) [Group G] [MulAction G α]

theorem IsPretransitive.of_partition (s : Set α) :
    (∀ a ∈ s, ∀ b ∈ s, ∃ g : G, g • a = b) →
      (∀ a ∈ sᶜ, ∀ b ∈ sᶜ, ∃ g : G, g • a = b) →
        stabilizer G s ≠ ⊤ →-- (∃ (a b : α) (g : G), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b) →
            IsPretransitive
            G α :=
  by
  intro hs hs' hG
  suffices hss' : ∃ (a b : α) (g : G), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b
  obtain ⟨a, b, g, ha, hb, hgab⟩ := hss'
  apply IsPretransitive.mk_base a
  intro x
  cases' em (x ∈ s) with hx hx'
  exact hs a ha x hx
  rw [← Set.mem_compl_iff] at hx' 
  obtain ⟨k, hk⟩ := hs' b hb x hx'
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
#align equiv.perm.is_pretransitive.of_partition Equiv.Perm.IsPretransitive.of_partition

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
#align equiv.perm.swap_mem_stabilizer Equiv.Perm.swap_mem_stabilizer

theorem ne_one_of_isSwap {f : Equiv.Perm α} (hf : f.IsSwap) : f ≠ 1 := by
  intro h1
  obtain ⟨x, y, hxy, h⟩ := hf
  rw [h1] at h ; apply hxy
  rw [← Equiv.swap_apply_left x y]; rw [← h]
  simp only [Equiv.Perm.coe_one, id.def]
#align equiv.perm.ne_one_of_is_swap Equiv.Perm.ne_one_of_isSwap

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
#align equiv.perm.swap_is_swap_iff Equiv.Perm.swap_isSwap_iff

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
#align fintype.card_add_compl Fintype.card_add_compl

theorem card_smul_eq (s : Set α) (g : Equiv.Perm α) :
    Fintype.card (g • s : Set α) = Fintype.card s := by
  rw [← Set.coe_toFinset s]
  simp only [← Set.toFinset_card]
  
  change ((fun x => g • x) '' ↑s.toFinset).toFinset.card = _
  simp_rw [← Finset.coe_image]
  simp only [Finset.toFinset_coe]
  rw [Finset.card_image_of_injective _ (MulAction.injective g)]
#align equiv.perm.card_smul_eq Equiv.Perm.card_smul_eq
-/

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
#align equiv.perm.moves_in Equiv.Perm.moves_in

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
#align equiv.perm.stabilizer_ne_top Equiv.Perm.stabilizer_ne_top

theorem stabilizer_empty_eq_top (G : Type _) [Group G] (α : Type _) [MulAction G α] :
    stabilizer G (∅ : Set α) = ⊤ := by
  rw [eq_top_iff]
  intro g; apply imp_intro
  rw [mem_stabilizer_iff]
  simp only [Set.smul_set_empty]
#align equiv.perm.stabilizer_empty_eq_top Equiv.Perm.stabilizer_empty_eq_top

theorem stabilizer_univ_eq_top (G : Type _) [Group G] (α : Type _) [MulAction G α] :
    stabilizer G (_root_.Set.univ : Set α) = ⊤ := by
  rw [eq_top_iff]
  intro g; apply imp_intro
  rw [mem_stabilizer_iff]
  simp only [Set.smul_set_univ]
#align equiv.perm.stabilizer_univ_eq_top Equiv.Perm.stabilizer_univ_eq_top

example : ↑(Nat.card α) ≤ PartENat.card α := by
  simp only [Nat.card_eq_fintype_card, PartENat.card_eq_coe_fintype_card, le_refl]
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
#align equiv.perm.stabilizer_nonempty_ne_top Equiv.Perm.stabilizer_nonempty_ne_top

theorem has_swap_of_lt_stabilizer (s : Set α) (G : Subgroup (Equiv.Perm α))
    (hG : stabilizer (Equiv.Perm α) s < G) : 
    ∃ g : Equiv.Perm α, g.IsSwap ∧ g ∈ G := by
  have : ∀ (t : Set α) (_ : 1 < t.ncard), ∃ (g : Equiv.Perm α), 
      g.IsSwap ∧ g ∈ stabilizer (Equiv.Perm α) t := by
    intro t ht
    rw [Set.one_lt_ncard_iff] at ht
    obtain ⟨a, b, ha, hb, h⟩ := ht
    simp only [Ne.def, Subtype.mk_eq_mk] at h 
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
#align equiv.perm.has_swap_of_lt_stabilizer Equiv.Perm.has_swap_of_lt_stabilizer

theorem isMaximalStab' (s : Set α) (h0 : s.Nonempty) (h1 : sᶜ.Nonempty)
    (hα : s.ncard < sᶜ.ncard) :
    Subgroup.IsMaximal (stabilizer (Equiv.Perm α) s) :=
  by
  constructor; constructor
  -- stabilizer (equiv.perm α) s ≠ ⊤
  exact stabilizer_ne_top s h0 h1
  -- ∀ (G : subgroup (equiv.perm α)), stabilizer (equiv.perm α) s < b) → b = ⊤
  intro G hG
  -- We need to prove that G = ⊤
  -- G contains a swap
  obtain ⟨g, hg_swap, hg⟩ := has_swap_of_lt_stabilizer s G hG
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply jordan_swap _ g hg_swap hg
  -- G acts transitively
  have : IsPretransitive G α :=
    by
    apply Equiv.Perm.IsPretransitive.of_partition G s
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
  -- The proof needs 4 steps 
  /- Step 1 : No block is equal to sᶜ
       This uses that fintype.card s < fintype.card sᶜ.
       In the equality case, fintype.card s = fintype.card sᶜ, it is possible that B = sᶜ,
       then G is the wreath product,
       this is case (b) of the O'Nan-Scott classification of max'l subgroups of the symmetric group -/
  have hB_ne_sc : ∀ (B : Set α) (_ : IsBlock G B), ¬B = sᶜ := by
    intro B hB hBsc
    obtain ⟨b, hb⟩ := h1; rw [← hBsc] at hb 
    obtain ⟨a, ha⟩ := h0
    obtain ⟨k, hk⟩ := exists_smul_eq G b a
    suffices B.ncard ≤ s.ncard by
      apply Nat.lt_irrefl B.ncard
      apply lt_of_le_of_lt this
      rw [hBsc]
      exact hα
    rw [← smul_set_ncard_eq k B]
    apply Set.ncard_le_of_subset _ (Set.toFinite s)
    change k • B ⊆ s
    rw [← Set.disjoint_compl_right_iff_subset, ← hBsc]
    apply or_iff_not_imp_left.mp (IsBlock.def_one.mp hB k)
    intro h
    apply Set.not_mem_empty a
    rw [← Set.inter_compl_self s]
    constructor
    exact ha
    rw [← hk, ← hBsc, ← h, Set.smul_mem_smul_set_iff]
    exact hb
  -- Step 2 : A block contained in sᶜ is a subsingleton
  have hB_not_le_sc : ∀ (B : Set α) (_ : IsBlock G B) (_ : B ⊆ sᶜ), B.Subsingleton := by
    intro B hB hBsc
    suffices : B = Subtype.val '' (Subtype.val ⁻¹' B : Set (sᶜ : Set α))
    rw [this]
    apply Set.Subsingleton.image
    suffices : IsTrivialBlock (Subtype.val ⁻¹' B : Set (sᶜ : Set α))
    apply Or.resolve_right this
    intro hB'
    apply hB_ne_sc B hB
    apply Set.Subset.antisymm hBsc
    intro x hx
    rw [← Subtype.coe_mk x _, ← Set.mem_preimage, hB', Set.top_eq_univ]
    apply Set.mem_univ
    exact hx
    · -- IsTrivialBlock (Subtype.val ⁻¹' B : Set (sᶜ : Set α)),
      suffices : IsPreprimitive (stabilizer G (sᶜ : Set α)) (sᶜ : Set α)
      refine' IsPreprimitive.has_trivial_blocks this _
      -- is_block (coe ⁻¹' B : set (sᶜ : set α))
      let φ' : stabilizer G (sᶜ : Set α) → G := Subtype.val
      let f' : (sᶜ : Set α) →ₑ[φ'] α :=
        { toFun := Subtype.val
          map_smul' := fun ⟨m, _⟩ x => by
            simp only [HasSmul.smul_stabilizer_def] }
      apply MulAction.IsBlock_preimage f' hB
      -- is_preprimitive (stabilizer G (sᶜ : set α)) (sᶜ : set α)
      let φ : stabilizer G (sᶜ : Set α) → Equiv.Perm (sᶜ : Set α) := MulAction.toPerm
      let f : (sᶜ : Set α) →ₑ[φ] (sᶜ : Set α) :=
        { toFun := id
          map_smul' := fun g x => by simp only [id.def, Equiv.Perm.smul_def, toPerm_apply] }
      have hf : Function.Bijective f := Function.bijective_id
      rw [isPreprimitive_of_bijective_map_iff _ hf]
      apply Equiv.Perm.isPreprimitive 
      -- Function.Surjective φ,
      -- will need to adjust for alternating_group
      intro g
      suffices hg : ofSubtype g ∈ stabilizer (Perm α) sᶜ 
--      rw [Set.coe_eq_subtype] at g
      use! Equiv.Perm.ofSubtype g
      · apply le_of_lt hG
        rw [← stabilizer_compl]
        exact hg
      · rw [mem_stabilizer_iff]
        change Equiv.Perm.ofSubtype g • sᶜ = sᶜ
        rw [← mem_stabilizer_iff]
        exact hg
      · ext ⟨x, hx⟩
        change Equiv.Perm.ofSubtype g • x = _
        simp only [Equiv.Perm.smul_def]
        rw [Equiv.Perm.ofSubtype_apply_of_mem]
      · -- equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) sᶜ
        rw [mem_stabilizer_iff]
        apply Set.Subset.antisymm
        · intro x
          rw [Set.mem_smul_set]
          rintro ⟨y, hy, rfl⟩
          simp only [Equiv.Perm.smul_def]
          rw [Equiv.Perm.ofSubtype_apply_of_mem g hy]
          refine' Subtype.mem _
        · intro x hx
          obtain ⟨y, hy⟩ := Equiv.surjective g ⟨x, hx⟩
          rw [Set.mem_smul_set]
          use y
          apply And.intro y.prop
          simp only [hy, Equiv.Perm.smul_def, Equiv.Perm.ofSubtype_apply_coe, Subtype.coe_mk]
    · -- B = coe '' (coe ⁻¹' B : set (sᶜ : set α)),
      apply Set.Subset.antisymm
      intro x hx
      use ⟨x, hBsc hx⟩
      simp only [hx, Set.mem_preimage, Subtype.coe_mk, eq_self_iff_true, and_self_iff]
      exact Set.image_preimage_subset Subtype.val B
  -- Step 3 : A block contained in s is a subsingleton
  have hB_not_le_s : ∀ (B : Set α) (_ : IsBlock G B), B ⊆ s → B.Subsingleton := by
    intro B hB hBs
    suffices hB_coe : B = Subtype.val '' (Subtype.val ⁻¹' B : Set s)
    suffices : IsTrivialBlock (Subtype.val ⁻¹' B : Set s)
    cases' this with hB' hB'
    · -- trivial case
      rw [hB_coe]
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
        suffices : (g' • B).Subsingleton
        apply Set.subsingleton_of_image _ B this
        apply Function.Bijective.injective
        apply MulAction.bijective
        apply hB_not_le_sc ((⟨g', hg'⟩ : G) • B)
        exact IsBlock_of_block _ hB
        rw [← hBs']
        apply Disjoint.subset_compl_right
        exact h
    -- is_trivial_block (coe ⁻¹' B : set s),
    suffices : IsPreprimitive (stabilizer G s) s
    refine' IsPreprimitive.has_trivial_blocks this _
    -- is_block (coe ⁻¹' B : set s)
    let φ' : stabilizer G s → G := Subtype.val
    let f' : s →ₑ[φ'] α :=
      { toFun := Subtype.val
        map_smul' := fun ⟨m, _⟩ x => by 
          simp only [HasSmul.smul_stabilizer_def] }
    apply MulAction.IsBlock_preimage f' hB
    -- is_preprimitive (stabilizer G s) s
    let φ : stabilizer G s → Equiv.Perm s := MulAction.toPerm
    let f : s →ₑ[φ] s :=
      { toFun := id
        map_smul' := fun g x => by simp only [id.def, Equiv.Perm.smul_def, toPerm_apply] }
    have hf : Function.Bijective f := Function.bijective_id
    rw [isPreprimitive_of_bijective_map_iff _ hf]
    apply Equiv.Perm.isPreprimitive
    -- function.surjective φ,
    -- will need to adjust for alternating_group
    intro g
    suffices hg : Equiv.Perm.ofSubtype g ∈ stabilizer (Equiv.Perm α) s
    use! Equiv.Perm.ofSubtype g
    · apply le_of_lt hG 
      exact hg
    · exact hg
    · ext ⟨x, hx⟩
      change Equiv.Perm.ofSubtype g • x = _
      simp only [Equiv.Perm.smul_def]
      rw [Equiv.Perm.ofSubtype_apply_of_mem]
    · -- equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) sz
      rw [mem_stabilizer_iff]
      apply Set.Subset.antisymm
      · intro x
        rw [Set.mem_smul_set]
        rintro ⟨y, hy, rfl⟩
        simp only [Equiv.Perm.smul_def]
        rw [Equiv.Perm.ofSubtype_apply_of_mem g hy]
        refine' Subtype.mem _
      · intro x hx
        obtain ⟨y, hy⟩ := Equiv.surjective g ⟨x, hx⟩
        rw [Set.mem_smul_set]
        use y
        apply And.intro y.prop
        simp only [hy, Equiv.Perm.smul_def, Equiv.Perm.ofSubtype_apply_coe, Subtype.coe_mk]
    · -- B = coe '' (coe ⁻¹' B : set ↥s),
      apply Set.Subset.antisymm
      intro x hx
      use ⟨x, hBs hx⟩
      simp only [hx, Set.mem_preimage, Subtype.coe_mk, eq_self_iff_true, and_self_iff]
      exact Set.image_preimage_subset Subtype.val B
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
    suffices : ∃ k : fixingSubgroup (Equiv.Perm α) s, k • b = x
    obtain ⟨⟨k, hk⟩, hkbx : k • b = x⟩ := this
    suffices : k • B = B
    rw [← hkbx, ← this, Set.smul_mem_smul_set_iff]
    exact hb
    · -- k • B = B,
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
      suffices :
        IsPretransitive (fixingSubgroup (Equiv.Perm α) s)
          (SubMulAction.ofFixingSubgroup (Equiv.Perm α) s)
      obtain ⟨k, hk⟩ :=
        exists_smul_eq (fixingSubgroup (Equiv.Perm α) s)
          (⟨b, hb'⟩ : SubMulAction.ofFixingSubgroup (Equiv.Perm α) s) ⟨x, hx'⟩
      use k
      rw [← Subtype.coe_inj, SubMulAction.val_smul] at hk 
      exact hk
      -- is_pretransitive …
      rw [isPretransitive_iff_is_one_pretransitive]
      apply remaining_transitivity'
      exact Equiv.Perm.isMultiplyPretransitive α (Nat.card α)
      -- simp only [PartENat.card_eq_coe_fintype_card]
      · rw [add_comm]
        rw [← Set.ncard_add_ncard_compl s]
        simp only [add_le_add_iff_left]
        rw [Nat.succ_le_iff, Set.ncard_pos]
        -- change 0 < _
        -- rw [Fintype.card_pos_iff]
        -- simp only [Set.nonempty_coe_sort]
        exact h1
      simp only [Nat.card_eq_fintype_card, PartENat.card_eq_coe_fintype_card, le_refl]
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
  rw [Nat.add_lt_add_iff_right _ _ sᶜ.ncard]
  exact hα
  rw [MulAction.smul_set_ncard_eq] 
  simp only [← two_mul]
  apply Nat.mul_le_mul_left
  exact Set.ncard_le_of_subset hsc_le_B (Set.toFinite B) 
#align equiv.perm.is_maximal_stab' Equiv.Perm.isMaximalStab'


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
#align equiv.perm.is_maximal_stab Equiv.Perm.isMaximalStab

end Equiv.Perm

namespace MulAction

variable {α : Type _} [DecidableEq α] [Fintype α]

/-- The action of `Equiv.Perm α` on `n.Combination α` is preprimitive
provided 1 ≤ n < #α and #α ≠ 2*n -/
theorem Nat.Combination_isPreprimitive 
    {n : ℕ} (h_one_le : 1 ≤ n) (hn : n < Fintype.card α)
    (hα : Fintype.card α ≠ 2 * n) : 
    IsPreprimitive (Equiv.Perm α) (n.Combination α) := by
--  classical
  cases' Nat.eq_or_lt_of_le h_one_le with h_one h_one_lt
  · -- n = 1 :
    let f : α →ₑ[@id (Equiv.Perm α)] Nat.Combination α 1 :=
      { toFun := fun x => ⟨{x}, Finset.card_singleton x⟩
        map_smul' := fun g x => rfl }
    rw [← h_one]
    suffices hf : Function.Surjective f
    · apply isPreprimitive_of_surjective_map hf
      exact Equiv.Perm.isPreprimitive α
    rintro ⟨s, hs⟩
    change s.card = 1 at hs 
    rw [Finset.card_eq_one] at hs 
    obtain ⟨a, ha⟩ := hs
    use a
    simp only [Subtype.mk.injEq, ha]
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
#align mul_action.nat.finset_is_preprimitive_of MulAction.Nat.Combination_isPreprimitive

end MulAction


/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module jordan
-/
import Jordan.Mathlib.Set
import Jordan.Primitive
import Jordan.IndexNormal
import Jordan.MultiplePrimitivity

import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Theorems of Jordan

A proof of theorems of Jordan regarding primitive permutation groups

This mostly follows the book of Wielandt, *Finite permutation groups*

- `is_two_pretransitive_weak_jordan` and `is_two_preprimitive_weak_jordan`
are technical lemmas that prove 2-pretransitivity / 2-preprimitivity
for some group actions (Wielandt, 13.1)

- `is_multiply_preprimitive_jordan` is a multiple preprimitivity criterion of Jordan (1871)
for a preprimitive action: the hypothesis is the preprimitivity
of the sub_mul_action of `fixing_subgroup s` (Wielandt, 13.2)

- `jordan_swap` proves that a primitive subgroup of a permutation group that contains a
swap is equal to the full permutation group (Wielandt, 13.3)

- `jordan_three_cycle` proves that a primitive subgroup of a permutation group that contains a
3-cycle contains the alternating group (Wielandt, 13.3)

## TODO

- Prove `jordan_prime_cycle` that a primitive subgroup of a permutation group that contains
a cycle of prime order contains the alternating group (Wielandt, 13.9 )

- Prove the stronger versions of the technical lemmas of Jordan. (Wielandt, 13.1')

- Golf the proofs of the technical lemmas (prove them at the same time, or find
an adequate induction lemma)
-/


open MulAction

open scoped Pointwise

instance  {α : Type _} {G : Type _} [Group G] [MulAction G α] {s : Set α} :
    SMul (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s) := 
  SetLike.smul (SubMulAction.ofFixingSubgroup G s)

/-- A pretransitivity criterion -/
theorem isPretransitive_ofFixingSubgroup_inter {α : Type _} {G : Type _} [Group G] [MulAction G α]
    {s : Set α} (hs : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s))
    {g : G} {a : α} (ha : a ∉ s ∪ g • s) :
    IsPretransitive (fixingSubgroup G (s ∩ g • s)) (SubMulAction.ofFixingSubgroup G (s ∩ g • s)) := by
  have ha' : a ∈ (s ∩ g • s)ᶜ := by
    intro ha'; apply ha
    apply Set.mem_union_left
    exact Set.mem_of_mem_inter_left ha'
  -- For an unknown reason, rw does not work
  apply (IsPretransitive.mk_base_iff (⟨a, ha'⟩ : SubMulAction.ofFixingSubgroup G (s ∩ g • s))).mpr
  let hs_trans_eq := hs.exists_smul_eq
  rintro ⟨x, hx⟩
  rw [SubMulAction.mem_ofFixingSubgroup_iff] at hx 
  rw [Set.mem_inter_iff, not_and_or] at hx 
  cases' hx with hx hx
  · -- x ∉ s
    obtain ⟨⟨k, hk⟩, hkax⟩ := hs_trans_eq ⟨a, ?_⟩ ⟨x, hx⟩
    use ⟨k, (by 
      rw [mem_fixingSubgroup_iff] at hk ⊢
      intro y  hy
      apply hk
      apply Set.mem_of_mem_inter_left hy)⟩
    · simp only [← SetLike.coe_eq_coe] at hkax ⊢
      exact hkax
    · intro ha'; apply ha
      apply Set.mem_union_left
      exact ha'
  · -- x ∉ g • s
    obtain ⟨⟨k, hk⟩, hkax⟩ := hs_trans_eq ⟨g⁻¹ • a, ?_⟩ ⟨g⁻¹ • x, ?_⟩
    use ⟨g * k * g⁻¹, (by 
      rw [mem_fixingSubgroup_iff] at hk ⊢
      intro y hy
      simp [← smul_smul, smul_eq_iff_eq_inv_smul g]
      apply hk
      rw [← Set.mem_smul_set_iff_inv_smul_mem]
      exact Set.mem_of_mem_inter_right hy)⟩
    · simp only [← SetLike.coe_eq_coe] at hkax ⊢
      simp only [SetLike.val_smul] at hkax ⊢
      rw [← smul_eq_iff_eq_inv_smul] at hkax 
      change (g * k * g⁻¹) • a = x
      simp only [← smul_smul]      
      exact hkax
    · rw [SubMulAction.mem_ofFixingSubgroup_iff]
      rw [← Set.mem_smul_set_iff_inv_smul_mem]
      intro h
      apply ha
      apply Set.mem_union_right _ h
    · rw [SubMulAction.mem_ofFixingSubgroup_iff]
      intro h
      apply hx
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact h  
#align is_pretransitive_of_fixing_subgroup_inter isPretransitive_ofFixingSubgroup_inter

section Jordan

variable {α : Type _}

variable {G : Type _} [Group G] [MulAction G α]

/-- In a 2-pretransitive action, the normal closure of stabilizers is the full group -/
theorem normalClosure_of_stabilizer_eq_top (hsn' : 2 < PartENat.card α)
    (hG' : IsMultiplyPretransitive G α 2) {a : α} :
    Subgroup.normalClosure ((stabilizer G a) : Set G) = ⊤ := by
  have hG : IsPretransitive G α := by
    rw [isPretransitive_iff_is_one_pretransitive]
    apply isMultiplyPretransitive_of_higher
    exact hG'
    norm_num
    rw [Nat.cast_two]
    exact le_of_lt hsn'
  have : Nontrivial α := by
    rw [← PartENat.one_lt_card_iff_nontrivial]
    refine' lt_trans _ hsn'
    rw [← Nat.cast_two, ← Nat.cast_one, PartENat.coe_lt_coe]
    norm_num
  have hGa : (stabilizer G a).IsMaximal :=  by
    rw [maximal_stabilizer_iff_preprimitive G a]
    exact hG'.isPreprimitive_of_two
  rw [Subgroup.isMaximal_def] at hGa 
  apply hGa.right
  -- Remains to prove: (stabilizer G a) < Subgroup.normalClosure (stabilizer G a)
  -- SIMPLIFIER !!
  constructor
  · apply Subgroup.le_normalClosure
  · intro hyp
    -- prendre b, c ≠ a
    have : ∃ b c : SubMulAction.ofStabilizer G a, b ≠ c := by
      let x : Fin 1 ↪ α :=
        { toFun := fun _ => a
          inj' := Function.injective_of_subsingleton _ }
      obtain ⟨y : Fin 3 ↪ α, hy⟩ := may_extend _ ?_ x
      let hy_inj := y.inj'
      simp at hy_inj 
      have ha : x ⟨0, by norm_num⟩ = a; rfl
      have ha' : y ⟨0, by norm_num⟩ = a := by
        rw [← ha, ← hy]
        rfl
        norm_num
      use ⟨y 1, (by 
        rw [SubMulAction.mem_ofStabilizer_iff]
        intro h
        rw [← ha', EmbeddingLike.apply_eq_iff_eq] at h
        norm_num at h)⟩ 
      use ⟨y 2, (by
        rw [SubMulAction.mem_ofStabilizer_iff]
        intro h
        rw [← ha', EmbeddingLike.apply_eq_iff_eq] at h
        norm_num at h)⟩
      · intro h
        rw [← SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq] at h
        refine ne_of_lt ?_ h
        rw [← Fin.coe_sub_iff_lt]
        rfl
      /- 

      · intro h
        simpa only [Fin.mk_one, Set.mem_singleton_iff, ← ha', Fin.mk_zero,
          EmbeddingLike.apply_eq_iff_eq, Fin.one_eq_zero_iff, Nat.succ_succ_ne_one] using h
      use y ⟨2, by norm_num⟩
      · intro h; simp at h ; rw [← ha'] at h 
        simp only [Fin.mk_zero, EmbeddingLike.apply_eq_iff_eq, Fin.eq_iff_veq] at h 
        simpa using h
      · intro h; rw [← SetLike.coe_eq_coe] at h 
        simp only [SubMulAction.coe_mk] at h 
        rw [EmbeddingLike.apply_eq_iff_eq, Fin.eq_iff_veq] at h 
        simpa using h
      -- 1 ≤ 3
      simp only [one_le_bit1, zero_le']
      -- ↑3 ≤ part_enat.card α,
      rw [PartENat.coe_le_iff]
      intro h; rw [Nat.succ_le_iff]; revert h
      rw [← PartENat.coe_lt_iff, Nat.cast_two]
      exact hsn'
    /-
            rw ← nontrivial_iff ,
    
            rw ← cardinal.one_lt_iff_nontrivial,
            change 1 < cardinal.mk (sub_mul_action.of_stabilizer G a).carrier,
            rw sub_mul_action.of_stabilizer.def,
            rw [← nat.cast_one, cardinal.mk_fintype, cardinal.nat_cast_lt],
            rw ← add_lt_add_iff_left 1,
            refine lt_of_lt_of_le hsn' (le_of_eq _),
            rw ← fintype.card_of_subsingleton _,
            apply cardinal.nat_cast_injective,
    
            rw [← cardinal.mk_fintype, nat.cast_add, ← cardinal.mk_fintype],
            simp only [← cardinal.mk_fintype],
            rw cardinal.mk_sum_compl ,
            { use a, exact set.mem_singleton a },
            exact unique.subsingleton -/ -/
    · rw [PartENat.coe_le_iff]
      intro h; rw [Nat.succ_le_iff]; revert h
      rw [← PartENat.coe_lt_iff, Nat.cast_two]
      exact hsn'
    obtain ⟨⟨b, hb⟩, ⟨c, hc⟩, hbc⟩ := this
    simp only [Ne.def, Subtype.mk_eq_mk] at hbc 
    have : IsPretransitive (stabilizer G a) (SubMulAction.ofStabilizer G a) := by
      rw [isPretransitive_iff_is_one_pretransitive]
      exact (stabilizer.isMultiplyPretransitive G α hG).mp hG'
    --      let hatrans_eq := hatrans.exists_smul_eq,
    -- trouver g ∈ stabilizer G a, g • b = c,
    obtain ⟨⟨g, hg⟩, hgbc⟩ :=
      exists_smul_eq (stabilizer G a) (⟨b, hb⟩ : SubMulAction.ofStabilizer G a) ⟨c, hc⟩
    have hgbc' : g • b = c := by rw [← SetLike.coe_eq_coe] at hgbc ; exact hgbc
    -- trouver h ∈ G, h⁻¹ • a = b,
    obtain ⟨h : G, hinvab : h • b = a⟩ := exists_smul_eq G b a
    suffices (h * g * h⁻¹) • a ≠ a
      by
      -- h * g * h⁻¹ ∈ subgroup.normal_closure (stabilizer G a)
      apply this
      rw [← mem_stabilizer_iff]
      apply hyp
      refine' Subgroup.normalClosure_normal.conj_mem _ _ _
      apply Subgroup.subset_normalClosure
      exact hg
    -- h * g * h⁻¹ • a = h • g • b = h • c ≠ h • b = a
    suffices (h * g * h⁻¹) • a = h • c by
      rw [this]; rw [← hinvab]
      intro z
      apply hbc; apply MulAction.injective h; exact z.symm
    simp only [← smul_smul]
    rw [← hgbc']
    refine' congr_arg₂ _ rfl _
    refine' congr_arg₂ _ rfl _
    rw [inv_smul_eq_iff]; exact hinvab.symm
#align normal_closure_of_stabilizer_eq_top normalClosure_of_stabilizer_eq_top

variable [Fintype α]

open scoped Classical

theorem card_eq_one_iff_is_singleton (s : Set α) (hs : Fintype.card s = 1) : ∃ a : α, s = {a} := by
  classical
  obtain ⟨⟨a, ha⟩, ha'⟩ := fintype.card_eq_one_iff.mp hs
  use a
  rw [Set.eq_singleton_iff_unique_mem]
  apply And.intro ha
  intro x hx
  exact subtype.mk_eq_mk.mp (ha' ⟨x, hx⟩)
#align card_eq_one_iff_is_singleton card_eq_one_iff_is_singleton

/-- A primitivity criterion -/
theorem isPreprimitive_ofFixingSubgroup_inter {G : Type _} [Group G] [MulAction G α] {s : Set α}
    (hs : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) {g : G} {a : α}
    (ha : a ∉ s ∪ g • s) :
    IsPreprimitive (fixingSubgroup G (s ∩ g • s)) (SubMulAction.ofFixingSubgroup G (s ∩ g • s)) :=
  by
  have : fixingSubgroup G s ≤ fixingSubgroup G (s ∩ g • s) := by apply fixingSubgroup_antitone;
    apply Set.inter_subset_left
  let t := s ∩ g • s
  have hts : t ≤ s := Set.inter_subset_left s _
  let f := SubMulAction.ofFixingSubgroup.mapOfInclusion G hts
  have hf : Function.Injective f := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rw [← SetLike.coe_eq_coe] at hxy ⊢
    simp only [SetLike.coe_mk]
    exact hxy
  haveI :
    is_pretransitive (↥(fixingSubgroup G (s ∩ g • s)))
      ↥(SubMulAction.ofFixingSubgroup G (s ∩ g • s)) :=
    isPretransitive_ofFixingSubgroup_inter hs.to_is_pretransitive ha
  apply isPreprimitive_of_large_image hs
  change Fintype.card (SubMulAction.ofFixingSubgroup G (s ∩ g • s)).carrier < _
  simp only [← Set.toFinset_card]
  simp_rw [SubMulAction.ofFixingSubgroup.def]
  rw [Set.toFinset_compl, Set.toFinset_inter, Finset.compl_inter]
  apply Nat.lt_of_add_lt_add_right
  rw [Finset.card_union_add_card_inter]
  suffices : (g • s).toFinsetᶜ.card = s.to_finsetᶜ.card
  rw [this, ← two_mul]
  rw [Nat.lt_iff_add_one_le]
  apply Nat.add_le_add
  · apply le_of_eq
    apply congr_arg _ _
    rw [← Set.toFinset_compl]
    simp only [Set.toFinset_card]
    rw [Set.card_range_of_injective]
    change Fintype.card (sᶜ : Set α) = Fintype.card (SubMulAction.ofFixingSubgroup G s).carrier
    rw [SubMulAction.ofFixingSubgroup.def]
    simp only [Fintype.card_ofFinset, Set.mem_compl_iff]
    exact hf
  · rw [Nat.succ_le_iff]
    simp only [← Set.toFinset_compl, ← Set.toFinset_inter, ← Set.compl_union]
    rw [Set.toFinset_card]
    --  (sᶜ ∩ (g • s)ᶜ),
    rw [Fintype.card_pos_iff]
    use a
  · simp only [Finset.card_compl, Set.toFinset_card]
    rw [smul_set_card_eq]
  infer_instance
#align is_preprimitive_of_fixing_subgroup_inter isPreprimitive_ofFixingSubgroup_inter

-- α = Ω, s = Δ, α \ s = Γ
-- 1 ≤ #Δ < #Ω, 1 < #Γ < #Ω
/- -- TODO : prove :
theorem strong_jordan_of_pretransitive (hG : is_preprimitive G α)
    {s : set α} {n : ℕ } (hsn : fintype.card s = n.succ)
    (hsn' : 1 + n.succ < fintype.card α)
    (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 :=
sorry
 -/
theorem aux_pigeonhole {s t : Set α} (h : Fintype.card α < Fintype.card s + Fintype.card t) :
    (s ∩ t).Nonempty := by
  simp only [← Set.toFinset_card] at h 
  rw [Set.nonempty_iff_ne_empty]
  intro hst
  rw [← Set.toFinset_inj, Set.toFinset_inter, Set.toFinset_empty, ←
    Finset.not_nonempty_iff_eq_empty] at hst 
  apply hst
  rw [← Finset.card_compl_lt_iff_nonempty, Finset.compl_inter]
  apply lt_of_le_of_lt (Finset.card_union_le _ _)
  apply Nat.lt_of_add_lt_add_left
  rw [← add_assoc]
  simp only [Finset.card_compl]
  rw [Nat.add_sub_of_le (Finset.card_le_univ s.to_finset)]
  conv_rhs => rw [add_comm]
  apply Nat.add_lt_add_left
  apply Nat.lt_of_add_lt_add_left
  rw [Nat.add_sub_of_le (Finset.card_le_univ t.to_finset)]
  rw [add_comm]
  exact h
#align aux_pigeonhole aux_pigeonhole

/-- A criterion due to Jordan for being 2-pretransitive (Wielandt, 13.1) -/
theorem is_two_pretransitive_weak_jordan (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : Fintype.card s = n.succ) (hsn' : 1 + n.succ < Fintype.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPretransitive G α 2 := by
  revert α G
  induction' n using Nat.strong_induction_on with n hrec
  intro α G _ _ _ hG s hsn hsn' hs_trans
  skip
  --   let hs_trans_eq := hs_trans.exists_smul_eq,
  have hs_ne_top : s ≠ ⊤ := by
    intro hs
    rw [Set.top_eq_univ, ← set_fintype_card_eq_univ_iff, hsn] at hs 
    rw [hs] at hsn' 
    simpa only [add_lt_iff_neg_right, not_lt_zero'] using hsn'
  have hs_nonempty : s.nonempty := by
    rw [← Set.nonempty_coe_sort]; rw [← not_isEmpty_iff]
    intro hs
    rw [← Fintype.card_eq_zero_iff] at hs 
    rw [hs] at hsn 
    simpa only using hsn
  cases' Nat.lt_or_ge n.succ 2 with hn hn
  · -- Initialization : n = 0
    have hn : n = 0 := by
      rw [← le_zero_iff]
      apply Nat.le_of_succ_le_succ
      apply Nat.le_of_lt_succ
      exact hn
    rw [hn] at *
    let hG_eq := hG.to_is_pretransitive.exists_smul_eq
    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn
    rw [hsa] at *
    rw [stabilizer.is_multiply_pretransitive G α hG.to_is_pretransitive]
    rw [← is_pretransitive_iff_is_one_pretransitive]
    exact
      isPretransitive_of_surjective_map
        (SubMulAction.OfFixingSubgroupOfSingleton.map_bijective G a).Surjective hs_trans
  -- Induction step : n ≥ 1
  cases' Nat.lt_or_ge (2 * n.succ) (Fintype.card α) with hn1 hn2
  · -- hn : 2 * s.card < fintype.card α
    -- get a, b ∈ s, a ≠ b
    obtain ⟨⟨a, ha : a ∈ s⟩, ⟨b, hb : b ∈ s⟩, hab⟩ :=
      fintype.one_lt_card_iff_nontrivial.mp (nat.succ_le_iff.mp (by rw [hsn]; exact hn))
    simp only [Ne.def, Subtype.mk_eq_mk] at hab 
    -- apply rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ := rudio hG s (Set.toFinite s) hs_nonempty hs_ne_top a b hab
    have : (s.to_finsetᶜ ∩ (g • s.to_finset)ᶜ).Nonempty :=
      by
      rw [← Finset.card_compl_lt_iff_nonempty]
      simp only [Finset.compl_inter, compl_compl]
      apply lt_of_le_of_lt (Finset.card_union_le _ _)
      rw [Set.toFinset_card]
      suffices : (g • s.to_finset).card = Fintype.card s
      rw [this, hsn, ← two_mul]
      exact hn1
      change (Finset.image (fun x => g • x) s.to_finset).card = _
      rw [Finset.card_image_of_injective _ (MulAction.injective g)]
      rw [Set.toFinset_card]
    obtain ⟨c, hc⟩ := this.bex
    simp only [Finset.mem_inter, Finset.mem_compl, Set.mem_toFinset] at hc 
    let hcs := hc.left
    have hcgs : g⁻¹ • c ∉ s := by
      intro h
      rw [← Set.mem_toFinset] at h 
      apply hc.right
      rw [Finset.mem_smul_finset]
      use g⁻¹ • c; apply And.intro h
      simp only [smul_inv_smul]
    let t := s ∩ g • s
    have hct : c ∉ t := by intro h; apply hcs; apply Set.mem_of_mem_inter_left h
    have hct' : c ∉ s ∪ g • s := by
      intro h; rw [Set.mem_union] at h ; cases' h with h h
      exact hc.left h
      apply hcgs; rw [← Set.mem_smul_set_iff_inv_smul_mem]; exact h
    let ht_trans : is_pretransitive (fixingSubgroup G t) (SubMulAction.ofFixingSubgroup G t) :=
      isPretransitive_ofFixingSubgroup_inter hs_trans hct'
    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ m : ℕ, Fintype.card t = m.succ ∧ m < n :=
      by
      suffices : Fintype.card t ≠ 0
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero this
      use m; apply And.intro hm
      rw [← Nat.succ_lt_succ_iff]; rw [← hm]; rw [← hsn]
      apply Set.card_lt_card
      constructor
      apply Set.inter_subset_left
      intro hst; apply hgb; apply Set.inter_subset_right s
      apply hst; exact hb
      intro ht
      rw [Fintype.card_eq_zero_iff] at ht 
      apply ht.false
      use ⟨a, ha, hga⟩
    obtain ⟨m, htm, hmn⟩ := this
    have htm' : 1 + m.succ < Fintype.card α :=
      by
      apply lt_trans _ hsn'
      simp only [add_lt_add_iff_left]
      rw [Nat.succ_lt_succ_iff]
      exact hmn
    -- apply hrec :
    -- is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    refine' hrec m hmn hG _ htm' ht_trans
    -- htm does not suffice (because of different hidden instances on fintype)
    convert htm
  · -- 2 * s.card ≥ fintype.card α
    have : Nontrivial (sᶜ : Set α) :=
      by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      rw [← Set.toFinset_card]
      rw [Set.toFinset_compl]
      rw [Finset.card_compl]
      rw [lt_tsub_iff_right]
      rw [Set.toFinset_card, hsn]; exact hsn'
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨⟨a, ha : a ∈ sᶜ⟩, ⟨b, hb : b ∈ sᶜ⟩, hab⟩ := this
    simp only [Ne.def, Subtype.mk_eq_mk] at hab 
    have hsc_ne : sᶜ.Nonempty := Set.nonempty_of_mem ha
    have hsc_ne_top : sᶜ ≠ ⊤ := by
      intro h
      simp only [Set.top_eq_univ, Set.compl_univ_iff] at h 
      simpa only [h, Set.not_nonempty_empty] using hs_nonempty
    -- apply rudio to get g ∈ G such that a ∈ g • sᶜ, b ∉ g • sᶜ
    obtain ⟨g, hga, hgb⟩ := rudio hG (sᶜ) (Set.toFinite (sᶜ)) hsc_ne hsc_ne_top a b hab
    let t := s ∩ g • s
    have hbt : b ∉ t := by
      intro h; rw [Set.mem_compl_iff] at hb ; apply hb
      apply Set.mem_of_mem_inter_left h
    have hat' : a ∉ s ∪ g • s := by
      intro h; rw [Set.mem_union] at h 
      cases' h with h h
      rw [Set.mem_compl_iff] at ha ; exact ha h
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hga h 
      rw [Set.mem_compl_iff] at hga ; exact hga h
    let ht_trans : is_pretransitive (fixingSubgroup G t) (SubMulAction.ofFixingSubgroup G t) :=
      isPretransitive_ofFixingSubgroup_inter hs_trans hat'
    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ m : ℕ, Fintype.card t = m.succ ∧ m < n :=
      by
      suffices t.nonempty
        by
        rw [← Set.nonempty_coe_sort, ← Fintype.card_pos_iff] at this 
        use (Fintype.card t).pred
        rw [← Nat.succ_lt_succ_iff]
        rw [Nat.succ_pred_eq_of_pos this]
        rw [← hsn]
        apply And.intro rfl
        apply Set.card_lt_card
        constructor
        apply Set.inter_subset_left
        intro hst
        rw [Set.mem_compl_iff] at hb 
        simp only [smul_compl_set, Set.mem_compl_iff, Set.not_not_mem] at hgb 
        suffices s = g • s by apply hb; rw [this]; exact hgb
        apply Set.eq_of_subset_of_card_le
        · refine' subset_trans hst _
          apply Set.inter_subset_right
        · apply le_of_eq
          apply smul_set_card_eq
      · -- aux_pigeonhole ne marche pas !
        rw [Set.nonempty_iff_ne_empty]
        intro h
        rw [← Set.toFinset_inj, Set.toFinset_inter, Set.toFinset_empty, ←
          Finset.not_nonempty_iff_eq_empty] at h 
        apply h
        rw [← Finset.card_compl_lt_iff_nonempty, Finset.compl_inter]
        apply Nat.lt_of_add_lt_add_right
        rw [Finset.card_union_add_card_inter]
        apply Nat.lt_of_add_lt_add_left
        rw [← add_assoc]
        simp only [Finset.card_compl]
        rw [Nat.add_sub_of_le (Finset.card_le_univ s.to_finset)]
        conv_rhs =>
          rw [add_comm]
          rw [add_assoc]
        apply Nat.add_lt_add_left
        apply Nat.lt_of_add_lt_add_left
        rw [Nat.add_sub_of_le (Finset.card_le_univ (g • s).toFinset)]
        rw [add_comm]
        suffices (g • s).toFinset.card = s.to_finset.card
          by
          rw [this]; conv_rhs => rw [add_assoc]
          rw [← two_mul, Set.toFinset_card, hsn]
          rw [← Nat.one_add_le_iff]
          apply Nat.add_le_add _ hn2
          rw [Nat.succ_le_iff]
          rw [Finset.card_pos]
          use a
          simp only [Finset.mem_inter, Finset.mem_compl, Set.mem_toFinset]
          rw [← not_or, ← Set.mem_union]
          exact hat'
        · conv_lhs => simp only [Set.toFinset_card, Fintype.card_ofFinset]
          rw [Finset.card_image_of_injective _ (MulAction.injective g)]
    obtain ⟨m, htm, hmn⟩ := this
    have htm' : 1 + m.succ < Fintype.card α :=
      by
      apply lt_trans _ hsn'
      simp only [add_lt_add_iff_left]
      rw [Nat.succ_lt_succ_iff]
      exact hmn
    -- apply hrec :
    -- is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    refine' hrec m hmn hG _ htm' ht_trans
    -- htm does not work, because of different hidden fintype instances
    rw [← htm];
    apply Fintype.card_congr'; rfl
#align is_two_pretransitive_weak_jordan is_two_pretransitive_weak_jordan

/- -- TODO : prove
theorem strong_jordan_of_preprimitive (hG : is_preprimitive G α)
  {s : set α} {n : ℕ} (hsn : fintype.card s = n.succ) (hsn' : 1 + n.succ < fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_preprimitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 := sorry
 -/
theorem is_two_preprimitive_weak_jordan {n : ℕ} :
    ∀ {α : Type _} [Fintype α] {G : Type _} [Group G] [MulAction G α],
      ∀ (hG : IsPreprimitive G α) {s : Set α} (hsn : Fintype.card s = n.succ)
        (hsn' : 1 + n.succ < Fintype.card α)
        (hs_prim : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)),
        is_multiply_preprimitive G α 2 :=
  by
  induction' n using Nat.strong_induction_on with n hrec
  intro α _ G _ _ hG s hsn hsn' hs_prim
  let hs_trans_eq := hs_prim.to_is_pretransitive.exists_smul_eq
  have hs_ne_top : s ≠ ⊤ := by
    intro hs
    rw [Set.top_eq_univ, ← set_fintype_card_eq_univ_iff, hsn] at hs 
    rw [hs] at hsn' 
    simpa only [add_lt_iff_neg_right, not_lt_zero'] using hsn'
  have hs_nonempty : s.nonempty := by
    rw [← Set.nonempty_coe_sort]; rw [← not_isEmpty_iff]
    intro hs
    rw [← Fintype.card_eq_zero_iff] at hs 
    rw [hs] at hsn 
    simpa only using hsn
  cases' Nat.lt_or_ge n.succ 2 with hn hn
  · -- Initialization : n = 0
    have hn : n = 0 := by
      rw [← le_zero_iff]
      apply Nat.le_of_succ_le_succ
      apply Nat.le_of_lt_succ
      exact hn
    rw [hn] at *
    let hG_eq := hG.to_is_pretransitive.exists_smul_eq
    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn
    rw [hsa] at *
    rw [is_multiply_preprimitive_of_stabilizer G α (Nat.le_refl 1) hG.to_is_pretransitive]
    rw [← is_preprimitive_iff_is_one_preprimitive]
    apply
      isPreprimitive_of_surjective_map
        (SubMulAction.OfFixingSubgroupOfSingleton.map_bijective G a).Surjective
    exact hs_prim
  -- Induction step : n ≥ 1
  cases' Nat.lt_or_ge (2 * n.succ) (Fintype.card α) with hn1 hn2
  · -- hn : 2 * s.card < fintype.card α
    -- get a, b ∈ s, a ≠ b
    obtain ⟨⟨a, ha : a ∈ s⟩, ⟨b, hb : b ∈ s⟩, hab⟩ :=
      fintype.one_lt_card_iff_nontrivial.mp (nat.succ_le_iff.mp (by rw [hsn]; exact hn))
    simp only [Ne.def, Subtype.mk_eq_mk] at hab 
    -- apply rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ := rudio hG s (Set.toFinite s) hs_nonempty hs_ne_top a b hab
    have : (s.to_finsetᶜ ∩ (g • s.to_finset)ᶜ).Nonempty :=
      by
      rw [← Finset.card_compl_lt_iff_nonempty]
      simp only [Finset.compl_inter, compl_compl]
      apply lt_of_le_of_lt (Finset.card_union_le _ _)
      rw [Set.toFinset_card]
      suffices : (g • s.to_finset).card = Fintype.card s
      rw [this, hsn, ← two_mul]
      exact hn1
      change (Finset.image (fun x => g • x) s.to_finset).card = _
      rw [Finset.card_image_of_injective _ (MulAction.injective g)]
      rw [Set.toFinset_card]
    obtain ⟨c, hc⟩ := this.bex
    simp only [Finset.mem_inter, Finset.mem_compl, Set.mem_toFinset] at hc 
    let hcs := hc.left
    have hcgs : g⁻¹ • c ∉ s := by
      intro h
      rw [← Set.mem_toFinset] at h 
      apply hc.right
      rw [Finset.mem_smul_finset]
      use g⁻¹ • c; apply And.intro h
      simp only [smul_inv_smul]
    let t := s ∩ g • s
    have hct : c ∉ t := by intro h; apply hcs; apply Set.mem_of_mem_inter_left h
    have hct' : c ∉ s ∪ g • s := by
      intro h; rw [Set.mem_union] at h ; cases' h with h h
      exact hc.left h
      apply hcgs; rw [← Set.mem_smul_set_iff_inv_smul_mem]; exact h
    let ht_prim : IsPreprimitive (fixingSubgroup G t) (SubMulAction.ofFixingSubgroup G t) :=
      isPreprimitive_ofFixingSubgroup_inter hs_prim hct'
    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ m : ℕ, Fintype.card t = m.succ ∧ m < n :=
      by
      suffices : Fintype.card t ≠ 0
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero this
      use m; apply And.intro hm
      rw [← Nat.succ_lt_succ_iff]; rw [← hm]; rw [← hsn]
      apply Set.card_lt_card
      constructor
      apply Set.inter_subset_left
      intro hst; apply hgb; apply Set.inter_subset_right s
      apply hst; exact hb
      intro ht
      rw [Fintype.card_eq_zero_iff] at ht 
      apply ht.false
      use ⟨a, ha, hga⟩
    obtain ⟨m, htm, hmn⟩ := this
    have htm' : 1 + m.succ < Fintype.card α :=
      by
      apply lt_trans _ hsn'
      simp only [add_lt_add_iff_left]
      rw [Nat.succ_lt_succ_iff]
      exact hmn
    -- apply hrec :
    -- is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    refine' hrec m hmn hG _ htm' ht_prim
    rw [← htm]; apply Fintype.card_congr'; rfl
  · -- 2 * s.card ≥ fintype.card α
    have : Nontrivial (sᶜ : Set α) :=
      by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      rw [← Set.toFinset_card]
      rw [Set.toFinset_compl]
      rw [Finset.card_compl]
      rw [lt_tsub_iff_right]
      rw [Set.toFinset_card, hsn]; exact hsn'
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨⟨a, ha : a ∈ sᶜ⟩, ⟨b, hb : b ∈ sᶜ⟩, hab⟩ := this
    simp only [Ne.def, Subtype.mk_eq_mk] at hab 
    have hsc_ne : sᶜ.Nonempty := Set.nonempty_of_mem ha
    have hsc_ne_top : sᶜ ≠ ⊤ := by
      intro h
      simp only [Set.top_eq_univ, Set.compl_univ_iff] at h 
      simpa only [h, Set.not_nonempty_empty] using hs_nonempty
    -- apply rudio to get g ∈ G such that a ∈ g • sᶜ, b ∉ g • sᶜ
    obtain ⟨g, hga, hgb⟩ := rudio hG (sᶜ) (Set.toFinite (sᶜ)) hsc_ne hsc_ne_top a b hab
    let t := s ∩ g • s
    have hat' : a ∉ s ∪ g • s := by
      intro h; rw [Set.mem_union] at h 
      cases' h with h h
      rw [Set.mem_compl_iff] at ha ; exact ha h
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hga h 
      rw [Set.mem_compl_iff] at hga ; exact hga h
    let ht_prim : IsPreprimitive (fixingSubgroup G t) (SubMulAction.ofFixingSubgroup G t) :=
      isPreprimitive_ofFixingSubgroup_inter hs_prim hat'
    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ m : ℕ, Fintype.card t = m.succ ∧ m < n :=
      by
      suffices t.nonempty
        by
        rw [← Set.nonempty_coe_sort, ← Fintype.card_pos_iff] at this 
        use (Fintype.card t).pred
        rw [← Nat.succ_lt_succ_iff]
        rw [Nat.succ_pred_eq_of_pos this]
        rw [← hsn]
        apply And.intro rfl
        apply Set.card_lt_card
        constructor
        apply Set.inter_subset_left
        intro hst
        rw [Set.mem_compl_iff] at hb 
        simp only [smul_compl_set, Set.mem_compl_iff, Set.not_not_mem] at hgb 
        suffices s = g • s by apply hb; rw [this]; exact hgb
        apply Set.eq_of_subset_of_card_le
        · refine' subset_trans hst _
          apply Set.inter_subset_right
        · apply le_of_eq
          apply smul_set_card_eq
      · -- aux_pigeonhole ne marche pas !
        rw [Set.nonempty_iff_ne_empty]
        intro h
        rw [← Set.toFinset_inj, Set.toFinset_inter, Set.toFinset_empty, ←
          Finset.not_nonempty_iff_eq_empty] at h 
        apply h
        rw [← Finset.card_compl_lt_iff_nonempty, Finset.compl_inter]
        apply Nat.lt_of_add_lt_add_right
        rw [Finset.card_union_add_card_inter]
        apply Nat.lt_of_add_lt_add_left
        rw [← add_assoc]
        simp only [Finset.card_compl]
        rw [Nat.add_sub_of_le (Finset.card_le_univ s.to_finset)]
        conv_rhs =>
          rw [add_comm]
          rw [add_assoc]
        apply Nat.add_lt_add_left
        apply Nat.lt_of_add_lt_add_left
        rw [Nat.add_sub_of_le (Finset.card_le_univ (g • s).toFinset)]
        rw [add_comm]
        suffices (g • s).toFinset.card = s.to_finset.card
          by
          rw [this]; conv_rhs => rw [add_assoc]
          rw [← two_mul, Set.toFinset_card, hsn]
          rw [← Nat.one_add_le_iff]
          apply Nat.add_le_add _ hn2
          rw [Nat.succ_le_iff]
          rw [Finset.card_pos]
          use a
          simp only [Finset.mem_inter, Finset.mem_compl, Set.mem_toFinset]
          rw [← not_or, ← Set.mem_union]
          exact hat'
        · conv_lhs => simp only [Set.toFinset_card, Fintype.card_ofFinset]
          rw [Finset.card_image_of_injective _ (MulAction.injective g)]
    obtain ⟨m, htm, hmn⟩ := this
    have htm' : 1 + m.succ < Fintype.card α :=
      by
      apply lt_trans _ hsn'
      simp only [add_lt_add_iff_left]
      rw [Nat.succ_lt_succ_iff]
      exact hmn
    -- apply hrec :
    -- is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    refine' hrec m hmn hG _ htm' ht_prim
    rw [← htm]; apply Fintype.card_congr'; rfl
#align is_two_preprimitive_weak_jordan is_two_preprimitive_weak_jordan

/- These theorems will be deduced from the strong one
theorem is_two_pretransitive_weak_jordan' (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_pretransitive G α 2 :=
begin
 -- We can deduce it from jordan0
  apply is_pretransitive_of_subgroup,
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply strong_jordan_of_pretransitive hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_trans,
end

theorem weak_jordan_of_preprimitive' (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_preprimitive G α 2 :=
begin
 -- We can deduce it from strong_jordan_of_preprimitive
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply is_multiply_preprimitive_of_subgroup,
  norm_num,
  refine strong_jordan_of_preprimitive hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_prim
end
-/
-- Notations of Wielandt : s = Δ, n - m = #s, n = #α, m = #sᶜ, 1 < m < n
-- 1 + #s < n , #s ≥ 1
/-- Jordan's multiple primitivity criterion (Wielandt, 13.3) -/
theorem isMultiplyPreprimitive_jordan (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : Fintype.card s = n.succ) (hsn' : 1 + n.succ < Fintype.card α)
    (hprim : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α (1 + n.succ) :=
  by
  revert α G
  induction' n with n hrec
  · -- case n = 0
    intro α G _ _ _ hG s hsn hα hGs
    haveI : is_pretransitive G α := hG.to_is_pretransitive
    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn
    rw [hsa] at *
    constructor
    · rw [stabilizer.is_multiply_pretransitive]
      rw [← is_pretransitive_iff_is_one_pretransitive]
      apply
        isPretransitive_of_surjective_map
          (SubMulAction.OfFixingSubgroupOfSingleton.map_bijective G a).Surjective
          hGs.to_is_pretransitive
      exact hG.to_is_pretransitive
    · intro t h
      suffices ht' : Fintype.card t = 1
      · obtain ⟨b, htb⟩ := card_eq_one_iff_is_singleton t ht'
        rw [htb] at *
        obtain ⟨g, hg⟩ := exists_smul_eq G a b
        have hst : g • ({a} : Set α) = ({b} : Set α) :=
          by
          change (fun x => g • x) '' {a} = {b}
          rw [Set.image_singleton, hg]
        refine'
          isPreprimitive_of_surjective_map
            (SubMulAction.ofFixingSubgroup.conjMap_bijective G hst).Surjective hGs
      · rw [part_enat.of_fintype, ← Nat.cast_one, ← Nat.cast_add, PartENat.natCast_inj,
          add_left_inj] at h 
        exact h
  -- Induction step
  intro α G _ _ _ hG s hsn hα hGs
  suffices : ∃ (a : α) (t : Set (SubMulAction.ofStabilizer G a)), a ∈ s ∧ s = insert a (coe '' t)
  obtain ⟨a, t, ha, hst⟩ := this
  have ha' : a ∉ coe '' t := by
    intro h; rw [Set.mem_image] at h ; obtain ⟨x, hx⟩ := h
    apply x.prop; rw [hx.right]; exact Set.mem_singleton a
  have ht_prim : IsPreprimitive (stabilizer G a) (SubMulAction.ofStabilizer G a) :=
    by
    rw [is_preprimitive_iff_is_one_preprimitive]
    rw [← is_multiply_preprimitive_of_stabilizer G α (Nat.le_refl 1) hG.to_is_pretransitive]
    apply is_two_preprimitive_weak_jordan hG hsn hα hGs
  have hGs' :
    IsPreprimitive (↥(fixingSubgroup (↥(stabilizer G a)) t))
      ↥(SubMulAction.ofFixingSubgroup (↥(stabilizer G a)) t) :=
    by
    apply
      isPreprimitive_of_surjective_map
        (SubMulAction.OfFixingSubgroupOfStabilizer.map_bijective G a t).Surjective
    apply
      isPreprimitive_of_surjective_map
        (SubMulAction.OfFixingSubgroupOfEq.map_bijective G hst).Surjective
    exact hGs
  rw [← Nat.succ_eq_one_add]
  rw [is_multiply_preprimitive_of_stabilizer G α _ hG.to_is_pretransitive]
  rw [Nat.succ_eq_one_add]
  refine' hrec ht_prim _ _ hGs'
  · -- fintype.card t = n.succ
    rw [← Set.card_image_of_injective t Subtype.coe_injective]
    apply Nat.add_right_cancel
    rw [← Set.card_insert (coe '' t) ha']
    simp_rw [← hst]; rw [← Nat.succ_eq_add_one]; exact hsn
    infer_instance
  · -- 1 + n.succ < fintype.card ↥(sub_mul_action_of_stabilizer G α a)
    change _ < Fintype.card ↥(SubMulAction.ofStabilizer G a).carrier
    rw [← Nat.succ_eq_one_add]
    apply Nat.lt_of_add_lt_add_right
    rw [SubMulAction.ofStabilizer.def]
    rw [Fintype.card_compl_set]
    rw [Nat.sub_add_cancel (set_fintype_card_le_univ _)]
    simp only [Set.card_singleton]
    rw [add_comm]
    exact hα
  · apply Nat.succ_le_succ; apply Nat.zero_le
  -- ∃ (a : α), a ∈ s
  · suffices : s.nonempty
    rw [Set.nonempty_def] at this 
    obtain ⟨a, ha⟩ := this
    use a
    use coe ⁻¹' s
    apply And.intro ha
    rw [Set.insert_eq]
    rw [Set.image_preimage_eq_inter_range]
    simp only [Subtype.range_coe_subtype, Set.singleton_union]
    simp_rw [SubMulAction.ofStabilizer.mem_iff]
    simp only [Ne.def]
    ext x
    --    apply subset_antisymm,
    · rw [Set.mem_insert_iff]
      simp
      rw [or_and_left]
      simp_rw [or_not]
      rw [and_true_iff]
      constructor
      intro hx; apply Or.intro_right _ hx
      intro hx; cases' hx with hx hx
      rw [hx]; exact ha
      exact hx
    rw [Set.nonempty_iff_ne_empty]
    intro h
    simp only [h, Set.empty_card'] at hsn 
    simpa using hsn
#align is_multiply_preprimitive_jordan isMultiplyPreprimitive_jordan

end Jordan

section Jordan'

open MulAction

open scoped Pointwise

variable {α : Type _} [Fintype α]

variable {G : Subgroup (Equiv.Perm α)}

theorem eq_s2_of_nontrivial (hα : Fintype.card α ≤ 2) (hG : Nontrivial G) :
    G = (⊤ : Subgroup (Equiv.Perm α)) := by
  classical
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm
  apply Fintype.card_subtype_le
  rw [Fintype.card_equiv (Equiv.cast rfl)]
  refine' le_trans _ _
  exact (2 : ℕ).factorial
  exact Nat.factorial_le hα
  rw [Nat.factorial_two]
  rw [← Fintype.one_lt_card_iff_nontrivial] at hG 
  exact hG
#align eq_s2_of_nontrivial eq_s2_of_nontrivial

theorem nontrivial_on_equiv_perm_two {K : Type _} [Group K] [MulAction K α]
    (hα : Fintype.card α = 2) {g : K} {a : α} (hga : g • a ≠ a) : IsMultiplyPretransitive K α 2 :=
  by
  classical
  let φ := MulAction.toPermHom K α
  let f : α →ₑ[φ] α :=
    { toFun := id
      map_smul' := fun k x => rfl }
  have hf : Function.Bijective f := Function.bijective_id
  suffices Function.Surjective φ
    by
    rw [is_multiply_pretransitive_of_bijective_map_iff this hf]
    rw [← hα]
    exact equiv_perm_is_fully_pretransitive α
  rw [← MonoidHom.range_top_iff_surjective]
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm
  apply Fintype.card_subtype_le
  suffices hg : to_perm g ∈ φ.range
  · rw [Fintype.card_perm, hα, Nat.factorial_two, Nat.succ_le_iff, Subgroup.one_lt_card_iff_ne_bot]
    intro h; apply hga
    rw [h, Subgroup.mem_bot] at hg 
    simpa using congr_fun (congr_arg coeFn hg) a
  use g
  rfl
#align nontrivial_on_equiv_perm_two nontrivial_on_equiv_perm_two

theorem isPretransitive_of_cycle [DecidableEq α] {g : Equiv.Perm α} (hg : g ∈ G) (hgc : g.IsCycle) :
    IsPretransitive (fixingSubgroup G ((↑g.support : Set α)ᶜ))
      (SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ)) :=
  by
  obtain ⟨a, hga, hgc⟩ := hgc
  have hs : ∀ x : α, g • x ≠ x ↔ x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ) :=
    by
    intro x
    rw [SubMulAction.mem_ofFixingSubgroup_iff]
    simp only [Set.mem_compl_iff, Finset.mem_coe, Equiv.Perm.not_mem_support]
    rfl
  let ha := (hs a).mp hga
  suffices
    ∀ x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ),
      ∃ k : fixingSubgroup G ((↑g.support : Set α)ᶜ), x = k • a
    by
    apply IsPretransitive.mk
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨k, hk⟩ := this x hx
    obtain ⟨k', hk'⟩ := this y hy
    use k' * k⁻¹
    rw [← SetLike.coe_eq_coe]; rw [SetLike.coe_mk]
    simp only [SubMulAction.val_smul_of_tower, SubMulAction.coe_mk]
    rw [hk, hk', smul_smul, inv_mul_cancel_right]
  intro x hx
  have hg' : (⟨g, hg⟩ : ↥G) ∈ fixingSubgroup G ((↑g.support : Set α)ᶜ) :=
    by
    simp_rw [mem_fixingSubgroup_iff G]
    intro y hy
    simpa only [Set.mem_compl_iff, Finset.mem_coe, Equiv.Perm.not_mem_support] using hy
  let g' : fixingSubgroup (↥G) ((↑g.support : Set α)ᶜ) := ⟨(⟨g, hg⟩ : ↥G), hg'⟩
  obtain ⟨i, hi⟩ := hgc ((hs x).mpr hx)
  use g' ^ i; exact hi.symm
#align is_pretransitive_of_cycle isPretransitive_of_cycle

theorem Equiv.Perm.IsSwap.cycleType [DecidableEq α] {σ : Equiv.Perm α} (h : σ.IsSwap) :
    σ.cycleType = {2} := by
  simp only [h.isCycle.cycleType, Equiv.Perm.card_support_eq_two.mpr h]
#align equiv.perm.is_swap.cycle_type Equiv.Perm.IsSwap.cycleType

theorem Equiv.Perm.IsSwap.orderOf [DecidableEq α] {σ : Equiv.Perm α} (h : σ.IsSwap) :
    orderOf σ = 2 := by
  rw [← Equiv.Perm.lcm_cycleType, h.cycleType, Multiset.lcm_singleton, normalize_eq]
#align equiv.perm.is_swap.order_of Equiv.Perm.IsSwap.orderOf

/-- A primitive permutation group that contains a swap is the full permutation group (Jordan)-/
theorem jordan_swap [DecidableEq α] (hG : IsPreprimitive G α) (g : Equiv.Perm α)
    (h2g : Equiv.Perm.IsSwap g) (hg : g ∈ G) : G = ⊤ := by
  classical
  cases' Nat.lt_or_ge (Fintype.card α) 3 with hα3 hα3
  · -- trivial case : Fintype.card α ≤ 2
    rw [Nat.lt_succ_iff] at hα3 
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Fintype.card_subtype_le _)
    rw [Fintype.card_equiv (Equiv.cast rfl)]
    refine' le_trans (Nat.factorial_le hα3) _
    rw [Nat.factorial_two]
    apply Nat.le_of_dvd Fintype.card_pos
    rw [← h2g.orderOf, orderOf_subgroup ⟨g, hg⟩]
    exact orderOf_dvd_card_univ
  -- important case : Fintype.card α ≥ 3
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hα3
  rw [add_comm] at hn 
  let s := (g.support : Set α)
  have hs2 : Fintype.card s = 2 := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe, Equiv.Perm.card_support_eq_two]
    exact h2g
  have hsc : Fintype.card (sᶜ : Set α) = n.succ := by
    rw [Fintype.card_compl_set, hs2, hn]
    simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero, add_eq_zero, and_false, tsub_zero]

  suffices : IsMultiplyPreprimitive G α (Fintype.card α - 1)
  exact this.left.eq_top_of_is_full_minus_one_pretransitive 
  have hn' : Fintype.card α - 1 = 1 + n.succ := by
    rw [hn]
    conv_rhs => rw [add_comm, Nat.succ_eq_add_one]
    simp only [Nat.add_succ_sub_one]
  rw [hn']
  refine' isMultiplyPreprimitive_jordan hG _ _ _
  exact (g.supportᶜ : Set α)
  · rw [← hsc]
    simp only [Fintype.card_ofFinset, Set.mem_compl_iff]
  · rw [hn]
    rw [Nat.one_add, ← Nat.add_one, ← Nat.add_one, add_assoc, add_lt_add_iff_left]
    norm_num
  have : is_pretransitive _ _ := by
    apply isPretransitive_of_cycle hg
    exact Equiv.Perm.IsSwap.isCycle h2g
  apply isPreprimitive_of_prime
  change Nat.Prime (Fintype.card (SubMulAction.ofFixingSubgroup G ((g.support : Set α)ᶜ)).carrier)
  rw [SubMulAction.ofFixingSubgroup.def]
  simp only [compl_compl, Finset.coe_sort_coe, Fintype.card_coe]
  rw [equiv.perm.card_support_eq_two.mpr h2g]
  exact Nat.prime_two
#align jordan_swap jordan_swap

/-- A primitive permutation that contains a 3-cycle contains the alternating group (Jordan) -/
theorem jordan_three_cycle [DecidableEq α] (hG : IsPreprimitive G α) {g : Equiv.Perm α}
    (h3g : Equiv.Perm.IsThreeCycle g) (hg : g ∈ G) : alternatingGroup α ≤ G :=
  by
  cases' Nat.lt_or_ge (Fintype.card α) 4 with hα4 hα4
  · -- trivial case : fintype.card α ≤ 3
    rw [Nat.lt_succ_iff] at hα4 
    apply large_subgroup_of_perm_contains_alternating
    rw [Fintype.card_perm]
    apply le_trans (Nat.factorial_le hα4)
    norm_num
    change 2 * 3 ≤ _
    simp only [mul_le_mul_left, Nat.succ_pos']
    apply Nat.le_of_dvd Fintype.card_pos
    suffices : 3 = orderOf (⟨g, hg⟩ : G)
    rw [this]
    classical
    exact orderOf_dvd_card_univ
    rw [← Equiv.Perm.IsThreeCycle.orderOf h3g]
    conv_lhs => rw [← SetLike.coe_mk g hg]
    apply orderOf_subgroup
    exact One.nonempty
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hα4; rw [add_comm] at hn 
  --  refine is_full_minus_two_pretransitive_iff α _,
  suffices : is_multiply_preprimitive G α (Fintype.card α - 2)
  apply alternating_group_le_of_full_minus_two_pretransitive this.left
  have hn' : Fintype.card α - 2 = 1 + n.succ :=
    by
    rw [hn]
    conv_rhs => rw [add_comm, Nat.succ_eq_add_one]
    simp only [Nat.succ_sub_succ_eq_sub, Nat.add_succ_sub_one]
  rw [hn']
  have hs3 : Fintype.card g.support = 3 :=
    by
    simp only [Fintype.card_coe]
    exact Equiv.Perm.IsThreeCycle.card_support h3g
  refine' isMultiplyPreprimitive_jordan hG _ _ _
  exact (g.supportᶜ : Set α)
  · simp only [Fintype.card_compl_set, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Equiv.Perm.IsThreeCycle.card_support h3g]
    rw [hn]
    simp only [Nat.succ_sub_succ_eq_sub, Nat.add_succ_sub_one]
  · rw [hn]
    rw [Nat.one_add, ← Nat.add_one, ← Nat.add_one, add_assoc, add_lt_add_iff_left]
    norm_num
  have : is_pretransitive _ _ := by
    apply isPretransitive_of_cycle hg
    exact Equiv.Perm.IsThreeCycle.isCycle h3g
  apply isPreprimitive_of_prime
  change Nat.Prime (Fintype.card (SubMulAction.ofFixingSubgroup G ((g.support : Set α)ᶜ)).carrier)
  rw [SubMulAction.ofFixingSubgroup.def]
  simp only [compl_compl, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Equiv.Perm.IsThreeCycle.card_support h3g]
  exact Nat.prime_three
#align jordan_three_cycle jordan_three_cycle

/- -- TODO : prove
theorem jordan_prime_cycle [decidable_eq α] (hG : is_preprimitive G α)
  {p : nat} (hp : prime p) (hp' : p + 3 ≤ fintype.card α)
  {g : equiv.perm α} (hgc : equiv.perm.is_cycle g) (hgp : fintype.card g.support = p)
  (hg : g ∈ G) : alternating_group α ≤ G := sorry
 -/
end Jordan'

#lint


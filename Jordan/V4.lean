/- Copyright (c) 2022 ACL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ACL

! This file was ported from Lean 3 source module V4
-/
import Mathbin.Tactic.Default
import Mathbin.GroupTheory.SpecificGroups.Alternating
import Mathbin.GroupTheory.Abelianization
import Mathbin.GroupTheory.Sylow
import Oneshot.MultipleTransitivity
import Oneshot.MultiplePrimitivity
import Oneshot.IndexNormal
import Oneshot.ConjClassCount

-- import logic.equiv.basic
-- import logic.equiv.basic
-- import tactic.basic tactic.group
-- import tactic.basic tactic.group
-- import group_theory.subgroup.basic
-- import group_theory.subgroup.basic
-- import group_theory.group_action.sub_mul_action
-- import group_theory.group_action.sub_mul_action
-- import group_theory.group_action.embedding
-- import group_theory.group_action.embedding
-- import group_theory.perm.cycle.type
-- import group_theory.perm.cycle.type
-- import group_theory.perm.list
-- import group_theory.perm.list
-- import group_theory.perm.cycle.concrete
-- import group_theory.perm.cycle.concrete
-- import group_theory.group_action.quotient
-- import group_theory.group_action.quotient
namespace alternatingGroup

variable (α : Type _) [DecidableEq α] [Fintype α]

def v4 : Subgroup (alternatingGroup α) :=
  Subgroup.closure {g : alternatingGroup α | (g : Equiv.Perm α).cycleType = {2, 2}}
#align alternating_group.V4 alternatingGroup.v4

theorem mem_V4_of_order_two_pow (hα4 : Fintype.card α = 4) (g : Equiv.Perm α)
    (hg0 : g ∈ alternatingGroup α) (n : ℕ) (hg : orderOf g ∣ 2 ^ n) :
    g.cycleType = { } ∨ g.cycleType = {2, 2} :=
  by
  rw [← Equiv.Perm.lcm_cycleType] at hg 
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType] at hg0 
  have hg4 : g.cycle_type.sum ≤ 4 := by rw [← hα4]; rw [Equiv.Perm.sum_cycleType];
    apply Finset.card_le_univ
  by_cases h4 : 4 ∈ g.cycle_type
  · exfalso
    suffices : g.cycle_type = {4}
    rw [this, ← Units.eq_iff] at hg0 ; norm_num at hg0 
    rw [← Multiset.cons_erase h4]
    apply symm
    rw [Multiset.singleton_eq_cons_iff]
    apply And.intro rfl
    rw [← Multiset.cons_erase h4] at hg4 
    simp only [Multiset.sum_cons, add_le_iff_nonpos_right, le_zero_iff, Multiset.sum_eq_zero_iff] at
      hg4 
    ext x; simp only [Multiset.count_zero, Multiset.count_eq_zero]
    intro hx
    apply not_le.mpr (Equiv.Perm.one_lt_of_mem_cycleType (Multiset.mem_of_mem_erase hx))
    rw [hg4 x hx]; norm_num
  · -- we know 4 ∉ g.cycle_type,
    suffices g.cycle_type = Multiset.replicate g.cycle_type.card 2
      by
      rw [this] at hg0 
      simp only [pow_add, pow_mul, Multiset.sum_replicate, Algebra.id.smul_eq_mul,
        Multiset.card_replicate, Int.units_sq, one_mul] at hg0 
      -- prove : g.cycle_type.card ≤ 2
      have hk2 : g.cycle_type.card ≤ 2 := by
        rw [this] at hg4 ; rw [Multiset.sum_replicate] at hg4 
        apply Nat.le_of_mul_le_mul_left; rw [Nat.mul_comm 2]
        exact hg4
        norm_num
      cases' Nat.eq_or_lt_of_le hk2 with hk2 hk1
      -- g.cycle_type.card = 2
      rw [hk2] at this ;
      simp only [this]
      simp only [Finset.mem_univ, Multiset.replicate_succ, Multiset.replicate_one,
        Multiset.empty_eq_zero, Multiset.cons_ne_zero, Multiset.insert_eq_cons, eq_self_iff_true,
        false_or_iff, and_self_iff]
      -- we know : g.cycle_type.card ≤ 1
      rw [Nat.lt_succ_iff] at hk1 
      cases' Nat.eq_or_lt_of_le hk1 with hk1 hk0
      -- g.cycle_type.card = 1 : exfalso
      exfalso;
      rw [hk1, ← Units.eq_iff] at hg0 ; norm_num at hg0 
      -- g.cycle_type.card = 0
      simp only [Nat.lt_one_iff] at hk0 
      rw [hk0] at this ; simp only [this]
      simp
    rw [Multiset.eq_replicate_card]
    intro i hi
    have := dvd_trans (Multiset.dvd_lcm hi) hg
    rw [Nat.dvd_prime_pow] at this 
    obtain ⟨k, ⟨hk, rfl⟩⟩ := this
    suffices : k = 1; rw [this]; norm_num
    apply le_antisymm
    rw [← not_lt]; intro hk1
    suffices : k = 2
    apply h4; rw [this] at hi ; exact hi
    refine' le_antisymm _ hk1
    · -- k ≤ 2
      rw [← Nat.pow_le_iff_le_right (Nat.le_refl 2)]
      norm_num; rw [← hα4]
      apply le_trans (Equiv.Perm.le_card_support_of_mem_cycleType hi)
      apply Finset.card_le_univ
    rw [Nat.one_le_iff_ne_zero]; intro hk0
    rw [hk0] at hi ; norm_num at hi 
    apply Nat.lt_irrefl 1; exact Equiv.Perm.one_lt_of_mem_cycleType hi
    exact Nat.prime_two
#align alternating_group.mem_V4_of_order_two_pow alternatingGroup.mem_V4_of_order_two_pow

open scoped Classical

theorem A4_card (hα4 : Fintype.card α = 4) : Fintype.card (alternatingGroup α) = 12 :=
  by
  have : Nontrivial α; rw [← Fintype.one_lt_card_iff_nontrivial, hα4]; norm_num
  apply mul_right_injective₀ _
  rw [two_mul_card_alternatingGroup, Fintype.card_perm, hα4]
  norm_num
  infer_instance; infer_instance
  norm_num
#align alternating_group.A4_card alternatingGroup.A4_card

theorem A4_sylow_card (hα4 : Fintype.card α = 4) (S : Sylow 2 (alternatingGroup α)) :
    Fintype.card S = 4 :=
  by
  rw [Sylow.card_eq_multiplicity, ← Nat.factors_count_eq, A4_card α hα4]
  suffices : Nat.factors 12 ~ [2, 2, 3]
  rw [List.Perm.count_eq this]; norm_num
  apply symm
  apply Nat.factors_unique
  norm_num
  norm_num
  exact ⟨Nat.prime_two, Nat.prime_three⟩
#align alternating_group.A4_sylow_card alternatingGroup.A4_sylow_card

theorem A4_sylow_carrier (hα4 : Fintype.card α = 4) (S : Sylow 2 (alternatingGroup α)) :
    S.carrier =
      {g : alternatingGroup α |
        (g : Equiv.Perm α).cycleType = 0 ∨ (g : Equiv.Perm α).cycleType = {2, 2}} :=
  by
  apply Set.eq_of_subset_of_card_le
  · -- inclusion S ⊆ (cycle_type = 0 ∨ cycle_type = { 2, 2 })
    intro k hk
    simp only [Set.mem_setOf_eq]
    obtain ⟨n, hn⟩ := (is_p_group.iff_order_of.mp S.is_p_group') ⟨k, hk⟩
    apply mem_V4_of_order_two_pow α hα4 (↑k) k.prop n
    rw [← orderOf_subgroup ⟨k, hk⟩, Subgroup.coe_mk] at hn 
    rw [orderOf_subgroup, hn]
  -- card K4 ≤ card S
  change _ ≤ Fintype.card S
  rw [A4_sylow_card α hα4 S]
  apply le_trans (Fintype.card_subtype_or _ _)
  rw [Fintype.card_subtype]; rw [Fintype.card_subtype]
  simp only [OnCycleFactors.AlternatingGroup.card_of_cycleType, hα4]
  norm_num
#align alternating_group.A4_sylow_carrier alternatingGroup.A4_sylow_carrier

theorem v4_is_unique_sylow (hα4 : Fintype.card α = 4) (S : Sylow 2 (alternatingGroup α)) :
    v4 α = S := by
  classical
  apply le_antisymm
  · simp only [V4]; rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, ← Subgroup.mem_carrier, ← Sylow.toSubgroup_eq_coe,
      A4_sylow_carrier α hα4 S, Set.mem_setOf_eq]
    apply Or.intro_right; exact hg
  · intro k hk
    rw [← Sylow.toSubgroup_eq_coe, ← Subgroup.mem_carrier, A4_sylow_carrier α hα4 S,
      Set.mem_setOf_eq] at hk 
    cases' hk with hk hk
    · suffices hk : k = 1; rw [hk]; exact Subgroup.one_mem _
      rw [← Subtype.coe_inj, Subgroup.coe_one, ← Equiv.Perm.cycleType_eq_zero, hk]
    · simp only [V4]
      apply Subgroup.subset_closure
      simp only [Set.mem_setOf_eq]
      exact hk
#align alternating_group.V4_is_unique_sylow alternatingGroup.v4_is_unique_sylow

theorem A4_card_two_sylow_eq_one (hα4 : Fintype.card α = 4) :
    Fintype.card (Sylow 2 (alternatingGroup α)) = 1 :=
  by
  rw [Fintype.card_eq_one_iff]
  obtain ⟨S : Sylow 2 (alternatingGroup α)⟩ := Sylow.nonempty
  use S
  intro T
  rw [Sylow.ext_iff]
  rw [← V4_is_unique_sylow α hα4 S]
  rw [V4_is_unique_sylow α hα4 T]
#align alternating_group.A4_card_two_sylow_eq_one alternatingGroup.A4_card_two_sylow_eq_one

theorem v4_is_characteristic (hα4 : Fintype.card α = 4) : (v4 α).Characteristic :=
  by
  obtain ⟨S : Sylow 2 (alternatingGroup α)⟩ := Sylow.nonempty
  rw [V4_is_unique_sylow α hα4 S]
  refine' Sylow.characteristic_of_normal S _
  rw [← Subgroup.normalizer_eq_top]
  rw [← Subgroup.index_eq_one]
  rw [← card_sylow_eq_index_normalizer]
  exact A4_card_two_sylow_eq_one α hα4
#align alternating_group.V4_is_characteristic alternatingGroup.v4_is_characteristic

/- rw ← V4_is_unique_sylow α hα4 S,
  exact V4_is_normal α hα4, -/
theorem v4_is_normal (hα4 : Fintype.card α = 4) : (v4 α).Normal :=
  by
  haveI := V4_is_characteristic α hα4
  infer_instance
#align alternating_group.V4_is_normal alternatingGroup.v4_is_normal

/-  obtain ⟨S : sylow 2 (alternating_group α)⟩ := sylow.nonempty ,
  rw V4_is_unique_sylow α hα4 S,
  rw ← subgroup.normalizer_eq_top ,
  rw ← subgroup.index_eq_one,
  rw ← card_sylow_eq_index_normalizer,
  exact A4_card_two_sylow_eq_one α hα4, -/
theorem v4_card (hα4 : Fintype.card α = 4) : Fintype.card (v4 α) = 4 :=
  by
  obtain ⟨S : Sylow 2 (alternatingGroup α)⟩ := Sylow.nonempty
  rw [V4_is_unique_sylow α hα4 S]
  change Fintype.card S = 4
  exact A4_sylow_card α hα4 S
#align alternating_group.V4_card alternatingGroup.v4_card

theorem isCommutative_of_exponent_two (G : Type _) [Group G] (hG2 : ∀ g : G, g ^ 2 = 1) :
    IsCommutative G (· * ·) := by
  suffices : ∀ g : G, g⁻¹ = g
  apply IsCommutative.mk
  intro a b
  rw [← mul_inv_eq_iff_eq_mul, ← mul_inv_eq_one, this, this, ← hG2 (a * b), pow_two,
    mul_assoc (a * b) a b]
  · intro g; rw [← mul_eq_one_iff_inv_eq, ← hG2 g, pow_two]
#align alternating_group.is_commutative_of_exponent_two alternatingGroup.isCommutative_of_exponent_two

theorem v4_carrier_eq (hα4 : Fintype.card α = 4) :
    (v4 α).carrier =
      {g : alternatingGroup α |
        (g : Equiv.Perm α).cycleType = 0 ∨ (g : Equiv.Perm α).cycleType = {2, 2}} :=
  by
  obtain ⟨S : Sylow 2 (alternatingGroup α)⟩ := Sylow.nonempty
  rw [V4_is_unique_sylow α hα4 S]
  simpa only [Sylow.toSubgroup_eq_coe] using A4_sylow_carrier α hα4 S
#align alternating_group.V4_carrier_eq alternatingGroup.v4_carrier_eq

theorem v4_is_of_exponent_two (hα4 : Fintype.card α = 4) : ∀ g : v4 α, g ^ 2 = 1 :=
  by
  rintro ⟨⟨g, hg⟩, hg'⟩
  simp only [← Subtype.coe_inj, SubmonoidClass.mk_pow, Subgroup.coe_mk, Subgroup.coe_one]
  rw [← Subgroup.mem_carrier, V4_carrier_eq α hα4] at hg' 
  cases' hg' with hg' hg'
  · simp only [Subgroup.coe_mk, Equiv.Perm.cycleType_eq_zero] at hg' 
    simp only [hg', one_pow]
  · convert pow_orderOf_eq_one g
    simp only [Subgroup.coe_mk] at hg' 
    rw [← Equiv.Perm.lcm_cycleType, hg']
    norm_num
#align alternating_group.V4_is_of_exponent_two alternatingGroup.v4_is_of_exponent_two

theorem v4_isCommutative (hα4 : Fintype.card α = 4) : (v4 α).IsCommutative :=
  by
  refine' { is_comm := _ }
  apply is_commutative_of_exponent_two
  exact V4_is_of_exponent_two α hα4
#align alternating_group.V4_is_commutative alternatingGroup.v4_isCommutative

theorem Subgroup.quotient_isCommutative_iff_commutator_le {G : Type _} [Group G] (H : Subgroup G)
    [nH : H.Normal] : IsCommutative (G ⧸ H) (· * ·) ↔ commutator G ≤ H :=
  by
  constructor
  · intro h
    simp only [commutator_eq_closure, Subgroup.closure_le]
    rintro g ⟨g1, g2, rfl⟩
    simp only [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
    rw [← QuotientGroup.mk'_apply, map_commutatorElement (QuotientGroup.mk' H) g1 g2]
    simp only [QuotientGroup.mk'_apply, commutatorElement_eq_one_iff_mul_comm, h.comm]
  · intro h
    apply IsCommutative.mk
    intro a b
    obtain ⟨g1, rfl⟩ := QuotientGroup.mk'_surjective H a
    obtain ⟨g2, rfl⟩ := QuotientGroup.mk'_surjective H b
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement _ g1 g2]
    rw [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff]
    apply h
    apply Subgroup.commutator_mem_commutator
    refine' Subgroup.mem_top g1
    refine' Subgroup.mem_top g2
#align alternating_group.subgroup.quotient_is_commutative_iff_commutator_le alternatingGroup.Subgroup.quotient_isCommutative_iff_commutator_le

example (hα4 : 4 ≤ Fintype.card α) (a b : α) (hab : a ≠ b) : ∃ c : α, c ≠ a ∧ c ≠ b :=
  by
  suffices : ({a, b} : Finset α)ᶜ.Nonempty
  obtain ⟨c, hc⟩ := this
  use c
  simp only [Finset.compl_insert, Finset.mem_erase, Finset.mem_compl, Finset.mem_singleton] at hc ;
  exact hc
  rw [← Finset.card_compl_lt_iff_nonempty, compl_compl]
  refine' lt_of_lt_of_le _ hα4
  rw [Finset.card_doubleton hab]
  norm_num

theorem AlternatingGroup.center_bot (hα4 : 4 ≤ Fintype.card α) : (alternatingGroup α).center = ⊥ :=
  by
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hg'
  simp only [Subgroup.mem_bot]
  simp only [← Subtype.coe_inj, Subgroup.coe_mk, Subgroup.coe_one]
  rw [← Equiv.Perm.support_eq_empty_iff]
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro a ha; let b := g a
  have hab : b ≠ a := by simp only [b]; rw [← Equiv.Perm.mem_support]; exact ha
  have : ({a, b} : Finset α)ᶜ.Nonempty :=
    by
    rw [← Finset.card_compl_lt_iff_nonempty, compl_compl, Finset.card_doubleton hab.symm]
    refine' lt_of_lt_of_le (by norm_num) hα4
  obtain ⟨c, hc⟩ := this
  simp only [Finset.compl_insert, Finset.mem_erase, Ne.def, Finset.mem_compl,
    Finset.mem_singleton] at hc 
  have h2trans : MulAction.IsMultiplyPretransitive (alternatingGroup α) α 2 :=
    by
    refine'
      MulAction.isMultiplyPretransitive_of_higher (alternatingGroup α) α
        (MulAction.alternatingGroup_is_fully_minus_two_pretransitive α) _ _
    rw [Nat.le_sub_iff_right]
    exact hα4
    exact le_trans (by norm_num) hα4
    simp only [PartENat.card_eq_coe_fintype_card, PartENat.coe_le_coe, tsub_le_self]
  rw [MulAction.is_two_pretransitive_iff] at h2trans 
  obtain ⟨k, hk, hk'⟩ := h2trans a b a c hab.symm (Ne.symm hc.left)
  suffices : k • (⟨g, hg⟩ : alternatingGroup α) • a ≠ c
  apply this; rw [← hk']; rfl
  suffices : k • (⟨g, hg⟩ : alternatingGroup α) • a = (⟨g, hg⟩ : alternatingGroup α) • k • a
  rw [this, hk]; exact Ne.symm hc.right
  rw [Subgroup.mem_center_iff] at hg' 
  specialize hg' k
  simp only [smul_smul, hg']
#align alternating_group.alternating_group.center_bot alternatingGroup.AlternatingGroup.center_bot

theorem v4_eq_commutator (hα4 : Fintype.card α = 4) : v4 α = commutator (alternatingGroup α) :=
  by
  haveI : (V4 α).Normal := V4_is_normal α hα4
  have comm_le : commutator (alternatingGroup α) ≤ V4 α
  rw [← subgroup.quotient_is_commutative_iff_commutator_le]
  · apply isCommutative_of_prime_order _
    infer_instance
    exact 3
    exact Nat.fact_prime_three
    apply mul_left_injective₀ _
    dsimp
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup, V4_card α hα4, A4_card α hα4]
    norm_num
    infer_instance; infer_instance
    rw [V4_card α hα4]; norm_num
  have comm_ne_bot : commutator (alternatingGroup α) ≠ ⊥ :=
    by
    intro h
    simp only [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.centralizer_top,
      ← eq_top_iff] at h 
    rw [alternating_group.center_bot _] at h 
    suffices : Nat.card (alternatingGroup α) ≠ 1
    apply this; rw [← Subgroup.index_bot, h, Subgroup.index_top]
    apply Ne.symm
    apply ne_of_lt
    rw [Finite.one_lt_card_iff_nontrivial]
    apply nontrivial_of_three_le_card
    rw [hα4]; norm_num
    rw [hα4]
  obtain ⟨k, hk, hk'⟩ := Or.resolve_left (Subgroup.bot_or_exists_ne_one _) comm_ne_bot
  suffices hk22 : (k : Equiv.Perm α).cycleType = {2, 2}
  refine' le_antisymm _ comm_le
  intro g hg
  rw [← Subgroup.mem_carrier, V4_carrier_eq α hα4] at hg 
  cases' hg with hg hg
  · rw [Equiv.Perm.cycleType_eq_zero, OneMemClass.coe_eq_one] at hg 
    rw [hg]
    exact Subgroup.one_mem _
  · rw [← hg, ← Equiv.Perm.isConj_iff_cycleType_eq, isConj_iff] at hk22 
    obtain ⟨c, hc⟩ := hk22
    rw [← MulAut.conjNormal_apply, Subtype.coe_inj] at hc 
    simp only [commutator, ← hc]
    let fc : MulAut (alternatingGroup α) := MulAut.conjNormal c
    suffices :
      (⊤ : Subgroup (alternatingGroup α)) =
        Subgroup.map fc.to_monoid_hom (⊤ : Subgroup (alternatingGroup α))
    rw [this, ← Subgroup.map_commutator]
    refine' Subgroup.mem_map_of_mem _ hk
    · apply symm
      rw [← MonoidHom.range_eq_map]
      rw [MonoidHom.range_top_iff_surjective]
      exact MulEquiv.surjective _
  · have hk2 := comm_le hk
    rw [← Subgroup.mem_carrier, V4_carrier_eq α hα4] at hk2 
    cases' hk2 with hk2 hk2
    · exfalso
      apply hk'
      rw [Equiv.Perm.cycleType_eq_zero] at hk2 
      simp only [← Subtype.coe_inj, hk2, Subgroup.coe_one]
    exact hk2
#align alternating_group.V4_eq_commutator alternatingGroup.v4_eq_commutator

end alternatingGroup


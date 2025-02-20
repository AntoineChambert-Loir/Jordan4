/- Copyright (c) 2022 ACL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ACL

! This file was ported from Lean 3 source module V4
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Abelianization
import Mathlib.GroupTheory.Sylow
import Jordan.MultipleTransitivity
import Jordan.MultiplePrimitivity
import Jordan.IndexNormal
import Jordan.ConjClassCount

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

def V4 : Subgroup (alternatingGroup α) :=
  Subgroup.closure {g : alternatingGroup α | (g : Equiv.Perm α).cycleType = {2, 2}}

theorem mem_V4_of_order_two_pow (hα4 : Fintype.card α = 4) (g : Equiv.Perm α)
    (hg0 : g ∈ alternatingGroup α) (n : ℕ) (hg : orderOf g ∣ 2 ^ n) :
    g.cycleType = { } ∨ g.cycleType = {2, 2} := by
  rw [← Equiv.Perm.lcm_cycleType] at hg
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType] at hg0
  have hg4 : g.cycleType.sum ≤ 4 := by
    rw [← hα4, Equiv.Perm.sum_cycleType]
    apply Finset.card_le_univ
  by_cases h4 : 4 ∈ g.cycleType
  · exfalso
    suffices g.cycleType = {4} by
      rw [this, ← Units.eq_iff] at hg0 ; norm_num at hg0
    rw [← Multiset.cons_erase h4]
    apply symm
    rw [Multiset.singleton_eq_cons_iff]
    apply And.intro rfl
    rw [← Multiset.cons_erase h4] at hg4
    simp only [Multiset.sum_cons, add_le_iff_nonpos_right, le_zero_iff, Multiset.sum_eq_zero_iff] at hg4
    ext x; simp only [Multiset.count_zero, Multiset.count_eq_zero]
    intro hx
    apply not_le.mpr (Equiv.Perm.one_lt_of_mem_cycleType (Multiset.mem_of_mem_erase hx))
    rw [hg4 x hx]; norm_num
  · -- we know 4 ∉ g.cycleType,
    suffices g.cycleType = Multiset.replicate (Multiset.card g.cycleType) 2 by
      rw [this] at hg0
      simp only [pow_add, pow_mul, Multiset.sum_replicate, Algebra.id.smul_eq_mul,
        Multiset.card_replicate, Int.units_sq, one_mul] at hg0
      -- prove : Multiset.card g.cycleType ≤ 2
      have hk2 : Multiset.card g.cycleType ≤ 2 := by
        rw [this] at hg4 ; rw [Multiset.sum_replicate] at hg4
        apply Nat.le_of_mul_le_mul_left; rw [Nat.mul_comm 2]
        exact hg4
        norm_num
      cases' Nat.eq_or_lt_of_le hk2 with hk2 hk1
      · -- g.cycleType.card = 2
        rw [hk2] at this ;
        simp only [this]
        simp only [Finset.mem_univ, Multiset.replicate_succ, Multiset.replicate_one,
          Multiset.empty_eq_zero, Multiset.cons_ne_zero, Multiset.insert_eq_cons, eq_self_iff_true,
          false_or_iff, and_self_iff]
        simp only [Multiset.replicate_zero, Multiset.cons_zero]
      · -- we know : g.cycleType.card ≤ 1
        rw [Nat.lt_succ_iff] at hk1
        cases' Nat.eq_or_lt_of_le hk1 with hk1 hk0
        -- g.cycleType.card = 1 : exfalso
        exfalso
        rw [hk1, ← Units.eq_iff] at hg0 ; norm_num at hg0
        -- g.cycleType.card = 0
        simp only [Nat.lt_one_iff] at hk0
        rw [hk0] at this ; simp only [this]
        left
        simp only [Multiset.replicate_zero, Multiset.empty_eq_zero]
    rw [Multiset.eq_replicate_card]
    intro i hi
    have : i ∣ 2 ^ n := by
      apply Nat.dvd_trans _ hg
      exact Multiset.dvd_lcm hi
    rw [Nat.dvd_prime_pow] at this
    obtain ⟨k, hk, hlcm⟩ := this
    suffices k = 1 by
      rw [hlcm, this]; norm_num
    apply le_antisymm
    rw [← not_lt]; intro hk1
    suffices k = 2 by
      apply h4
      rw [this] at hlcm ; norm_num at hlcm
      rw [← hlcm]
      exact hi
    refine le_antisymm ?_ hk1
    · -- k ≤ 2
      rw [← Nat.pow_le_pow_iff_right (Nat.le_refl 2)]
      norm_num; rw [← hα4, ← hlcm]
      apply le_trans (Equiv.Perm.le_card_support_of_mem_cycleType hi)
      apply Finset.card_le_univ
    rw [Nat.one_le_iff_ne_zero]
    intro hk0
    rw [hk0] at hlcm ; norm_num at hlcm
    rw [hlcm] at hi
    apply Nat.lt_irrefl 1
    exact Equiv.Perm.one_lt_of_mem_cycleType hi
    exact Nat.prime_two

open scoped Classical

theorem A4_card (hα4 : Fintype.card α = 4) :
    Fintype.card (alternatingGroup α) = 12 := by
  have : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hα4]
    norm_num
  apply mul_right_injective₀ (_: 2 ≠ 0)
  dsimp
  rw [two_mul_card_alternatingGroup, Fintype.card_perm, hα4]
  all_goals
    norm_num
  rfl

theorem A4_sylow_card (hα4 : Fintype.card α = 4) (S : Sylow 2 (alternatingGroup α)) :
    Fintype.card S = 4 := by
  rw [← Nat.card_eq_fintype_card]
  rw [Sylow.card_eq_multiplicity, ← Nat.primeFactorsList_count_eq, Nat.card_eq_fintype_card,
    A4_card α hα4]
  rfl

theorem A4_sylow_carrier (hα4 : Fintype.card α = 4) (S : Sylow 2 (alternatingGroup α)) :
    S.carrier =
      {g : alternatingGroup α |
        (g : Equiv.Perm α).cycleType = 0 ∨ (g : Equiv.Perm α).cycleType = {2, 2}} := by
  apply Set.eq_of_subset_of_card_le
  · -- inclusion S ⊆ (cycleType = 0 ∨ cycleType = { 2, 2 })
    intro k hk
    simp only [Set.mem_setOf_eq]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨k, hk⟩
    apply mem_V4_of_order_two_pow α hα4 (↑k) k.prop n
    rw [← orderOf_submonoid ⟨k, hk⟩, Subgroup.coe_mk] at hn
    rw [orderOf_submonoid, hn]
  -- card K4 ≤ card S
  change _ ≤ Fintype.card S
  rw [A4_sylow_card α hα4 S]
  apply le_trans (Fintype.card_subtype_or _ _)
  rw [Fintype.card_subtype]; rw [Fintype.card_subtype]
  simp only [OnCycleFactors.AlternatingGroup.card_of_cycleType, hα4]
  norm_num
  rfl

theorem V4_is_unique_sylow (hα4 : Fintype.card α = 4) (S : Sylow 2 (alternatingGroup α)) :
    V4 α = S := by
  classical
  apply le_antisymm
  · simp only [V4]; rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, ← Subgroup.mem_carrier, A4_sylow_carrier α hα4 S, Set.mem_setOf_eq]
    apply Or.intro_right
    exact hg
  · intro k
    rw [← Subgroup.mem_carrier, A4_sylow_carrier α hα4 S, Set.mem_setOf_eq, or_imp]
    constructor
    · intro hk
      suffices hk : k = 1 by
        rw [hk]; exact Subgroup.one_mem _
      rw [← Subtype.coe_inj, Subgroup.coe_one, ← Equiv.Perm.cycleType_eq_zero, hk]
    · intro hk
      simp only [V4]
      apply Subgroup.subset_closure
      simp only [Set.mem_setOf_eq]
      exact hk

theorem A4_card_two_sylow_eq_one (hα4 : Fintype.card α = 4) :
    Fintype.card (Sylow 2 (alternatingGroup α)) = 1 := by
  rw [Fintype.card_eq_one_iff]
  obtain ⟨S : Sylow 2 (alternatingGroup α)⟩ := Sylow.nonempty (G := alternatingGroup α)
  use S
  intro T
  rw [Sylow.ext_iff]
  rw [← V4_is_unique_sylow α hα4 S]
  rw [V4_is_unique_sylow α hα4 T]

theorem V4_is_characteristic (hα4 : Fintype.card α = 4) : (V4 α).Characteristic := by
  obtain ⟨S : Sylow 2 (alternatingGroup α)⟩ := Sylow.nonempty (G := alternatingGroup α)
  rw [V4_is_unique_sylow α hα4 S]
  refine Sylow.characteristic_of_normal S ?_
  rw [← Subgroup.normalizer_eq_top]
  rw [← Subgroup.index_eq_one]
  rw [← card_sylow_eq_index_normalizer]
  rw [Nat.card_eq_fintype_card]
  exact A4_card_two_sylow_eq_one α hα4

/- rw ← V4_is_unique_sylow α hα4 S,
  exact V4_is_normal α hα4, -/
theorem V4_is_normal (hα4 : Fintype.card α = 4) : (V4 α).Normal :=
  by
  haveI := V4_is_characteristic α hα4
  infer_instance

/-  obtain ⟨S : sylow 2 (alternating_group α)⟩ := sylow.nonempty ,
  rw V4_is_unique_sylow α hα4 S,
  rw ← subgroup.normalizer_eq_top ,
  rw ← subgroup.index_eq_one,
  rw ← card_sylow_eq_index_normalizer,
  exact A4_card_two_sylow_eq_one α hα4, -/
theorem V4_card (hα4 : Fintype.card α = 4) : Fintype.card (V4 α) = 4 := by
  obtain ⟨S : Sylow 2 (alternatingGroup α)⟩ := Sylow.nonempty (G := alternatingGroup α)
  rw [V4_is_unique_sylow α hα4 S]
  change Fintype.card S = 4
  exact A4_sylow_card α hα4 S

theorem isCommutative_of_exponent_two {G : Type _} [Group G] (hG2 : ∀ g : G, g ^ 2 = 1) :
    Std.Commutative (α := G) (· * ·) := by
  suffices ∀ g : G, g⁻¹ = g by
    constructor
    intro a b
    rw [← mul_inv_eq_iff_eq_mul, ← mul_inv_eq_one, this, this, ← hG2 (a * b), pow_two,
      mul_assoc (a * b) a b]
  intro g; rw [← mul_eq_one_iff_inv_eq, ← hG2 g, pow_two]

theorem V4_carrier_eq (hα4 : Fintype.card α = 4) :
    (V4 α).carrier =
      {g : alternatingGroup α |
        (g : Equiv.Perm α).cycleType = 0 ∨ (g : Equiv.Perm α).cycleType = {2, 2}} := by
  obtain ⟨S : Sylow 2 (alternatingGroup α)⟩ := Sylow.nonempty (G := alternatingGroup α)
  rw [V4_is_unique_sylow α hα4 S]
  rw [A4_sylow_carrier α hα4 S]

theorem V4_is_of_exponent_two (hα4 : Fintype.card α = 4) :
    ∀ g : V4 α, g ^ 2 = 1 := by
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

theorem V4_isCommutative (hα4 : Fintype.card α = 4) :
    (V4 α).IsCommutative := by
  refine { is_comm := isCommutative_of_exponent_two (V4_is_of_exponent_two α hα4) }

theorem Subgroup.quotient_isCommutative_iff_commutator_le {G : Type _} [Group G] (H : Subgroup G)
    [nH : H.Normal] : Std.Commutative (α := G ⧸ H) (· * ·) ↔ commutator G ≤ H := by
  constructor
  · intro h
    simp only [commutator_eq_closure, Subgroup.closure_le]
    rintro g ⟨g1, g2, rfl⟩
    simp only [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
    rw [← QuotientGroup.mk'_apply, map_commutatorElement (QuotientGroup.mk' H) g1 g2]
    simp only [QuotientGroup.mk'_apply, commutatorElement_eq_one_iff_mul_comm, h.comm]
  · intro h
    constructor
    intro a b
    obtain ⟨g1, rfl⟩ := QuotientGroup.mk'_surjective H a
    obtain ⟨g2, rfl⟩ := QuotientGroup.mk'_surjective H b
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement _ g1 g2]
    rw [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff]
    apply h
    apply Subgroup.commutator_mem_commutator
    refine Subgroup.mem_top g1
    refine Subgroup.mem_top g2

theorem center_bot (hα4 : 4 ≤ Fintype.card α) :
    Subgroup.center (alternatingGroup α) = ⊥ := by
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
    rw [← Finset.card_compl_lt_iff_nonempty, compl_compl, Finset.card_pair hab.symm]
    refine lt_of_lt_of_le (by norm_num) hα4
  obtain ⟨c, hc⟩ := this
  simp only [Finset.compl_insert, Finset.mem_erase, Ne, Finset.mem_compl,
    Finset.mem_singleton] at hc
  have h2trans : MulAction.IsMultiplyPretransitive (alternatingGroup α) α 2 := by
    refine MulAction.isMultiplyPretransitive_of_higher (alternatingGroup α) α
      (MulAction.IsMultiplyPretransitive.alternatingGroup_of_sub_two α) ?_ ?_
    exact Nat.le_sub_of_add_le hα4
    simp
  rw [MulAction.is_two_pretransitive_iff] at h2trans
  obtain ⟨k, hk, hk'⟩ := h2trans a b a c hab.symm (Ne.symm hc.left)
  suffices k • (⟨g, hg⟩ : alternatingGroup α) • a ≠ c by
    apply this; rw [← hk']; rfl
  suffices k • (⟨g, hg⟩ : alternatingGroup α) • a = (⟨g, hg⟩ : alternatingGroup α) • k • a by
    rw [this, hk]; exact Ne.symm hc.right
  rw [Subgroup.mem_center_iff] at hg'
  specialize hg' k
  simp only [smul_smul, hg']

theorem V4_eq_commutator (hα4 : Fintype.card α = 4) :
    V4 α = commutator (alternatingGroup α) := by
  haveI : (V4 α).Normal := V4_is_normal α hα4
  have comm_le : commutator (alternatingGroup α) ≤ V4 α := by
    rw [← Subgroup.quotient_isCommutative_iff_commutator_le]
    · apply isCommutative_of_prime_order (hp := Nat.fact_prime_three) _
      apply mul_left_injective₀ _
      dsimp
      rw [← Nat.card_eq_fintype_card, ← Subgroup.card_eq_card_quotient_mul_card_subgroup,
        Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,V4_card α hα4, A4_card α hα4]
      have : Nonempty (V4 α) := by exact One.instNonempty
      exact Nat.card_pos.ne'
  have comm_ne_bot : commutator (alternatingGroup α) ≠ ⊥ := by
    have : Nontrivial (Subgroup (alternatingGroup α)) := by
      rw [Subgroup.nontrivial_iff]
      rw [← Fintype.one_lt_card_iff_nontrivial]
      rw [A4_card α hα4]
      norm_num
    rw [Ne, commutator, Subgroup.commutator_eq_bot_iff_le_centralizer,
      ← eq_top_iff, Subgroup.coe_top, Subgroup.centralizer_univ,
      alternatingGroup.center_bot _]
    exact bot_ne_top
    rw [hα4]
  obtain ⟨k, hk, hk'⟩ := Or.resolve_left (Subgroup.bot_or_exists_ne_one _) comm_ne_bot
  suffices hk22 : (k : Equiv.Perm α).cycleType = {2, 2} by
    refine le_antisymm ?_ comm_le
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
      suffices (⊤ : Subgroup (alternatingGroup α)) =
        Subgroup.map fc.toMonoidHom (⊤ : Subgroup (alternatingGroup α)) by
        rw [this, ← Subgroup.map_commutator]
        refine Subgroup.mem_map_of_mem _ hk
      apply symm
      rw [← MonoidHom.range_eq_map]
      rw [MonoidHom.range_top_iff_surjective]
      exact MulEquiv.surjective _
  have hk2 := comm_le hk
  rw [← Subgroup.mem_carrier, V4_carrier_eq α hα4] at hk2
  cases' hk2 with hk2 hk2
  · exfalso
    apply hk'
    rw [Equiv.Perm.cycleType_eq_zero] at hk2
    simp only [← Subtype.coe_inj, hk2, Subgroup.coe_one]
  · exact hk2

end alternatingGroup

/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
! This file was ported from Lean 3 source module index_normal
-/
import Mathbin.GroupTheory.Index
import Mathbin.GroupTheory.SpecificGroups.Alternating
import Mathbin.GroupTheory.SpecificGroups.Cyclic
import Mathbin.GroupTheory.Sylow
import Mathbin.Data.Fintype.Basic

/-!
# Some complements on finite groups

- A subgroup of index two is normal
- A subgroup whose index is the smallest prime factor of the cardinal is normal
- The alternating group is characteristic

-/


open scoped Classical

variable {α : Type _} [Fintype α] [DecidableEq α]

/-- The alternating group of a subsingleton is ⊥ -/
theorem alternatingGroup_of_subsingleton (hα : Subsingleton α) :
    alternatingGroup α = (⊥ : Subgroup (Equiv.Perm α)) :=
  by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  let hα := @alternatingGroup.unique α _ _ hα
  rw [← SetLike.coe_mk g hg]
  rw [← Subgroup.coe_one (alternatingGroup α)]
  let hαq := hα.uniq
  rw [SetLike.coe_eq_coe]
  rw [hαq 1]; rw [hαq ⟨g, hg⟩]
#align alternating_group_of_subsingleton alternatingGroup_of_subsingleton

variable (α)

/-- The alternating group is a characteristic subgroup -/
theorem alternating_is_characteristic : (alternatingGroup α).Characteristic :=
  by
  cases' subsingleton_or_nontrivial α with hα hα
  -- hα : subsingleton α
  · rw [alternatingGroup_of_subsingleton hα]
    exact Subgroup.botCharacteristic
  -- hα : nontrivial α
  skip
  apply Subgroup.Characteristic.mk
  intro φ
  rw [alternatingGroup_eq_sign_ker]
  rw [MonoidHom.comap_ker]
  let s := equiv.perm.sign.comp φ.to_monoid_hom
  have hs : Function.Surjective s :=
    by
    change Function.Surjective (Equiv.Perm.sign ∘ φ)
    rw [Function.Surjective.of_comp_iff _]
    exact Equiv.Perm.sign_surjective α
    exact MulEquiv.surjective φ
  obtain ⟨g', hg'⟩ := hs (-1)
  have hg' : s g' ≠ 1 := by
    rw [hg']; intro h; rw [← Units.eq_iff] at h 
    simpa only using h
  apply congr_arg
  ext g
  apply congr_arg
  refine' Equiv.Perm.swap_induction_on g _ _
  · rw [map_one, equiv.perm.sign.map_one]
  · intro f x y hxy hf
    rw [s.map_mul, equiv.perm.sign.map_mul, hf]
    apply congr_arg₂ (· * ·) _ rfl
    revert x y hxy
    by_contra
    push_neg at h 
    obtain ⟨a, b, hab, hk⟩ := h
    rw [Equiv.Perm.sign_swap hab] at hk 
    let hk := Or.resolve_right (Int.units_eq_one_or (s _)) hk
    apply hg'
    refine' Equiv.Perm.swap_induction_on g' s.map_one _
    intro f x y hxy hf
    rw [s.map_mul, hf, mul_one]
    obtain ⟨u, hu⟩ := Equiv.Perm.isConj_swap hxy hab
    apply mul_left_cancel
    swap; exact s u
    rw [← s.map_mul, SemiconjBy.eq hu, s.map_mul, hk, mul_one, one_mul]
#align alternating_is_characteristic alternating_is_characteristic

/-- A finite group of prime order is commutative -/
theorem isCommutative_of_prime_order {G : Type _} [Group G] [Fintype G] {p : ℕ} [hp : Fact p.Prime]
    (h : Fintype.card G = p) : IsCommutative G (· * ·) :=
  by
  skip
  apply IsCommutative.mk
  haveI := isCyclic_of_prime_card h
  exact IsCyclic.commGroup.mul_comm
#align is_commutative_of_prime_order isCommutative_of_prime_order

example (a b : ℕ) (h : a * 2 = b * 2) : a = b := by apply mul_left_injective₀ _ h; norm_num

/-- The alternating group on a fintype of cardinal 3 is commutative -/
theorem alternatingGroup.isCommutative_of_order_three {α : Type _} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α = 3) : IsCommutative (alternatingGroup α) (· * ·) :=
  by
  apply @isCommutative_of_prime_order _ _ _ 3 _
  have hα' : Nontrivial α := by rw [← Fintype.one_lt_card_iff_nontrivial]; rw [hα]; norm_num
  apply mul_right_injective₀ _
  rw [two_mul_card_alternatingGroup, Fintype.card_perm, hα]; norm_num
  infer_instance
  infer_instance
  norm_num
#align alternating_group.is_commutative_of_order_three alternatingGroup.isCommutative_of_order_three

theorem aux_dvd_lemma (r p : ℕ) (hp : p.Prime) (h : r ∣ Nat.factorial p)
    (hr : ∀ {l : ℕ} (hl : l.Prime) (hl' : l ∣ r), p ≤ l) : r ∣ p :=
  by
  rw [← Nat.coprime.dvd_mul_right _]
  rw [Nat.mul_factorial_pred (Nat.Prime.pos hp)]
  exact h
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra
  obtain ⟨l, hl, hl'⟩ := Nat.exists_prime_and_dvd h
  rw [Nat.dvd_gcd_iff, Nat.Prime.dvd_factorial hl] at hl' 
  apply (lt_iff_not_ge p.pred p).mp (Nat.pred_lt (Nat.Prime.ne_zero hp))
  rw [Nat.pred_eq_sub_one]; rw [ge_iff_le]
  exact le_trans (hr hl hl'.left) hl'.right
#align aux_dvd_lemma aux_dvd_lemma

/-- A subgroup of a finite group whose index is the smallest prime factor is normal -/
theorem Subgroup.normal_of_index_eq_smallest_prime_factor {G : Type _} [Fintype G] [Group G]
    (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hHp : H.index = p)
    (hp' : ∀ {l : ℕ} (hl : l.Prime) (hl' : l ∣ Fintype.card G), p ≤ l) : H.Normal :=
  by
  let f := MulAction.toPermHom G (G ⧸ H)
  suffices f.ker = H by rw [← this]; refine' MonoidHom.normal_ker f
  suffices H.normal_core.relindex H = 1
    by
    rw [← Subgroup.normalCore_eq_ker]
    unfold Subgroup.relindex at this 
    rw [Subgroup.index_eq_one] at this 
    apply le_antisymm; apply Subgroup.normalCore_le
    intro x hx
    rw [← Subgroup.coe_mk H x hx, ← Subgroup.mem_subgroupOf, this]
    apply Subgroup.mem_top
  suffices : H.index ≠ 0
  apply mul_left_injective₀ this; dsimp
  --  rw ← nat.mul_left_inj (nat.prime.pos hp),
  --  conv_lhs { rw ← hHp },
  rw [Subgroup.relindex_mul_index (Subgroup.normalCore_le H)]
  rw [one_mul]
  rw [Subgroup.normalCore_eq_ker]; rw [hHp]
  change f.ker.index = p
  refine' Or.resolve_left (Nat.Prime.eq_one_or_self_of_dvd hp f.ker.index _) _
  --  f.ker.index ∣ p,
  apply aux_dvd_lemma _ _ hp
  -- f.ker.index ∣ p.factorial : Lagrange on range
  · /- -- These two lines furnished the standard equality : f.ker.index = fintype.card ↥(f.range)
        let hf := subgroup.index_comap ⊥ f,
        simp only [monoid_hom.comap_bot, subgroup.relindex_bot_left, nat.card_eq_fintype_card] at hf, -/
    have hf := Subgroup.index_ker f; rw [Nat.card_eq_fintype_card] at hf 
    rw [hf, ← hHp]
    unfold Subgroup.index
    rw [Nat.card_eq_fintype_card, ← Fintype.card_perm]
    refine' f.range.card_subgroup_dvd_card
  -- Condition on prime factors of f.ker.index : hypothesis on G
  · intro l hl hl'; apply hp' hl
    exact dvd_trans hl' f.ker.index_dvd_card
  -- f.ker.index ≠ 1
  · intro hf
    apply Nat.Prime.ne_one hp
    rw [← hHp, Subgroup.index_eq_one, eq_top_iff]
    apply le_trans _ (Subgroup.normalCore_le H)
    rw [← eq_top_iff, ← Subgroup.index_eq_one, Subgroup.normalCore_eq_ker]
    exact hf
  rw [hHp]; exact Nat.Prime.ne_zero hp
#align subgroup.normal_of_index_eq_smallest_prime_factor Subgroup.normal_of_index_eq_smallest_prime_factor

/-- A subgroup of index 2 is normal -/
theorem Subgroup.normal_of_index_eq_two {G : Type _} [Group G] {H : Subgroup G} (hH : H.index = 2) :
    H.Normal :=
  by
  have : Fintype (G ⧸ H) := by
    refine' fintypeOfNotInfinite _
    intro h
    suffices : 2 ≠ 0; apply this
    rw [← hH]
    unfold Subgroup.index
    unfold Nat.card
    rw [Cardinal.mk_toNat_of_infinite]
    exact two_ne_zero
  let f := MulAction.toPermHom G (G ⧸ H)
  suffices f.ker = H by rw [← this]; refine' MonoidHom.normal_ker f
  suffices H.normal_core.relindex H = 1
    by
    rw [← Subgroup.normalCore_eq_ker]
    unfold Subgroup.relindex at this 
    rw [Subgroup.index_eq_one] at this 
    apply le_antisymm; apply Subgroup.normalCore_le
    intro x hx
    rw [← Subgroup.coe_mk H x hx, ← Subgroup.mem_subgroupOf, this]
    apply Subgroup.mem_top
  suffices : H.index ≠ 0
  apply mul_left_injective₀ this; dsimp
  rw [Subgroup.relindex_mul_index (Subgroup.normalCore_le H)]
  rw [one_mul]
  rw [Subgroup.normalCore_eq_ker]
  rw [hH]
  --  change f.ker.index = 2,
  apply Nat.eq_of_lt_succ_of_not_lt
  rw [Subgroup.index_ker f, Nat.card_eq_fintype_card]
  rw [Nat.lt_succ_iff]; apply Nat.le_of_dvd two_pos
  refine' dvd_trans f.range.card_subgroup_dvd_card _
  rw [Fintype.card_perm, ← Nat.card_eq_fintype_card]
  unfold Subgroup.index at hH ; rw [hH]; norm_num
  -- ¬(f.ker.index < 2)
  intro h
  apply Nat.not_succ_le_self 1
  rw [Nat.lt_succ_iff] at h ; change 2 ≤ 1
  apply le_trans _ h
  rw [← hH, ← Subgroup.normalCore_eq_ker H]
  apply Nat.le_of_dvd
  · rw [zero_lt_iff]
    rw [Subgroup.normalCore_eq_ker H, Subgroup.index_ker f, Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  apply Subgroup.index_dvd_of_le
  exact Subgroup.normalCore_le H
  · rw [hH]; norm_num
#align subgroup.normal_of_index_eq_two Subgroup.normal_of_index_eq_two

variable {α}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- I don't know why this stuff is not there !
/-- Any permutation is a product of a list of swaps -/
theorem Equiv.Perm.is_prod_swap_list (g : Equiv.Perm α) :
    ∃ l : List (Equiv.Perm α), (∀ s : Equiv.Perm α, s ∈ l → s.IsSwap) ∧ g = l.Prod :=
  by
  apply Equiv.Perm.swap_induction_on g
  · use List.nil
    constructor
    · intro s hs; exfalso; exact List.not_mem_nil s hs
    · simp only [List.prod_nil]
  · intro f x y hxy hf
    obtain ⟨l, hl, hf⟩ := hf
    use Equiv.swap x y::l
    constructor
    · intro s hs
      rw [List.mem_cons] at hs 
      cases' hs with hs hs
      rw [hs]; exact ⟨x, y, hxy, rfl⟩
      exact hl s hs
    rw [List.prod_cons]
    rw [hf]
#align equiv.perm.is_prod_swap_list Equiv.Perm.is_prod_swap_list

/-- The alternating group is the only subgroup of index 2 of the permutation group -/
theorem is_alternating_of_index_2 {G : Subgroup (Equiv.Perm α)} (hG : G.index = 2) :
    alternatingGroup α = G :=
  by
  haveI hG' := Subgroup.normal_of_index_eq_two hG
  let s : Equiv.Perm α →* Equiv.Perm α ⧸ G := QuotientGroup.mk' G
  rw [alternatingGroup_eq_sign_ker]
  rw [← QuotientGroup.ker_mk' G]
  have hG'' : IsCommutative (Equiv.Perm α ⧸ G) (· * ·) :=
    by
    refine' isCommutative_of_prime_order _
    exact 2; exact Nat.fact_prime_two
    rw [← Nat.card_eq_fintype_card]
    exact hG
  have : ∃ g : Equiv.Perm α, g.IsSwap ∧ g ∉ G :=
    by
    by_contra; push_neg at h 
    suffices : G = ⊤
    rw [this] at hG ; rw [Subgroup.index_top] at hG 
    apply (1 : ℕ).one_ne_bit0; exact hG
    rw [eq_top_iff]
    rw [← Equiv.Perm.closure_isSwap]
    rw [Subgroup.closure_le G]
    intro g hg
    simp only [Set.mem_setOf_eq] at hg 
    simp only [SetLike.mem_coe]
    exact h g hg
  obtain ⟨k, hk, hk'⟩ := this
  have this' : ∀ g : Equiv.Perm α, g.IsSwap → s g = s k :=
    by
    intro g hg
    obtain ⟨a, b, hab, habg⟩ := hg
    obtain ⟨x, y, hxy, hxyk⟩ := hk
    obtain ⟨u, hu⟩ := Equiv.Perm.isConj_swap hab hxy
    let hu' := congr_arg s (SemiconjBy.eq hu)
    simp only [map_mul] at hu' 
    apply mul_left_cancel
    swap; exact s u
    rw [habg, hxyk, hu']
    apply hG''.comm
  have hsk2 : s k ^ 2 = 1 := by
    rw [pow_two]; rw [← map_mul]
    obtain ⟨x, y, hxy, hxyk⟩ := hk
    rw [hxyk]
    rw [Equiv.swap_mul_self]
    rw [map_one]
  ext g
  simp only [equiv.perm.sign.mem_ker, (QuotientGroup.mk' G).mem_ker]
  obtain ⟨l, hl, hg⟩ := g.is_prod_swap_list
  let hsg := Equiv.Perm.sign_prod_list_swap hl
  rw [← hg] at hsg 
  have hsg' : s g = s k ^ l.length := by
    rw [hg]
    rw [map_list_prod]
    rw [List.prod_eq_pow_card (List.map s l) (s k) _]
    rw [List.length_map]
    intro x hx
    simp only [List.mem_map] at hx 
    obtain ⟨y, hyl, hxy⟩ := hx
    rw [← hxy]
    apply this'; exact hl y hyl
  obtain ⟨m, hm⟩ := Nat.even_or_odd' l.length
  have neg_one_neq_one : (-1 : Units ℤ) ≠ 1 := by
    intro h
    rw [← Units.eq_iff] at h 
    simpa only using h
  cases' hm with hm hm
  · rw [hm, pow_mul] at hsg hsg' 
    rw [hsk2] at hsg' ; rw [Int.units_sq] at hsg 
    rw [one_pow] at hsg' hsg 
    simp only [hsg, hsg']
    simp only [eq_self_iff_true]
  · rw [hm, pow_add, pow_mul, pow_one] at hsg hsg' 
    rw [hsk2] at hsg' ; rw [Int.units_sq] at hsg 
    rw [one_pow, one_mul] at hsg' hsg 
    rw [hsg, hsg']
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h; exfalso; exact neg_one_neq_one h
    · intro h; exfalso; exact hk' h
#align is_alternating_of_index_2 is_alternating_of_index_2

theorem large_subgroup_of_perm_contains_alternating {G : Subgroup (Equiv.Perm α)}
    (hG : Fintype.card (Equiv.Perm α) ≤ 2 * Fintype.card G) : alternatingGroup α ≤ G :=
  by
  cases Nat.eq_zero_or_pos G.index
  · exfalso
    exact Subgroup.index_ne_zero_of_finite h
  cases' eq_or_gt_of_le (nat.succ_le_iff.mpr h) with h h
  · rw [Subgroup.index_eq_one] at h ; rw [h]; exact le_top
  rw [← Nat.succ_le_iff] at h ; norm_num at h 
  apply @le_of_eq _ _ (alternatingGroup α) G
  apply is_alternating_of_index_2
  refine' le_antisymm _ h
  refine' Nat.le_of_mul_le_mul_left _ _
  swap
  · rw [mul_comm, Subgroup.index_mul_card, mul_comm]
    exact hG
  exact Fintype.card_pos
#align large_subgroup_of_perm_contains_alternating large_subgroup_of_perm_contains_alternating

/-- A subgroup of the permutation group of index ≤ 2 contains the alternating group -/
theorem contains_alternating_of_index_le_2' {G : Subgroup (Equiv.Perm α)} (hG : G.index ≤ 2) :
    alternatingGroup α ≤ G :=
  by
  apply large_subgroup_of_perm_contains_alternating
  rw [← Subgroup.index_mul_card G]
  apply Nat.mul_le_mul_right _ hG
#align contains_alternating_of_index_le_2' contains_alternating_of_index_le_2'

#lint


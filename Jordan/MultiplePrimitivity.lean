/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module multiple_primitivity
-/
import Mathbin.Tactic.Lift
import Mathbin.GroupTheory.GroupAction.Embedding
import Oneshot.MultipleTransitivity
import Oneshot.ForMathlib.Cardinal

open scoped BigOperators Pointwise Cardinal

open scoped Classical

section MultiplePrimitivity

namespace MulAction

variable (M α : Type _) [Group M] [MulAction M α]

example (e : PartENat) (h : e + 1 = 1) : e = 0 :=
  by
  rw [← PartENat.add_right_cancel_iff, zero_add]
  exact h
  rw [← Nat.cast_one]
  exact PartENat.natCast_ne_top 1

example (n : ℕ) (h : (n : PartENat) = 0) : n = 0 :=
  by
  rw [← Nat.cast_zero] at h 
  rw [PartENat.natCast_inj] at h ; exact h

example (c : Cardinal) (n : ℕ) (h : c.toPartENat = n) : c = n :=
  by
  apply symm
  rw [← PartENat.coe_nat_eq_iff_eq]
  exact h.symm

/-- An action is n-fold preprimitive if it is n-fold pretransitive
and if the action of fixator of any (n-1) element subset on the remaining set
is not only pretransitive but also preprimitive. (Wielandt, §10)
-/
def IsMultiplyPreprimitive (n : ℕ) :=
  IsMultiplyPretransitive M α n ∧
    ∀ (s : Set α) (hs : PartENat.card s + 1 = n),
      IsPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s)
#align mul_action.is_multiply_preprimitive MulAction.IsMultiplyPreprimitive

/-- Any action is 0-fold preprimitive -/
theorem isMultiplyPreprimitive_zero : IsMultiplyPreprimitive M α 0 :=
  by
  constructor
  apply MulAction.is_zero_pretransitive
  · intro s
    apply Not.elim
    intro h
    simp only [Nat.cast_zero, add_eq_zero_iff] at h 
    simpa only [one_ne_zero, and_false_iff] using h
#align mul_action.is_multiply_preprimitive_zero MulAction.isMultiplyPreprimitive_zero

/-- An action is preprimitive iff it is 1-preprimitive -/
theorem isPreprimitive_iff_is_one_preprimitive :
    IsPreprimitive M α ↔ IsMultiplyPreprimitive M α 1 :=
  by
  constructor
  · intro h
    constructor
    rw [← is_pretransitive_iff_is_one_pretransitive]
    exact h.to_is_pretransitive
    intro s hs; rw [Nat.cast_one] at hs 
    suffices s = ∅ by
      rw [this]
      rw [isPreprimitive_of_bijective_map_iff
          (SubMulAction.of_fixingSubgroup_empty_map_scalars_surjective M α)
          (SubMulAction.ofFixingSubgroupEmptyMap_bijective M α)]
      exact h
    suffices PartENat.card s = 0
      by
      rw [← Cardinal.mk_emptyCollection_iff]
      apply symm
      rw [← Nat.cast_zero, ← PartENat.coe_nat_eq_iff_eq]
      unfold PartENat.card at this ; rw [this]
      simp only [Nat.cast_zero]
    rw [← PartENat.add_right_cancel_iff, zero_add]; exact hs
    rw [← Nat.cast_one]; exact PartENat.natCast_ne_top 1
  · rintro ⟨h1, h1'⟩
    apply
      isPreprimitive_of_surjective_map
        (Function.Bijective.surjective (SubMulAction.ofFixingSubgroupEmptyMap_bijective M α))
    apply h1'
    simp only [PartENat.card_eq_coe_fintype_card, Set.empty_card', Nat.cast_zero, zero_add,
      Nat.cast_one]
#align mul_action.is_preprimitive_iff_is_one_preprimitive MulAction.isPreprimitive_iff_is_one_preprimitive

/-- A pretransitive  action is n.succ-fold preprimitive  iff
  the action of stabilizers is n-fold preprimitive -/
theorem isMultiplyPreprimitive_ofStabilizer {n : ℕ} (hn : 1 ≤ n) (h : IsPretransitive M α)
    {a : α} :-- (hα : (n.succ : cardinal) ≤ #α):
        IsMultiplyPreprimitive
        M α n.succ ↔
      IsMultiplyPreprimitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n :=
  by
  let h_eq := h.exists_smul_eq
  constructor
  · intro hn
    cases' Nat.lt_or_ge n 1 with h0 h1
    · rw [Nat.lt_one_iff] at h0 ; rw [h0]; apply is_multiply_preprimitive_zero
    constructor
    -- n-pretransitive
    exact (stabilizer.is_multiply_pretransitive M α h).mp hn.left
    -- multiple preprimitivity property
    intro s hs
    --    let j := sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s,
    apply
      isPreprimitive_of_surjective_map
        (SubMulAction.OfFixingSubgroupOfStabilizer.map_bijective M a s).Surjective
    apply hn.right
    suffices part_enat_one_ne_top : (1 : PartENat) ≠ ⊤
    · simp only [Nat.cast_succ]
      rw [PartENat.add_right_cancel_iff part_enat_one_ne_top]
      apply symm
      unfold PartENat.card
      rw [PartENat.coe_nat_eq_iff_eq]
      rw [Cardinal.mk_insert, Cardinal.mk_image_eq Subtype.coe_injective]
      rw [← PartENat.coe_nat_eq_iff_eq]
      rw [← hs]; simp only [map_add]
      conv_rhs => rw [← Nat.cast_one]
      rw [Cardinal.toPartENat_cast, Nat.cast_one,
        PartENat.add_right_cancel_iff part_enat_one_ne_top]
      rfl
      · -- a ∉ coe '' s
        rintro ⟨x, hx, hx'⟩
        apply x.prop; simp only [Set.mem_singleton_iff]
        exact hx'
    ·-- (1 : part_enat) ≠ ⊤
      rw [← Nat.cast_one];
      exact PartENat.natCast_ne_top 1
  · intro hn_0
    constructor
    · rw [stabilizer.is_multiply_pretransitive M α h]
      exact hn_0.left
    · suffices
        ∀ (s : Set α) (hs : PartENat.card s + 1 = n.succ) (has : a ∈ s),
          IsPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s)
        by
        intro s hs
        have : ∃ b : α, b ∈ s :=
          by
          rw [← Set.nonempty_def, Set.nonempty_iff_ne_empty]
          intro h
          suffices n = 0 by
            simpa only [this, ge_iff_le, nonpos_iff_eq_zero, Nat.one_ne_zero] using hn
          rw [← Cardinal.mk_emptyCollection_iff] at h 
          unfold PartENat.card at hs 
          rw [h] at hs 
          simp only [map_zero, Nat.cast_succ] at hs 
          rw [← Nat.cast_zero] at hs 
          rw [PartENat.add_right_cancel_iff, PartENat.natCast_inj] at hs 
          exact hs.symm
          rw [← Nat.cast_one]; exact PartENat.natCast_ne_top 1
        obtain ⟨b, hb⟩ := this
        obtain ⟨g, hg : g • b = a⟩ := h_eq b a
        apply
          isPreprimitive_of_surjective_map
            (SubMulAction.ofFixingSubgroup.conjMap_bijective M (inv_smul_smul g s)).Surjective
        refine' this (g • s) _ _
        · suffices : (#↥(g • s)) = (#↥s)
          rw [← hs]; unfold PartENat.card; rw [this]
          change (#(fun x => g • x) '' s) = _
          rw [Cardinal.mk_image_eq (MulAction.injective g)]
        exact ⟨b, hb, hg⟩
      intro s hs has
      rw [← Nat.cast_one, Nat.cast_add n 1] at hs 
      rw [PartENat.add_right_cancel_iff (PartENat.natCast_ne_top 1)] at hs 
      let t : Set (SubMulAction.ofStabilizer M a) := coe ⁻¹' s
      have hst : s = insert a (coe '' t) := by
        ext
        constructor
        · intro hxs
          cases' Classical.em (x = a) with hxa hxa
          rw [hxa]; apply Set.mem_insert
          apply Set.mem_insert_of_mem; use x
          refine' And.intro _ rfl
          simp only [Set.mem_preimage, SubMulAction.coe_mk]; exact hxs
        · intro hxat
          cases' set.mem_insert_iff.mp hxat with hxa hxt
          rw [hxa]; exact has
          obtain ⟨y, hy, rfl⟩ := hxt
          simpa only using hy
      rw [hst]
      rw [isPreprimitive_of_bijective_map_iff
          (SubMulAction.OfFixingSubgroupOfStabilizer.scalar_map_bijective M a t).Surjective
          (SubMulAction.OfFixingSubgroupOfStabilizer.map_bijective M a t)]
      · apply hn_0.right t
        have ha : a ∉ (coe '' t : Set α) := by
          rintro ⟨x, hx⟩
          apply x.prop; rw [hx.right]; simp only [Set.mem_singleton]
        let hz : (#↥(insert a (coe '' t))) = _ := Cardinal.mk_insert ha
        rw [← hst, Cardinal.mk_image_eq Subtype.coe_injective] at hz 
        rw [← hs]
        unfold PartENat.card
        simp only [hz, map_add]
        apply congr_arg₂ (· + ·) rfl
        conv_lhs => rw [← Nat.cast_one]
        rw [PartENat.coe_nat_eq_iff_eq]; rw [Nat.cast_one]
#align mul_action.is_multiply_preprimitive_of_stabilizer MulAction.isMultiplyPreprimitive_ofStabilizer

/- lemma is_multiply_preprimitive_of_subgroup {H : subgroup M}
  {n : ℕ} (hn : n ≥ 1) (hH : is_multiply_preprimitive H α n) :
  is_multiply_preprimitive M α n :=
begin
  let j : mul_action_bihom H α M α :=
  { to_fun := id,
    to_monoid_hom := subgroup_class.subtype H,
    map_smul' := λ m x, rfl },

  split,
  apply is_pretransitive_of_subgroup,
  exact hH.left,

  intros s hs,
  apply is_preprimitive.mk,
  rw is_pretransitive_iff_is_one_pretransitive,
  have hn1 : n = (n - 1) + 1,
  by rw ← (nat.sub_eq_iff_eq_add hn),

  suffices : #s = ↑(n - 1) ∧ 1 = n - (n-1),
  { rw this.right,
    apply remaining_transitivity M α (n-1) s this.left,
    apply is_pretransitive_of_subgroup,
    exact hH.left, },
  split,
  { apply cardinal.add_cancel,
    swap, exact 1,
    rw [nat.cast_one, hs],
    suffices : n = (n - 1) + 1,
    conv_lhs { rw this },
    simp only [nat.cast_add, nat.cast_one],
    exact hn1 },
  suffices : n ≥ (n - 1),
  rw add_comm at hn1, apply symm,
  exact (nat.sub_eq_iff_eq_add this).mpr hn1,
  exact nat.sub_le n 1,

  intros B hB,
  apply  (hH.right s hs).has_trivial_blocks,
  rw is_block.mk_mem at hB ⊢,
  rintros ⟨⟨g, hgH⟩, hgs⟩ ⟨a, ha⟩ haB hga,
  suffices : (⟨g, _⟩ : fixing_subgroup M s) • B = B,
  exact this,
  apply hB ⟨g, begin simpa only using hgs end⟩ ⟨a, begin simpa only using ha end⟩,
  simpa only using haB,
  simpa only using hga,
end
 -/
/-- The fixator of a subset of cardinal d in an n-primitive action
  acts (n-d) primitively on the remaining (d ≤ n)-/
theorem remaining_primitivity {n : ℕ} (h : IsMultiplyPreprimitive M α n) {d : ℕ} (hdn : d ≤ n)
    {s : Set α} (hs : PartENat.card s = d) :
    IsMultiplyPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) (n - d) :=
  by
  constructor
  · apply remaining_transitivity M α d s hs; exact h.left
  · intro t ht
    let t' : Set α := coe '' t
    have htt' : t = coe ⁻¹' t' := by apply symm; apply Set.preimage_image_eq;
      exact Subtype.coe_injective
    rw [htt']
    apply
      isPreprimitive_of_surjective_map
        (SubMulAction.OfFixingSubgroupUnion.map_bijective M s t').Surjective
    apply h.right
    unfold PartENat.card at ht hs ⊢
    rw [Cardinal.mk_union_of_disjoint]
    · simp only [map_add, Cardinal.mk_image_eq Subtype.coe_injective]
      rw [add_assoc, ht, hs, ← Nat.cast_add, PartENat.natCast_inj]
      exact Nat.add_sub_of_le hdn
    · rw [Set.disjoint_iff]
      intro a; simp only [t']
      rintro ⟨hbs, ⟨b, hbt, rfl⟩⟩
      exfalso
      exact b.prop hbs
#align mul_action.remaining_primitivity MulAction.remaining_primitivity

/-- n.succ-fold pretransitivity implies n-fold preprimitivity -/
theorem isMultiplyPreprimitive_of_multiply_pretransitive_succ {n : ℕ}
    (hα : ↑n.succ ≤ PartENat.card α) (h : IsMultiplyPretransitive M α n.succ) :
    IsMultiplyPreprimitive M α n :=
  by
  cases' Nat.eq_zero_or_pos n with hn hn
  · rw [hn]; apply is_multiply_preprimitive_zero
  constructor
  apply is_multiply_pretransitive_of_higher M α h
  exact Nat.le_succ n
  exact hα
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [hm]
  intro s hs
  apply is_preprimitive_of_two_pretransitive
  suffices : 2 = n.succ - m
  rw [this]
  apply remaining_transitivity
  · simp at hs 
    rw [← PartENat.add_right_cancel_iff]
    rw [hs]; exact add_comm 1 ↑m
    rw [← Nat.cast_one]; exact PartENat.natCast_ne_top 1
  exact h
  simp only [hm, Nat.succ_eq_one_add, ← add_assoc]
  norm_num
#align mul_action.is_multiply_preprimitive_of_multiply_pretransitive_succ MulAction.isMultiplyPreprimitive_of_multiply_pretransitive_succ

/-- An n-fold preprimitive action is m-fold preprimitive for m ≤ n -/
theorem isMultiplyPreprimitive_of_higher {n : ℕ} {m : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ PartENat.card α)
    (hn : IsMultiplyPreprimitive M α n) : IsMultiplyPreprimitive M α m :=
  by
  cases' Nat.eq_zero_or_pos m with hm hm
  · rw [hm]; apply is_multiply_preprimitive_zero
  induction' n with n hrec
  · exfalso; apply lt_irrefl 0
    apply lt_of_lt_of_le; exact hm; exact hmn
  cases' Nat.eq_or_lt_of_le hmn with hmn hmn'
  · rw [hmn]; exact hn
  apply hrec (nat.lt_succ_iff.mp hmn')
  refine' le_trans _ hα
  rw [PartENat.coe_le_coe]
  exact Nat.le_succ n
  apply is_multiply_preprimitive_of_multiply_pretransitive_succ M α hα hn.left
#align mul_action.is_multiply_preprimitive_of_higher MulAction.isMultiplyPreprimitive_of_higher

variable {M α}

theorem isMultiplyPreprimitive_of_bijective_map {N β : Type _} [Group N] [MulAction N β] {φ : M → N}
    {f : α →ₑ[φ] β} (hf : Function.Bijective f) {n : ℕ} (h : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive N β n := by
  constructor
  apply is_multiply_pretransitive_of_surjective_map hf.surjective h.left
  intro t ht
  let s := f ⁻¹' t
  have hs' : f '' s = t := Set.image_preimage_eq t hf.surjective
  have hs : PartENat.card s + 1 = n := by
    rw [← ht, ← hs']
    rw [PartENat.card_image_of_injective f s hf.injective]
  let φ' : fixingSubgroup M s → fixingSubgroup N t := fun ⟨m, hm⟩ =>
    ⟨φ m, fun ⟨y, hy⟩ => by
      rw [← hs', Set.mem_image_iff_bex] at hy 
      obtain ⟨x, hx, hx'⟩ := hy
      simp only [Subtype.coe_mk]
      rw [← hx', ← EquivariantMap.toFun_eq_coe, ← f.map_smul']
      apply congr_arg
      rw [mem_fixingSubgroup_iff] at hm 
      exact hm x hx⟩
  let f' : SubMulAction.ofFixingSubgroup M s →ₑ[φ'] SubMulAction.ofFixingSubgroup N t :=
    { toFun := fun ⟨x, hx⟩ => ⟨f.to_fun x, fun h => hx (set.mem_preimage.mp h)⟩
      map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ =>
        by
        rw [← SetLike.coe_eq_coe]
        exact f.map_smul' m x }
  have hf' : Function.Surjective f' := by
    rintro ⟨y, hy⟩; obtain ⟨x, hx⟩ := hf.right y
    use x
    · intro h; apply hy; rw [← hs']; exact ⟨x, h, hx⟩
    rw [← SetLike.coe_eq_coe]
    exact hx
  exact isPreprimitive_of_surjective_map hf' (h.right s hs)
#align mul_action.is_multiply_preprimitive_of_bijective_map MulAction.isMultiplyPreprimitive_of_bijective_map

end MulAction

end MultiplePrimitivity

#lint

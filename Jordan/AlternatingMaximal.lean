/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module alternating_maximal
-/
import Mathbin.GroupTheory.GroupAction.SubMulAction
import Mathbin.GroupTheory.SpecificGroups.Alternating
import Oneshot.ForMathlib.Alternating
import Oneshot.IndexNormal
import Oneshot.Primitive
import Oneshot.MultipleTransitivity
import Oneshot.StabilizerPrimitive
import Oneshot.PermIwasawa
import Oneshot.PermMaximal
import Oneshot.V4

-- import tactic.basic tactic.group
-- import group_theory.solvable
-- import group_theory.perm.cycle.concrete
-- import group_theory.perm.cycle.concrete
-- import .for_mathlib.group_theory__subgroup__basic
-- import .for_mathlib.group_theory__subgroup__basic
open scoped Pointwise

-- open_locale classical
open MulAction

section Junk

variable {α G H : Type _} [Group G] [Group H] [MulAction G α] {N : Subgroup G}

theorem Subgroup.map_subgroupOf_eq {K : Subgroup N} : (K.map N.Subtype).subgroupOf N = K := by
  rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
#align subgroup.map_subgroup_of_eq Subgroup.map_subgroupOf_eq

theorem MulAction.stabilizer_subgroupOf_eq {a : α} :
    stabilizer N a = (stabilizer G a).subgroupOf N :=
  by
  ext n
  simp only [Subgroup.mem_subgroupOf, mem_stabilizer_iff]
  rfl
#align mul_action.stabilizer_subgroup_of_eq MulAction.stabilizer_subgroupOf_eq

example (K K' : Subgroup G) : K < K' ↔ K ≤ K' ∧ K ≠ K' :=
  lt_iff_le_and_ne

theorem Subgroup.map_iff_mono_of_injective {f : G →* H} {K K' : Subgroup G}
    (hf : Function.Injective f) : K ≤ K' ↔ Subgroup.map f K ≤ Subgroup.map f K' :=
  by
  constructor
  exact Subgroup.map_mono
  · intro h
    intro x hx
    suffices f x ∈ Subgroup.map f K'
      by
      simp only [Subgroup.mem_map] at this 
      obtain ⟨y, hy, hx⟩ := this
      rw [← hf hx]; exact hy
    apply h
    rw [Subgroup.mem_map]
    use ⟨x, hx, rfl⟩
#align subgroup.map_iff_mono_of_injective Subgroup.map_iff_mono_of_injective

theorem Subgroup.map_strict_mono_of_injective {f : G →* H} {K K' : Subgroup G}
    (hf : Function.Injective f) : K < K' ↔ Subgroup.map f K < Subgroup.map f K' :=
  by
  simp only [lt_iff_le_not_le]
  simp_rw [← Subgroup.map_iff_mono_of_injective hf]
#align subgroup.map_strict_mono_of_injective Subgroup.map_strict_mono_of_injective

theorem Subgroup.map_injective_of_injective {f : G →* H} {K K' : Subgroup G}
    (hf : Function.Injective f) : Subgroup.map f K = Subgroup.map f K' ↔ K = K' := by
  simp only [le_antisymm_iff, ← Subgroup.map_iff_mono_of_injective hf]
#align subgroup.map_injective_of_injective Subgroup.map_injective_of_injective

end Junk

variable {α : Type _} [Fintype α] [DecidableEq α]

namespace alternatingGroup

open scoped Classical

theorem isPretransitive_ofFixingSubgroup (s : Set α) (h0 : s.Nontrivial)
    (hα : Fintype.card s < Fintype.card (sᶜ : Set α)) :
    IsPretransitive (fixingSubgroup (alternatingGroup α) s)
      (SubMulAction.ofFixingSubgroup (alternatingGroup α) s) :=
  by
  rw [is_pretransitive_iff_is_one_pretransitive]
  refine' remaining_transitivity' _ _ _ _ (Fintype.card α - 2) _ _ _
  simp only [part_enat.of_fintype α, PartENat.coe_le_coe, tsub_le_self]
  · have h1' : 2 < Fintype.card (sᶜ : Set α) :=
      by
      apply lt_of_le_of_lt _ hα
      rw [Nat.succ_le_iff, Fintype.one_lt_card_iff_nontrivial, Set.nontrivial_coe_sort]
      exact h0
    rw [add_comm, ← Fintype.card_add_compl s, Nat.add_sub_assoc (le_of_lt h1'), add_le_add_iff_left,
      Nat.le_sub_iff_right (le_of_lt h1')]
    exact h1'
  -- Here, we needed to add an instance in multiple_transitivity.lean to apply the following lemma
  exact MulAction.alternatingGroup_is_fully_minus_two_pretransitive α
#align alternating_group.is_pretransitive_of_fixing_subgroup alternatingGroup.isPretransitive_ofFixingSubgroup

theorem stabilizer_ne_top' (s : Set α) (hs : s.Nonempty) (hsc : sᶜ.Nontrivial) :
    stabilizer (alternatingGroup α) s ≠ ⊤ :=
  by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb, c, hc, hbc⟩ := hsc
  rw [Set.mem_compl_iff] at hb hc 
  have hac : a ≠ c := by intro h; apply hc; rw [← h]; exact ha
  have hab : a ≠ b := by intro h; apply hb; rw [← h]; exact ha
  intro h; apply hc
  -- let gc := cycle.form_perm ↑[a,b,c] (begin rw cycle.nodup_coe_iff, simp [hab, hac, hbc] end ),
  let g := Equiv.swap a b * Equiv.swap a c
  have hg : g ∈ alternatingGroup α :=
    by
    rw [Equiv.Perm.mem_alternatingGroup]
    apply Equiv.Perm.IsThreeCycle.sign
    apply Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  suffices g • s = s by
    rw [← this]
    use a
    constructor; exact ha
    dsimp [g]
    rw [Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  change (⟨g, hg⟩ : alternatingGroup α) • s = s
  rw [← MulAction.mem_stabilizer_iff]; erw [h]; apply Subgroup.mem_top
#align alternating_group.stabilizer_ne_top' alternatingGroup.stabilizer_ne_top'

theorem stabilizer_ne_top (s : Set α) (hs : s.Nonempty) (hsc : sᶜ.Nonempty)
    (hssc : s.Nontrivial ∨ (sᶜ : Set α).Nontrivial) : stabilizer (alternatingGroup α) s ≠ ⊤ :=
  by
  cases' hssc with hs' hsc'
  · rw [← stabilizer_compl]
    rw [← compl_compl s] at hs' 
    exact stabilizer_ne_top' (sᶜ) hsc hs'
  exact stabilizer_ne_top' s hs hsc'
#align alternating_group.stabilizer_ne_top alternatingGroup.stabilizer_ne_top

-- open_locale classical
example (s t : Set α) (h : s ⊆ t) : Fintype.card s ≤ Fintype.card t :=
  Set.card_le_of_subset h

example (s : Finset α) : Fintype.card (s : Set α) = s.card := by
  simp only [Finset.coe_sort_coe, Fintype.card_coe]

-- Il va falloir, soit que t ait ≥ 3 éléments, soit que tᶜ en ait ≥ 2.
-- autrement dit : fintype.card α ≥ 4.
-- La condition est nécessaire :
-- dans le cas α = {1, 2, 3}, t = {1,2} ou t = {1}, le résultat est faux
theorem moves_in (hα : 4 ≤ Fintype.card α) (t : Set α) :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g ∈ stabilizer (Equiv.Perm α) t ⊓ alternatingGroup α, g • a = b :=
  by
  intro a ha b hb
  cases' em (a = b) with hab hab
  · -- a = b, on prend g = 1,
    use 1
    simp only [hab, Subgroup.one_mem, one_smul, eq_self_iff_true, and_self_iff]
  rw [← Ne.def] at hab 
  cases' le_or_gt (Fintype.card t) 2 with ht ht'
  · -- fintype.card t ≤ 2, alors on prend le produit d'un swap (a b) avec un swap dans tᶜ
    have h : 1 < Fintype.card (tᶜ : Set α) := by
      by_contra
      rw [not_lt] at h 
      rw [← not_lt] at hα 
      apply hα
      rw [← Fintype.card_add_compl t]
      apply Nat.lt_succ_of_le
      apply add_le_add ht h
    rw [Fintype.one_lt_card_iff] at h 
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩, hcd⟩ := h
    simp only [Ne.def, Subtype.mk_eq_mk] at hcd 
    use Equiv.swap a b * Equiv.swap c d
    constructor
    · simp only [Subgroup.mem_inf]
      constructor
      · rw [mem_stabilizer_of_finite_iff]
        rintro _ ⟨x, hx, rfl⟩
        simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
        have hx_ne : ∀ u ∈ tᶜ, x ≠ u := fun u hu h => Set.mem_compl hu (by rw [← h]; exact hx)
        rw [Equiv.swap_apply_of_ne_of_ne (hx_ne c hc) (hx_ne d hd)]
        cases' em (x = a) with hxa hxa'
        · rw [hxa, Equiv.swap_apply_left]; exact hb
        cases' em (x = b) with hxb hxb'
        · rw [hxb, Equiv.swap_apply_right]; exact ha
        rw [Equiv.swap_apply_of_ne_of_ne hxa' hxb']; exact hx
        exact t.to_finite
      · simp only [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
        rw [Equiv.Perm.sign_swap hab]; rw [Equiv.Perm.sign_swap hcd]
        simp only [Int.units_mul_self]
    simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Set.mem_compl_iff t] at hc hd 
    have hac : a ≠ c; intro h; apply hc; rw [← h]; exact ha
    have had : a ≠ d; intro h; apply hd; rw [← h]; exact ha
    rw [Equiv.swap_apply_of_ne_of_ne hac had]
    rw [Equiv.swap_apply_left]
  · -- fintype t ≥ 3, alors on prend un 3-cycle dans t
    suffices : ∃ c ∈ t, c ≠ a ∧ c ≠ b
    obtain ⟨c, hc, hca, hcb⟩ := this
    use Equiv.swap a c * Equiv.swap a b
    constructor
    · simp only [Subgroup.mem_inf]
      constructor
      · rw [mem_stabilizer_of_finite_iff]
        rintro _ ⟨x, hx, rfl⟩
        simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
        cases' em (x = a) with hxa hxa'
        · rw [hxa, Equiv.swap_apply_left]
          rw [Equiv.swap_apply_of_ne_of_ne hab.symm hcb.symm]
          exact hb
        rw [← Ne.def] at hxa' 
        cases' em (x = b) with hxb hxb'
        · rw [hxb, Equiv.swap_apply_right, Equiv.swap_apply_left]; exact hc
        rw [← Ne.def] at hxb' 
        rw [Equiv.swap_apply_of_ne_of_ne hxa' hxb']
        cases' em (x = c) with hxc hxc'
        · rw [hxc, Equiv.swap_apply_right]; exact ha
        rw [← Ne.def] at hxc' 
        rw [Equiv.swap_apply_of_ne_of_ne hxa' hxc']
        exact hx
        exact t.to_finite
      · simp only [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
        rw [Equiv.Perm.sign_swap hab]; rw [Equiv.Perm.sign_swap (Ne.symm hca)]
        simp only [Int.units_mul_self]
    · simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)]
    suffices (t \ {a, b}).Nonempty by
      obtain ⟨c, h⟩ := this
      simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h 
      use c
      apply And.intro h.left
      exact h.right
    rw [Set.nonempty_diff]
    intro ht
    rw [gt_iff_lt, ← not_le] at ht' ; apply ht'
    rw [← Finset.card_doubleton hab]
    simp only [← Fintype.card_coe, ← Finset.coe_sort_coe]
    apply Set.card_le_of_subset
    simp only [Finset.coe_insert, Finset.coe_singleton]
    exact ht
#align alternating_group.moves_in alternatingGroup.moves_in

theorem moves_in' (hα : 4 ≤ Fintype.card α) (G : Subgroup (Equiv.Perm α)) (t : Set α)
    (hGt : stabilizer (Equiv.Perm α) t ⊓ alternatingGroup α ≤ G) :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g : G, g • a = b :=
  by
  intro a ha b hb
  obtain ⟨g, hg, H⟩ := moves_in hα t a ha b hb
  use g; apply hGt; exact hg; exact H
#align alternating_group.moves_in' alternatingGroup.moves_in'

theorem has_three_cycle_of_stabilizer' (s : Set α)
    (hs : 2 < Fintype.card s) :-- (G : subgroup (equiv.perm α)) :
    --  (hG : stabilizer (equiv.perm α) s ⊓ alternating_group α < G) :
    ∃ g : Equiv.Perm α, g.IsThreeCycle ∧ g ∈ stabilizer (Equiv.Perm α) s :=
  by
  rw [Fintype.two_lt_card_iff] at hs 
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, hab, hac, hbc⟩ := hs
  rw [Ne.def, Subtype.mk_eq_mk, ← Ne.def] at hab hac hbc 
  use Equiv.swap a b * Equiv.swap a c
  constructor
  apply Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  rw [← stabilizer_compl]
  rw [mem_stabilizer_of_finite_iff]
  rintro _ ⟨x, hx, rfl⟩
  simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [Set.mem_compl_iff] at hx 
  suffices h : ∀ u ∈ s, x ≠ u
  · rw [Equiv.swap_apply_of_ne_of_ne (h a ha) (h c hc)]
    rw [Equiv.swap_apply_of_ne_of_ne (h a ha) (h b hb)]
    exact hx
  · intro u hu h; apply hx; rw [h]; exact hu
  exact sᶜ.toFinite
#align alternating_group.has_three_cycle_of_stabilizer' alternatingGroup.has_three_cycle_of_stabilizer'

theorem has_three_cycle_of_stabilizer [DecidableEq α] (s : Set α) (hα : 4 < Fintype.card α) :
    ∃ g : Equiv.Perm α, g.IsThreeCycle ∧ g ∈ stabilizer (Equiv.Perm α) s :=
  by
  cases' Nat.lt_or_ge 2 (Fintype.card s) with hs hs
  exact has_three_cycle_of_stabilizer' s hs
  obtain ⟨g, hg, hg'⟩ := has_three_cycle_of_stabilizer' (sᶜ) _
  · use g; rw [stabilizer_compl] at hg' ; exact ⟨hg, hg'⟩
  · rw [lt_iff_not_le] at hα ⊢
    intro hs'; apply hα
    rw [← Fintype.card_add_compl s]
    suffices 2 + 2 ≤ 4 by
      apply le_trans _ this
      apply Nat.add_le_add; exact hs
      apply le_trans _ hs'; apply le_of_eq
      simp only [Fintype.card_ofFinset, Set.mem_compl_iff]
    norm_num
#align alternating_group.has_three_cycle_of_stabilizer alternatingGroup.has_three_cycle_of_stabilizer

theorem le_of_isPreprimitive (s : Set α) (hα : 4 < Fintype.card α)
    -- (h0 : s.nonempty) (h1 : sᶜ.nonempty)
    -- (hs : fintype.card s < fintype.card (sᶜ : set α))
    (G : Subgroup (Equiv.Perm α))
    (hG : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α ≤ G) :
    IsPreprimitive G α → alternatingGroup α ≤ G :=
  by
  intro hG'
  -- intros s h0 h1 hα G hG,
  -- G : subgroup (equiv.perm α))
  -- hG : stabilizer (equiv.perm α) s ⊓ (alternating_group α) < G)
  -- We need to prove that alternating_group α ≤ ⊤
  -- G contains a three_cycle
  obtain ⟨g, hg3, hg⟩ := has_three_cycle_of_stabilizer s hα
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply jordan_three_cycle hG' hg3
  · apply hG
    simp only [Subgroup.mem_inf, hg, true_and_iff]
    exact Equiv.Perm.IsThreeCycle.mem_alternatingGroup hg3
#align alternating_group.le_of_is_preprimitive alternatingGroup.le_of_isPreprimitive

/- lemma stabilizer.is_preprimitive (s : set α) (hs : (sᶜ : set α).nontrivial):
  is_preprimitive (stabilizer (alternating_group α) s) s :=
begin
  let φ : stabilizer (alternating_group α) s → equiv.perm s := mul_action.to_perm,
  let f : s →ₑ[φ] s := {
  to_fun := id,
  map_smul' := λ ⟨g, hg⟩ ⟨x, hx⟩, by simp only [id.def, equiv.perm.smul_def, to_perm_apply], },
  have hf : function.bijective f := function.bijective_id,
  rw is_preprimitive_of_bijective_map_iff _ hf,
  exact equiv.perm.is_preprimitive s,

  -- function.surjective φ
  suffices : ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨k, hk_sign⟩ := this,
  have hks : (equiv.perm.of_subtype k) • s = s,
  { rw ← mem_stabilizer_iff,
    apply equiv.perm.of_subtype_mem_stabilizer', },

  -- function.surjective φ
  { intro g,
    have hgs : (equiv.perm.of_subtype g) • s = s,
    apply equiv.perm.of_subtype_mem_stabilizer,

    have hminus_one_ne_one : (-1 : units ℤ) ≠ 1,
    { intro h, rw [← units.eq_iff, units.coe_one, units.coe_neg_one] at h, norm_num at h, },

    let g' := ite (equiv.perm.sign g = 1)
      (equiv.perm.of_subtype g)
      (equiv.perm.of_subtype g * (equiv.perm.of_subtype k)),

    use g',

    rw equiv.perm.mem_alternating_group,
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg;
    { dsimp [g'], -- rw hsg,
      simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false,
        equiv.perm.sign_of_subtype,
        equiv.perm.sign_mul, mul_neg, mul_one, neg_neg, hsg, hk_sign], },

    rw mem_stabilizer_iff,
    change (ite (equiv.perm.sign g = 1)
      (equiv.perm.of_subtype g)
      (equiv.perm.of_subtype g * (equiv.perm.of_subtype k))) • s = s,
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg,
    { simp only [hsg,  eq_self_iff_true, if_true],
      exact hgs, },
    { simp only [hsg, hminus_one_ne_one, if_false],
      rw mul_smul, rw hks, exact hgs, },

    dsimp [φ],
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg,
    { dsimp [g'], simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false],
      ext,
      simp only [to_perm_apply, has_smul.smul_stabilizer_def, subtype.coe_mk],
      change equiv.perm.of_subtype g ↑x = ↑(g x),
      exact equiv.perm.of_subtype_apply_coe g x, },
    { dsimp [g'], simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false],
      ext,
      simp only [to_perm_apply, has_smul.smul_stabilizer_def, subtype.coe_mk],
      change ((equiv.perm.of_subtype g) * (equiv.perm.of_subtype k)) ↑x = ↑(g x),
      rw equiv.perm.mul_apply ,
      rw equiv.perm.of_subtype_apply_of_not_mem k _,
      exact equiv.perm.of_subtype_apply_coe g x,
      rw set.not_mem_compl_iff, exact x.prop, }, },

  -- ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨a, ha, b, hb, hab⟩ := hs,
  use equiv.swap ⟨a, ha⟩ ⟨b, hb⟩,
  rw equiv.perm.sign_swap _,
  rw ← function.injective.ne_iff (subtype.coe_injective),
  simp only [subtype.coe_mk], exact hab,
end

example (s t : set α) (a : α) (ha : a ∈ s ⊓ t) : a ∈ s :=
begin
  apply @inf_le_left _ _ s t,  exact ha,
end
-/
/-
lemma stabilizer.is_preprimitive' (s : set α) (hsc : sᶜ.nontrivial)
  (G : subgroup (equiv.perm α)) (hG : stabilizer (equiv.perm α) s ⊓ alternating_group α ≤ G) :
  is_preprimitive (stabilizer G s) s :=
begin
  let φ : stabilizer (alternating_group α) s → stabilizer G s := λ g,
  begin
    use (g : alternating_group α), apply hG, rw subgroup.mem_inf,
    split,
    { let h := g.prop, rw mem_stabilizer_iff at h ⊢, exact h, },
    { exact set_like.coe_mem ↑g, },
    { rw mem_stabilizer_iff, let h := g.prop, rw mem_stabilizer_iff at h, exact h, },
  end,
  let f : s →ₑ[φ] s := {
    to_fun := id,
    map_smul' := λ ⟨⟨m, hm'⟩, hm⟩ ⟨a, ha⟩, rfl, },
  have hf : function.surjective f := function.surjective_id,
  apply is_preprimitive_of_surjective_map hf,
  apply stabilizer.is_preprimitive,
  exact hsc,
end

-/
theorem isPreprimitive_of_stabilizer_lt (s : Set α) (h0 : s.Nontrivial) (h1 : sᶜ.Nontrivial)
    (hα : Fintype.card s < Fintype.card (sᶜ : Set α)) (h4 : 4 ≤ Fintype.card α)
    (G : Subgroup (Equiv.Perm α))
    (hG : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α < G ⊓ alternatingGroup α) :
    IsPreprimitive G α :=
  by
  -- G acts transitively
  have : is_pretransitive G α :=
    by
    have hG' : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α ≤ G :=
      le_trans (le_of_lt hG) inf_le_left
    apply Equiv.Perm.IsPretransitive.of_partition G s
    · intro a ha b hb
      obtain ⟨g, hg, H⟩ := alternatingGroup.moves_in h4 s a ha b hb
      use g
      apply hG'
      exact hg
      exact H
    · intro a ha b hb
      obtain ⟨g, hg, H⟩ := alternatingGroup.moves_in h4 (sᶜ) a ha b hb
      use g
      apply hG'
      rw [stabilizer_compl] at hg ; exact hg
      exact H
    · intro h
      apply (lt_iff_le_not_le.mp hG).right
      --  G ⊓ alternating_group α ≤ stabilizer (equiv.perm α) s ⊓ alternating_group α,
      rw [le_inf_iff]
      constructor
      · intro g; rw [Subgroup.mem_inf]; rintro ⟨hg, hg'⟩
        rw [mem_stabilizer_iff]
        rw [← Subgroup.coe_mk G g hg]
        change (⟨g, hg⟩ : ↥G) • s = s
        rw [← mem_stabilizer_iff]
        change _ ∈ stabilizer (↥G) s
        rw [h]; exact Subgroup.mem_top ⟨g, hg⟩
      · exact inf_le_right
  apply IsPreprimitive.mk
  -- The proof needs 4 steps 
  /- Step 1 : No block is equal to sᶜ
       This uses that fintype.card s < fintype.card sᶜ.
       In the equality case, fintype.card s = fintype.card sᶜ, it is possible that B = sᶜ,
       then G is the wreath product,
       this is case (b) of the O'Nan-Scott classification of max'l subgroups of the symmetric group -/
  have hB_ne_sc : ∀ (B : Set α) (hB : is_block G B), ¬B = sᶜ :=
    by
    intro B hB hBsc
    obtain ⟨b, hb⟩ := h1.nonempty; rw [← hBsc] at hb 
    obtain ⟨a, ha⟩ := h0.nonempty
    obtain ⟨k, hk⟩ := exists_smul_eq G b a
    suffices Fintype.card (B : Set α) ≤ Fintype.card s
      by
      apply Nat.lt_irrefl (Fintype.card B)
      apply lt_of_le_of_lt this
      simp_rw [hBsc]; exact hα
    rw [← smul_set_card_eq k B]
    apply Set.card_le_of_subset
    change k • B ⊆ s
    rw [← Set.disjoint_compl_right_iff_subset, ← hBsc]
    apply or_iff_not_imp_left.mp (is_block.def_one.mp hB k)
    intro h
    apply Set.not_mem_empty a
    rw [← Set.inter_compl_self s]
    constructor
    exact ha
    rw [← hk, ← hBsc, ← h, Set.smul_mem_smul_set_iff]; exact hb
  -- Step 2 : A block contained in sᶜ is a subsingleton
  have hB_not_le_sc : ∀ (B : Set α) (hB : is_block G B) (hBsc : B ⊆ sᶜ), B.Subsingleton :=
    by
    intro B hB hBsc
    suffices : B = coe '' (coe ⁻¹' B : Set (sᶜ : Set α))
    rw [this]
    apply Set.Subsingleton.image
    suffices : is_trivial_block (coe ⁻¹' B : Set (sᶜ : Set α))
    apply Or.resolve_right this
    intro hB'
    apply hB_ne_sc B hB
    apply Set.Subset.antisymm hBsc
    intro x hx
    rw [← Subtype.coe_mk x hx, ← Set.mem_preimage]
    rw [hB', Set.top_eq_univ]; apply Set.mem_univ
    · -- is_trivial_block (coe ⁻¹' B : set (sᶜ : set α)),
      suffices : IsPreprimitive (stabilizer G (sᶜ : Set α)) (sᶜ : Set α)
      refine' IsPreprimitive.has_trivial_blocks this _
      -- is_block (coe ⁻¹' B : set (sᶜ : set α))
      let φ' : stabilizer G (sᶜ : Set α) → G := coe
      let f' : (sᶜ : Set α) →ₑ[φ'] α :=
        { toFun := coe
          map_smul' := fun m x => by simp only [φ', has_smul.smul_stabilizer_def] }
      apply MulAction.isBlock_preimage f' hB
      apply stabilizer.is_preprimitive'
      rw [← stabilizer_compl] at hG 
      rw [compl_compl]; exact h0
      rw [stabilizer_compl]
      apply le_trans (le_of_lt hG)
      exact inf_le_left
    · -- B = coe '' (coe ⁻¹' B : set (sᶜ : set α)),
      apply Set.Subset.antisymm
      intro x hx
      use ⟨x, hBsc hx⟩
      simp only [hx, Set.mem_preimage, Subtype.coe_mk, eq_self_iff_true, and_self_iff]
      exact Set.image_preimage_subset coe B
  -- Step 3 : A block contained in s is a subsingleton
  have hB_not_le_s : ∀ (B : Set α) (hB : is_block G B), B ⊆ s → B.Subsingleton :=
    by
    intro B hB hBs
    suffices hB_coe : B = coe '' (coe ⁻¹' B : Set ↥s)
    suffices : is_trivial_block (coe ⁻¹' B : Set s)
    cases' this with hB' hB'
    · -- trivial case
      rw [hB_coe]
      apply Set.Subsingleton.image
      exact hB'
    · -- coe ⁻¹' B = s
      have hBs' : B = s := by
        apply Set.Subset.antisymm hBs
        intro x hx
        rw [← Subtype.coe_mk x hx]
        rw [← Set.mem_preimage]
        rw [hB']
        rw [Set.top_eq_univ]
        apply Set.mem_univ
      have : ∃ g' ∈ G, g' • s ≠ s := by
        by_contra
        apply ne_of_lt hG
        push_neg at h 
        apply le_antisymm
        exact le_of_lt hG
        intro g' hg'
        rw [Subgroup.mem_inf] at hg' ⊢
        rw [mem_stabilizer_iff]; apply And.intro (h g' hg'.left)
        exact hg'.right
      obtain ⟨g', hg', hg's⟩ := this
      cases' is_block.def_one.mp hB ⟨g', hg'⟩ with h h
      · -- case g' • B = B : absurd, since B = s and choice of g'
        exfalso
        apply hg's; rw [← hBs']; exact h
      · -- case g' • B disjoint from B
        suffices : (g' • B).Subsingleton
        apply Set.subsingleton_of_image _ B this
        apply Function.Bijective.injective
        apply MulAction.bijective
        apply hB_not_le_sc ((⟨g', hg'⟩ : G) • B)
        exact is_block_of_block _ hB
        rw [← hBs']
        apply Disjoint.subset_compl_right
        exact h
    · -- is_trivial_block (coe ⁻¹' B : set s),
      suffices : IsPreprimitive (stabilizer G s) (s : Set α)
      refine' IsPreprimitive.has_trivial_blocks this _
      -- is_block (coe ⁻¹' B : set s)
      let φ' : stabilizer G s → G := coe
      let f' : s →ₑ[φ'] α :=
        { toFun := coe
          map_smul' := fun ⟨m, hm⟩ x => by simp only [φ', has_smul.smul_stabilizer_def] }
      apply MulAction.isBlock_preimage f' hB
      apply stabilizer.is_preprimitive' s h1
      apply le_trans (le_of_lt hG); exact inf_le_left
    · -- B = coe '' (coe ⁻¹' B : set ↥s),
      apply Set.Subset.antisymm
      intro x hx
      use ⟨x, hBs hx⟩
      simp only [hx, Set.mem_preimage, Subtype.coe_mk, eq_self_iff_true, and_self_iff]
      exact Set.image_preimage_subset coe B
  intro B hB
  unfold is_trivial_block
  rw [or_iff_not_imp_left]
  intro hB'
  obtain ⟨a, ha, ha'⟩ :=
    set.not_subset_iff_exists_mem_not_mem.mp fun h => hB' ((hB_not_le_sc B hB) h)
  rw [Set.not_mem_compl_iff] at ha' 
  obtain ⟨b, hb, hb'⟩ :=
    set.not_subset_iff_exists_mem_not_mem.mp fun h => hB' ((hB_not_le_s B hB) h)
  rw [← Set.mem_compl_iff] at hb' 
  have hsc_le_B : sᶜ ⊆ B := by
    intro x hx'
    suffices : ∃ k : fixingSubgroup (alternatingGroup α) s, k • b = x
    obtain ⟨⟨k, hk⟩, hkbx : k • b = x⟩ := this
    suffices : k • B = B
    rw [← hkbx, ← this, Set.smul_mem_smul_set_iff]
    exact hb
    · -- k • B = B,
      apply or_iff_not_imp_right.mp (is_block.def_one.mp hB ⟨k, _⟩)
      · rw [Set.not_disjoint_iff_nonempty_inter]
        change (k • B ∩ B).Nonempty
        use a
        constructor
        rw [mem_fixingSubgroup_iff] at hk 
        rw [← hk a ha']
        exact Set.smul_mem_smul_set ha
        exact ha
      · -- ↑k ∈ G
        apply le_trans (le_of_lt hG); exact inf_le_left
        rw [Subgroup.mem_inf]; constructor
        suffices hk' : k ∈ stabilizer (alternatingGroup α) s
        · simpa [mem_stabilizer_iff] using hk'
        apply MulAction.fixingSubgroup_le_stabilizer; exact hk
        exact k.prop
    · -- ∃ (k : fixing_subgroup (alternating_group α) s), k • b = x,
      haveI :
        is_pretransitive (fixingSubgroup (alternatingGroup α) s)
          (SubMulAction.ofFixingSubgroup (alternatingGroup α) s) :=
        is_pretransitive_of_fixing_subgroup s h0 hα
      obtain ⟨k, hk⟩ :=
        exists_smul_eq (fixingSubgroup (alternatingGroup α) s)
          (⟨b, hb'⟩ : SubMulAction.ofFixingSubgroup (alternatingGroup α) s) ⟨x, hx'⟩
      use k
      rw [← Subtype.coe_inj, SubMulAction.val_smul] at hk 
      exact hk
  -- Conclusion of the proof : B = ⊤
  rw [eq_top_iff]
  intro x _
  obtain ⟨b, hb⟩ := h1.nonempty
  obtain ⟨⟨g, hg⟩, hgbx : g • b = x⟩ := exists_smul_eq G b x
  suffices g • B = B by
    rw [← hgbx, ← this, Set.smul_mem_smul_set_iff]
    exact hsc_le_B hb
  -- g • B = B,
  apply or_iff_not_imp_right.mp (is_block.def_one.mp hB ⟨g, hg⟩)
  rw [Set.not_disjoint_iff_nonempty_inter]
  change (g • B ∩ B).Nonempty
  apply aux_pigeonhole
  -- card B + card (g • B) = card B + card B
  -- ... ≥ card sᶜ + card sᶜ
  -- ... > card s + card s ᶜ = card α
  rw [← Fintype.card_add_compl s]
  apply Nat.lt_of_lt_of_le
  · apply Nat.add_lt_add_right _ (Fintype.card (sᶜ : Set α))
    use Fintype.card (sᶜ : Set α)
    exact hα
  apply Nat.add_le_add
  · apply le_trans (Set.card_le_of_subset hsc_le_B)
    apply le_of_eq
    rw [← Set.coe_toFinset B]
    simp only [← Set.toFinset_card]
    change _ = ((fun x => g • x) '' ↑B.to_finset).toFinset.card
    simp_rw [← Finset.coe_image]
    simp only [Finset.toFinset_coe]
    rw [Finset.card_image_of_injective _ (MulAction.injective g)]
  exact Set.card_le_of_subset hsc_le_B
#align alternating_group.is_preprimitive_of_stabilizer_lt alternatingGroup.isPreprimitive_of_stabilizer_lt

theorem isMaximalStab'
    -- (hα : 4 < fintype.card α)
    (s : Set α)
    (h0' : s.Nontrivial) (h1' : sᶜ.Nontrivial) (hs : Fintype.card s < Fintype.card (sᶜ : Set α)) :
    Subgroup.IsMaximal (stabilizer (alternatingGroup α) s) :=
  by
  suffices hα : 4 < Fintype.card α
  -- h0 : s.nonempty, h1  : sᶜ.nonempty
  /-   have h1' : sᶜ.nontrivial,
    { rw [← set.nontrivial_coe, ← fintype.one_lt_card_iff_nontrivial],
      apply lt_of_le_of_lt _ hs,
      rw [nat.succ_le_iff, fintype.card_pos_iff, set.nonempty_coe_sort],
      exact h0, },
   -/
  --  cases em(s.nontrivial) with h0' h0',
  -- We start with the case where s.nontrivial
  constructor;
  constructor
  -- stabilizer (alternating_group α) s ≠ ⊤
  exact stabilizer_ne_top' s h0'.nonempty h1'
  -- ∀ (G : subgroup (alternating_group α)), stabilizer (alternating_group α) s < b) → b = ⊤
  · intro G' hG'
    suffices alternatingGroup α ≤ G'.map (alternatingGroup α).Subtype
      by
      rw [eq_top_iff]; intro g hg
      obtain ⟨g', hg', hgg'⟩ := this g.prop
      simp only [Subgroup.coeSubtype, SetLike.coe_eq_coe] at hgg' 
      rw [← hgg']; exact hg'
    --   apply is_maximal_stab'_temp' s hα,
    apply le_of_is_preprimitive s hα
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.map_subtype_le_map_subtype]
    rw [MulAction.stabilizer_subgroupOf_eq] at hG' 
    exact le_of_lt hG'
    apply is_preprimitive_of_stabilizer_lt s h0' h1' hs (le_of_lt hα)
    rw [lt_iff_le_not_le]
    constructor
    · intro g
      simp only [Subgroup.mem_inf]
      rintro ⟨hg, hg'⟩
      refine' And.intro _ hg'
      simp only [Subgroup.mem_map, Subgroup.coeSubtype, exists_prop]
      use ⟨g, hg'⟩
      constructor
      · apply le_of_lt hG'
        simpa only [mem_stabilizer_iff] using hg
      rfl
    · intro h
      rw [lt_iff_le_not_le] at hG' ; apply hG'.right
      intro g' hg'
      rw [mem_stabilizer_iff]
      change (g' : Equiv.Perm α) • s = s; rw [← mem_stabilizer_iff]
      apply @inf_le_left (Subgroup (Equiv.Perm α)) _; apply h
      rw [Subgroup.mem_inf]
      apply And.intro _ g'.prop
      simp only [Subgroup.mem_map, Subgroup.coeSubtype, SetLike.coe_eq_coe, exists_prop,
        exists_eq_right]
      exact hg'
  -- hα : 4 < fintype.card α
  have h0 : 2 ≤ Fintype.card s
  rw [Nat.succ_le_iff, Fintype.one_lt_card_iff_nontrivial, Set.nontrivial_coe_sort]
  exact h0'
  change 2 + 2 < _
  rw [← Fintype.card_add_compl s]
  apply lt_of_le_of_lt
  exact Nat.add_le_add_right h0 2
  apply Nat.add_lt_add_left
  exact lt_of_le_of_lt h0 hs
#align alternating_group.is_maximal_stab' alternatingGroup.isMaximalStab'

theorem three_le {c n : ℕ} (h : 1 ≤ n) (h' : n < c) (hh' : c ≠ 2 * n) : 3 ≤ c :=
  by
  cases' Nat.eq_or_lt_of_le h with h h
  · rw [← h] at h' hh' 
    cases' Nat.eq_or_lt_of_le h' with h' h'
    · exfalso; apply hh' h'.symm
    exact h'
  rw [Nat.succ_le_iff]
  exact lt_of_le_of_lt h h'
#align alternating_group.three_le alternatingGroup.three_le

/-- stabilizer (alternating_group α) s is a maximal subgroup of alternating_group α,
provided s ≠ ⊥, s ≠ ⊤ and fintype.card α ≠ 2 * fintype.card ↥s) -/
theorem Stabilizer.isMaximal (s : Set α) (h0 : s.Nonempty) (h1 : sᶜ.Nonempty)
    (hs : Fintype.card α ≠ 2 * Fintype.card ↥s) :
    Subgroup.IsMaximal (stabilizer (alternatingGroup α) s) :=
  by
  have hα : 3 ≤ Fintype.card α :=
    by
    rw [← Set.nonempty_coe_sort, ← Fintype.card_pos_iff, ← Nat.succ_le_iff] at h0 h1 
    refine' three_le h0 _ hs
    rw [← tsub_pos_iff_lt, ← Fintype.card_compl_set]; exact h1
  have : Nontrivial α := by rw [← Fintype.one_lt_card_iff_nontrivial]; apply lt_of_lt_of_le _ hα;
    norm_num
  have h :
    ∀ (t : Set α) (h0 : t.Nonempty) (h0' : t.Subsingleton),
      (stabilizer (alternatingGroup α) t).IsMaximal :=
    by
    intro t ht ht'
    suffices : ∃ a : α, t = ({a} : Set α)
    obtain ⟨a, rfl⟩ := this
    have : stabilizer (alternatingGroup α) ({a} : Set α) = stabilizer (alternatingGroup α) a := by
      ext g; simp only [mem_stabilizer_iff, Set.smul_set_singleton, Set.singleton_eq_singleton_iff]
    rw [this]
    apply hasMaximalStabilizersOfPreprimitive
    apply alternating_group.is_preprimitive hα
    · obtain ⟨a, ha⟩ := ht
      use a; exact Set.Subsingleton.eq_singleton_of_mem ht' ha
  cases' em s.nontrivial with h0' h0'
  cases' em sᶜ.Nontrivial with h1' h1'
  -- h0' : s.nontrivial, h1' : sᶜ.nontrivial
  cases' Nat.lt_trichotomy (Fintype.card s) (Fintype.card (sᶜ : Set α)) with hs' hs'
  · exact is_maximal_stab' s h0' h1' hs'
  cases' hs' with hs' hs'
  · exfalso; apply hs
    rw [← Fintype.card_add_compl s, ← hs', ← two_mul]
  · rw [← compl_compl s] at h0' 
    rw [← stabilizer_compl]
    apply is_maximal_stab' (sᶜ) h1' h0'
    simp_rw [compl_compl s]
    convert hs'
  -- h0' : s.nontrivial, h1' : ¬(s.nontrivial)
  · simp only [Set.not_nontrivial_iff] at h1' 
    rw [← stabilizer_compl]; exact h (sᶜ) h1 h1'
  -- h0' : ¬(s.nontrivial),
  · simp only [Set.not_nontrivial_iff] at h0' 
    exact h s h0 h0'
#align alternating_group.stabilizer.is_maximal alternatingGroup.Stabilizer.isMaximal

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The action of alternating_group α on the n-element subsets of α is preprimitive
provided 0 < n < #α and #α ≠ 2*n -/
theorem Nat.finset_isPreprimitive_of_alt (n : ℕ) (h_one_le : 1 ≤ n) (hn : n < Fintype.card α)
    (hα : Fintype.card α ≠ 2 * n) : IsPreprimitive (alternatingGroup α) (n.Finset α) :=
  by
  have hα' : 3 ≤ Fintype.card α := three_le h_one_le hn hα
  have : Nontrivial α := by rw [← Fintype.one_lt_card_iff_nontrivial];
    exact lt_of_le_of_lt h_one_le hn
  cases' Nat.eq_or_lt_of_le h_one_le with h_one h_one_lt
  · -- n = 1 :
    let f : α →[alternatingGroup α] Nat.finset α 1 :=
      { toFun := fun x => ⟨{x}, Finset.card_singleton x⟩
        map_smul' := fun g x => rfl }
    rw [← h_one]
    suffices hf : Function.Surjective f
    · apply isPreprimitive_of_surjective_map hf
      exact alternating_group.is_preprimitive hα'
    rintro ⟨s, hs⟩
    change s.card = 1 at hs 
    rw [Finset.card_eq_one] at hs 
    obtain ⟨a, ha⟩ := hs
    use a
    simp only [ha, EquivariantMap.coe_mk]; rfl
  -- h_one_lt : 1 < n
  have ht : is_pretransitive (alternatingGroup α) (n.finset α) :=
    by
    -- apply nat.finset_is_pretransitive_of_multiply_pretransitive,
    have : Fintype.card α - n + n = Fintype.card α := by apply Nat.sub_add_cancel; exact le_of_lt hn
    rw [isPretransitive_of_bijective_map_iff Function.surjective_id
        (Nat.finsetCompl_bijective α (alternatingGroup α) n this)]
    apply Nat.finset_isPretransitive_of_multiply_pretransitive
    have h' : Fintype.card α - n ≤ Fintype.card α - 2 := by apply Nat.sub_le_sub_left;
      exact h_one_lt
    apply is_multiply_pretransitive_of_higher (alternatingGroup α) α _ h'
    rw [PartENat.card_eq_coe_fintype_card]; simp only [PartENat.coe_le_coe, tsub_le_self]
    exact alternating_group_is_fully_minus_two_pretransitive α
  haveI : Nontrivial (n.finset α) :=
    Nat.finset_nontrivial α n (lt_trans (Nat.lt_succ_self 0) h_one_lt) hn
  obtain ⟨sn : n.finset α⟩ := Nontrivial.to_nonempty
  let s := sn.val
  let hs : s.card = n := sn.prop
  -- have hs : (s : finset α).card = n := s.prop,
  rw [← maximal_stabilizer_iff_preprimitive (alternatingGroup α) sn]
  have : stabilizer (alternatingGroup α) sn = stabilizer (alternatingGroup α) (s : Set α) :=
    by
    ext g
    simp only [mem_stabilizer_iff]
    rw [← Subtype.coe_inj]
    change g • s = s ↔ _
    rw [← Finset.coe_smul_finset, ← Finset.coe_inj]
  rw [this]
  apply stabilizer.is_maximal (s : Set α)
  · simp only [Finset.coe_nonempty, ← Finset.card_pos, hs]
    apply lt_trans one_pos h_one_lt
  · simp only [← Finset.coe_compl, Finset.coe_nonempty, ← Finset.card_compl_lt_iff_nonempty,
      compl_compl, hs]
    exact hn
  · simp only [Finset.coe_sort_coe, Fintype.card_coe, hs]
    exact hα
  infer_instance
#align alternating_group.nat.finset_is_preprimitive_of_alt alternatingGroup.Nat.finset_isPreprimitive_of_alt

end alternatingGroup


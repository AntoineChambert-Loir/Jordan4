/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module primitive
-/
import Oneshot.ForMathlib.Stabilizer
import Oneshot.ForMathlib.Pretransitive
import Oneshot.ForMathlib.Set
import Oneshot.EquivariantMap
import Oneshot.SubMulActions
import Oneshot.ForMathlib.Partitions
import Oneshot.MaximalSubgroups
import Oneshot.ForMathlib.Commutators
import Oneshot.Blocks
import Mathbin.Data.Setoid.Partition
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.GroupAction.SubMulAction
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.GroupTheory.Subgroup.Simple
import Mathbin.GroupTheory.Abelianization
import Mathbin.GroupTheory.Commutator
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Data.Nat.Prime
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Fintype.Card
import Mathbin.Algebra.BigOperators.Order

/-!
# Primitive actions and the Iwasawa criterion

## Definitions

- `is_preprimitive G X`
a structure that says that the action of a type `G`
on a type `X` (defined by an instance `has_smul G X`) is *preprimitive*,
namely, it is pretransitive and the only blocks are ⊤ and subsingletons.
(The pretransitivity assumption is essentially trivial, because orbits are blocks,
unless the action itself is trivial.)

The notion which is introduced in classical books on group theory
is restricted to `mul_action` of groups.
In fact, it may be irrelevant if the action is degenerate,
when “trivial blocks” might not be blocks.
Moreover, the classical notion is *primitive*,
which assumes moreover that `X` is not empty.

- `is_quasipreprimitive G X`
a structure that says that the `mul_action`
of the group `G` on the type `X` is *quasipreprimitive*,
namely, normal subgroups of `G` which act nontrivially act pretransitively.

- We prove some straightforward theorems that relate preprimitivity under equivariant maps, for images and preimages.

## Relation with stabilizers

- `is_preprimitive_of_block_order`
relates primitivity and the fact that the inclusion
order on blocks containing is simple.

- `maximal_stabilizer_iff_preprimitive`
an action is preprimitive iff the stabilizers of points are maximal subgroups.

## Relation with normal subgroups

- `is_preprimitive.is_quasipreprimitive`
preprimitive actions are quasipreprimitive

## Particular results for actions on finite types

- `is_preprimitive_of_prime` :
a pretransitive action on a finite type of prime cardinal is preprimitive

- `is_preprimitive_of_large_image`
Given an equivariant map from a preprimitive action,
if the image is at least twice the codomain, then the codomain is preprimitive

- `rudio`
Theorem of Rudio :
Given a preprimitive action of a group `G` on `X`, a finite `A : set X`
and two points, find a translate of `A` that contains one of them
and not the other one.
The proof relies on `is_block.of_subset` that itself requires finiteness of `A`,
but I don't know whether the theorem does…

## Iwasawa criterion

- `iwasawa_structure`
the structure underlying the Iwasawa criterion for simplicity

- `commutator_le_iwasawa` and `is_simple_iwasawa`
give two versions of that Iwasawa criterion

-/


open MulAction

section Primitive

variable (G : Type _) (X : Type _)

-- Note : if the action is degenerate, singletons may not be blocks.
/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
class IsPreprimitive [SMul G X] extends IsPretransitive G X : Prop where
  has_trivial_blocks' : ∀ {B : Set X}, IsBlock G B → IsTrivialBlock B
#align is_preprimitive IsPreprimitive

/--
A `mul_action` of a group is quasipreprimitive if any normal subgroup that has no fixed point acts pretransitively -/
class IsQuasipreprimitive [Group G] [MulAction G X] extends IsPretransitive G X : Prop where
  pretransitive_of_normal :
    ∀ {N : Subgroup G} (nN : N.Normal), fixedPoints N X ≠ ⊤ → MulAction.IsPretransitive N X
#align is_quasipreprimitive IsQuasipreprimitive

variable {G X}

theorem IsPreprimitive.has_trivial_blocks [SMul G X] (h : IsPreprimitive G X) {B : Set X}
    (hB : IsBlock G B) : B.Subsingleton ∨ B = ⊤ := by apply h.has_trivial_blocks'; exact hB
#align is_preprimitive.has_trivial_blocks IsPreprimitive.has_trivial_blocks

theorem IsPreprimitive.on_subsingleton [SMul G X] [Nonempty G] [Subsingleton X] :
    IsPreprimitive G X :=
  by
  have : is_pretransitive G X := by
    apply is_pretransitive.mk
    intro x y
    use Classical.arbitrary G
    rw [eq_iff_true_of_subsingleton]
    trivial
  apply IsPreprimitive.mk
  intro B hB
  apply Or.intro_left
  exact Set.subsingleton_of_subsingleton
#align is_preprimitive.on_subsingleton IsPreprimitive.on_subsingleton

theorem IsTrivialBlock.of_card_le_2 [Fintype X] (hX : Fintype.card X ≤ 2) (B : Set X) :
    IsTrivialBlock B := by
  classical
  cases' le_or_lt (Fintype.card B) 1 with h1 h1
  · apply Or.intro_left
    rw [← Set.subsingleton_coe, ← Fintype.card_le_one_iff_subsingleton]
    exact h1
  · apply Or.intro_right
    rw [Set.top_eq_univ, ← set_fintype_card_eq_univ_iff]
    exact le_antisymm (set_fintype_card_le_univ B) (le_trans hX h1)
#align is_trivial_block.of_card_le_2 IsTrivialBlock.of_card_le_2

variable [Group G] [MulAction G X]

open scoped BigOperators Pointwise

variable {G X}

theorem isTrivialBlock_of_block {B : Set X} (g : G) (hB : IsTrivialBlock B) :
    IsTrivialBlock (g • B) := by
  cases hB
  · apply Or.intro_left
    apply Set.Subsingleton.image hB
  · apply Or.intro_right
    rw [hB]
    rw [eq_top_iff]
    intro x _
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact Set.mem_univ _
#align is_trivial_block_of_block isTrivialBlock_of_block

theorem isTrivialBlock_of_block_iff {B : Set X} (g : G) :
    IsTrivialBlock B ↔ IsTrivialBlock (g • B) :=
  by
  constructor
  exact isTrivialBlock_of_block g
  · intro hgB
    rw [← inv_smul_smul g B]
    apply isTrivialBlock_of_block
    exact hgB
#align is_trivial_block_of_block_iff isTrivialBlock_of_block_iff

theorem IsPreprimitive.mk_mem [htGX : IsPretransitive G X] (a : X)
    (H : ∀ (B : Set X) (ha : a ∈ B) (hB : IsBlock G B), IsTrivialBlock B) : IsPreprimitive G X :=
  by
  apply IsPreprimitive.mk
  intro B hB
  cases Set.eq_empty_or_nonempty B
  · apply Or.intro_left; rw [h]; exact Set.subsingleton_empty
  · obtain ⟨b, hb⟩ := h
    obtain ⟨g, hg⟩ := exists_smul_eq G b a
    rw [isTrivialBlock_of_block_iff g]
    refine' H (g • B) _ (is_block_of_block g hB)
    use b; exact ⟨hb, hg⟩
#align is_preprimitive.mk_mem IsPreprimitive.mk_mem

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) (based condition) -/
theorem IsPreprimitive.mk_mem' (a : X) (ha : a ∉ fixedPoints G X)
    (H : ∀ (B : Set X) (haB : a ∈ B) (hB : IsBlock G B), IsTrivialBlock B) : IsPreprimitive G X :=
  by
  have : is_pretransitive G X := by
    apply is_pretransitive.mk_base a
    cases' H (orbit G a) (mem_orbit_self a) (is_block_of_orbit a) with H H
    · exfalso; apply ha
      rw [Set.subsingleton_iff_singleton (mem_orbit_self a)] at H 
      simp only [mem_fixed_points]; intro g
      rw [← Set.mem_singleton_iff]; rw [← H]
      exact mem_orbit a g
    · intro x; rw [← MulAction.mem_orbit_iff, H]; exact Set.mem_univ x
  apply IsPreprimitive.mk
  intro B hB
  cases Set.eq_empty_or_nonempty B
  · apply Or.intro_left; rw [h]; exact Set.subsingleton_empty
  · obtain ⟨b, hb⟩ := h
    obtain ⟨g, hg⟩ := exists_smul_eq G b a
    rw [isTrivialBlock_of_block_iff g]
    refine' H (g • B) _ (is_block_of_block g hB)
    use b; exact ⟨hb, hg⟩
#align is_preprimitive.mk_mem' IsPreprimitive.mk_mem'

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) -/
theorem IsPreprimitive.mk' (Hnt : fixedPoints G X ≠ ⊤)
    (H : ∀ (B : Set X) (hB : IsBlock G B), IsTrivialBlock B) : IsPreprimitive G X :=
  by
  have : ∃ a : X, a ∉ fixed_points G X := by
    by_contra; push_neg at h ; apply Hnt; rw [eq_top_iff]
    intro a _; exact h a
  obtain ⟨a, ha⟩ := this
  apply IsPreprimitive.mk_mem' a ha
  intro B _; exact H B
#align is_preprimitive.mk' IsPreprimitive.mk'

end Primitive

section EquivariantMap

variable {M : Type _} [Group M] {α : Type _} [MulAction M α]

variable {N β : Type _} [Group N] [MulAction N β]

theorem isTrivialBlock_of_surjective_map {φ : M → N} {f : α →ₑ[φ] β} (hf : Function.Surjective f)
    {B : Set α} (hB : IsTrivialBlock B) : IsTrivialBlock (f '' B) :=
  by
  cases' hB with hB hB
  · apply Or.intro_left; apply Set.Subsingleton.image hB
  · apply Or.intro_right; rw [hB]
    simp only [Set.top_eq_univ, Set.image_univ, Set.range_iff_surjective]
    exact hf
#align is_trivial_block_of_surjective_map isTrivialBlock_of_surjective_map

theorem isTrivialBlock_of_injective_map {φ : M → N} {f : α →ₑ[φ] β} (hf : Function.Injective f)
    {B : Set β} (hB : IsTrivialBlock B) : IsTrivialBlock (f ⁻¹' B) :=
  by
  cases' hB with hB hB
  apply Or.intro_left; exact Set.Subsingleton.preimage hB hf
  apply Or.intro_right; simp only [hB, Set.top_eq_univ]; apply Set.preimage_univ
#align is_trivial_block_of_injective_map isTrivialBlock_of_injective_map

theorem isPreprimitive_of_surjective_map {φ : M → N} {f : α →ₑ[φ] β} (hf : Function.Surjective f)
    (h : IsPreprimitive M α) : IsPreprimitive N β :=
  by
  haveI : is_pretransitive N β := isPretransitive_of_surjective_map hf h.to_is_pretransitive
  apply IsPreprimitive.mk
  · intro B hB
    rw [← Set.image_preimage_eq B hf]
    apply isTrivialBlock_of_surjective_map hf
    apply h.has_trivial_blocks
    apply is_block_preimage
    exact hB
#align is_preprimitive_of_surjective_map isPreprimitive_of_surjective_map

/-
lemma is_pretransitive_of_bijective_map_iff
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.surjective f.to_fun)
  (h : is_preprimitive M α) : is_preprimitive N β :=

(f : mul_action_bihom M α N β)
  (hf : function.bijective f.to_fun) (hφ : function.surjective f.to_monoid_hom.to_fun) :
  is_pretransitive M α ↔ is_pretransitive N β :=
begin
  split,
  apply is_pretransitive_of_bihom f (function.bijective.surjective hf),
  intro hN, let hN_eq := hN.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x y,
  obtain ⟨k, hk⟩ := exists_smul_eq N (f.to_fun x) (f.to_fun y),
  obtain ⟨g, rfl⟩ := hφ k,
  use g,
  apply function.bijective.injective hf,
  rw ← f.map_smul', exact hk,
end -/
theorem isPreprimitive_of_bijective_map_iff {φ : M → N} {f : α →ₑ[φ] β} (hφ : Function.Surjective φ)
    (hf : Function.Bijective f) : IsPreprimitive M α ↔ IsPreprimitive N β :=
  by
  constructor
  apply isPreprimitive_of_surjective_map hf.surjective
  · intro hN
    haveI := (isPretransitive_of_bijective_map_iff hφ hf).mpr hN.to_is_pretransitive
    apply IsPreprimitive.mk
    · intro B hB
      rw [← Set.preimage_image_eq B hf.injective]
      apply isTrivialBlock_of_injective_map hf.injective
      apply hN.has_trivial_blocks
      apply is_block_image f hφ hf.injective
      exact hB
#align is_preprimitive_of_bijective_map_iff isPreprimitive_of_bijective_map_iff

theorem isPreprimitive_of_bijective_map_iff' (φ : M → N) (f : α →ₑ[φ] β)
    (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPreprimitive M α ↔ IsPreprimitive N β :=
  by
  constructor
  apply isPreprimitive_of_surjective_map hf.surjective
  · intro hN
    haveI := (isPretransitive_of_bijective_map_iff hφ hf).mpr hN.to_is_pretransitive
    apply IsPreprimitive.mk
    · intro B hB
      rw [← Set.preimage_image_eq B hf.injective]
      apply isTrivialBlock_of_injective_map hf.injective
      apply hN.has_trivial_blocks
      apply is_block_image f hφ hf.injective
      exact hB
#align is_preprimitive_of_bijective_map_iff' isPreprimitive_of_bijective_map_iff'

end EquivariantMap

section Stabilizer

variable (G : Type _) [Group G] {X : Type _} [MulAction G X]

open scoped BigOperators Pointwise

instance Block.boundedOrderOfMem (a : X) : BoundedOrder { B : Set X // a ∈ B ∧ IsBlock G B }
    where
  top := ⟨⊤, by rw [Set.top_eq_univ]; apply Set.mem_univ, top_isBlock X⟩
  le_top := by
    rintro ⟨B, ha, hB⟩
    simp only [Set.top_eq_univ, Subtype.mk_le_mk, Set.le_eq_subset, Set.subset_univ]
  bot := ⟨{a}, Set.mem_singleton a, singleton_isBlock a⟩
  bot_le := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, Set.le_eq_subset, Set.singleton_subset_iff]
    exact ha
#align block.bounded_order_of_mem Block.boundedOrderOfMem

theorem Block.boundedOrderOfMem.top_eq (a : X) : ((Block.boundedOrderOfMem G a).top : Set X) = ⊤ :=
  rfl
#align block.bounded_order_of_mem.top_eq Block.boundedOrderOfMem.top_eq

theorem Block.boundedOrderOfMem.bot_eq (a : X) :
    ((Block.boundedOrderOfMem G a).bot : Set X) = {a} :=
  rfl
#align block.bounded_order_of_mem.bot_eq Block.boundedOrderOfMem.bot_eq

theorem Block.mem_is_nontrivial_order_of_nontrivial [Nontrivial X] (a : X) :
    Nontrivial { B : Set X // a ∈ B ∧ IsBlock G B } :=
  by
  rw [nontrivial_iff]
  use (Block.boundedOrderOfMem G a).bot
  use (Block.boundedOrderOfMem G a).top
  intro h
  rw [← Subtype.coe_inj] at h 
  simp only [Block.boundedOrderOfMem.top_eq, Block.boundedOrderOfMem.bot_eq] at h 
  obtain ⟨b, hb⟩ := exists_ne a
  apply hb
  rw [← Set.mem_singleton_iff]
  rw [h]
  rw [Set.top_eq_univ]; apply Set.mem_univ
#align block.mem_is_nontrivial_order_of_nontrivial Block.mem_is_nontrivial_order_of_nontrivial

/-- A pretransitive action on a nontrivial type is preprimitive iff
the set of blocks containing a given element is a simple order -/
theorem isPreprimitive_iff_isSimpleOrder_blocks [htGX : IsPretransitive G X] [Nontrivial X]
    (a : X) : IsPreprimitive G X ↔ IsSimpleOrder { B : Set X // a ∈ B ∧ IsBlock G B } :=
  by
  haveI : Nontrivial { B : Set X // a ∈ B ∧ is_block G B } :=
    Block.mem_is_nontrivial_order_of_nontrivial G a
  constructor
  · intro hGX'; apply IsSimpleOrder.mk
    rintro ⟨B, haB, hB⟩
    simp only [← Subtype.coe_inj, Subtype.coe_mk]
    cases hGX'.has_trivial_blocks hB
    · apply Or.intro_left
      change B = ↑(Block.boundedOrderOfMem G a).bot
      rw [Block.boundedOrderOfMem.bot_eq]
      exact Set.Subsingleton.eq_singleton_of_mem h haB
    · apply Or.intro_right
      change B = ↑(Block.boundedOrderOfMem G a).top
      exact h
  · intro h; let h_bot_or_top := h.eq_bot_or_eq_top
    apply IsPreprimitive.mk_mem a
    intro B haB hB
    cases' h_bot_or_top ⟨B, haB, hB⟩ with hB' hB' <;>
      simp only [← Subtype.coe_inj, Subtype.coe_mk] at hB' 
    · apply Or.intro_left
      rw [hB']; exact Set.subsingleton_singleton
    · apply Or.intro_right
      rw [hB']; rfl
    infer_instance
#align is_preprimitive_iff_is_simple_order_blocks isPreprimitive_iff_isSimpleOrder_blocks

/-- An pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/
theorem maximal_stabilizer_iff_preprimitive [htGX : IsPretransitive G X] [hnX : Nontrivial X]
    (a : X) : (stabilizer G a).IsMaximal ↔ IsPreprimitive G X :=
  by
  --  let s := stabilizer_block_equiv a,
  rw [isPreprimitive_iff_isSimpleOrder_blocks G a]
  rw [Subgroup.isMaximal_def]
  rw [← Set.isSimpleOrder_Ici_iff_isCoatom]
  simp only [isSimpleOrder_iff_isCoatom_bot]
  rw [← OrderIso.isCoatom_iff (stabilizer_block_equiv G a)]
  rw [OrderIso.map_bot]
#align maximal_stabilizer_iff_preprimitive maximal_stabilizer_iff_preprimitive

/-- In a preprimitive action, stabilizers are maximal subgroups -/
theorem hasMaximalStabilizersOfPreprimitive [hnX : Nontrivial X] (hpGX : IsPreprimitive G X)
    (a : X) : (stabilizer G a).IsMaximal :=
  by
  haveI : is_pretransitive G X := hpGX.to_is_pretransitive
  rw [maximal_stabilizer_iff_preprimitive]
  exact hpGX
#align has_maximal_stabilizers_of_preprimitive hasMaximalStabilizersOfPreprimitive

end Stabilizer

section Normal

variable {M : Type _} [Group M] {α : Type _} [MulAction M α]

/-- If a subgroup acts nontrivially, then the type is nontrivial -/
theorem isnontrivial_of_nontrivial_action {N : Subgroup M} (h : fixedPoints N α ≠ ⊤) :
    Nontrivial α := by
  apply Or.resolve_left (subsingleton_or_nontrivial α)
  intro hα; apply h
  rw [eq_top_iff]; intro x hx
  rw [mem_fixed_points]; intro g
  rw [subsingleton_iff] at hα 
  apply hα
#align isnontrivial_of_nontrivial_action isnontrivial_of_nontrivial_action

/-
theorem pretransitive_of_normal_of_preprimitive {N : subgroup M} (nN : subgroup.normal N)
  (hGX : is_preprimitive M α) (hNX : fixed_points N α ≠ ⊤) :
  mul_action.is_pretransitive N α :=
begin
  have : ∃ (x : α), x ∉ fixed_points N α,
  { rw [← set.ne_univ_iff_exists_not_mem, ← set.top_eq_univ],
    exact hNX },
  obtain ⟨a, ha⟩ := this,
  rw ← mul_action.orbit.is_pretransitive_iff a,
  apply or.resolve_left (hGX.has_trivial_blocks (orbit.is_block_of_normal nN a)),
  intro h,
  apply ha, simp only [mem_fixed_points], intro n,
  rw ← set.mem_singleton_iff,
  suffices : orbit N a = {a}, { rw ← this, use n, },
  { ext b,
    rw set.subsingleton.eq_singleton_of_mem h (mul_action.mem_orbit_self a) },
end
-/
/-- In a preprimitive action,
  any normal subgroup that acts nontrivially is pretransitive
  (Wielandt, th. 7.1)-/
theorem IsPreprimitive.isQuasipreprimitive (hGX : IsPreprimitive M α) : IsQuasipreprimitive M α :=
  by
  apply IsQuasipreprimitive.mk
  intro N hN hNX
  have : ∃ x : α, x ∉ fixed_points N α :=
    by
    rw [← Set.ne_univ_iff_exists_not_mem, ← Set.top_eq_univ]
    exact hNX
  obtain ⟨a, ha⟩ := this
  rw [← MulAction.orbit.isPretransitive_iff a]
  apply Or.resolve_left (hGX.has_trivial_blocks (orbit.is_block_of_normal hN a))
  intro h
  apply ha; simp only [mem_fixed_points]; intro n
  rw [← Set.mem_singleton_iff]
  suffices orbit N a = {a} by rw [← this]; use n
  · ext b
    rw [Set.Subsingleton.eq_singleton_of_mem h (MulAction.mem_orbit_self a)]
#align is_preprimitive.is_quasipreprimitive IsPreprimitive.isQuasipreprimitive

/-
/-- If the action of M on α is primitive,
then for any normal subgroup N that acts nontrivially,
any a : α, the groups N and (stabilizer G a) generate M.
-/
lemma prim_to_full (is_prim: is_preprimitive M α)
  (a: α) (N : subgroup M) (nN : subgroup.normal N) (hNX : mul_action.fixed_points N α ≠ ⊤) :
  N ⊔ (mul_action.stabilizer M a) = ⊤ :=
begin
  haveI : is_pretransitive M α := is_prim.to_is_pretransitive,
  let is_pretrans := is_prim.to_is_pretransitive.exists_smul_eq,
  haveI : nontrivial α := isnontrivial_of_nontrivial_action hNX,
  -- Using that stabilizers are maximal, we reduce the assertion to contradicting
  -- an inclusion N ≤ stabilizer M a
  rw [← maximal_stabilizer_iff_preprimitive M a, subgroup.is_maximal_def, is_coatom] at is_prim,
  apply is_prim.right (N ⊔ (mul_action.stabilizer M a)),
  rw right_lt_sup, intro hz,
  -- The contradiction come from the hypothesis that N acts nontrivially
  apply hNX,
  -- Synthetically, N = g • N • g⁻¹ is contained in stabilizer M (g • a),
  -- so acts trivially in g • a.
  -- Using transitivity of the action, we get that N acts trivially
  -- (This is done by hand)
  rw [mul_action.fixed_points, set.top_eq_univ],
  apply set.eq_univ_of_forall,
  intro y, rw set.mem_set_of_eq, rintro ⟨g, hg⟩,
  change g • y = y,
  obtain ⟨h, hy⟩ := is_pretrans y a,
  rw smul_eq_iff_eq_inv_smul at hy,
  rw hy,
  rw ← smul_eq_iff_eq_inv_smul,
  simp only [← mul_smul, ← mul_assoc],
  rw ← mul_action.mem_stabilizer_iff,
  apply hz,
  apply nN.conj_mem g _ h,
  exact hg
end

lemma normal_core_of_stabilizer_acts_trivially (trans: is_pretransitive M α) (a: α) :
  mul_action.fixed_points (stabilizer M a).normal_core α = ⊤  :=
begin
  let trans_eq := trans.exists_smul_eq,
  rw eq_top_iff,
/-  apply (fixing_subgroup_fixed_points_gc M α).le_u,
  simp only [set.top_eq_univ, function.comp_app, order_dual.to_dual_le],
-/
  intros x _,
  rw mem_fixed_points, rintro ⟨g, hg⟩,
  change g • x = x,
  obtain ⟨k, hk⟩ := trans_eq x a,
  rw smul_eq_iff_eq_inv_smul at hk,
  rw hk,
  rw ← smul_eq_iff_eq_inv_smul,
  simp only [← mul_smul, ← mul_assoc],
  rw ← mem_stabilizer_iff,
  apply subgroup.normal_core_le,
  apply (stabilizer M a).normal_core_normal.conj_mem,
  exact hg
end

example (N K : subgroup M) (h : K < K ⊔ N) : ¬ (N ≤ K) :=
begin
exact left_lt_sup.mp h
end


lemma prim_to_full' (is_prim: is_preprimitive M α)
  (a: α) {N : subgroup M} (nN : subgroup.normal N) (hNX : mul_action.fixed_points N α ≠ ⊤) :
  N ⊔ (mul_action.stabilizer M a) = ⊤ :=
begin
  haveI : is_pretransitive M α := is_prim.to_is_pretransitive,
  resetI,
  let is_pretrans := is_prim.to_is_pretransitive.exists_smul_eq,
  haveI : nontrivial α := isnontrivial_of_nontrivial_action hNX,
  let is_prim' := id is_prim,
  rw [← maximal_stabilizer_iff_preprimitive M a, subgroup.is_maximal_def, is_coatom] at is_prim,
  apply is_prim.right (N ⊔ (mul_action.stabilizer M a)),
  rw right_lt_sup, intro hz, apply hNX,
  rw ← N.normal_core_eq_self,
  rw eq_top_iff,
  refine le_trans _ ((fixed_points_subgroup_antitone M α) (subgroup.normal_core_mono hz)),
  simp only,
  rw normal_core_of_stabilizer_acts_trivially is_prim'.to_is_pretransitive,
  exact le_of_eq rfl
end

-/
end Normal

section Finite

variable {M : Type _} [Group M] {α : Type _} [MulAction M α]

variable {N β : Type _} [Group N] [MulAction N β]

open scoped Classical BigOperators Pointwise

/-- A pretransitive action on a set of prime order is preprimitive -/
theorem isPreprimitive_of_prime [Fintype α] [hGX : IsPretransitive M α]
    (hp : Nat.Prime (Fintype.card α)) : IsPreprimitive M α :=
  by
  apply IsPreprimitive.mk
  intro B hB
  cases' subsingleton_or_nontrivial B with hB' hB'
  · apply Or.intro_left; rw [← Set.subsingleton_coe]; exact hB'
  apply Or.intro_right
  suffices : Fintype.card ↥B = 1 ∨ Fintype.card B = Fintype.card α
  cases' this with h h
  · exfalso
    rw [← Fintype.one_lt_card_iff_nontrivial] at hB' 
    exact ne_of_lt hB' h.symm
  · rw [Set.top_eq_univ, ← Set.coe_toFinset B, ← Set.coe_toFinset Set.univ, Finset.coe_inj]
    rw [Set.toFinset_univ, ← Finset.card_eq_iff_eq_univ, ← h]
    simp only [Set.toFinset_card]
    exact setFintype Set.univ
  · rw [← Nat.dvd_prime hp]
    simp only [← Nat.card_eq_fintype_card]
    apply nat_card_of_block_divides hB
    rw [← Set.nonempty_coe_sort]; exact @Nontrivial.to_nonempty _ hB'
#align is_preprimitive_of_prime isPreprimitive_of_prime

/-- The target of an equivariant map of large image is preprimitive if the source is -/
theorem isPreprimitive_of_large_image [Fintype β] [htβ : IsPretransitive N β] {φ : M → N}
    {f : α →ₑ[φ] β} (hM : IsPreprimitive M α)
    (hf' : Fintype.card β < 2 * Fintype.card (Set.range f)) : IsPreprimitive N β :=
  by
  apply IsPreprimitive.mk
  intro B hB
  cases' subsingleton_or_nontrivial B with hB hB_nt
  apply Or.intro_left; rwa [Set.subsingleton_coe] at hB 
  unfold is_trivial_block; rw [or_iff_not_imp_right]
  intro hB_ne_top
  have hB_ne : Nonempty ↥B := @Nontrivial.to_nonempty _ hB_nt
  have hB_ne' : 0 < Fintype.card B := fintype.card_pos_iff.mpr hB_ne
  rw [Set.nonempty_coe_sort] at hB_ne 
  -- We reduce to proving fintype.card ↥B < 2
  rw [← Set.subsingleton_coe, ← Fintype.card_le_one_iff_subsingleton, ← Nat.lt_succ_iff]
  -- We reduce to proving that
  -- fintype.card (set.range f) ≤ fintype.card (set.range (λ g, g • B))
  apply lt_of_mul_lt_mul_right
  apply lt_of_le_of_lt _ hf'
  simp only [← Nat.card_eq_fintype_card, ← nat_card_block_mul_card_orbit_eq hB hB_ne]
  apply Nat.mul_le_mul_left _
  -- We reduce to proving that
  -- fintype.card (set.range f ∩ g • B)) ≤ 1 for every g
  simp only [Nat.card_eq_fintype_card]
  simp only [← Set.toFinset_card]
  rw [Setoid.IsPartition.card_set_eq_sum_parts (Set.range f)
      (is_block_system.of_block hB hB_ne).left]
  rw [Finset.card_eq_sum_ones]
  refine' Finset.sum_le_sum _
  intro t ht
  simp only [Set.mem_toFinset, Set.mem_range] at ht 
  obtain ⟨g, ht⟩ := ht
  rw [← ht]
  rw [Set.toFinset_card]
  -- It suffices to prove that the preimage is subsingleton
  rw [Fintype.card_le_one_iff_subsingleton, Set.inter_comm, ← Set.image_preimage_eq_inter_range,
    Set.subsingleton_coe]
  apply Set.Subsingleton.image
  -- Since the action of M on α is primitive, it suffices to prove that
  -- the preimage is a block which is not ⊤
  apply Or.resolve_right (hM.has_trivial_blocks (is_block_preimage f (is_block_of_block g hB)))
  intro h
  have h' : ⊤ ⊆ f ⁻¹' (g • B) := subset_of_eq h.symm
  rw [Set.top_eq_univ, ← Set.image_subset_iff, Set.image_univ] at h' 
  -- We will prove that B is large, which will contradict the assumption that it is not ⊤
  apply hB_ne_top
  apply is_top_of_large_block hB
  -- It remains to show that fintype.card β < 2 * fintype.card B
  simp only [Nat.card_eq_fintype_card]
  apply lt_of_lt_of_le hf'
  simp only [mul_le_mul_left, Nat.succ_pos']
  rw [← smul_set_card_eq g B]
  -- This last step is disgusting :
  -- the types are identical, but not the proofs that they are finite
  refine' le_trans _ (le_trans (Set.card_le_of_subset h') _)
  apply le_of_eq; rfl
  apply le_of_eq; rfl
  exact zero_le (Fintype.card ↥(Set.range ⇑f))
#align is_preprimitive_of_large_image isPreprimitive_of_large_image

/-- Theorem of Rudio (Wielandt, 1964, Th. 8.1) -/
theorem rudio (hpGX : IsPreprimitive M α) (A : Set α) (hfA : A.Finite) (hA : A.Nonempty)
    (hA' : A ≠ ⊤) (a b : α) (h : a ≠ b) : ∃ g : M, a ∈ g • A ∧ b ∉ g • A :=
  by
  let B := ⋂ (g : M) (ha : a ∈ g • A), g • A
  suffices b ∉ B by
    rw [Set.mem_iInter] at this 
    simpa only [Set.mem_iInter, not_forall, exists_prop] using this
  suffices B = {a} by rw [this]; rw [Set.mem_singleton_iff]; exact Ne.symm h
  have ha : a ∈ B := by rw [Set.mem_iInter]; intro g; simp only [Set.mem_iInter, imp_self]
  -- B is a block hence is a trivial block
  cases' hpGX.has_trivial_blocks (is_block.of_subset a A hfA) with hyp hyp
  · -- B.subsingleton
    apply Set.Subsingleton.eq_singleton_of_mem hyp
    rw [Set.mem_iInter]; intro g; simp only [Set.mem_iInter, imp_self]
  · -- B = ⊤ : contradiction
    change B = ⊤ at hyp 
    exfalso; apply hA'
    suffices ∃ g : M, a ∈ g • A by
      obtain ⟨g, hg⟩ := this
      have : B ≤ g • A := by rw [Set.le_eq_subset]; exact Set.biInter_subset_of_mem hg
      rw [hyp, top_le_iff, ← eq_inv_smul_iff] at this 
      rw [this, Set.top_eq_univ, Set.smul_set_univ]
    -- ∃ (g : M), a ∈ g • A
    obtain ⟨x, hx⟩ := hA
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M x a
    use g; use x; exact ⟨hx, hg⟩
#align rudio rudio

end Finite

section Iwasawa

open scoped BigOperators Pointwise

variable {M : Type _} [Group M] {α : Type _} [MulAction M α]

variable (M α)

/-- The structure underlying the Iwasawa criterion -/
structure IwasawaStructure where
  t : α → Subgroup M
  is_comm : ∀ x : α, (T x).IsCommutative
  IsConj : ∀ g : M, ∀ x : α, T (g • x) = MulAut.conj g • T x
  is_generator : iSup T = ⊤
#align iwasawa_structure IwasawaStructure

/- Variante de la structure d'Iwasawa :
* M action primitive sur α
* a : α
* A := T a, sous-groupe commutatif de G
* g • a = a → mul_aut.conj g A = A
* stabilizer M a ≤ normalizer A
* subgroup.normal_closure A = ⊤

Ou encore : (?)
* A : subgroup M, commutative
* normalizer A maximal
* subgroup.normal_closure A = ⊤

-/
variable {M α}

/-- The Iwasawa criterion : If a quasiprimitive action of a group G on X
has an Iwasawa structure, then any normal subgroup that acts nontrivially
contains the group of commutators. -/
theorem commutator_le_iwasawa (is_qprim : IsQuasipreprimitive M α) (IwaS : IwasawaStructure M α)
    {N : Subgroup M} (nN : N.Normal) (hNX : MulAction.fixedPoints N α ≠ ⊤) : commutator M ≤ N :=
  by
  haveI is_transN := is_qprim.pretransitive_of_normal nN hNX
  haveI ntα : Nontrivial α := isnontrivial_of_nontrivial_action hNX
  obtain a : α := nontrivial.to_nonempty.some
  refine' contains_commutators_of N nN (IwaS.T a) _ (IwaS.is_comm a)
  -- by contains_commutators_of, it suffices to prove that N ⊔ IwaS.T x = ⊤
  rw [eq_top_iff, ← IwaS.is_generator, iSup_le_iff]
  intro x
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq N a x
  rw [Subgroup.smul_def, IwaS.is_conj g a]
  rintro _ ⟨k, hk, rfl⟩
  have hg' : ↑g ∈ N ⊔ IwaS.T a := Subgroup.mem_sup_left (Subtype.mem g)
  have hk' : k ∈ N ⊔ IwaS.T a := Subgroup.mem_sup_right hk
  exact (N ⊔ IwaS.T a).mul_mem ((N ⊔ IwaS.T a).mul_mem hg' hk') ((N ⊔ IwaS.T a).inv_mem hg')
#align commutator_le_iwasawa commutator_le_iwasawa

/-- The Iwasawa criterion for simplicity -/
theorem is_simple_iwasawa (is_nontrivial : Nontrivial M) (is_perfect : commutator M = ⊤)
    (is_qprim : IsQuasipreprimitive M α) (is_faithful : FaithfulSMul M α)
    (IwaS : IwasawaStructure M α) : IsSimpleGroup M :=
  by
  refine' ⟨is_nontrivial.exists_pair_ne, fun N nN => _⟩
  cases or_iff_not_imp_left.mpr (commutator_le_iwasawa is_qprim IwaS nN)
  · refine' Or.inl (N.eq_bot_iff_forall.mpr fun n hn => _)
    apply is_faithful.eq_of_smul_eq_smul
    intro x
    rw [one_smul]
    exact set.eq_univ_iff_forall.mp h x ⟨n, hn⟩
  · exact Or.inr (top_le_iff.mp (le_trans (ge_of_eq is_perfect) h))
#align is_simple_iwasawa is_simple_iwasawa

end Iwasawa

#lint


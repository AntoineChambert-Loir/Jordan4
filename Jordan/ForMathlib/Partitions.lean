/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.partitions
-/
import Mathbin.Data.Setoid.Partition
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Data.Finite.Card

/-!

# Four lemmas on partitions

We provide four lemmas regarding `setoid.is_partition`

* `setoid.is_partition_on` proves that a partition of a type induces
a partition on each of its sets

The three other lemmas show that given a partition of a fintype, its cardinality
is the sum of the cardinalities of its parts, in three different contexts:

* `partition.card_of_partition` : for a fintype
* `partition.card_of_partition'` : for an ambient fintype, with a stronger hypothesis
that the partition is a finset of finsets
* `setoid.is_partition.card_set_eq_sum_parts` : for any finset of a type

## TODO

I am not sure that `partition.card_of_partition'` is useful per se,
but I use it to prove the other two.

-/


variable {α : Type _}

open scoped BigOperators

/-- A partion of a type induces partitions on subsets -/
theorem Setoid.isPartition_on {α : Type _} {P : Set (Set α)} (hP : Setoid.IsPartition P)
    (s : Set α) :
    Setoid.IsPartition {u : Set ↥s | ∃ t : Set α, t ∈ P ∧ coe ⁻¹' t = u ∧ t ∩ s ≠ ∅} :=
  by
  constructor
  · intro h
    obtain ⟨t, htP, ht, hts⟩ := set.mem_set_of_eq.mp h
    apply hts
    rw [← Subtype.image_preimage_coe, ht, Set.image_empty]
  · intro a
    obtain ⟨t, ht⟩ := hP.right ↑a
    simp only [exists_unique_iff_exists, exists_prop, and_imp] at ht 
    use coe ⁻¹' t
    constructor
    · simp only [Ne.def, Set.mem_setOf_eq, Set.mem_preimage, exists_unique_iff_exists, exists_prop]
      use t
      apply And.intro ht.left.left
      apply And.intro rfl
      intro h; rw [← Set.mem_empty_iff_false (a : α)]; rw [← h]
      exact Set.mem_inter ht.left.right (Subtype.mem a)
      exact ht.left.right
    · simp only [Ne.def, Set.mem_setOf_eq, exists_unique_iff_exists, exists_prop, and_imp,
        forall_exists_index]
      intro y x hxP hxy hxs hay; rw [← hxy]
      rw [Subtype.preimage_coe_eq_preimage_coe_iff]
      refine' congr_arg₂ _ _ rfl
      apply ht.right x hxP; rw [← Set.mem_preimage, hxy]; exact hay
#align setoid.is_partition_on Setoid.isPartition_on

open scoped Classical

/-- The cardinal of ambient fintype equals
  the sum of cardinals of the parts of a partition (finset style)-/
theorem Partition.card_of_partition' [Fintype α] {c : Finset (Finset α)}
    (hc : Setoid.IsPartition ({s : Set α | ∃ t : Finset α, s.toFinset = t ∧ t ∈ c} : Set (Set α))) :
    ∑ s : Finset α in c, s.card = Fintype.card α :=
  by
  rw [← mul_one (Fintype.card α), ← Finset.sum_card]
  intro a
  rw [Finset.card_eq_one]
  obtain ⟨s, hs, hs'⟩ := hc.right a
  simp only [exists_unique_iff_exists, exists_prop, and_imp, exists_eq_left', Set.mem_setOf_eq] at
    hs hs' 
  have hs'2 : ∀ z : Finset α, z ∈ c → a ∈ z → z = s.to_finset :=
    by
    intro z hz ha
    rw [← Finset.coe_inj, Set.coe_toFinset]
    refine' hs' z _ (finset.mem_coe.mpr ha)
    -- To get the correct type automatically and perform the rewrite
    suffices ∀ {u v : Finset α}, v ∈ c → u = v → u ∈ c
      by
      refine' this hz _
      rw [← Finset.coe_inj, Set.coe_toFinset]
    · intro u v hu huv; rw [huv]; exact hu
  use s.to_finset
  ext t
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨ht, ha⟩
    exact hs'2 t ht ha
  · intro ht
    rw [← ht] at hs ; apply And.intro hs.left
    rw [ht]; simp only [Set.mem_toFinset]; exact hs.right
#align partition.card_of_partition' Partition.card_of_partition'

/-- The cardinal of ambient fintype equals
  the sum of cardinals of the parts of a partition (set style)-/
theorem Partition.card_of_partition [Fintype α] {c : Set (Set α)} (hc : Setoid.IsPartition c) :
    ∑ s : Set α in c.toFinset, s.toFinset.card = Fintype.card α :=
  by
  let c' : Finset (Finset α) := {s : Finset α | (s : Set α) ∈ c}.toFinset
  have hcc' : c = {s : Set α | ∃ t : Finset α, s.toFinset = t ∧ t ∈ c'} := by
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, exists_eq_left', Set.coe_toFinset,
      Set.setOf_mem_eq]
  rw [hcc'] at hc 
  rw [← Partition.card_of_partition' hc]
  have hi : ∀ (a : Set α) (ha : a ∈ c.to_finset), a.toFinset ∈ c' :=
    by
    intro a ha
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, Set.coe_toFinset]
    simpa only [Set.mem_toFinset] using ha
  have hj : ∀ (a : Finset α) (ha : a ∈ c'), (a : Set α) ∈ c.to_finset := by intro a ha;
    simpa only [Set.mem_toFinset] using ha
  rw [Finset.sum_bij' _ hi _ _ hj]
  · intro a ha; simp only [Set.coe_toFinset]
  · intro a ha; rw [← Finset.coe_inj, Set.coe_toFinset]
  · intro a ha; rfl
#align partition.card_of_partition Partition.card_of_partition

/-- Given a partition of the ambient finite type,
the cardinal of a set is the sum of the cardinalities of its trace on the parts of the partition -/
theorem Setoid.IsPartition.card_set_eq_sum_parts {α : Type _} [Fintype α] (s : Set α)
    {P : Set (Set α)} (hP : Setoid.IsPartition P) :
    s.toFinset.card = Finset.sum P.toFinset fun t : Set α => (s ∩ t).toFinset.card :=
  by
  rw [← Finset.card_biUnion]
  apply congr_arg
  · rw [← Finset.coe_inj]; simp only [Set.coe_toFinset, Finset.coe_biUnion]
    rw [Set.biUnion_eq_iUnion, ← Set.inter_iUnion, ← Set.sUnion_eq_iUnion]
    rw [Setoid.IsPartition.sUnion_eq_univ hP]
    exact (Set.inter_univ s).symm
  · intro t ht u hu htu
    simp only [Set.mem_toFinset] at ht hu 
    simp only [← Finset.disjoint_coe, Set.coe_toFinset]
    exact
      Set.disjoint_of_subset (Set.inter_subset_right s t) (Set.inter_subset_right s u)
        (Setoid.IsPartition.pairwiseDisjoint hP ht hu htu)
#align setoid.is_partition.card_set_eq_sum_parts Setoid.IsPartition.card_set_eq_sum_parts

/-- The cardinality of a finite type is
  the sum of the cardinalities of the parts of any partition -/
theorem Setoid.IsPartition.card_eq_sum_parts {α : Type _} [Fintype α] {P : Set (Set α)}
    (hP : Setoid.IsPartition P) :
    Fintype.card α = Finset.sum P.toFinset fun t : Set α => t.toFinset.card :=
  by
  change finset.univ.card = _
  have : ∀ (t : Set α) (ht : t ∈ P.to_finset), t.to_finset.card = (Set.univ ∩ t).toFinset.card :=
    by
    intro t ht; apply congr_arg
    rw [Set.toFinset_inj]; exact (Set.univ_inter t).symm
  simp_rw [Finset.sum_congr rfl this]
  simpa only [Set.toFinset_card, Fintype.card_ofFinset, Finset.filter_congr_decidable,
    Set.toFinset_univ] using Setoid.IsPartition.card_set_eq_sum_parts Set.univ hP
#align setoid.is_partition.card_eq_sum_parts Setoid.IsPartition.card_eq_sum_parts

/-- The cardinality of a finset is the sum of the cardinalities
of the traces of any partition of the ambient type  -/
theorem Setoid.IsPartition.card_finset_eq_sum_parts {α : Type _} {P : Set (Set α)}
    (hP : Setoid.IsPartition P) {s : Finset α} :
    let P' := {u : Set ↥s | ∃ t : Set α, t ∈ P ∧ coe ⁻¹' t = u ∧ t ∩ s ≠ ∅}
    let hP' := Setoid.isPartition_on hP
    s.card = Finset.sum P'.toFinset fun t : Set ↥s => t.toFinset.card :=
  by
  -- let P' := { u : set ↥s | ∃ (t : set α), t ∈ P ∧ coe ⁻¹' t = u ∧ t ∩ s ≠ ∅ },
  -- let hP' := setoid.is_partition_on hP,
  /-   have fs : fintype ↥(↑s : set α) := finset_coe.fintype s,
    have fcs : fintype.card ↥s =  fintype.card ↥(s : set α) :=
    by simp only [fintype.card_coe, finset.coe_sort_coe, fintype.card_coe],
    have fcs' : fintype.card ↥(s : set α) = s.card :=
    by simp only [finset.coe_sort_coe, fintype.card_coe],
    -/
  have :=
    @Partition.card_of_partition _ (FinsetCoe.fintype s) _ (Setoid.isPartition_on hP (s : Set α))
  simp only [Finset.coe_sort_coe, Fintype.card_coe] at this 
  rw [← this]
  apply congr_arg₂
  · apply Finset.coe_injective
    simp only [Ne.def, Set.coe_toFinset]
    exact rfl
  · ext; apply congr_arg; rw [Set.toFinset_inj]
#align setoid.is_partition.card_finset_eq_sum_parts Setoid.IsPartition.card_finset_eq_sum_parts

/-
noncomputable def setoid.quotient_equiv {α β : Type*} {s : setoid α} (f : α → β)
  (hf : ∀ x y, s.rel x y ↔ f x = f y) (hf' : f.surjective) : quotient s ≃ β :=
begin
  refine equiv.of_bijective (λ q, q.lift_on' f (λ x y h, (hf x y).mp h)) _,
  split,
  -- injective
  intros x y,
  obtain ⟨a, rfl⟩:= quotient.exists_rep x,
  obtain ⟨b, rfl⟩:= quotient.exists_rep y,
  exact λ h, quotient.eq.mpr ((hf a b).mpr h),
  -- surjective
  exact (quotient.surjective_lift_on' (λ x y, (hf x y).mp)).mpr hf',
end

noncomputable def setoid.is_partition_equiv_quotient {α : Type*}
  {c : set (set α)} (hc : setoid.is_partition c) :
  quotient (setoid.mk_classes c hc.2) ≃ c :=
begin
  apply setoid.quotient_equiv (λ a, (⟨_, @setoid.eqv_class_mem _ c hc.2 a⟩ : c)),
  { intros x y,
    exact ⟨
      λ h,  subtype.ext ( set.ext ( λ z, ⟨λ h', setoid.trans' _ h' h, λ h', setoid.trans' _ h' (setoid.symm' _ h)⟩ )),
      λ hz,  (set.ext_iff.mp(subtype.ext_iff.mp hz) x).mp (setoid.refl' _ x), ⟩, },
  { -- surjective
    rintro ⟨u, hu⟩,
    have hu' : u.nonempty,
    { rw set.nonempty_iff_ne_empty,
      intro hu', apply hc.1,  rw ← hu', exact hu, },
    obtain ⟨a, ha⟩ := hu',
    use a,
    simp only [subtype.mk_eq_mk],
    rw setoid.eq_eqv_class_of_mem hc.2 hu ha, }
end

noncomputable def setoid.is_partition_equiv_quotient' {α : Type*}
  {c : set (set α)} (hc : setoid.is_partition c) :
  quotient (setoid.mk_classes c hc.2) ≃ c :=
begin
  -- Eric Wieser golfed this !
  let φ : quotient (setoid.mk_classes c hc.2) → c := λ q,  q.lift_on' (λ a, (⟨_, @setoid.eqv_class_mem _ c hc.2 a⟩ : c))
    (λ a b hab, subtype.ext $ set.ext $ λ x,
      ⟨λ h, setoid.trans' _ h hab, λ h, setoid.trans' _ h (setoid.symm' _ hab)⟩),
  apply equiv.of_bijective φ,

  let f : α → c := λ a, ⟨_, @setoid.eqv_class_mem _ c hc.2 a⟩,
  have hf : ∀ x y, f x = f y ↔ (setoid.mk_classes c hc.2).rel x y := λ x y, ⟨
    λ hz,  (set.ext_iff.mp(subtype.ext_iff.mp hz) x).mp (setoid.refl' _ x),
    λ h,  subtype.ext ( set.ext ( λ z, ⟨λ h', setoid.trans' _ h' h, λ h', setoid.trans' _ h' (setoid.symm' _ h)⟩ ))⟩,

/-
  have hf : ∀ x y, f x = f y ↔ (setoid.mk_classes c hc.2).rel x y,
  { intros x y,
--    simp only [f],
    simp only [subtype.mk_eq_mk, set.ext_iff, set.mem_set_of],
    split,
    intro hz,
    rw ← hz x, exact setoid.refl' _ _,
    intros h z,
    split,
    intro h', exact setoid.trans' _ h' h,
    intro h', exact setoid.trans' _ h' (setoid.symm' _ h), },
-/

/-
  let f : α → c := λ a, ⟨_, @setoid.eqv_class_mem _ c hc.2 a⟩,
  refine equiv.of_bijective (@quotient.lift _ _ (setoid.mk_classes c hc.2) f _) _,
  { -- well defined
    intros a b hab,
    change (setoid.mk_classes c hc.2).rel a b at hab,
    rw setoid.rel_iff_exists_classes at hab,
    rw setoid.classes_mk_classes at hab,
    obtain ⟨u, h, ha, hb⟩ := hab,
    let hc2 := hc.2,
    simp only [f, subtype.mk_eq_mk],
    rw ← setoid.eq_eqv_class_of_mem hc.2 h ha,
    rw ← setoid.eq_eqv_class_of_mem hc.2 h hb, }, -/

  split,
  { -- injective
    intros x y,
    obtain ⟨a, rfl⟩ := @quotient.exists_rep α (setoid.mk_classes c hc.2) x,
    obtain ⟨b, rfl⟩ := @quotient.exists_rep α (setoid.mk_classes c hc.2) y,
    simp only [quotient.lift_mk, φ, subtype.mk_eq_mk],
    intro hab,
    apply quotient.sound,
    change (setoid.mk_classes c hc.2).rel a b,
    rw setoid.rel_iff_exists_classes,
    use { x : α | (setoid.mk_classes c hc.2).rel x a},
    split,
    rw setoid.classes_mk_classes,
    apply setoid.eqv_class_mem,
    split,
    rw set.mem_set_of, apply setoid.refl' _ a,
    simp only [quotient.lift_on'_mk, subtype.mk_eq_mk] at hab,
    rw hab, rw set.mem_set_of, apply setoid.refl' _ b, },
  { -- surjective
    rw quotient.surjective_lift_on',
    rintro ⟨u, hu⟩,
    have hu' : u.nonempty,
    { rw set.nonempty_iff_ne_empty,
      intro hu', apply hc.1,  rw ← hu', exact hu, },
    obtain ⟨a, ha⟩ := hu',
    use a,
    simp only [subtype.mk_eq_mk],
    rw setoid.eq_eqv_class_of_mem hc.2 hu ha, }
end

-/

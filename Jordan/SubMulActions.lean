/-¨
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module sub_mul_actions
-/
-- ==> Mathlib.GroupTheory.GroupAction.SubMulAction.Invariant
import Jordan.EquivariantMap

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Tactic.Group

/-!
# Complements on sub_mul_actions
-/



open scoped Pointwise

/-!
# Sub_mul_actions on complements of invariant subsets

- We define sub_mul_action of an invariant subset in various contexts,
especially stabilizers and fixing subgroups : `sub_mul_action_of_compl`,
`sub_mul_action_of_stabilizer`, `sub_mul_action_of_fixing_subgroup`.

- We define equivariant maps that relate various of these sub_mul_actions
and permit to manipulate them in a relatively smooth way.
-/

open scoped Pointwise

open MulAction
section SubMulActions

namespace SubMulAction

section Complements

variable (M : Type _) [Group M] {α : Type _} [MulAction M α]

/-- SubMulAction on the complement of an invariant subset -/
instance : HasCompl (SubMulAction M α) where
  compl := fun s ↦ {
    carrier := sᶜ
    smul_mem' := fun g x ↦ by
      simp only [SetLike.mem_coe, Set.mem_compl_iff, SubMulAction.smul_mem_iff', imp_self] }

theorem Compl_def (s : SubMulAction M α) :
  sᶜ.carrier = (s : Set α)ᶜ :=
  rfl

/-- Action of stabilizer of a point on the complement -/
def ofStabilizer (a : α) : SubMulAction (stabilizer M a) α
    where
  carrier := {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not]
    rw [smul_eq_iff_eq_inv_smul]
    intro hgx
    apply symm
    rw [hgx, ← smul_eq_iff_eq_inv_smul]
    exact g.prop


theorem ofStabilizer_carrier (a : α) : (SubMulAction.ofStabilizer M a).carrier = {a}ᶜ :=
  rfl

theorem mem_ofStabilizer_iff (a : α) {x : α} : x ∈ SubMulAction.ofStabilizer M a ↔ x ≠ a :=
  Iff.rfl

theorem neq_of_mem_ofStabilizer (a : α) {x : (SubMulAction.ofStabilizer M a)} : ↑x ≠ a :=
  x.prop

/-
instance ofStabilizerLift (a : α) : HasLiftT (SubMulAction.ofStabilizer M a) α :=
  coeToLift
 -/


lemma add_card_ofStabilizer_eq (a : α) :
    1 + ENat.card (SubMulAction.ofStabilizer M a) = ENat.card α :=  by
  unfold ENat.card
  rw [← Cardinal.mk_sum_compl {a}, map_add, eq_comm]
  congr
  simp only [Cardinal.mk_fintype, Fintype.card_ofSubsingleton, Nat.cast_one, Cardinal.toENat_eq_one]

/-- The sub_mul_action of fixing_subgroup M s on the complement -/
def ofFixingSubgroup (s : Set α) : SubMulAction (fixingSubgroup M s) α
    where
  carrier := sᶜ
  smul_mem' := by
    rintro ⟨c, hc⟩ x
    rw [← Subgroup.inv_mem_iff] at hc
    simp only [Set.mem_compl_iff, not_imp_not]
    intro (hcx : c • x ∈ s)
    rw [← one_smul M x, ← inv_mul_cancel c, mul_smul]
    rw [(mem_fixingSubgroup_iff M).mp hc (c • x) hcx]
    exact hcx

instance (s : Set α) : SMul (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) :=
  inferInstance

instance (s : Set α) : MulAction (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) :=
  inferInstance

theorem ofFixingSubgroup_carrier {s : Set α} : (SubMulAction.ofFixingSubgroup M s).carrier = sᶜ :=
  rfl

theorem mem_ofFixingSubgroup_iff {s : Set α} {x : α} :
    x ∈ SubMulAction.ofFixingSubgroup M s ↔ x ∉ s :=
  Iff.rfl

theorem not_mem_of_mem_ofFixingSubgroup {s : Set α}
  (x : SubMulAction.ofFixingSubgroup M s) : ↑x ∉ s := x.prop

example (s : Set α) : SMul { x // x ∈ fixingSubgroup M s }
    { x // x ∈ SubMulAction.ofFixingSubgroup M s } :=
  SetLike.smul (ofFixingSubgroup M s)

example (s : Set α) : MulAction (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) :=
  mulAction (ofFixingSubgroup M s)

end Complements

end SubMulAction

section fixingSubgroup

variable (M : Type _) [Group M] {α : Type _} [MulAction M α]

example (a : α) (s : Set (SubMulAction.ofStabilizer M a)) : Set α :=
  (fun x => x.val) '' s

theorem fixingSubgroup_of_insert (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    fixingSubgroup M (insert a ((fun x => x.val) '' s : Set α)) =
      (fixingSubgroup (↥(stabilizer M a)) s).map (Subgroup.subtype (stabilizer M a)) := by
  ext m
  constructor
  · intro hm
    rw [mem_fixingSubgroup_iff] at hm
    rw [Subgroup.mem_map]
    suffices hm' : m ∈ stabilizer M a by
      use ⟨m, hm'⟩
      simp only [Subgroup.coeSubtype, and_true]
      rw [mem_fixingSubgroup_iff]
      rintro ⟨y, hy⟩ hy'
      simp only [SetLike.mk_smul_mk, Subtype.mk.injEq]
      change m • y = y
      apply hm
      apply Set.mem_insert_of_mem
      use ⟨y, hy⟩
    simp only [mem_stabilizer_iff]
    apply hm
    apply Set.mem_insert a
  · rintro ⟨⟨n, hn'⟩, hn, rfl⟩
    simp only [Subgroup.coeSubtype, SetLike.mem_coe, mem_fixingSubgroup_iff] at hn ⊢
    intro x hx
    rw [Set.mem_insert_iff] at hx
    cases' hx with hx hx
    · -- x = a
      simpa [hx] using hn'
    · -- x ∈ s
      simp only [Set.mem_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      conv_rhs => rw [← hn y hy]
      rfl

end fixingSubgroup

section EquivariantMap

variable (M : Type _) [Group M] {α : Type _} [MulAction M α]

/- /-- The equivariant map from the sub_mul_action_of stabilizer into the ambient type -/
def subMulActionOfStabilizerInclusion (a : α) :
    SubMulAction.ofStabilizer M a →[stabilizer M a] α where
  toFun x := ↑x
  map_smul' g x := rfl
-/

/-
def of_fixing_subgroup.inclusion (s : set α) :
  (sub_mul_action.of_fixing_subgroup M s) →[fixing_subgroup M s] α := {
to_fun := λ x, ↑x,
map_smul' := λ g x, rfl }
 -/

variable (α)

/-- The identity map of the sub_mul_action of the fixing_subgroup
of the empty set into the ambient set, as an equivariant map -/
def SubMulAction.ofFixingSubgroupEmpty_equivariantMap :
    let φ := (fixingSubgroup M (∅ : Set α)).subtype
    SubMulAction.ofFixingSubgroup M (∅ : Set α) →ₑ[φ] α
    where
  toFun x := x
  map_smul' _ _ := rfl

theorem SubMulAction.ofFixingSubgroupEmpty_equivariantMap_bijective :
    Function.Bijective (SubMulAction.ofFixingSubgroupEmpty_equivariantMap M α) :=
  by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    exact hxy
  · intro x
    use ⟨x, (SubMulAction.mem_ofFixingSubgroup_iff M).mp (Set.not_mem_empty x)⟩
    rfl

theorem SubMulAction.of_fixingSubgroupEmpty_mapScalars_surjective :
    Function.Surjective (fixingSubgroup M (∅ : Set α)).subtype := by
  intro g
  suffices g ∈ fixingSubgroup M (∅ : Set α) by
    exact ⟨⟨g, this⟩, rfl⟩
  rw [mem_fixingSubgroup_iff]
  simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]

variable {α}

instance (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    SMul (fixingSubgroup (stabilizer M a) s)
      (SubMulAction.ofFixingSubgroup (stabilizer M a) s) :=
  SetLike.smul (SubMulAction.ofFixingSubgroup (stabilizer M a) s)

instance (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    MulAction (fixingSubgroup (stabilizer M a) s)
      (SubMulAction.ofFixingSubgroup (stabilizer M a) s) :=
  SubMulAction.mulAction (SubMulAction.ofFixingSubgroup (stabilizer M a) s)

instance  (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    SMul (fixingSubgroup M (insert a (Subtype.val '' s)))
      (SubMulAction.ofFixingSubgroup M (insert a (Subtype.val '' s))) :=
  SetLike.smul (SubMulAction.ofFixingSubgroup M (insert a (Subtype.val '' s)))

instance  (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    MulAction (fixingSubgroup M (insert a (Subtype.val '' s)))
      (SubMulAction.ofFixingSubgroup M (insert a (Subtype.val '' s))) :=
  SubMulAction.mulAction (SubMulAction.ofFixingSubgroup M (insert a (Subtype.val '' s)))

/- def φ (m :
    fixingSubgroup M (insert a (Subtype.val '' s))) : fixingSubgroup (stabilizer M a) s :=
    ⟨⟨(m : M), by
          apply (mem_fixingSubgroup_iff M).mp m.prop
          apply Set.mem_insert⟩,
      fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine (mem_fixingSubgroup_iff M).mp m.prop _ _
        apply Set.mem_insert_of_mem
        use ⟨x, (SubMulAction.mem_ofStabilizer_iff  M a).mp x.prop⟩⟩ -/

/-- The identity map of fixing subgroup of stabilizer
into the fixing subgroup of the extended set, as an equivariant map -/
def SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer
    (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    let φ : fixingSubgroup M (insert a (Subtype.val '' s)) →
      fixingSubgroup (stabilizer M a) s := fun m ↦
      ⟨⟨(m : M), by
          apply (mem_fixingSubgroup_iff M).mp m.prop
          apply Set.mem_insert⟩,
      fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine (mem_fixingSubgroup_iff M).mp m.prop _ ?_
        apply Set.mem_insert_of_mem
        use ⟨x, (SubMulAction.mem_ofStabilizer_iff  M a).mp x.prop⟩⟩
    SubMulAction.ofFixingSubgroup M (insert a (Subtype.val '' s)) →ₑ[φ]
      (SubMulAction.ofFixingSubgroup (stabilizer M a) s) := {
  toFun := fun x ↦ ⟨⟨(x : α), by
        rintro (h : (x : α) = a)
        apply (SubMulAction.mem_ofFixingSubgroup_iff M).mp x.prop
        rw [h]; apply Set.mem_insert⟩,
      fun h =>
        (SubMulAction.mem_ofFixingSubgroup_iff M).mp x.prop <|
          Set.mem_insert_of_mem _ ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩⟩
  map_smul' := fun _ _ ↦ rfl }

theorem SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer_coe
    {x : α} (hx : x ∈ ofFixingSubgroup M (insert a (Subtype.val '' s))) :
    ↑((SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer M a s) ⟨x, hx⟩) = x := by
  rfl

theorem SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective
    (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    Function.Bijective
      (SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer M a s) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp only [Subtype.mk_eq_mk]
    rw [← SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer_coe M hx]
    rw [← SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer_coe M hy]
    rw [h]
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    refine ⟨⟨x, ?_⟩, rfl⟩
    -- ⊢ x ∈ sub_mul_action_of_fixing_subgroup M (insert a (coe '' s))
    rw [SubMulAction.mem_ofFixingSubgroup_iff]
    intro h; cases Set.mem_insert_iff.mp h with
    | inl h' => rw [SubMulAction.mem_ofStabilizer_iff] at hx1 ; exact hx1 h'
    | inr h' =>
      rw [SubMulAction.mem_ofFixingSubgroup_iff] at hx2
      apply hx2
      obtain ⟨x1, hx1', rfl⟩ := h'
      simp only [SetLike.eta]
      exact hx1'

theorem SubMulAction.scalarMap_ofFixingSubgroupOfStabilizer_bijective
    (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    Function.Bijective (SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer M a s).toMap := by
  constructor
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ hmn
    rw [← SetLike.coe_eq_coe, ← SetLike.coe_eq_coe] at hmn
    simp only [Subtype.mk_eq_mk]
    exact hmn
  · rintro ⟨⟨m, hm⟩, hm'⟩
    suffices m ∈ fixingSubgroup M (insert a (Subtype.val '' s)) by
      use ⟨m, this⟩
      rfl
    rw [mem_fixingSubgroup_iff]
    intro x hx
    cases' Set.mem_insert_iff.mp hx with hx hx
    ·-- x = a
      rw [hx]
      exact mem_stabilizer_iff.mp hm
    · -- x ∈ coe '' s
      obtain ⟨y, hy, rfl⟩ := (Set.mem_image _ _ _).mp hx
      rw [mem_fixingSubgroup_iff] at hm'
      let hz := hm' y hy
      rw [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower] at hz
      exact hz

/-- If the fixing_subgroup of `s` is `G`, then the fixing_subgroup of `g • x` is `gGg⁻¹`. -/
theorem fixingSubgroup_smul_eq_fixingSubgroup_map_conj (g : M) (s : Set α) :
    fixingSubgroup M (g • s) = (fixingSubgroup M s).map (MulAut.conj g).toMonoidHom :=
  by
  ext h
  constructor
  · intro hh
    use (MulAut.conj g⁻¹) h
    simp
    constructor
    rintro ⟨x, hx⟩
    simp only [Subtype.coe_mk, ← smul_smul]
    rw [inv_smul_eq_iff]
    simpa only [Subtype.coe_mk] using hh ⟨_, Set.smul_mem_smul_set hx⟩
    group
  · rintro ⟨k, hk, rfl⟩
    rintro ⟨x, hx⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subtype.coe_mk, ← smul_smul]
    rw [smul_eq_iff_eq_inv_smul]
    exact hk ⟨_, Set.mem_smul_set_iff_inv_smul_mem.mp hx⟩

/-- Conjugation induces an equivariant map between the sub_mul_action of
the fixing subgroup of a subset and that of a translate -/
def SubMulAction.conjMap_ofFixingSubgroup {s t : Set α} {g : M} (hst : g • s = t) :
    let φ : fixingSubgroup M s → fixingSubgroup M t := fun ⟨m, hm⟩ =>
      ⟨(MulAut.conj g) m, by
        rw [← hst]
        rw [fixingSubgroup_smul_eq_fixingSubgroup_map_conj]
        use m; apply And.intro hm; rfl⟩
    SubMulAction.ofFixingSubgroup M s →ₑ[φ] SubMulAction.ofFixingSubgroup M t
    where
  toFun := fun ⟨x, hx⟩ =>
    ⟨g • x, by
      intro hgxt; apply hx
      rw [← hst] at hgxt
      exact Set.smul_mem_smul_set_iff.mp hgxt⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe]
    change g • m • x = MulAut.conj g m • g • x
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul]

theorem SubMulAction.conjMap_ofFixingSubgroup_bijective {s t : Set α} {g : M} (hst : g • s = t) :
    Function.Bijective (SubMulAction.conjMap_ofFixingSubgroup M hst) :=
  by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    rw [← SetLike.coe_eq_coe] at hxy
    change g • x = g • y at hxy
    apply (MulAction.injective g) hxy
  · rintro ⟨x, hx⟩
    have hst' : g⁻¹ • t = s := by
      apply symm; rw [← inv_smul_eq_iff]; rw [inv_inv]
      exact hst
    use (SubMulAction.conjMap_ofFixingSubgroup M hst') ⟨x, hx⟩
    rw [← SetLike.coe_eq_coe]
    change g • g⁻¹ • x = x
    rw [← mul_smul, mul_inv_cancel, one_smul]

/-- Conjugation induces an equivariant map between the sub_mul_action of
the stabilizer of a pint and that of its translate -/
def SubMulAction.ofStabilizer.conjMap {a b : α} {g : M} (hab : g • a = b) :
    let φ : stabilizer M a → stabilizer M b := fun ⟨m, hm⟩ =>
      ⟨(MulAut.conj g) m, by
        rw [← hab]; rw [stabilizer_smul_eq_stabilizer_map_conj]
        use m; apply And.intro hm; rfl⟩
    SubMulAction.ofStabilizer M a →ₑ[φ] SubMulAction.ofStabilizer M b
    where
  toFun := fun ⟨x, hx⟩ =>
    ⟨g • x, by
      intro hy
      simp only [Set.mem_singleton_iff] at hy
      rw [← hab] at hy
      apply hx
      simp only [Set.mem_singleton_iff]
      exact MulAction.injective g hy⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe]
    simp only [SubMulAction.val_smul_of_tower]
    change g • m • x = MulAut.conj g m • g • x
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul]

theorem SubMulAction.ofStabilizer.conjMap_bijective {a b : α} {g : M} (hab : g • a = b) :
    Function.Bijective (SubMulAction.ofStabilizer.conjMap M hab) :=
  by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    rw [← SetLike.coe_eq_coe] at hxy
    change g • x = g • y at hxy
    apply (MulAction.injective g) hxy
  · rintro ⟨x, hx⟩
    use (SubMulAction.ofStabilizer.conjMap M (inv_smul_eq_iff.mpr hab.symm)) ⟨x, hx⟩
    rw [← SetLike.coe_eq_coe]
    change g • g⁻¹ • x = x
    simp only [smul_inv_smul]


/- def ψ (s t : Set α) (m : fixingSubgroup M (s ∪ t)) :
    fixingSubgroup (fixingSubgroup M s)
      (Subtype.val ⁻¹' t : Set (SubMulAction.ofFixingSubgroup M s)) :=
  ⟨⟨m, by
        let hm := m.prop
        simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
        exact hm.left⟩, by
    let hm := m.prop
    simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
    rintro ⟨⟨x, hx⟩, hx'⟩
    simp only [Set.mem_preimage] at hx'
    simp only [← SetLike.coe_eq_coe, Subtype.coe_mk, SubMulAction.val_smul_of_tower]
    exact hm.right ⟨x, hx'⟩⟩ -/

instance (s t : Set α) :
    SMul (fixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (SubMulAction.ofFixingSubgroup M s)))
      (SubMulAction.ofFixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t :
        Set (SubMulAction.ofFixingSubgroup M s))) :=
  SetLike.smul (SubMulAction.ofFixingSubgroup { x // x ∈ fixingSubgroup M s } (Subtype.val ⁻¹' t))

instance (s t : Set α) :
    MulAction (fixingSubgroup (fixingSubgroup M s)
        (Subtype.val ⁻¹' t : Set (SubMulAction.ofFixingSubgroup M s)))
      (SubMulAction.ofFixingSubgroup (fixingSubgroup M s)
        (Subtype.val ⁻¹' t : Set (SubMulAction.ofFixingSubgroup M s))) :=
  SubMulAction.mulAction
    (SubMulAction.ofFixingSubgroup (fixingSubgroup M s)
      (Subtype.val ⁻¹' t : Set (SubMulAction.ofFixingSubgroup M s)))

/-- The identity between the iterated sub_mul_action
  of the fixing_subgroups and the sub_mul_action of the fixing_subgroup
  of the union, as an equivariant map -/
def SubMulAction.map_ofFixingSubgroupUnion (s t : Set α) :
    let ψ : fixingSubgroup M (s ∪ t) →
      fixingSubgroup (fixingSubgroup M s)
        (Subtype.val ⁻¹' t : Set (SubMulAction.ofFixingSubgroup M s)) :=
      fun m ↦ ⟨⟨m, by
        let hm := m.prop
        simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
        exact hm.left⟩, by
      let hm := m.prop
      simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp only [← SetLike.coe_eq_coe, Subtype.coe_mk, SubMulAction.val_smul_of_tower]
      exact hm.right ⟨x, hx'⟩⟩
    SubMulAction.ofFixingSubgroup M (s ∪ t) →ₑ[ψ]
      SubMulAction.ofFixingSubgroup (fixingSubgroup M s)
        (Subtype.val ⁻¹' t : Set (SubMulAction.ofFixingSubgroup M s)) where
  toFun x :=
    ⟨⟨x, fun hx => x.prop (Set.mem_union_left t hx)⟩,
        fun hx => x.prop (by
          apply Set.mem_union_right s
          simpa only [Set.mem_preimage, Subtype.coe_mk] using hx)⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe, ← SetLike.coe_eq_coe]
    rfl

theorem SubMulAction.map_ofFixingSubgroupUnion_def (s t : Set α)
    (x : SubMulAction.ofFixingSubgroup M (s ∪ t)) :
    ((SubMulAction.map_ofFixingSubgroupUnion M s t) x : α) = x :=
  rfl

theorem SubMulAction.OfFixingSubgroupUnion.map_bijective (s t : Set α) :
    Function.Bijective (SubMulAction.map_ofFixingSubgroupUnion M s t) :=
  by
  constructor
  · intro a b h
    simp only [← SetLike.coe_eq_coe] at h ⊢
    exact h
  · rintro ⟨⟨a, ha⟩, ha'⟩
    suffices a ∈ ofFixingSubgroup M (s ∪ t) by
      exact ⟨⟨a, this⟩,  rfl⟩
    intro hy
    cases' (Set.mem_union a s t).mp hy with h h
    · exact ha h
    · apply ha'
      simp only [Set.mem_preimage]
      exact h

/-- The equivariant map on sub_mul_action.of_fixing_subgroup given a set inclusion -/
def SubMulAction.ofFixingSubgroup.mapOfInclusion {s t : Set α} (hst : t ⊆ s) :
    let φ : fixingSubgroup M s → fixingSubgroup M t := fun ⟨m, hm⟩ =>
      ⟨m, by
        apply fixingSubgroup_antitone
        exact hst; exact hm⟩
    SubMulAction.ofFixingSubgroup M s →ₑ[φ] SubMulAction.ofFixingSubgroup M t
    where
  toFun := fun y => ⟨y.val, fun h => y.prop (hst h)⟩
   -- ⟨x, hx⟩ => ⟨x, fun h => hx (hst h)⟩
  map_smul' := fun _ _ => rfl

lemma SubMulAction.ofFixingSubgroup.mapOfInclusion_injective
    {s t : Set α} (hst : t ⊆ s) :
    Function.Injective (SubMulAction.ofFixingSubgroup.mapOfInclusion M hst) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [← SetLike.coe_eq_coe] at hxy ⊢
  exact hxy

/-- The equivariant map between sub_mul_action.of_stabilizer
  and .of_fixing_subgroup of the singleton -/
def SubMulAction.OfFixingSubgroupOfSingleton.map (a : α) :
    let φ : fixingSubgroup M ({a} : Set α) → stabilizer M a := fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    SubMulAction.ofFixingSubgroup M ({a} : Set α) →ₑ[φ] SubMulAction.ofStabilizer M a
    where
  toFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl

theorem SubMulAction.OfFixingSubgroupOfSingleton.map_bijective (a : α) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfSingleton.map M a) :=
  by
  constructor
  · intro _ _ hxy
    exact hxy
  · intro x
    use x
    rfl

/-- The identity between the sub_mul_action of fixing_subgroups
of equal sets, as an equivariant map -/
def SubMulAction.OfFixingSubgroupOfEq.map {s t : Set α} (hst : s = t) :
    let φ : fixingSubgroup M s → fixingSubgroup M t := fun ⟨m, hm⟩ => ⟨m, by rw [← hst]; exact hm⟩
    SubMulAction.ofFixingSubgroup M s →ₑ[φ] SubMulAction.ofFixingSubgroup M t
    where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [← hst]; exact hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl

theorem SubMulAction.OfFixingSubgroupOfEq.map_def {s t : Set α} (hst : s = t) :
    ∀ (x : α) (hx : x ∈ SubMulAction.ofFixingSubgroup M s),
      ((SubMulAction.OfFixingSubgroupOfEq.map M hst) ⟨x, hx⟩ : α) = x :=
  fun _ _ => rfl

theorem SubMulAction.OfFixingSubgroupOfEq.toMap_def
    {s t : Set α} (hst : s = t) (g : M) (hg : g ∈ fixingSubgroup M s) :
    g = (SubMulAction.OfFixingSubgroupOfEq.map M hst).toMap (⟨g, hg⟩ : fixingSubgroup M s) :=
  rfl

theorem SubMulAction.OfFixingSubgroupOfEq.map_bijective
    {s t : Set α} (hst : s = t) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfEq.map M hst) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rw [← SetLike.coe_eq_coe] at hxy ⊢
    simp only [SubMulAction.OfFixingSubgroupOfEq.map_def M hst] at hxy
    simp only
    rw [hxy]
  · rintro ⟨x, hxt⟩
    use ⟨x, ?_⟩
    rfl
    rw [hst]
    exact hxt

theorem SubMulAction.OfFixingSubgroupOfEq.toMap_bijective {s t : Set α} (hst : s = t) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfEq.map M hst).toMap := by
  constructor
  · rintro ⟨g, hg⟩ ⟨k, hk⟩ hgk
    rw [← SetLike.coe_eq_coe] at hgk ⊢
    simp only
    exact hgk
  · rintro ⟨k, hk⟩
    use ⟨k, ?_⟩
    rfl
    rw [hst]
    exact hk

end EquivariantMap

#lint

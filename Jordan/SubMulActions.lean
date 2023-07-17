/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module sub_mul_actions
-/
import Mathlib.Algebra.Hom.GroupAction
-- import Jordan.EquivariantMap

import Mathlib.Data.Finset.Pointwise
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
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

section Inclusion

variable {M N α : Type _} [SMul M α]

/-- The inclusion of a SubMulAction into the ambient set, as an equivariant map -/
def inclusion (s : SubMulAction M α) : s →[M] α
    where
-- The inclusion map of the inclusion of a SubMulAction 
  toFun := fun x => x.val
-- The commutation property
  map_smul' _ _ := rfl
#align sub_mul_action.inclusion SubMulAction.inclusion

theorem inclusion.toFun_eq_coe (s : SubMulAction M α) : 
  s.inclusion.toFun = fun x => x.val := rfl
#align sub_mul_action.inclusion.to_fun_eq_coe SubMulAction.inclusion.toFun_eq_coe

end Inclusion

section Complements

variable (M : Type _) [Group M] {α : Type _} [MulAction M α]

/-- Action on the complement of an invariant subset -/
def ofCompl (s : SubMulAction M α) : SubMulAction M α
    where
  carrier := sᶜ
  smul_mem' g x := by
    simp only [SetLike.mem_coe, Set.mem_compl_iff, SubMulAction.smul_mem_iff', imp_self]
#align sub_mul_action.of_compl SubMulAction.ofCompl

theorem ofCompl_def (s : SubMulAction M α) : (ofCompl M s).carrier = (s : Set α)ᶜ :=
  rfl
#align sub_mul_action.of_compl_def SubMulAction.ofCompl_def

/-- Action of stabilizer of a point on the complement -/
def ofStabilizer (a : α) : SubMulAction (stabilizer M a) α
    where
  carrier := {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not]
    rw [smul_eq_iff_eq_inv_smul]
    intro hgx; rw [hgx]
    apply symm; rw [← smul_eq_iff_eq_inv_smul]
    conv_rhs => rw [← mem_stabilizer_iff.mp (SetLike.coe_mem g)]
#align sub_mul_action.of_stabilizer SubMulAction.ofStabilizer

theorem ofStabilizer.def (a : α) : (SubMulAction.ofStabilizer M a).carrier = {a}ᶜ :=
  rfl
#align sub_mul_action.of_stabilizer.def SubMulAction.ofStabilizer.def

theorem ofStabilizer.mem_iff (a : α) {x : α} : x ∈ SubMulAction.ofStabilizer M a ↔ x ≠ a :=
  Iff.rfl
#align sub_mul_action.of_stabilizer.mem_iff SubMulAction.ofStabilizer.mem_iff

theorem ofStabilizer.neq (a : α) {x : ↥(SubMulAction.ofStabilizer M a)} : ↑x ≠ a :=
  x.prop
#align sub_mul_action.of_stabilizer.neq SubMulAction.ofStabilizer.neq

/- 
instance ofStabilizerLift (a : α) : HasLiftT (SubMulAction.ofStabilizer M a) α :=
  coeToLift
#align sub_mul_action.of_stabilizer_lift SubMulAction.ofStabilizerLift
 -/

/-- The sub_mul_action of fixing_subgroup M s on the complement -/
def ofFixingSubgroup (s : Set α) : SubMulAction (fixingSubgroup M s) α
    where
  carrier := sᶜ
  smul_mem' := by
    rintro ⟨c, hc⟩ x
    rw [← Subgroup.inv_mem_iff] at hc
    simp only [Set.mem_compl_iff, not_imp_not]
    intro (hcx : c • x ∈ s)
    rw [← one_smul M x, ← inv_mul_self c, mul_smul]
    rw [(mem_fixingSubgroup_iff M).mp hc (c • x) hcx]
    exact hcx
#align sub_mul_action.of_fixing_subgroup SubMulAction.ofFixingSubgroup

theorem ofFixingSubgroup.def {s : Set α} : (SubMulAction.ofFixingSubgroup M s).carrier = sᶜ :=
  rfl
#align sub_mul_action.of_fixing_subgroup.def SubMulAction.ofFixingSubgroup.def

theorem ofFixingSubgroup.mem_iff {s : Set α} {x : α} :
    x ∈ SubMulAction.ofFixingSubgroup M s ↔ x ∉ s :=
  Iff.rfl
#align sub_mul_action.of_fixing_subgroup.mem_iff SubMulAction.ofFixingSubgroup.mem_iff

theorem SubMulActionOfFixingSubgroup.not_mem {s : Set α} 
  (x : SubMulAction.ofFixingSubgroup M s) : ↑x ∉ s := x.prop
#align sub_mul_action.sub_mul_action_of_fixing_subgroup.not_mem SubMulAction.SubMulActionOfFixingSubgroup.not_mem

end Complements

end SubMulAction

section fixingSubgroup

variable (M : Type _) [Group M] {α : Type _} [MulAction M α]

example (a : α) (s : Set (SubMulAction.ofStabilizer M a)) : Set α := 
  (fun x => x.val) '' s

theorem fixingSubgroup_of_insert (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    fixingSubgroup M (insert a ((fun x => x.val) '' s : Set α)) =
      (fixingSubgroup (↥(stabilizer M a)) s).map (Subgroup.subtype (stabilizer M a)) := 
      --  (fixingSubgroup (↥(stabilizer M a)) s) : Subgroup M) :=
  by
  ext m
  constructor
  · intro hm
    rw [mem_fixingSubgroup_iff] at hm
    rw [Subgroup.mem_map]
    suffices hm' : m ∈ stabilizer M a
    use ⟨m, hm'⟩
    simp only [Subgroup.coeSubtype, and_true]
    rw [mem_fixingSubgroup_iff]
    rintro ⟨y, hy⟩ hy'
    simp only [SetLike.mk_smul_mk, Subtype.mk.injEq, SubMulActiondef]
    change m • y = y 



    sorry
/-     intro hm
    rw [Subgroup.mem_map]
    simp_rw [mem_fixingSubgroup_iff]
    use m
    simp
    use m
    · rw [mem_stabilizer_iff]
      rw [mem_fixingSubgroup_iff] at hm 
      apply hm a (Set.mem_insert a _)
    · constructor
      simp only [SetLike.mem_coe, mem_fixingSubgroup_iff]
      intro y hy
      rw [mem_fixingSubgroup_iff] at hm 
      let t : Set α := insert a (coe '' s)
      suffices ↑y ∈ t by
        rw [← SetLike.coe_eq_coe, SubMulAction.val_smul]
        apply hm (↑y) this
      apply Set.mem_insert_of_mem
      use ⟨y, hy, rfl⟩
      rfl -/
  · rintro ⟨⟨n, hn'⟩, hn, rfl⟩
    simp only [Subgroup.coeSubtype, SetLike.mem_coe, mem_fixingSubgroup_iff] at hn ⊢
    intro x hx
    rw [Set.mem_insert_iff] at hx
    cases' hx with hx hx
    . -- x = a  
      simpa [hx] using hn'
    . -- x ∈ s
      simp only [Set.mem_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      conv_rhs => rw [← hn y hy]
#align fixing_subgroup_of_insert fixingSubgroup_of_insert

end fixingSubgroup

section EquivariantMap

variable (M : Type _) [Group M] {α : Type _} [MulAction M α]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The equivariant map from the sub_mul_action_of stabilizer into the ambient type -/
def subMulActionOfStabilizerInclusion (a : α) : SubMulAction.ofStabilizer M a →[stabilizer M a] α
    where
  toFun x := ↑x
  map_smul' g x := rfl
#align sub_mul_action_of_stabilizer_inclusion subMulActionOfStabilizerInclusion

/-
def of_fixing_subgroup.inclusion (s : set α) :
  (sub_mul_action.of_fixing_subgroup M s) →[fixing_subgroup M s] α := {
to_fun := λ x, ↑x,
map_smul' := λ g x, rfl }
 -/
variable (α)

/-- The identity map of the sub_mul_action of the fixing_subgroup
of the empty set into the ambient set, as an equivariant map -/
def SubMulAction.ofFixingSubgroupEmptyMap :
    let φ := (fixingSubgroup M (∅ : Set α)).Subtype
    SubMulAction.ofFixingSubgroup M (∅ : Set α) →ₑ[φ] α
    where
  toFun x := x
  map_smul' g x := rfl
#align sub_mul_action.of_fixing_subgroup_empty_map SubMulAction.ofFixingSubgroupEmptyMap

theorem SubMulAction.ofFixingSubgroupEmptyMap_bijective :
    Function.Bijective (SubMulAction.ofFixingSubgroupEmptyMap M α) :=
  by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    exact hxy
  · intro x; use x
    rw [SubMulAction.ofFixingSubgroup.mem_iff]
    exact Set.not_mem_empty x
    rfl
#align sub_mul_action.of_fixing_subgroup_empty_map_bijective SubMulAction.ofFixingSubgroupEmptyMap_bijective

theorem SubMulAction.of_fixingSubgroup_empty_map_scalars_surjective :
    Function.Surjective (fixingSubgroup M (∅ : Set α)).Subtype :=
  by
  intro g
  use g; rw [mem_fixingSubgroup_iff]
  intro x hx; exfalso; simpa using hx
  rfl
#align sub_mul_action.of_fixing_subgroup_empty_map_scalars_surjective SubMulAction.of_fixingSubgroup_empty_map_scalars_surjective

variable {α}

/-- The identity map of fixing subgroup of stabilizer
into the fixing subgroup of the extended set, as an equivariant map -/
def SubMulAction.OfFixingSubgroupOfStabilizer.map (a : α)
    (s : Set (SubMulAction.ofStabilizer M a)) :
    let φ : fixingSubgroup M (insert a (coe '' s : Set α)) → fixingSubgroup (stabilizer M a) s :=
      fun m =>
      ⟨⟨(m : M), by
          apply (mem_fixingSubgroup_iff M).mp m.prop
          apply Set.mem_insert⟩,
        fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine' (mem_fixingSubgroup_iff M).mp m.prop _ _
        apply Set.mem_insert_of_mem
        exact ⟨x, hx, rfl⟩⟩
    SubMulAction.ofFixingSubgroup M (insert a (coe '' s : Set α)) →ₑ[φ]
      SubMulAction.ofFixingSubgroup (stabilizer M a) s
    where
  toFun x :=
    ⟨⟨(x : α), by
        rintro (h : (x : α) = a)
        apply (SubMulAction.ofFixingSubgroup.mem_iff M).mp x.prop
        rw [h]; apply Set.mem_insert⟩,
      fun h =>
      (SubMulAction.ofFixingSubgroup.mem_iff M).mp x.Prop <|
        Set.mem_insert_of_mem _ ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩⟩
  map_smul' m x := rfl
#align sub_mul_action.of_fixing_subgroup_of_stabilizer.map SubMulAction.OfFixingSubgroupOfStabilizer.map

theorem SubMulAction.OfFixingSubgroupOfStabilizer.map_bijective (a : α)
    (s : Set (SubMulAction.ofStabilizer M a)) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfStabilizer.map M a s) :=
  by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    -- PROVE A LEMMA THAT DOES THIS AUTOMATICALLY
    simp only [Subtype.mk_eq_mk]
    suffices hx : x = ↑((SubMulAction.OfFixingSubgroupOfStabilizer.map M a s) ⟨x, hx⟩)
    suffices hy : y = ↑((SubMulAction.OfFixingSubgroupOfStabilizer.map M a s) ⟨y, hy⟩)
    rw [hx]; rw [hy]; rw [h]
    rfl; rfl
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    refine' ⟨⟨x, _⟩, rfl⟩
    -- ⊢ x ∈ sub_mul_action_of_fixing_subgroup M (insert a (coe '' s))
    rw [SubMulAction.ofFixingSubgroup.mem_iff]
    intro h; cases set.mem_insert_iff.mp h
    · rw [SubMulAction.ofStabilizer.mem_iff] at hx1 ; exact hx1 h_1
    · rw [SubMulAction.ofFixingSubgroup.mem_iff] at hx2 
      apply hx2
      obtain ⟨x1, hx1', rfl⟩ := h_1
      simp only [SetLike.eta]
      exact hx1'
#align sub_mul_action.of_fixing_subgroup_of_stabilizer.map_bijective SubMulAction.OfFixingSubgroupOfStabilizer.map_bijective

theorem SubMulAction.OfFixingSubgroupOfStabilizer.scalar_map_bijective (a : α)
    (s : Set (SubMulAction.ofStabilizer M a)) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfStabilizer.map M a s).toSmulMap :=
  by
  constructor
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ hmn
    rw [← SetLike.coe_eq_coe, ← SetLike.coe_eq_coe, ← coe_coe] at hmn 
    simp only [Subtype.mk_eq_mk]
    exact hmn
  · rintro ⟨⟨m, hm⟩, hm'⟩
    use m; swap; rfl
    rw [mem_fixingSubgroup_iff]
    intro x hx
    cases' set.mem_insert_iff.mp hx with hx hx
    ·-- x = a
      rw [hx];
      exact mem_stabilizer_iff.mp hm
    · -- x ∈ coe '' s
      obtain ⟨y, hy, rfl⟩ := (Set.mem_image _ _ _).mp hx
      rw [mem_fixingSubgroup_iff] at hm' 
      let hz := hm' y hy
      rw [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower] at hz 
      exact hz
#align sub_mul_action.of_fixing_subgroup_of_stabilizer.scalar_map_bijective SubMulAction.OfFixingSubgroupOfStabilizer.scalar_map_bijective

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
    exact hk ⟨_, set.mem_smul_set_iff_inv_smul_mem.mp hx⟩
#align fixing_subgroup_smul_eq_fixing_subgroup_map_conj fixingSubgroup_smul_eq_fixingSubgroup_map_conj

/-- Conjugation induces an equivariant map between the sub_mul_action of
the fixing subgroup of a subset and that of a translate -/
def SubMulAction.ofFixingSubgroup.conjMap {s t : Set α} {g : M} (hst : g • s = t) :
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
      exact set.smul_mem_smul_set_iff.mp hgxt⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe]
    change g • m • x = MulAut.conj g m • g • x
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul]
#align sub_mul_action.of_fixing_subgroup.conj_map SubMulAction.ofFixingSubgroup.conjMap

theorem SubMulAction.ofFixingSubgroup.conjMap_bijective {s t : Set α} {g : M} (hst : g • s = t) :
    Function.Bijective (SubMulAction.ofFixingSubgroup.conjMap M hst) :=
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
    use (SubMulAction.ofFixingSubgroup.conjMap M hst') ⟨x, hx⟩
    rw [← SetLike.coe_eq_coe]
    change g • g⁻¹ • x = x
    rw [← mul_smul, mul_inv_self, one_smul]
#align sub_mul_action.of_fixing_subgroup.conj_map_bijective SubMulAction.ofFixingSubgroup.conjMap_bijective

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
#align sub_mul_action.of_stabilizer.conj_map SubMulAction.ofStabilizer.conjMap

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
#align sub_mul_action.of_stabilizer.conj_map_bijective SubMulAction.ofStabilizer.conjMap_bijective

/-- The identity between the iterated sub_mul_action of the fixing_subgroups
and the sub_mul_action of the fixing_subgroup of the union,
as an equivariant map -/
def SubMulAction.OfFixingSubgroupUnion.map (s t : Set α) :
    let φ :
      fixingSubgroup M (s ∪ t) →
        fixingSubgroup (fixingSubgroup M s) (coe ⁻¹' t : Set (SubMulAction.ofFixingSubgroup M s)) :=
      fun ⟨m, hm⟩ =>
      ⟨⟨m, by
          rw [fixingSubgroup_union, Subgroup.mem_inf] at hm 
          exact hm.left⟩,
        by
        rintro ⟨⟨x, hx⟩, hx'⟩
        simp only [Set.mem_preimage] at hx' 
        simp only [← SetLike.coe_eq_coe, Subtype.coe_mk, SubMulAction.val_smul_of_tower]
        rw [fixingSubgroup_union, Subgroup.mem_inf] at hm 
        exact hm.right ⟨x, hx'⟩⟩
    SubMulAction.ofFixingSubgroup M (s ∪ t) →ₑ[φ]
      SubMulAction.ofFixingSubgroup (fixingSubgroup M s)
        (coe ⁻¹' t : Set (SubMulAction.ofFixingSubgroup M s))
    where
  toFun x :=
    ⟨⟨x, fun hx => x.Prop (Set.mem_union_left t hx)⟩, fun hx =>
      x.Prop
        (by
          apply Set.mem_union_right s
          simpa only [Set.mem_preimage, Subtype.coe_mk] using hx)⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ =>
    by
    rw [← SetLike.coe_eq_coe, ← SetLike.coe_eq_coe, ← coe_coe]
    rfl
#align sub_mul_action.of_fixing_subgroup_union.map SubMulAction.OfFixingSubgroupUnion.map

theorem SubMulAction.OfFixingSubgroupUnion.map_def (s t : Set α)
    (x : SubMulAction.ofFixingSubgroup M (s ∪ t)) :
    ((SubMulAction.OfFixingSubgroupUnion.map M s t) x : α) = x :=
  rfl
#align sub_mul_action.of_fixing_subgroup_union.map_def SubMulAction.OfFixingSubgroupUnion.map_def

theorem SubMulAction.OfFixingSubgroupUnion.map_bijective (s t : Set α) :
    Function.Bijective (SubMulAction.OfFixingSubgroupUnion.map M s t) :=
  by
  constructor
  · intro a b h
    simp only [coe_coe, ← SetLike.coe_eq_coe]
    simp only [← SetLike.coe_eq_coe] at h 
    exact h
  · rintro ⟨⟨a, ha⟩, ha'⟩; use a
    · intro hy; cases (Set.mem_union a s t).mp hy
      exact ha h
      apply ha'; simp only [Set.mem_preimage, SubMulAction.coe_mk]; exact h
    rfl
#align sub_mul_action.of_fixing_subgroup_union.map_bijective SubMulAction.OfFixingSubgroupUnion.map_bijective

/-- The equivariant map on sub_mul_action.of_fixing_subgroup given a set inclusion -/
def SubMulAction.ofFixingSubgroup.mapOfInclusion {s t : Set α} (hst : t ⊆ s) :
    let φ : fixingSubgroup M s → fixingSubgroup M t := fun ⟨m, hm⟩ =>
      ⟨m, by
        apply fixingSubgroup_antitone
        exact hst; exact hm⟩
    SubMulAction.ofFixingSubgroup M s →ₑ[φ] SubMulAction.ofFixingSubgroup M t
    where
  toFun := fun ⟨x, hx⟩ => ⟨x, fun h => hx (hst h)⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl
#align sub_mul_action.of_fixing_subgroup.map_of_inclusion SubMulAction.ofFixingSubgroup.mapOfInclusion

/-- The equivariant map between sub_mul_action.of_stabilizer
  and .of_fixing_subgroup of the singleton -/
def SubMulAction.OfFixingSubgroupOfSingleton.map (a : α) :
    let φ : fixingSubgroup M ({a} : Set α) → stabilizer M a := fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    SubMulAction.ofFixingSubgroup M ({a} : Set α) →ₑ[φ] SubMulAction.ofStabilizer M a
    where
  toFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl
#align sub_mul_action.of_fixing_subgroup_of_singleton.map SubMulAction.OfFixingSubgroupOfSingleton.map

theorem SubMulAction.OfFixingSubgroupOfSingleton.map_bijective (a : α) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfSingleton.map M a) :=
  by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy; exact hxy
  · rintro ⟨x, hx⟩; use x; rfl
#align sub_mul_action.of_fixing_subgroup_of_singleton.map_bijective SubMulAction.OfFixingSubgroupOfSingleton.map_bijective

/-- The identity between the sub_mul_action of fixing_subgroups
of equal sets, as an equivariant map -/
def SubMulAction.OfFixingSubgroupOfEq.map {s t : Set α} (hst : s = t) :
    let φ : fixingSubgroup M s → fixingSubgroup M t := fun ⟨m, hm⟩ => ⟨m, by rw [← hst]; exact hm⟩
    SubMulAction.ofFixingSubgroup M s →ₑ[φ] SubMulAction.ofFixingSubgroup M t
    where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [← hst]; exact hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl
#align sub_mul_action.of_fixing_subgroup_of_eq.map SubMulAction.OfFixingSubgroupOfEq.map

theorem SubMulAction.OfFixingSubgroupOfEq.map_def {s t : Set α} (hst : s = t) :
    ∀ (x : α) (hx : x ∈ SubMulAction.ofFixingSubgroup M s),
      ((SubMulAction.OfFixingSubgroupOfEq.map M hst) ⟨x, hx⟩ : α) = x :=
  fun x hx => rfl
#align sub_mul_action.of_fixing_subgroup_of_eq.map_def SubMulAction.OfFixingSubgroupOfEq.map_def

theorem SubMulAction.OfFixingSubgroupOfEq.toSmulMap_def {s t : Set α} (hst : s = t) (g : M)
    (hg : g ∈ fixingSubgroup M s) :
    g = (SubMulAction.OfFixingSubgroupOfEq.map M hst).toSmulMap (⟨g, hg⟩ : fixingSubgroup M s) :=
  rfl
#align sub_mul_action.of_fixing_subgroup_of_eq.to_smul_map_def SubMulAction.OfFixingSubgroupOfEq.toSmulMap_def

theorem SubMulAction.OfFixingSubgroupOfEq.map_bijective {s t : Set α} (hst : s = t) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfEq.map M hst) :=
  by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rw [← SetLike.coe_eq_coe] at hxy ⊢
    simp only [SetLike.coe_mk]
    simp only [SubMulAction.OfFixingSubgroupOfEq.map_def M hst] at hxy 
    rw [hxy]
  · rintro ⟨x, hxt⟩
    use x; rw [hst]; exact hxt
    rfl
#align sub_mul_action.of_fixing_subgroup_of_eq.map_bijective SubMulAction.OfFixingSubgroupOfEq.map_bijective

theorem SubMulAction.OfFixingSubgroupOfEq.toSmulMap_bijective {s t : Set α} (hst : s = t) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfEq.map M hst).toSmulMap :=
  by
  constructor
  · rintro ⟨g, hg⟩ ⟨k, hk⟩ hgk
    rw [← SetLike.coe_eq_coe] at hgk ⊢
    simp only [SetLike.coe_mk]
    exact hgk
  · rintro ⟨k, hk⟩; use k; rw [hst]; exact hk
    rfl
#align sub_mul_action.of_fixing_subgroup_of_eq.to_smul_map_bijective SubMulAction.OfFixingSubgroupOfEq.toSmulMap_bijective

end EquivariantMap

#lint


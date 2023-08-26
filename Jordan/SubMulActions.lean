/-¨
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module sub_mul_actions
-/

-- import Jordan.EquivariantMap


import Mathlib.Data.Finset.Pointwise
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Tactic.Group

import Jordan.EquivariantMap

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
def inclusion (s : SubMulAction M α) : s →ₑ[@id M] α
    where
-- The inclusion map of the inclusion of a SubMulAction 
  toFun := fun x => x.val
-- The commutation property
  map_smul' _ _ := rfl
#align sub_mul_action.inclusion SubMulAction.inclusion

theorem inclusion.toFun_eq_coe (s : SubMulAction M α) : 
    s.inclusion.toFun = fun x => x.val := rfl
#align sub_mul_action.inclusion.to_fun_eq_coe SubMulAction.inclusion.toFun_eq_coe

lemma image_inclusion (s : SubMulAction M α) : 
    Set.range s.inclusion = s.carrier  := by
  ext a
  simp only [Set.mem_range, Subtype.exists, mem_carrier, SetLike.mem_coe]
  constructor
  · intro ha
    obtain ⟨a, h, rfl⟩ := ha
    exact h
  · intro h
    use a
    use h
    rfl

lemma inclusion_injective (s : SubMulAction M α) :
    Function.Injective s.inclusion := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h 
  simp only [Subtype.mk.injEq]
  exact h


end Inclusion

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
#align sub_mul_action.of_compl_def SubMulAction.Compl_def

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
#align sub_mul_action.of_stabilizer SubMulAction.ofStabilizer


theorem ofStabilizer_carrier (a : α) : (SubMulAction.ofStabilizer M a).carrier = {a}ᶜ :=
  rfl
#align sub_mul_action.of_stabilizer.def SubMulAction.ofStabilizer_carrier

theorem mem_ofStabilizer_iff (a : α) {x : α} : x ∈ SubMulAction.ofStabilizer M a ↔ x ≠ a :=
  Iff.rfl
#align sub_mul_action.of_stabilizer.mem_iff SubMulAction.mem_ofStabilizer_iff

theorem neq_of_mem_ofStabilizer (a : α) {x : (SubMulAction.ofStabilizer M a)} : ↑x ≠ a :=
  x.prop
#align sub_mul_action.of_stabilizer.neq SubMulAction.neq_of_mem_ofStabilizer

/- 
instance ofStabilizerLift (a : α) : HasLiftT (SubMulAction.ofStabilizer M a) α :=
  coeToLift
#align sub_mul_action.of_stabilizer_lift SubMulAction.ofStabilizerLift
 -/


lemma add_card_ofStabilizer_eq (a : α) : 
    1 + PartENat.card (SubMulAction.ofStabilizer M a) = PartENat.card α :=  by
  unfold PartENat.card
  rw [← Cardinal.mk_sum_compl {a}, map_add]
  congr
  simp only [Cardinal.mk_fintype, Fintype.card_ofSubsingleton, Nat.cast_one]
  conv_lhs => rw [← Nat.cast_one]
  apply symm
  exact Iff.mpr Cardinal.toPartENat_eq_natCast_iff rfl

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

instance (s : Set α) : SMul (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) :=
  inferInstance

instance (s : Set α) : MulAction (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) :=
  inferInstance

theorem ofFixingSubgroup_carrier {s : Set α} : (SubMulAction.ofFixingSubgroup M s).carrier = sᶜ :=
  rfl
#align sub_mul_action.of_fixing_subgroup.def SubMulAction.ofFixingSubgroup_carrier

theorem mem_ofFixingSubgroup_iff {s : Set α} {x : α} :
    x ∈ SubMulAction.ofFixingSubgroup M s ↔ x ∉ s :=
  Iff.rfl
#align sub_mul_action.of_fixing_subgroup.mem_iff SubMulAction.mem_ofFixingSubgroup_iff

theorem not_mem_of_mem_ofFixingSubgroup {s : Set α} 
  (x : SubMulAction.ofFixingSubgroup M s) : ↑x ∉ s := x.prop
#align sub_mul_action.sub_mul_action_of_fixing_subgroup.not_mem SubMulAction.not_mem_of_mem_ofFixingSubgroup

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
      (fixingSubgroup (↥(stabilizer M a)) s).map (Subgroup.subtype (stabilizer M a)) := 
      --  (fixingSubgroup (↥(stabilizer M a)) s) : Subgroup M) :=
  by
  ext m
  constructor
  · intro hm
    rw [mem_fixingSubgroup_iff] at hm
    rw [Subgroup.mem_map]
    suffices hm' : m ∈ stabilizer M a
    · use ⟨m, hm'⟩
      simp only [Subgroup.coeSubtype, and_true]
      rw [mem_fixingSubgroup_iff]
      rintro ⟨y, hy⟩ hy'
      simp only [SetLike.mk_smul_mk, Subtype.mk.injEq]
      change m • y = y 
      apply hm
      apply Set.mem_insert_of_mem
      use ⟨y, hy⟩
    · simp only [mem_stabilizer_iff]
      apply hm
      apply Set.mem_insert a
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

/- /-- The equivariant map from the sub_mul_action_of stabilizer into the ambient type -/
def subMulActionOfStabilizerInclusion (a : α) : 
    SubMulAction.ofStabilizer M a →ₑ[@id (stabilizer M a)] α where
  toFun x := ↑x
  map_smul' g x := rfl
#align sub_mul_action_of_stabilizer_inclusion subMulActionOfStabilizerInclusion
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
#align sub_mul_action.of_fixing_subgroup_empty_map SubMulAction.ofFixingSubgroupEmpty_equivariantMap

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
#align sub_mul_action.of_fixing_subgroup_empty_map_bijective SubMulAction.ofFixingSubgroupEmpty_equivariantMap_bijective

theorem SubMulAction.of_fixingSubgroupEmpty_mapScalars_surjective :
    Function.Surjective (fixingSubgroup M (∅ : Set α)).subtype := by
  intro g
  suffices : g ∈ fixingSubgroup M (∅ : Set α)
  use ⟨g, this⟩
  rfl
  rw [mem_fixingSubgroup_iff]
  intro x hx
  exfalso
  exact hx
#align sub_mul_action.of_fixing_subgroup_empty_map_scalars_surjective SubMulAction.of_fixingSubgroupEmpty_mapScalars_surjective

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
        refine' (mem_fixingSubgroup_iff M).mp m.prop _ _
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
        refine' (mem_fixingSubgroup_iff M).mp m.prop _ _
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
#align sub_mul_action.of_fixing_subgroup_of_stabilizer.map SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer

theorem SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective 
    (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    Function.Bijective 
      (SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer M a s) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    -- PROVE A LEMMA THAT DOES THIS AUTOMATICALLY
    simp only [Subtype.mk_eq_mk]
    suffices hx : x = ↑((SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer M a s) ⟨x, hx⟩)
    suffices hy : y = ↑((SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer M a s) ⟨y, hy⟩)
    rw [hx]; rw [hy]; rw [h]
    rfl; rfl
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    refine' ⟨⟨x, _⟩, rfl⟩
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
#align sub_mul_action.of_fixing_subgroup_of_stabilizer.map_bijective SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective

theorem SubMulAction.scalarMap_ofFixingSubgroupOfStabilizer_bijective 
    (a : α) (s : Set (SubMulAction.ofStabilizer M a)) :
    Function.Bijective (SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer M a s).toSmulMap :=
  by
  constructor
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ hmn
    rw [← SetLike.coe_eq_coe, ← SetLike.coe_eq_coe] at hmn 
    simp only [Subtype.mk_eq_mk]
    exact hmn
  · rintro ⟨⟨m, hm⟩, hm'⟩
    suffices : m ∈ fixingSubgroup M (insert a (Subtype.val '' s))  
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
#align sub_mul_action.of_fixing_subgroup_of_stabilizer.scalar_map_bijective SubMulAction.scalarMap_ofFixingSubgroupOfStabilizer_bijective

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
#align fixing_subgroup_smul_eq_fixing_subgroup_map_conj fixingSubgroup_smul_eq_fixingSubgroup_map_conj

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
#align sub_mul_action.of_fixing_subgroup.conj_map SubMulAction.conjMap_ofFixingSubgroup

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
    rw [← mul_smul, mul_inv_self, one_smul]
#align sub_mul_action.of_fixing_subgroup.conj_map_bijective SubMulAction.conjMap_ofFixingSubgroup_bijective

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
#align sub_mul_action.of_fixing_subgroup_union.map SubMulAction.map_ofFixingSubgroupUnion

theorem SubMulAction.map_ofFixingSubgroupUnion_def (s t : Set α)
    (x : SubMulAction.ofFixingSubgroup M (s ∪ t)) :
    ((SubMulAction.map_ofFixingSubgroupUnion M s t) x : α) = x :=
  rfl
#align sub_mul_action.of_fixing_subgroup_union.map_def SubMulAction.map_ofFixingSubgroupUnion_def

theorem SubMulAction.OfFixingSubgroupUnion.map_bijective (s t : Set α) :
    Function.Bijective (SubMulAction.map_ofFixingSubgroupUnion M s t) :=
  by
  constructor
  · intro a b h
    simp only [← SetLike.coe_eq_coe] 
    simp only [← SetLike.coe_eq_coe] at h 
    exact h
  · rintro ⟨⟨a, ha⟩, ha'⟩
    suffices : a ∈ ofFixingSubgroup M (s ∪ t)
    use ⟨a, this⟩; rfl
    · intro hy
      cases' (Set.mem_union a s t).mp hy with h h
      · exact ha h
      · apply ha'
        simp only [Set.mem_preimage]
        exact h
#align sub_mul_action.of_fixing_subgroup_union.map_bijective SubMulAction.OfFixingSubgroupUnion.map_bijective

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
#align sub_mul_action.of_fixing_subgroup.map_of_inclusion SubMulAction.ofFixingSubgroup.mapOfInclusion

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
#align sub_mul_action.of_fixing_subgroup_of_singleton.map SubMulAction.OfFixingSubgroupOfSingleton.map

theorem SubMulAction.OfFixingSubgroupOfSingleton.map_bijective (a : α) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfSingleton.map M a) :=
  by
  constructor
  · intro _ _ hxy
    exact hxy
  · intro x
    use x
    rfl
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
  fun _ _ => rfl
#align sub_mul_action.of_fixing_subgroup_of_eq.map_def SubMulAction.OfFixingSubgroupOfEq.map_def

theorem SubMulAction.OfFixingSubgroupOfEq.toSmulMap_def 
    {s t : Set α} (hst : s = t) (g : M) (hg : g ∈ fixingSubgroup M s) :
    g = (SubMulAction.OfFixingSubgroupOfEq.map M hst).toSmulMap (⟨g, hg⟩ : fixingSubgroup M s) :=
  rfl
#align sub_mul_action.of_fixing_subgroup_of_eq.to_smul_map_def SubMulAction.OfFixingSubgroupOfEq.toSmulMap_def

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
#align sub_mul_action.of_fixing_subgroup_of_eq.map_bijective SubMulAction.OfFixingSubgroupOfEq.map_bijective

theorem SubMulAction.OfFixingSubgroupOfEq.toSmulMap_bijective {s t : Set α} (hst : s = t) :
    Function.Bijective (SubMulAction.OfFixingSubgroupOfEq.map M hst).toSmulMap :=
  by
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
#align sub_mul_action.of_fixing_subgroup_of_eq.to_smul_map_bijective SubMulAction.OfFixingSubgroupOfEq.toSmulMap_bijective

end EquivariantMap

#lint


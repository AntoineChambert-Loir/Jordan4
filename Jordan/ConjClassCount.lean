/-
Copyright (c) 2022 ACL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ACL

! This file was ported from Lean 3 source module conj_class_count
-/
import Mathbin.Tactic.Default
import Mathbin.Logic.Equiv.Basic
import Mathbin.Tactic.Basic
import Mathbin.Tactic.Group
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.GroupTheory.GroupAction.SubMulAction
import Mathbin.GroupTheory.GroupAction.Embedding
import Mathbin.GroupTheory.Perm.Cycle.Type
import Mathbin.GroupTheory.Perm.List
import Mathbin.GroupTheory.Perm.Cycle.Basic
import Mathbin.GroupTheory.Perm.Cycle.Concrete
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.SpecificGroups.Alternating
import Oneshot.EquivariantMap

-- import group_theory.abelianization
-- import group_theory.abelianization
-- import group_theory.sylow
-- import group_theory.sylow
-- import .sub_mul_actions
-- import .sub_mul_actions
-- import .multiple_transitivity
-- import .multiple_transitivity
-- import .for_mathlib.extensions
-- import .for_mathlib.extensions
open scoped Pointwise

/- instance pi.mul_one_class' {I : Type*} {f : I → Type*} {p : I → Prop}
[Π (i : I) (pi : p i), mul_one_class (f i)] :
mul_one_class (Π (i : I) (pi : p i), f i) :=
begin
  refine {
  one := λ i hi, _,
  mul := λ u v i hi,
  begin
    haveI : mul_one_class (f i) := _inst_1 i hi,
    exact (u i hi) * (v i hi),
  end,
  one_mul := λ u, begin
    ext i hi,
    dsimp, convert (_inst_1 i hi).one_mul (u i hi),
    end,
  mul_one := λ u, begin
    ext i hi,
    dsimp, convert (_inst_1 i hi).mul_one (u i hi),
    end, },
end

instance pi.group' {I : Type*} {f : I → Type*} {p : I → Prop}
[Π (i : I) (pi : p i), group (f i)] :
group (Π (i : I) (pi : p i), f i) :=
begin
  refine_struct {
  mul_assoc := λ u v w,
  begin
    ext i hi,
    haveI : group (f i) := _inst_1 i hi,
    dsimp,

    exact u i hi * v i hi * w i hi = u i hi * (v i hi * w i hi),
  end,
  inv := sorry,
  mul_left_inv := sorry,
.. },
end

 -/
/-
lemma function.extend_apply_first {α β γ : Type*}
  (f : α → β) (g : α → γ) (e' : β → γ)
  (hf : ∀ (a b : α), f a = f b → g a = g b) (a : α) :
  function.extend f g e' (f a) = g a :=
begin
  classical,
  simp only [function.extend_def, dif_pos, exists_apply_eq_apply],
  apply hf,
  exact (classical.some_spec (exists_apply_eq_apply f a)),
end

lemma function.extend_apply_first {α β γ : Type*}
  (f : α → β) (g : α → γ) (e' : β → γ)
  (hf : ∀ (a b : α), f a = f b → g a = g b) (a : α) :
  function.extend f g e' (f a) = g a := function.factors_through.extend_apply hf e' a


-/
/-
def subgroup.mul_equiv {α β : Type*} [group α] [group β] (e : mul_equiv α β)
  {G : subgroup α} {H : subgroup β} (h : ∀ g, g ∈ G ↔ e g ∈ H) :
  mul_equiv G H :=
{ to_fun := subtype.map e.to_fun (λ g hg, (h g).mp hg), -- λ ⟨g, hg⟩, ⟨e g, h.mp hg⟩,
  inv_fun := subtype.map e.inv_fun (λ k hk,
    by simp only [h, mul_equiv.inv_fun_eq_symm, mul_equiv.apply_symm_apply, hk]),
  left_inv := λ ⟨g, hg⟩,
  begin
    rw ← subtype.coe_inj,
    simp only [subtype.map_coe],
    simp only [mul_equiv.to_fun_eq_coe, mul_equiv.inv_fun_eq_symm, mul_equiv.symm_apply_apply],
  end,
  right_inv := λ ⟨k, hk⟩,
  begin
    rw ← subtype.coe_inj,
    simp only [subtype.map_coe],
    simp only [mul_equiv.inv_fun_eq_symm, mul_equiv.to_fun_eq_coe, mul_equiv.apply_symm_apply],
  end,
  map_mul' := λ ⟨g, hg⟩ ⟨k, hk⟩,
  begin
    simp only [← subtype.coe_inj],
    rw subgroup.coe_mul,
    simp only [subtype.map_coe],
    simp only [mul_mem_class.mk_mul_mk, subgroup.coe_mk, mul_equiv.to_fun_eq_coe, map_mul],
  end, }
-/
section Lists

variable {α β : Type _}

theorem List.disjoint_map (f : α → β) (s t : List α) (hf : Function.Injective f)
    (h : List.Disjoint s t) : List.Disjoint (s.map f) (t.map f) :=
  by
  simp only [List.Disjoint]
  intro b hbs hbt
  rw [List.mem_map] at hbs hbt 
  obtain ⟨a, ha, rfl⟩ := hbs
  apply h ha
  obtain ⟨a', ha', ha''⟩ := hbt
  rw [hf ha''.symm]; exact ha'
#align list.disjoint_map List.disjoint_map

theorem List.disjoint_pmap {p : α → Prop} (f : ∀ a : α, p a → β) (s t : List α) (hs : ∀ a ∈ s, p a)
    (ht : ∀ a ∈ t, p a) (hf : ∀ (a a' : α) (ha : p a) (ha' : p a'), f a ha = f a' ha' → a = a')
    (h : List.Disjoint s t) : List.Disjoint (List.pmap f s hs) (List.pmap f t ht) :=
  by
  simp only [List.Disjoint]
  intro b hbs hbt
  rw [List.mem_pmap] at hbs hbt 
  obtain ⟨a, ha, rfl⟩ := hbs
  apply h ha
  obtain ⟨a', ha', ha''⟩ := hbt
  rw [hf a a' (hs a ha) (ht a' ha') ha''.symm]
  exact ha'
#align list.disjoint_pmap List.disjoint_pmap

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def List.mkSubtype {p : α → Prop} : ∀ (l : List α) (hl : ∀ a ∈ l, p a), List (Subtype p)
  | [] => fun _ => List.nil
  | a::l => fun hl =>
    ⟨a,
        hl a
          (List.mem_cons_self a l)⟩::List.mkSubtype l fun b hb => hl b (List.mem_cons_of_mem a hb)
#align list.mk_subtype List.mkSubtype

theorem List.coe_mk {p : α → Prop} (l : List α) (hl : ∀ a ∈ l, p a) :
    List.map coe (List.mkSubtype l hl) = l :=
  by
  induction' l with a l' hl'
  -- nil
  simp only [List.mkSubtype, List.map_nil]
  -- (a :: l)
  simp only [List.mkSubtype, List.map_cons]
  constructor
  simp only [Subtype.coe_mk]
  apply hl'
#align list.coe_mk List.coe_mk

def List.mkSubtype' {p : α → Prop} (l : List α) (hl : ∀ a ∈ l, p a) : List (Subtype p) :=
  List.pmap (fun (a : α) (ha : p a) => (⟨a, ha⟩ : Subtype p)) l hl
#align list.mk_subtype' List.mkSubtype'

theorem List.coe_mk' {p : α → Prop} (l : List α) (hl : ∀ a ∈ l, p a) :
    List.map coe (List.mkSubtype' l hl) = l :=
  by
  simp only [List.mkSubtype']
  rw [List.map_pmap]
  rw [List.pmap_congr]
  rw [List.pmap_eq_map]
  rw [List.map_id]
  exact hl
  intro a ha hpa _
  simp only [Subtype.coe_mk, id.def]
#align list.coe_mk' List.coe_mk'

example [DecidableEq α] (p : α → Prop) [DecidablePred p] (s : Finset α) (hs : ∀ a ∈ s, p a) :
    Finset.image coe (Finset.subtype p s) = s :=
  by
  ext
  simp only [Finset.mem_image, Finset.mem_subtype, exists_prop, Subtype.exists, Subtype.coe_mk,
    exists_eq_right_right, and_iff_right_iff_imp]
  exact hs a

example (f : α → β) (hf : Function.Injective f) (l : List (Set α)) (hl : List.Pairwise Disjoint l) :
    List.Pairwise Disjoint (List.map (Set.image f) l) :=
  by
  rw [List.pairwise_map']
  simp_rw [Set.disjoint_image_iff hf]
  exact hl

end Lists

theorem Equiv.Perm.disjoint_iff_support_disjoint {α : Type _} [Fintype α] [DecidableEq α]
    {f g : Equiv.Perm α} : f.Disjoint g ↔ Disjoint f.support g.support := by
  simp only [Equiv.Perm.disjoint_iff_eq_or_eq, Finset.disjoint_iff_inter_eq_empty, ←
    Equiv.Perm.not_mem_support, ← Finset.mem_compl, ← Finset.mem_union, ← Finset.compl_inter, ←
    Finset.compl_eq_univ_iff, ← Finset.eq_univ_iff_forall]
#align equiv.perm.disjoint_iff_support_disjoint Equiv.Perm.disjoint_iff_support_disjoint

/-
section stabilizers

variables {G : Type*} [group G] {X : Type*} [mul_action G X] (s : set X)

open_locale pointwise

variables (G s)
def sub_mul_action_of_stabilizer : sub_mul_action (mul_action.stabilizer G s) X :=
{ carrier := s,
  smul_mem' := λ g x hx,
  begin
    have h : g • x ∈ g • s := ⟨x, hx, rfl⟩,
    let hg := g.prop, rw mul_action.mem_stabilizer_iff at hg,
    change g • s = s at hg,
    rw hg at h, exact h,
  end}

instance mul_action_of_stabilizer : mul_action (mul_action.stabilizer G s) s :=
  (sub_mul_action_of_stabilizer G s).mul_action

variables {G s}
def sub_mul_action_of_stabilizer_hom : mul_action.stabilizer G s →* equiv.perm s :=
  mul_action.to_perm_hom (mul_action.stabilizer G s) s

lemma sub_mul_action_of_stabilizer_hom_def
  (g : G) (hg : g ∈ mul_action.stabilizer G s) (x : X) (hx : x ∈ s) :
  ↑(sub_mul_action_of_stabilizer_hom (⟨g, hg⟩ : mul_action.stabilizer G s) (⟨x, hx⟩ : s)) = g • x :=
begin
  simp only [sub_mul_action_of_stabilizer_hom],
  simp only [mul_action.to_perm_hom_apply, mul_action.to_perm_apply],
  refl,
end

end stabilizers -/
section Ranges

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def List.ranges : List ℕ → List (List ℕ)
  | [] => List.nil
  | a::l => List.range a::List.map (List.map (Nat.add a)) (List.ranges l)
#align list.ranges List.ranges

-- #eval list.ranges [2,5,4]
theorem List.ranges_disjoint (l : List ℕ) : List.Pairwise List.Disjoint (List.ranges l) :=
  by
  induction' l with a l hl
  -- nil
  exact List.Pairwise.nil
  -- (a :: l)
  simp only [List.ranges, List.pairwise_cons]
  constructor
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := list.mem_map.mp hs
    intro u hu
    rw [List.mem_map]; rintro ⟨v, hv, rfl⟩
    rw [List.mem_range] at hu 
    exact lt_iff_not_le.mp hu le_self_add
  · rw [List.pairwise_map']
    apply List.Pairwise.imp _ hl
    intro u v; apply List.disjoint_map _ u v _
    exact fun u v => Nat.add_left_cancel
#align list.ranges_disjoint List.ranges_disjoint

theorem List.ranges_nodup (l : List ℕ) : ∀ s ∈ List.ranges l, List.Nodup s :=
  by
  induction' l with a l hl
  · -- nil
    intro s hs; exfalso
    simpa only [List.ranges, List.not_mem_nil] using hs
  · -- (a :: l)
    intro s hs
    simp only [List.ranges, List.mem_cons] at hs 
    cases' hs with hs hs
    -- s = a
    rw [hs];
    exact List.nodup_range a
    -- s ∈ l
    rw [List.mem_map] at hs ;
    obtain ⟨t, ht, rfl⟩ := hs
    refine' List.Nodup.map (fun u v => Nat.add_left_cancel) (hl t ht)
#align list.ranges_nodup List.ranges_nodup

theorem List.ranges_length (l : List ℕ) : List.map List.length l.ranges = l :=
  by
  induction' l with a l hl
  -- nil
  simp only [List.ranges, List.map_nil]
  -- (a :: l)
  simp only [List.ranges, List.map_cons]
  constructor
  exact Finset.card_range a
  simp only [List.map_map]
  conv_rhs => rw [← hl]
  apply List.map_congr
  intro s hs
  simp only [Function.comp_apply]
  rw [List.length_map]
#align list.ranges_length List.ranges_length

theorem List.ranges_lt (l : List ℕ) {s : List ℕ} {n : ℕ} (hs : s ∈ List.ranges l) (hn : n ∈ s) :
    n < l.Sum := by
  revert s n
  induction' l with a l hl
  · -- nil
    intro s n hs hn
    exfalso
    simp only [List.ranges] at hs 
    exact List.not_mem_nil s hs
  · -- (a :: l)
    intro s n hs hn
    simp only [List.ranges, List.mem_cons] at hs 
    cases' hs with hs hs
    · rw [hs, List.mem_range] at hn 
      apply lt_of_lt_of_le hn
      rw [List.sum_cons]
      exact le_self_add
    · rw [List.mem_map] at hs ; obtain ⟨t, ht, rfl⟩ := hs
      rw [List.mem_map] at hn ; obtain ⟨m, hm, rfl⟩ := hn
      simp only [List.sum_cons, Nat.add_def, add_lt_add_iff_left]
      exact hl ht hm
#align list.ranges_lt List.ranges_lt

end Ranges

section CycleTypes

variable (α : Type _) [DecidableEq α] [Fintype α]

def Equiv.permWithCycleType (c : Multiset ℕ) :=
  Finset.filter (fun g : Equiv.Perm α => Equiv.Perm.cycleType g = c) Finset.univ
#align equiv.perm_with_cycle_type Equiv.permWithCycleType

variable {α}

theorem Equiv.permWithCycleType_empty {c : Multiset ℕ} (hc : Fintype.card α < c.Sum) :
    Equiv.permWithCycleType α c = ∅ :=
  by
  apply Finset.eq_empty_of_forall_not_mem
  intro g
  unfold Equiv.permWithCycleType
  simp only [Set.toFinset_univ, Finset.mem_filter, Finset.mem_univ, true_and_iff]
  intro hg; apply lt_iff_not_le.mp hc; rw [← hg]
  rw [Equiv.Perm.sum_cycleType]
  refine' (Equiv.Perm.support g).card_le_univ
#align equiv.perm_with_cycle_type_empty Equiv.permWithCycleType_empty

theorem List.exists_pw_disjoint_with_card {c : List ℕ} (hc : c.Sum ≤ Fintype.card α) :
    ∃ o : List (List α),
      List.map List.length o = c ∧ (∀ s ∈ o, List.Nodup s) ∧ List.Pairwise List.Disjoint o :=
  by
  have : Nonempty (Fin (Fintype.card α) ≃ α) := by simp only [← Fintype.card_eq, Fintype.card_fin]
  have e := this.some
  let klift : ∀ n : ℕ, n < Fintype.card α → Fin (Fintype.card α) := fun n hn =>
    (⟨n, hn⟩ : Fin (Fintype.card α))
  let klift' : ∀ l : List ℕ, (∀ a ∈ l, a < Fintype.card α) → List (Fin (Fintype.card α)) :=
    List.pmap klift
  have hc'_lt : ∀ a : List ℕ, a ∈ c.ranges → ∀ a_1 : ℕ, a_1 ∈ a → a_1 < Fintype.card α :=
    by
    intro s u a ha
    apply lt_of_lt_of_le _ hc
    apply List.ranges_lt c u ha
  let l := List.pmap klift' (List.ranges c) hc'_lt
  have hl :
    ∀ (a : List ℕ) (ha : a ∈ c.ranges), List.map Fin.valEmbedding (klift' a (hc'_lt a ha)) = a :=
    by
    intro a ha
    simp only [klift', klift]
    conv_rhs => rw [← List.map_id a]; rw [List.map_pmap]
    simp only [Fin.valEmbedding_apply, Fin.val_mk, List.pmap_eq_map, List.map_id'', List.map_id]
  have hl' : List.map (List.map Fin.valEmbedding) l = List.ranges c :=
    by
    conv_rhs => rw [← List.map_id (List.ranges c)]
    rw [← List.pmap_eq_map _ id (List.ranges c) hc'_lt]
    simp only [l]
    rw [List.map_pmap]
    apply List.pmap_congr
    intro a ha ha' ha''
    simp only [hl a ha, id.def]
  use List.map (List.map e) l
  constructor
  · -- length
    rw [← List.ranges_length c]
    simp only [List.map_map, l, List.map_pmap, Function.comp_apply, List.length_map,
      List.length_pmap, List.pmap_eq_map]
  constructor
  · -- nodup
    intro s
    rw [List.mem_map]
    rintro ⟨t, ht, rfl⟩
    apply List.Nodup.map (Equiv.injective e)
    simp only [l, List.mem_pmap] at ht 
    obtain ⟨u, hu, rfl⟩ := ht
    apply List.Nodup.of_map
    rw [hl u hu]; apply List.ranges_nodup c u hu
  · -- pairwise disjoint
    suffices : List.Pairwise List.Disjoint l
    refine' List.Pairwise.map _ _ this
    · intro s t hst
      apply List.disjoint_map
      exact Equiv.injective e; exact hst
    · -- list.pairwise list.disjoint l,
      simp only [l]
      apply List.Pairwise.pmap (List.ranges_disjoint c)
      intro u hu v hv huv
      simp only [klift']
      apply List.disjoint_pmap
      · simp only [klift]
        intro a a' ha ha' h
        simpa only [Fin.mk_eq_mk] using h
      exact huv
#align list.exists_pw_disjoint_with_card List.exists_pw_disjoint_with_card

theorem Equiv.permWithCycleType_nonempty_iff {m : Multiset ℕ} :
    (m.Sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ↔ (Equiv.permWithCycleType α m).Nonempty :=
  by
  constructor
  · rintro ⟨hc, h2c⟩
    have hc' : m.to_list.sum ≤ Fintype.card α; simp only [Multiset.sum_toList]; exact hc
    obtain ⟨p, hp_length, hp_nodup, hp_disj⟩ := List.exists_pw_disjoint_with_card hc'
    use List.prod (List.map (fun l => List.formPerm l) p)
    simp only [Equiv.permWithCycleType, Finset.mem_filter, Set.toFinset_univ, Finset.mem_univ,
      true_and_iff]
    have hp2 : ∀ (x : List α) (hx : x ∈ p), 2 ≤ x.length :=
      by
      intro x hx
      apply h2c x.length
      rw [← Multiset.mem_toList, ← hp_length, List.mem_map]
      exact ⟨x, hx, rfl⟩
    rw [Equiv.Perm.cycleType_eq _ rfl]
    · -- lengths
      rw [← Multiset.coe_toList m]
      apply congr_arg
      rw [List.map_map]; rw [← hp_length]
      apply List.map_congr
      intro x hx; simp only [Function.comp_apply]
      have hx_nodup : x.nodup := hp_nodup x hx
      rw [List.support_formPerm_of_nodup x hx_nodup]
      ·-- length
        rw [List.toFinset_card_of_nodup hx_nodup]
      · -- length >= 1
        intro a h
        apply Nat.not_succ_le_self 1
        conv_rhs => rw [← List.length_singleton a]; rw [← h]
        exact hp2 x hx
    · -- cycles
      intro g
      rw [List.mem_map]
      rintro ⟨x, hx, rfl⟩
      have hx_nodup : x.nodup := hp_nodup x hx
      rw [← Cycle.formPerm_coe x hx_nodup]
      apply Cycle.isCycle_formPerm
      rw [Cycle.nontrivial_coe_nodup_iff hx_nodup]
      exact hp2 x hx
    · -- disjoint
      rw [List.pairwise_map']
      apply List.Pairwise.imp_of_mem _ hp_disj
      intro a b ha hb hab
      rw [List.formPerm_disjoint_iff (hp_nodup a ha) (hp_nodup b hb) (hp2 a ha) (hp2 b hb)]
      exact hab
  · -- empty case
    intro h
    obtain ⟨g, hg⟩ := h
    simp only [Equiv.permWithCycleType, Set.toFinset_univ, Finset.mem_filter, Finset.mem_univ,
      true_and_iff] at hg 
    constructor
    rw [← hg, Equiv.Perm.sum_cycleType]
    exact (Equiv.Perm.support g).card_le_univ
    intro a
    rw [← hg]
    exact Equiv.Perm.two_le_of_mem_cycleType
#align equiv.perm_with_cycle_type_nonempty_iff Equiv.permWithCycleType_nonempty_iff

theorem Equiv.Perm.mem_cycle_factors_conj (g k c : Equiv.Perm α) :
    c ∈ g.cycleFactorsFinset ↔ k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset :=
  by
  suffices imp_lemma :
    ∀ g k c : Equiv.Perm α,
      c ∈ g.cycleFactorsFinset → k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset
  · constructor
    apply imp_lemma g k c
    intro h
    suffices ∀ h : Equiv.Perm α, h = k⁻¹ * (k * h * k⁻¹) * k by rw [this g, this c];
      apply imp_lemma; exact h
    intro h
    simp only [← mul_assoc]
    simp only [mul_left_inv, one_mul, inv_mul_cancel_right]
  · intro g k c
    simp only [Equiv.Perm.mem_cycleFactorsFinset_iff]
    rintro ⟨hc, hc'⟩
    constructor
    exact Equiv.Perm.IsCycle.conj hc
    intro a ha
    simp only [Equiv.Perm.coe_mul, EmbeddingLike.apply_eq_iff_eq]
    apply hc'
    rw [Equiv.Perm.mem_support] at ha ⊢
    intro ha'; apply ha
    simp only [mul_smul, ← Equiv.Perm.smul_def] at ha' ⊢
    rw [ha']
    simp only [Equiv.Perm.smul_def, Equiv.Perm.apply_inv_self]
#align equiv.perm.mem_cycle_factors_conj Equiv.Perm.mem_cycle_factors_conj

example {β : Type _} (e : Equiv α β) (a : α) (b : β) : e a = b ↔ a = e.symm b := by
  refine' Equiv.apply_eq_iff_eq_symm_apply e

theorem Equiv.Perm.conj_support_eq (k : ConjAct (Equiv.Perm α)) (g : Equiv.Perm α) (a : α) :
    a ∈ (k • g).support ↔ k⁻¹.ofConjAct a ∈ g.support :=
  by
  simp only [Equiv.Perm.mem_support, ConjAct.smul_def]
  rw [not_iff_not]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, ConjAct.ofConjAct_inv]
  exact Equiv.apply_eq_iff_eq_symm_apply k.of_conj_act
#align equiv.perm.conj_support_eq Equiv.Perm.conj_support_eq

theorem Equiv.Perm.mem_cycle_factors_conj' (k : ConjAct (Equiv.Perm α)) (g c : Equiv.Perm α) :
    c ∈ g.cycleFactorsFinset ↔ k • c ∈ (k • g).cycleFactorsFinset :=
  by
  suffices imp_lemma :
    ∀ (k : ConjAct (Equiv.Perm α)) (g c : Equiv.Perm α),
      c ∈ g.cycleFactorsFinset → k • c ∈ (k • g).cycleFactorsFinset
  · constructor
    · apply imp_lemma k g c
    · intro h
      rw [← inv_smul_smul k c]; rw [← inv_smul_smul k g]
      apply imp_lemma; exact h
  · intro k g c
    simp only [Equiv.Perm.mem_cycleFactorsFinset_iff]
    rintro ⟨hc, hc'⟩
    constructor
    · exact hc.conj
    · intro a
      rw [Equiv.Perm.conj_support_eq]
      intro ha
      simp only [ConjAct.smul_def]
      simpa using hc' _ ha
#align equiv.perm.mem_cycle_factors_conj' Equiv.Perm.mem_cycle_factors_conj'

-- open_locale classical
example (g : Equiv.Perm α) (x : α) (hx : x ∈ g.support) :
    ∃ (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset), x ∈ c.support :=
  by
  use g.cycle_of x
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
  apply And.intro hx
  rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]
  exact hx

theorem Equiv.Perm.mem_cycle_factors_conj_eq (k : ConjAct (Equiv.Perm α)) (g : Equiv.Perm α) :
    Equiv.Perm.cycleFactorsFinset (k • g) = k • Equiv.Perm.cycleFactorsFinset g :=
  by
  ext c
  rw [Equiv.Perm.mem_cycle_factors_conj' k⁻¹ (k • g) c]
  simp only [inv_smul_smul]
  exact Finset.inv_smul_mem_iff
#align equiv.perm.mem_cycle_factors_conj_eq Equiv.Perm.mem_cycle_factors_conj_eq

example {α : Type _} (s : Finset α) (a b : α) (h : a = b) : a ∈ s ↔ b ∈ s := by
  refine' iff_of_eq (congr_fun (congr_arg Membership.Mem h) s)

example (k : Equiv.Perm α) : MulEquiv.symm (MulAut.conj k) = MulAut.conj k⁻¹ :=
  by
  -- simp only [map_inv],
  ext g x
  rw [map_inv, MulAut.conj_symm_apply, MulAut.conj_inv_apply]

theorem is_conj_iff_inv_is_conj {G : Type _} [Group G] (a b k : G) :
    k * a * k⁻¹ = b ↔ a = k⁻¹ * b * k := by
  rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]
#align is_conj_iff_inv_is_conj is_conj_iff_inv_is_conj

theorem Equiv.Perm.cycle_factors_conj (g k : Equiv.Perm α) :
    Finset.map (MulAut.conj k).toEquiv.toEmbedding g.cycleFactorsFinset =
      (k * g * k⁻¹).cycleFactorsFinset :=
  by
  ext c
  rw [Finset.mem_map_equiv]
  rw [Equiv.Perm.mem_cycle_factors_conj g k]
  apply iff_of_eq
  apply congr_arg₂ _ _
  rfl
  rw [is_conj_iff_inv_is_conj]
  rw [← MulEquiv.toEquiv_symm, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_symm_apply]
#align equiv.perm.cycle_factors_conj Equiv.Perm.cycle_factors_conj

theorem MulAction.ConjAct.mem_stabilizer_iff {G : Type _} [Group G] (k : ConjAct G) (g : G) :
    k ∈ MulAction.stabilizer (ConjAct G) g ↔ k * g * k⁻¹ = g :=
  by
  simp only [MulAction.mem_stabilizer_iff, SMul.smul]
  rfl
#align mul_action.conj_act.mem_stabilizer_iff MulAction.ConjAct.mem_stabilizer_iff

theorem MulAction.ConjAct.mem_stabilizer_iff' {G : Type _} [Group G] (k : ConjAct G) (g : G) :
    k ∈ MulAction.stabilizer (ConjAct G) g ↔ Commute k g :=
  by
  rw [MulAction.ConjAct.mem_stabilizer_iff]
  rw [Commute, SemiconjBy, mul_inv_eq_iff_eq_mul]
#align mul_action.conj_act.mem_stabilizer_iff' MulAction.ConjAct.mem_stabilizer_iff'

open scoped Pointwise

/-
def equiv.perm.mul_action_conj_cycle_factors' (g : equiv.perm α) :=
  sub_mul_action_of_stabilizer (conj_act (equiv.perm α)) (equiv.perm α) (g.cycle_factors_finset)

def equiv.perm.mul_action_conj_cycle_factors (g : equiv.perm α) :
  sub_mul_action (mul_action.stabilizer (conj_act (equiv.perm α)) g) (equiv.perm α) :=
{ carrier := g.cycle_factors_finset,
  smul_mem' :=
  begin
    rintro ⟨k, hk⟩, intros c hc,
    simp only [finset.mem_coe] at ⊢ hc,
    change k • c ∈ _,
    rw conj_act.smul_def k c,
    rw [mul_action.mem_stabilizer_iff, conj_act.smul_def k g] at hk,
    rw [← hk, ← equiv.perm.mem_cycle_factors_conj],
    exact hc,
  end }
-/
/-
instance equiv.perm.cycle_factors_smul' {g : equiv.perm α} :
  has_smul (mul_action.stabilizer (conj_act (equiv.perm α)) g) (g.cycle_factors_finset) :=
{ smul := λ ⟨k, hk⟩ ⟨c, hc⟩, ⟨k • c,
  begin
    simp only [has_smul.smul],
    convert (equiv.perm.mem_cycle_factors_conj g k c).mp hc,
    apply symm,
    exact (mul_action.conj_act.mem_stabilizer_iff k g).mp hk,
  end⟩}
-/
theorem Equiv.Perm.cycle_factors_conj_smul_eq {g : Equiv.Perm α}
    (k : MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) (c : g.cycleFactorsFinset) :
    (k • c : Equiv.Perm α) = ConjAct.ofConjAct ↑k * ↑c * ConjAct.ofConjAct ↑k⁻¹ :=
  rfl
#align equiv.perm.cycle_factors_conj_smul_eq Equiv.Perm.cycle_factors_conj_smul_eq

/-
instance equiv.perm.cycle_factors_mul_action' (g : equiv.perm α) :
  mul_action (mul_action.stabilizer (conj_act (equiv.perm α)) g) (g.cycle_factors_finset) :=
{ one_smul := λ c, sorry,
  mul_smul := λ ⟨h, hh⟩ ⟨k, hk⟩ ⟨c, hc⟩,
  begin
    rw ← subtype.coe_inj,
    simp only [submonoid.mk_mul_mk],

    let hzz := equiv.perm.cycle_factors_smul'_eq ⟨k, hk⟩ ⟨c, hc⟩,


      sorry,

  end, },

def equiv.perm.cycle_factors_smul' (g : equiv.perm α) :
  mul_action (subgroup.zpowers g).centralizer (g.cycle_factors_finset) :=
{ one_smul := λ c, by simp only [one_mul, finset.mk_coe, subgroup.coe_one, inv_one, mul_one,
      equiv.coe_fn_mk, equiv.perm.coe_one, id.def],
  mul_smul := λ h k c, by simp only [subtype.coe_mk,
      subgroup.coe_mul, mul_inv_rev, equiv.coe_fn_mk,
      equiv.perm.coe_mul, subtype.mk_eq_mk, ← mul_assoc],
  to_has_smul := { smul :=  λ k c, ⟨k * c * k⁻¹,
    begin
      convert (equiv.perm.mem_cycle_factors_conj g k c).mp c.prop,
      simp only [← (subgroup.mem_centralizer_iff.mp k.prop) g (subgroup.mem_zpowers g),
    mul_inv_cancel_right],
    end⟩ } } -/
-- open_locale classical
example {G : Type _} [Group G] (g k : G) : g⁻¹ * k = k * g⁻¹ ↔ k * g = g * k := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_inv_eq_iff_eq_mul, inv_inv]

theorem Group.commute_iff_mem_centralizer_zpowers {G : Type _} [Group G] (g k : G) :
    Commute g k ↔ k ∈ Subgroup.centralizer (Subgroup.zpowers g) :=
  by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro H h
    rw [Subgroup.mem_zpowers_iff]
    rintro ⟨n, rfl⟩
    apply Commute.zpow_left
    exact H
  · intro H
    simp only [Commute, SemiconjBy]
    rw [H g (Subgroup.mem_zpowers g)]
#align group.commute_iff_mem_centralizer_zpowers Group.commute_iff_mem_centralizer_zpowers

/-
example (g : equiv.perm α) : mul_action.stabilizer (conj_act (equiv.perm α)) g
≃* subgroup.centralizer (subgroup.zpowers g) :=
  subgroup.mul_equiv (conj_act.of_conj_act)
  (begin
    intro k,
    rw mul_action.mem_stabilizer_iff,
    simp only [has_smul.smul],
    rw mul_inv_eq_iff_eq_mul,
    rw ← group.commute_iff_mem_centralizer_zpowers,
    simp only [commute, semiconj_by],
    conv_lhs { rw eq_comm, },
  end)

example {α β : Type*} [decidable_eq α] [decidable_eq β] [group α] [mul_action α β]
  (s : finset β) (g : α) : coe (g • s)  = g • (s : set β) :=
finset.coe_smul_finset g s
-/
-- open_locale classical
theorem Equiv.Perm.commute_of_mem_cycles_factors_commute (k g : Equiv.Perm α)
    (hk : ∀ (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset), Commute k c) : Commute k g :=
  by
  rw [← Equiv.Perm.cycleFactorsFinset_noncommProd g (Equiv.Perm.cycleFactorsFinset_mem_commute g)]
  apply Finset.noncommProd_commute
  simp only [id.def]
  exact hk
#align equiv.perm.commute_of_mem_cycles_factors_commute Equiv.Perm.commute_of_mem_cycles_factors_commute

theorem Equiv.Perm.self_mem_cycle_factors_commute (g c : Equiv.Perm α)
    (hc : c ∈ g.cycleFactorsFinset) : Commute c g :=
  by
  apply Equiv.Perm.commute_of_mem_cycles_factors_commute
  intro c' hc'
  by_cases hcc' : c = c'
  rw [hcc']
  apply g.cycle_factors_finset_mem_commute hc hc'; exact hcc'
#align equiv.perm.self_mem_cycle_factors_commute Equiv.Perm.self_mem_cycle_factors_commute

theorem Equiv.Perm.mem_cycleFactorsFinset_support (g c : Equiv.Perm α)
    (hc : c ∈ g.cycleFactorsFinset) (a : α) : a ∈ c.support ↔ g a ∈ c.support :=
  by
  let hc' := equiv.perm.mem_cycle_factors_finset_iff.mp hc
  constructor
  · intro ha
    rw [← hc'.2 a ha]
    exact equiv.perm.apply_mem_support.mpr ha
  · intro ha
    rw [← Equiv.Perm.apply_mem_support]
    suffices : c a = g a
    rw [this]; exact ha
    apply Equiv.injective g
    rw [← hc'.2 (g a) ha]
    simp only [← Equiv.Perm.mul_apply]
    have := Equiv.Perm.self_mem_cycle_factors_commute g c hc
    simp only [Commute, SemiconjBy] at this 
    rw [this]
#align equiv.perm.mem_cycle_factors_finset_support Equiv.Perm.mem_cycleFactorsFinset_support

theorem Equiv.Perm.subtypePerm_apply_pow_of_mem (g : Equiv.Perm α) (s : Finset α)
    (hs : ∀ x : α, x ∈ s ↔ g x ∈ s) (n : ℕ) (x : α) (hx : x ∈ s) :
    ((g.subtypePerm hs ^ n) (⟨x, hx⟩ : s) : α) = (g ^ n) x :=
  by
  revert x
  induction' n with n hrec
  · -- zero case
    intro x hx
    simp only [pow_zero, Equiv.Perm.coe_one, id.def, Subtype.coe_mk]
  · -- induction case
    intro x hx
    simp only [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]
    apply hrec
#align equiv.perm.subtype_perm_apply_pow_of_mem Equiv.Perm.subtypePerm_apply_pow_of_mem

theorem Equiv.Perm.subtypePerm_apply_zpow_of_mem (g : Equiv.Perm α) (s : Finset α)
    (hs : ∀ x : α, x ∈ s ↔ g x ∈ s) (i : ℤ) (x : α) (hx : x ∈ s) :
    ((g.subtypePerm hs ^ i) (⟨x, hx⟩ : s) : α) = (g ^ i) x :=
  by
  induction i
  -- nat case
  apply Equiv.Perm.subtypePerm_apply_pow_of_mem
  -- neg_succ case
  simp only [zpow_negSucc]
  apply Equiv.injective (g ^ (i + 1))
  simp only [Equiv.Perm.apply_inv_self]
  rw [← Equiv.Perm.subtypePerm_apply_pow_of_mem g s hs]
  simp only [Finset.mk_coe, Equiv.Perm.apply_inv_self, Subtype.coe_mk]
  apply Finset.coe_mem
#align equiv.perm.subtype_perm_apply_zpow_of_mem Equiv.Perm.subtypePerm_apply_zpow_of_mem

/-- Restrict a permutation to its support -/
def Equiv.Perm.subtypePermOfSupport (c : Equiv.Perm α) : Equiv.Perm c.support :=
  Equiv.Perm.subtypePerm c fun x : α => Equiv.Perm.apply_mem_support.symm
#align equiv.perm.subtype_perm_of_support Equiv.Perm.subtypePermOfSupport

/-- Restrict a permutation to a finset containing its support -/
def Equiv.Perm.subtypePermOfSupportLe (c : Equiv.Perm α) (s : Finset α) (hcs : c.support ≤ s) :
    Equiv.Perm s :=
  Equiv.Perm.subtypePerm c
    (by
      intro x
      by_cases hx' : x ∈ c.support
      · simp only [hcs hx', true_iff_iff]
        apply hcs; rw [Equiv.Perm.apply_mem_support]; exact hx'
      rw [Equiv.Perm.not_mem_support] at hx' ; rw [hx'])
#align equiv.perm.subtype_perm_of_support_le Equiv.Perm.subtypePermOfSupportLe

theorem Equiv.Perm.le_support_is_invariant {c : Equiv.Perm α} {s : Finset α} (hcs : c.support ≤ s)
    (x : α) : x ∈ s ↔ c x ∈ s := by
  by_cases hx' : x ∈ c.support
  · simp only [hcs hx', true_iff_iff]
    exact hcs (equiv.perm.apply_mem_support.mpr hx')
  rw [equiv.perm.not_mem_support.mp hx']
#align equiv.perm.le_support_is_invariant Equiv.Perm.le_support_is_invariant

/-- Support of a cycle is nonempty -/
theorem Equiv.Perm.support_of_cycle_nonempty {g : Equiv.Perm α} (hg : g.IsCycle) :
    g.support.Nonempty :=
  by
  rw [Finset.nonempty_iff_ne_empty, Ne.def, Equiv.Perm.support_eq_empty_iff]
  exact Equiv.Perm.IsCycle.ne_one hg
#align equiv.perm.support_of_cycle_nonempty Equiv.Perm.support_of_cycle_nonempty

/- rw ←  finset.card_pos,
  apply lt_of_lt_of_le _ (equiv.perm.is_cycle.two_le_card_support hg),
  norm_num, -/
example (g : Equiv.Perm α) :
    ∃ a : g.cycleFactorsFinset → α, ∀ c : g.cycleFactorsFinset, a c ∈ (c : Equiv.Perm α).support :=
  haveI : ∀ c : g.cycle_factors_finset, (c : Equiv.Perm α).support.Nonempty :=
    by
    intro c
    exact Equiv.Perm.support_of_cycle_nonempty (equiv.perm.mem_cycle_factors_finset_iff.mp c.prop).1
  ⟨fun c => (this c).some, fun c => (this c).choose_spec⟩

/-- If g and c commute, then g stabilizes the support of c -/
theorem Equiv.Perm.mem_support_of_commute {g c : Equiv.Perm α} (hgc : g * c = c * g) :
    ∀ x : α, x ∈ c.support ↔ g x ∈ c.support :=
  by
  intro x
  simp only [Equiv.Perm.mem_support, not_iff_not, ← Equiv.Perm.mul_apply]
  rw [← hgc, Equiv.Perm.mul_apply]
  exact (Equiv.apply_eq_iff_eq g).symm
#align equiv.perm.mem_support_of_commute Equiv.Perm.mem_support_of_commute

/-- Centralizer of a cycle is a power of that cycle on the cycle -/
theorem Equiv.Perm.centralizer_of_cycle_on' (g c : Equiv.Perm α) (hc : c.IsCycle) :
    g * c = c * g ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ g x ∈ c.support,
        Equiv.Perm.subtypePerm g hc' ∈ Subgroup.zpowers c.subtypePermOfSupport :=
  by
  constructor
  · intro hgc
    let hgc' := Equiv.Perm.mem_support_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := Equiv.Perm.support_of_cycle_nonempty hc
    suffices : c.same_cycle a (g a)
    simp only [Equiv.Perm.SameCycle] at this 
    obtain ⟨i, hi⟩ := this; use i
    ext ⟨x, hx⟩
    simp only [Equiv.Perm.subtypePermOfSupport, Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    rw [Equiv.Perm.subtypePerm_apply_zpow_of_mem]
    suffices c.same_cycle a x by
      obtain ⟨j, rfl⟩ := this
      · simp only [← Equiv.Perm.mul_apply, Commute.eq (Commute.zpow_right hgc j)]
        rw [← zpow_add, add_comm i j, zpow_add]
        simp only [Equiv.Perm.mul_apply]
        simp only [EmbeddingLike.apply_eq_iff_eq]
        exact hi
    -- c.same_cycle a x,
    exact
      Equiv.Perm.IsCycle.sameCycle hc (equiv.perm.mem_support.mp ha) (equiv.perm.mem_support.mp hx)
    -- c.same_cycle a (g a),
    apply Equiv.Perm.IsCycle.sameCycle hc (equiv.perm.mem_support.mp ha)
    exact equiv.perm.mem_support.mp ((hgc' a).mp ha)
  · -- converse
    rintro ⟨hc', h⟩
    obtain ⟨i, hi⟩ := h
    suffices hi' : ∀ (x : α) (hx : x ∈ c.support), g x = (c ^ i) x
    · ext x
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      by_cases hx : x ∈ c.support
      · -- hx : x ∈ c.support
        rw [hi' x hx]
        rw [hi' (c x) (equiv.perm.apply_mem_support.mpr hx)]
        simp only [← Equiv.Perm.mul_apply, ← zpow_add_one, ← zpow_one_add]
        rw [Int.add_comm 1 i]
      · -- hx : x ∉ c.support
        rw [equiv.perm.not_mem_support.mp hx]; apply symm
        rw [← Equiv.Perm.not_mem_support]
        intro hx'; apply hx
        exact (hc' x).mpr hx'
    · -- proof of hi'
      intro x hx
      let hix := Equiv.Perm.congr_fun hi ⟨x, hx⟩
      simp only [← Subtype.coe_inj, Equiv.Perm.subtypePermOfSupport] at hix 
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply,
        Equiv.Perm.subtypePerm_apply_zpow_of_mem] at hix 
      exact hix.symm
#align equiv.perm.centralizer_of_cycle_on' Equiv.Perm.centralizer_of_cycle_on'

example (g c : Equiv.Perm α) (hc : c.IsCycle) (hc' : ∀ x : α, x ∈ c.support ↔ g x ∈ c.support) :
    (Equiv.Perm.subtypePerm g hc').ofSubtype ∈ Subgroup.zpowers c ↔
      Equiv.Perm.subtypePerm g hc' ∈ Subgroup.zpowers c.subtypePermOfSupport :=
  by
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro n
  constructor
  · intro h; ext ⟨x, hx⟩; let h' := Equiv.Perm.congr_fun h x
    simp only [h', Equiv.Perm.subtypePermOfSupport, Equiv.Perm.subtypePerm_apply_zpow_of_mem,
      Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    exact hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x ∈ c.support
    · rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [Equiv.Perm.subtypePermOfSupport, Equiv.Perm.subtypePerm_apply_zpow_of_mem];
      exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      rw [← Equiv.Perm.not_mem_support]
      intro hx'; apply hx
      apply Equiv.Perm.support_zpow_le; exact hx'
      exact hx

theorem Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff' (g c : Equiv.Perm α)
    (hc' : ∀ x, x ∈ c.support ↔ g x ∈ c.support) (n : ℤ) :
    c ^ n = Equiv.Perm.ofSubtype (g.subtypePerm hc') ↔
      c.subtypePermOfSupport ^ n = g.subtypePerm hc' :=
  by
  constructor
  · intro h; ext ⟨x, hx⟩; let h' := Equiv.Perm.congr_fun h x
    simp only [h', Equiv.Perm.subtypePermOfSupport, Equiv.Perm.subtypePerm_apply_zpow_of_mem,
      Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    exact hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x ∈ c.support
    · rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [Equiv.Perm.subtypePermOfSupport, Equiv.Perm.subtypePerm_apply_zpow_of_mem];
      exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      rw [← Equiv.Perm.not_mem_support]
      intro hx'; apply hx
      apply Equiv.Perm.support_zpow_le; exact hx'
      exact hx
#align equiv.perm.zpow_eq_of_subtype_subtype_perm_iff' Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff'

theorem Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff (g c : Equiv.Perm α) (s : Finset α)
    (hg : ∀ x, x ∈ s ↔ g x ∈ s) (hc : c.support ⊆ s) (n : ℤ) :
    c ^ n = Equiv.Perm.ofSubtype (g.subtypePerm hg) ↔
      c.subtypePerm (Equiv.Perm.le_support_is_invariant hc) ^ n = g.subtypePerm hg :=
  by
  constructor
  · intro h; ext ⟨x, hx⟩; let h' := Equiv.Perm.congr_fun h x
    simp only [h', Equiv.Perm.subtypePerm_apply_zpow_of_mem, Subtype.coe_mk,
      Equiv.Perm.subtypePerm_apply]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    exact hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x ∈ s
    · rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [Equiv.Perm.subtypePerm_apply_zpow_of_mem]; exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      rw [← Equiv.Perm.not_mem_support]
      intro hx'
      apply hx
      apply hc; apply Equiv.Perm.support_zpow_le; exact hx'
      exact hx
#align equiv.perm.zpow_eq_of_subtype_subtype_perm_iff Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff

theorem Equiv.Perm.centralizer_of_cycle_on (g c : Equiv.Perm α) (hc : c.IsCycle) :
    g * c = c * g ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ g x ∈ c.support,
        (Equiv.Perm.subtypePerm g hc').ofSubtype ∈ Subgroup.zpowers c :=
  by
  constructor
  · intro hgc
    let hgc' := Equiv.Perm.mem_support_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := Equiv.Perm.support_of_cycle_nonempty hc
    suffices : c.same_cycle a (g a)
    simp only [Equiv.Perm.SameCycle] at this 
    obtain ⟨i, hi⟩ := this; use i
    ext x
    by_cases hx : x ∈ c.support
    · rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
      obtain ⟨j, rfl⟩ :=
        Equiv.Perm.IsCycle.sameCycle hc (equiv.perm.mem_support.mp ha)
          (equiv.perm.mem_support.mp hx)
      simp only [← Equiv.Perm.mul_apply]
      rw [Commute.eq (Commute.zpow_right hgc j)]
      rw [Commute.eq (Commute.zpow_zpow_self c i j)]
      simp only [Equiv.Perm.mul_apply, hi]
      exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      rw [← Equiv.Perm.not_mem_support]
      intro hx'; apply hx
      apply Equiv.Perm.support_zpow_le
      exact hx'
      exact hx
    -- c.same_cycle a (g a)
    apply Equiv.Perm.IsCycle.sameCycle hc (equiv.perm.mem_support.mp ha)
    exact equiv.perm.mem_support.mp ((hgc' a).mp ha)
  · -- converse
    rintro ⟨hc', h⟩
    obtain ⟨i, hi⟩ := h
    suffices hi' : ∀ (x : α) (hx : x ∈ c.support), g x = (c ^ i) x
    · ext x
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      by_cases hx : x ∈ c.support
      · -- hx : x ∈ c.support
        rw [hi' x hx]
        rw [hi' (c x) (equiv.perm.apply_mem_support.mpr hx)]
        simp only [← Equiv.Perm.mul_apply, ← zpow_add_one, ← zpow_one_add]
        rw [Int.add_comm 1 i]
      · -- hx : x ∉ c.support
        rw [equiv.perm.not_mem_support.mp hx]; apply symm
        rw [← Equiv.Perm.not_mem_support]
        intro hx'; apply hx
        exact (hc' x).mpr hx'
    · -- proof of hi'
      intro x hx
      rw [hi]
      rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
      exact hx
#align equiv.perm.centralizer_of_cycle_on Equiv.Perm.centralizer_of_cycle_on

/-- A permutation restricted to the support of a cycle factor is that cycle factor -/
theorem Equiv.Perm.subtypePerm_on_cycle_factor (g c : Equiv.Perm α)
    (hc : c ∈ g.cycleFactorsFinset) :
    g.subtypePerm (Equiv.Perm.mem_cycleFactorsFinset_support g c hc) = c.subtypePermOfSupport :=
  by
  ext ⟨x, hx⟩
  simp only [Equiv.Perm.subtypePermOfSupport, Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
  exact ((equiv.perm.mem_cycle_factors_finset_iff.mp hc).2 x hx).symm
#align equiv.perm.subtype_perm_on_cycle_factor Equiv.Perm.subtypePerm_on_cycle_factor

theorem Equiv.Perm.centralizer_mem_cycle_factors_iff' (g k : Equiv.Perm α) (c : Equiv.Perm α)
    (hc : c ∈ g.cycleFactorsFinset) :
    k * c = c * k ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ k x ∈ c.support,
        k.subtypePerm hc' ∈
          Subgroup.zpowers (g.subtypePerm (Equiv.Perm.mem_cycleFactorsFinset_support g c hc)) :=
  by
  constructor
  · intro H
    obtain ⟨hc', H'⟩ :=
      (Equiv.Perm.centralizer_of_cycle_on' k c (equiv.perm.mem_cycle_factors_finset_iff.mp hc).1).mp
        H
    rw [← Equiv.Perm.subtypePerm_on_cycle_factor g c hc] at H' 
    exact ⟨hc', H'⟩
  · rintro ⟨hc', H'⟩
    rw [Equiv.Perm.subtypePerm_on_cycle_factor g c hc] at H' 
    rw [Equiv.Perm.centralizer_of_cycle_on' k c (equiv.perm.mem_cycle_factors_finset_iff.mp hc).1]
    exact ⟨hc', H'⟩
#align equiv.perm.centralizer_mem_cycle_factors_iff' Equiv.Perm.centralizer_mem_cycle_factors_iff'

theorem Equiv.Perm.centralizer_mem_cycle_factors_iff (g k : Equiv.Perm α) (c : Equiv.Perm α)
    (hc : c ∈ g.cycleFactorsFinset) :
    k * c = c * k ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ k x ∈ c.support,
        (k.subtypePerm hc').ofSubtype ∈ Subgroup.zpowers c :=
  by
  rw [Equiv.Perm.centralizer_of_cycle_on]
  rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc 
  exact hc.1
#align equiv.perm.centralizer_mem_cycle_factors_iff Equiv.Perm.centralizer_mem_cycle_factors_iff

/- -- The axiom of choice…
example (ι : Type*) (α : Π (i : ι), Type*) (f : Π i, set (α i))
  (h :∀ i, (f i).nonempty)  : ∃ (a : Π i, α i), (∀ i, a i ∈ f i) :=
begin
  suffices : nonempty (Π i, (f i)),
  obtain a := this.some,
  use λ i, ↑(a i),
  intro i, refine subtype.mem (a i),
  rw ← not_is_empty_iff ,
  intro h',
  rw is_empty_pi at h',
  obtain ⟨i, hi⟩ := h',
  rw ← not_nonempty_iff  at hi,
  apply hi,
  simp only [set.nonempty_coe_sort],
  exact h i,
end

-- Finite choices
example (ι : Type*) (α : Π (i : ι), Type*) (f : Π (i : ι), finset (α i))
  (h :∀  i, (f i).nonempty) (s : finset ι) : ∃ (a : Π (i : s), α i), (∀ i : s, a i ∈ f i) :=
begin
  apply finset.induction_on s,
  { -- empty s
    apply exists.intro,
    intro i, exfalso, exact finset.not_mem_empty _ i.prop,
    intro i, exfalso, exact finset.not_mem_empty _ i.prop, },
  { -- insert
    intros k s hks hrec,
    obtain ⟨a, ha⟩ := hrec,
    apply exists.intro,
    rintro ⟨i,hi⟩,
    rw finset.mem_insert at hi,
    cases hi with hi hi,



    sorry, },
end
 -/
theorem Equiv.Perm.zpow_mod_card_support_cycleOf_self_apply [Fintype α] (f : Equiv.Perm α) (n : ℤ)
    (x : α) : (f ^ (n % (f.cycleOf x).support.card)) x = (f ^ n) x :=
  by
  by_cases hx : f x = x
  ·
    rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx]
  ·
    rw [← f.cycle_of_zpow_apply_self, ← f.cycle_of_zpow_apply_self, ←
      (f.is_cycle_cycle_of hx).orderOf, ← zpow_eq_mod_orderOf]
#align equiv.perm.zpow_mod_card_support_cycle_of_self_apply Equiv.Perm.zpow_mod_card_support_cycleOf_self_apply

example (n : ℤ) (hn : 0 ≤ n) : ∃ nn : ℕ, n = nn :=
  Int.eq_ofNat_of_zero_le hn

theorem Equiv.Perm.cycle_zpow_mem_support_iff {g : Equiv.Perm α} (hg : g.IsCycle) {n : ℤ} {x : α}
    (hx : g x ≠ x) : (g ^ n) x = x ↔ n % g.support.card = 0 :=
  by
  let q := n / g.support.card; let r := n % g.support.card
  change _ ↔ r = 0
  have div_euc : r + g.support.card * q = n ∧ 0 ≤ r ∧ r < g.support.card :=
    by
    rw [← Int.ediv_emod_unique _]
    constructor; rfl; rfl
    simp only [Int.coe_nat_pos]
    apply lt_of_lt_of_le _ (Equiv.Perm.IsCycle.two_le_card_support hg); norm_num
  simp only [← hg.order_of] at div_euc 
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le div_euc.2.1
  simp only [hm, Nat.cast_nonneg, Nat.cast_lt, true_and_iff] at div_euc 
  simp only [hm, Nat.cast_eq_zero]
  rw [← div_euc.1, zpow_add g, zpow_mul, zpow_ofNat]
  simp only [pow_orderOf_eq_one, zpow_ofNat, one_zpow, mul_one]
  have : (g ^ m) x = x ↔ g ^ m = 1 := by
    constructor
    · intro hgm
      simp [Equiv.Perm.IsCycle.pow_eq_one_iff hg]
      use x
      exact ⟨hx, hgm⟩
    · intro hgm; rw [hgm]; simp only [Equiv.Perm.coe_one, id.def]
  rw [this]
  cases' dec_em (m = 0) with hm hm
  simp only [hm, pow_zero, eq_self_iff_true]
  simp only [hm, iff_false_iff]
  exact pow_ne_one_of_lt_orderOf' hm div_euc.2
#align equiv.perm.cycle_zpow_mem_support_iff Equiv.Perm.cycle_zpow_mem_support_iff

theorem Equiv.Perm.zpow_eq_zpow_on_iff (g : Equiv.Perm α) (m n : ℤ) (x : α) (hx : g x ≠ x) :
    (g ^ m) x = (g ^ n) x ↔ m % (g.cycleOf x).support.card = n % (g.cycleOf x).support.card :=
  by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  conv_lhs => rw [← Int.sub_add_cancel m n, Int.add_comm, zpow_add]
  simp only [Equiv.Perm.coe_mul, EmbeddingLike.apply_eq_iff_eq]
  rw [← Equiv.Perm.cycleOf_zpow_apply_self g x]
  rw [← Equiv.Perm.cycle_zpow_mem_support_iff]
  · exact g.is_cycle_cycle_of hx
  · simp only [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]; exact hx
#align equiv.perm.zpow_eq_zpow_on_iff Equiv.Perm.zpow_eq_zpow_on_iff

example (p q : Prop) : p ∧ q → p :=
  And.left

example (g c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) (x y : α) (hx : x ∈ c.support) :
    g.SameCycle x y ↔ y ∈ c.support :=
  by
  have hx' : g.cycle_of x = c := (Equiv.Perm.cycle_is_cycleOf hx hc).symm
  have hx'' : x ∈ g.support := by
    apply Equiv.Perm.support_cycleOf_le g x
    rw [hx']; exact hx
  constructor
  · intro hxy
    rw [← hx']
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨hxy, hx''⟩
  · intro hy
    apply And.left
    rw [← Equiv.Perm.mem_support_cycleOf_iff]
    rw [hx']; exact hy

/-  -- SUPPRIMÉ AU PROFIT DE DÉFINITIONS PLUS GÉNÉRALES QUI PROUVENT LE PRODUIT SEMI DIRECT
/- Ici, on utilise a, k, et les propriétés 2 et 3
 - dans conj_class2, on utilise tout -/
lemma is_surjective_aux (g : equiv.perm α) (τ: equiv.perm (g.cycle_factors_finset))
  (H : ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.card = ((τ c) : equiv.perm α).support.card) :
  ∃ (a : g.cycle_factors_finset → α) (k : equiv.perm α),
    (∀ (c : g.cycle_factors_finset), a c ∈ (c : equiv.perm α).support)
    ∧ (g * k = k * g)
    ∧ (∀ (c : g.cycle_factors_finset), (conj_act.to_conj_act k) • (c : equiv.perm α) = τ c)
    ∧ k ∘ a = a ∘ τ
    ∧ k.support ⊆ g.support :=
begin
  have hsupp_ne : ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.nonempty,
  { intro c,
    exact equiv.perm.support_of_cycle_nonempty
      (equiv.perm.mem_cycle_factors_finset_iff.mp c.prop).1, },
  let a : g.cycle_factors_finset → α := λc, (hsupp_ne c).some,
  use a,
  let ha' : ∀ (c : g.cycle_factors_finset), g.cycle_of (a c) = (c : equiv.perm α) :=
  λ c,  (equiv.perm.cycle_is_cycle_of (hsupp_ne c).some_spec c.prop).symm,
  have ha : ∀ c : g.cycle_factors_finset, g (a c) ≠ (a c),
  { intro c,
    rw ← equiv.perm.mem_support,
    rw ← equiv.perm.cycle_of_mem_cycle_factors_finset_iff ,
    rw ha' c, exact c.prop, },
  have ha'': ∀ (c : g.cycle_factors_finset) (i : ℤ), g.cycle_of ((g ^ i) (a c)) = c,
  { intros c i, rw equiv.perm.cycle_of_self_apply_zpow, rw ha', },

  let Kf : equiv.perm (g.cycle_factors_finset) → (g.cycle_factors_finset) × ℤ → α :=
    λ e ⟨c, i⟩, (g ^ i) (a (e c)),
  have Kf_apply : ∀ {e : equiv.perm (g.cycle_factors_finset)} {c : g.cycle_factors_finset} {i : ℤ},
    Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) := λ e c i, rfl,
  let k := function.extend (Kf 1) (Kf τ) id,

  have haK : ∀ (e : equiv.perm (g.cycle_factors_finset)) (c : g.cycle_factors_finset) (i : ℤ),
  g.cycle_of (Kf e ⟨c, i⟩) = (e c : equiv.perm α),
  { intros e c i, rw Kf_apply,
    rw equiv.perm.cycle_of_self_apply_zpow, rw ha', },
  have ha2 : ∀ (e : equiv.perm (g.cycle_factors_finset)) (c : g.cycle_factors_finset) (i : ℤ),
   g (Kf e ⟨c,i⟩) = Kf e ⟨c, i + 1⟩,
  { intros e c i,
    simp only [Kf_apply],
    rw ← equiv.perm.mul_apply, rw ← zpow_one_add, rw add_comm 1 i, },
  have ha3 :  ∀ (e : equiv.perm (g.cycle_factors_finset)) (c d : g.cycle_factors_finset) (i : ℤ),
   (d = e c) → (d : equiv.perm α) (Kf e ⟨c,i⟩) = Kf e ⟨c, i + 1⟩,
-- Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) appartient au cycle de e c
  { intros e c d i h,
    rw h,
    rw ← haK e c i,
    rw equiv.perm.cycle_of_apply_self,
    apply ha2, },
  have ha4 : ∀ (e : equiv.perm (g.cycle_factors_finset)) (c d : g.cycle_factors_finset) (i : ℤ),
   (d ≠ e c) → (d : equiv.perm α) (Kf e ⟨c,i⟩) = Kf e ⟨c, i⟩,
  { intros e c d i h,
    suffices hdc : (d : equiv.perm α).disjoint (e c : equiv.perm α),
    { apply or.resolve_right (equiv.perm.disjoint_iff_eq_or_eq.mp hdc (Kf e ⟨c, i⟩)),
      -- intro hd,
      rw ← haK e c i,
      rw equiv.perm.cycle_of_apply_self ,
      rw ← equiv.perm.cycle_of_eq_one_iff,
      rw haK e c i,
      apply equiv.perm.is_cycle.ne_one ,
      refine (equiv.perm.mem_cycle_factors_finset_iff.mp _).1,
      exact g,
      exact (e c).prop, },
    apply g.cycle_factors_finset_pairwise_disjoint d.prop (e c).prop,
    rw function.injective.ne_iff (subtype.coe_injective), exact h, },
  have ha5 : ∀ (x : α) (hx : ¬ (∃ (cj : g.cycle_factors_finset × ℤ), Kf 1 cj = x)),
    k x = x,
  { intros x hx,
    simp only [k, function.extend_apply' _ _ _ hx, id.def], },
  have ha6 : ∀ (x : α) (hx : ¬ (∃ (cj : g.cycle_factors_finset × ℤ), Kf 1 cj = x))
    (c : g.cycle_factors_finset), (c : equiv.perm α) x = x,
  { intros x hx c,
    by_contradiction, apply hx,
    rw [← ne.def, ← equiv.perm.mem_support] at h,
    suffices : g.same_cycle (a c) x,
    { obtain ⟨i, hi⟩ := this,
      use ⟨c, i⟩,
      rw [Kf_apply, ← hi, equiv.perm.coe_one, id.def], },

    apply and.left,
    rw ← equiv.perm.mem_support_cycle_of_iff,
    rw ha' c, exact h, },
  have hkfg : ∀ (e e' : equiv.perm (g.cycle_factors_finset))
    (hee' : ∀ (c : g.cycle_factors_finset), (e c : equiv.perm α).support.card = (e' c : equiv.perm α).support.card),
    (Kf e').factors_through (Kf e), --    Kf e ci = Kf e dj → Kf e' ci = Kf e' dj,
  { rintros e e' Hee' ⟨c, i⟩ ⟨d, j⟩ He,
    change (g ^ i) (a (e c)) = (g ^ j) (a (e d)) at He,
    change (g ^ i) (a (e' c)) = (g ^ j) (a (e' d)),
    suffices hcd : c = d,
    { rw hcd at He ⊢,
      rw [g.zpow_eq_zpow_on_iff i j, ha'] at He,
      rw [g.zpow_eq_zpow_on_iff, ha', ← Hee' d],
      exact He,
      { exact ha (e' d), },
      { exact ha (e d), }, },
    { -- d = c
        apply equiv.injective e,
        rw [← subtype.coe_inj, ← ha'' (e c) i, ← ha'' (e d) j, He], }, },

  have k_apply : ∀ (c : g.cycle_factors_finset) (i : ℤ), k (Kf 1 ⟨c,i⟩) = Kf τ ⟨c,i⟩,
  { intros c i,
    simp only [k],
    rw function.factors_through.extend_apply (hkfg 1 τ _) id ⟨c,i⟩,
    -- rw function.extend_apply_first (Kf 1) (Kf τ) id _ ⟨c,i⟩,
    { intro c, simp only [← H c, equiv.perm.coe_one, id.def], }, },
  have k_apply' : ∀ (x : α), x ∉ g.support → k x = x,
  { intros x hx,
    simp only [k],
    rw function.extend_apply',
    simp only [id.def],
    intro hyp,
    obtain ⟨⟨c, i⟩, rfl⟩ := hyp,
    apply hx,
    change (g ^ i) (a c) ∈ g.support,
    rw equiv.perm.zpow_apply_mem_support ,
    rw equiv.perm.mem_support,
    exact ha c, },
  have hk_bij : function.bijective k,
  { rw fintype.bijective_iff_injective_and_card,
    refine and.intro _ rfl,
    intros x y hxy,
    by_cases hx : ∃ (a : (g.cycle_factors_finset) × ℤ), Kf 1 a = x,
    { obtain ⟨⟨c, i⟩, rfl⟩ := hx,
      simp only [k_apply] at hxy,
      by_cases hy : ∃ (b : (g.cycle_factors_finset) × ℤ), Kf 1 b = y,
      { -- x = Kf 1 a, y = Kf 1 b
        obtain ⟨⟨d, j⟩, rfl⟩ := hy,
        simp only [k_apply] at hxy,
        refine @hkfg τ 1 _ ⟨c,i⟩ ⟨d,j⟩ hxy,
        { intros c, simp only [equiv.perm.coe_one, id.def, H c], }, },
      { -- x = kf a, y non
        exfalso, apply hy,
        rw ha5 y hy at hxy,
        use (⟨τ c, i⟩ : g.cycle_factors_finset × ℤ),
        rw ← hxy, refl, }, },
    { rw ha5 x hx at hxy,
      by_cases hy : ∃ (b : (g.cycle_factors_finset) × ℤ), Kf 1 b = y,
      { -- x pas kfa, -- y = kf b,
        obtain ⟨⟨d, j⟩, rfl⟩ := hy,
        exfalso, apply hx,
        simp only [k_apply] at hxy,
        use ⟨τ d, j⟩, rw hxy, refl, },
      { -- x pas kf a, y non plus
        rw ha5 y hy at hxy,
        exact hxy, }, }, },
    use equiv.of_bijective k hk_bij,
    split,
    { exact λ c, (hsupp_ne c).some_spec, },
    split,
    { -- commutation
      ext x,
      simp only [equiv.perm.coe_mul, function.comp_app, equiv.of_bijective_apply],
      by_cases hx : ∃ (a : (g.cycle_factors_finset) × ℤ), Kf 1 a = x,
      { obtain ⟨⟨c, i⟩, rfl⟩ := hx,
        simp only [ha2, k_apply], },
      { have hx' : ¬ (∃ dj : (g.cycle_factors_finset) × ℤ, Kf 1 dj = g x),
        { intro hx', apply hx,
          obtain ⟨⟨d, j⟩, hx'⟩ := hx',
          use ⟨d, j-1⟩,
          apply equiv.injective g,
          simp only [← hx', ha2, sub_add_cancel], },
        rw ha5 x hx, rw ha5 _ hx', }, },
    split,
    { -- action on g.cycle_factors_finset
      intro c,
      rw conj_act.smul_def,
      rw mul_inv_eq_iff_eq_mul,
      simp only [conj_act.of_conj_act_to_conj_act],
      ext x,
      simp,
      by_cases hx : ∃ (a : (g.cycle_factors_finset) × ℤ), Kf 1 a = x,
      { obtain ⟨⟨d, j⟩, rfl⟩ := hx,
        by_cases hcd : d = c,
        { -- d = c
          rw hcd,
          rw ha3, simp only [k_apply],
          rw ha3,
          exact rfl,
          simp only [equiv.perm.coe_one, id.def], },
        { -- d ≠ c
          rw ha4, simp only [k_apply], rw ha4,
          rw function.injective.ne_iff (equiv.injective τ), exact ne.symm hcd,
          simp only [equiv.perm.coe_one, id.def, ne.def], exact ne.symm hcd, }, },
      { simp only [ha5 x hx, ha6 x hx], }, },
    split,
    { -- k ∘ a = a ∘ τ
      ext c,
      simp only [function.comp_app, equiv.of_bijective_apply],
      suffices : a c = Kf 1 (c, 0),
      rw [this, k_apply],
      all_goals { simp only [Kf_apply, zpow_zero, equiv.perm.coe_one, id.def], }, },
    { -- k.support ⊆ g.support
      intro x,
      simp only [equiv.perm.mem_support, ne.def],
      intros hxk hxg, apply hxk,
      apply k_apply',
      rw equiv.perm.not_mem_support, exact hxg, },
end
 -/
example (j : ℤ) : j = 1 + (j - 1) :=
  eq_add_of_sub_eq' rfl

example (g : Equiv.Perm α) (i j : ℤ) (x : α) : (g ^ i) x = (g ^ j) x ↔ (g ^ (j - i)) x = x :=
  by
  conv_lhs => rw [← sub_add_cancel j i, add_comm, zpow_add, Equiv.Perm.mul_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  exact comm

instance MulAction.decidableMemFixedBy {α β : Type _} [Monoid α] [DecidableEq β] [MulAction α β]
    (a : α) : DecidablePred fun b : β => b ∈ MulAction.fixedBy α β a :=
  by
  intro b
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
  infer_instance
#align mul_action.decidable_mem_fixed_by MulAction.decidableMemFixedBy

instance MulAction.decidableMemStabilizer {α β : Type _} [Group α] [DecidableEq β] [MulAction α β]
    (b : β) : DecidablePred fun g : α => g ∈ MulAction.stabilizer α b :=
  by
  simp only [DecidablePred, MulAction.mem_stabilizer_iff]
  intro g; infer_instance
#align mul_action.decidable_mem_stabilizer MulAction.decidableMemStabilizer

def Equiv.permConjStabilizerFun (g : Equiv.Perm α) :
    (Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g) ×
        ∀ c ∈ g.cycleFactorsFinset, Subgroup.zpowers (c : Equiv.Perm α)) →
      Equiv.Perm α :=
  fun uv :
    Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g) ×
      ∀ c ∈ g.cycleFactorsFinset, Subgroup.zpowers (c : Equiv.Perm α) =>
  uv.fst.of_subtype *
    Finset.noncommProd g.cycle_factors_finset
      (fun c => dite (c ∈ g.cycle_factors_finset) (fun hc => uv.snd c hc) fun hc => 1)
      fun c hc d hd h => by
      simp only [Finset.mem_coe] at hc hd 
      rw [dif_pos hc]; rw [dif_pos hd]
      obtain ⟨m, hc'⟩ := subgroup.mem_zpowers_iff.mp (uv.snd c hc).Prop
      obtain ⟨n, hd'⟩ := subgroup.mem_zpowers_iff.mp (uv.snd d hd).Prop
      rw [← hc', ← hd']
      apply Commute.zpow_zpow
      exact g.cycle_factors_finset_mem_commute hc hd h
#align equiv.perm_conj_stabilizer_fun Equiv.permConjStabilizerFun

example (g : Equiv.Perm α) (u : Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g))
    (v : ∀ c ∈ g.cycleFactorsFinset, Subgroup.zpowers (c : Equiv.Perm α)) :
    ConjAct.toConjAct (Equiv.permConjStabilizerFun g ⟨u, v⟩) ∈
      MulAction.stabilizer (ConjAct (Equiv.Perm α)) g :=
  by
  simp only [Equiv.permConjStabilizerFun, map_mul]
  apply Subgroup.mul_mem
  · rw [MulAction.mem_stabilizer_iff]
    rw [ConjAct.smul_def]
    rw [mul_inv_eq_iff_eq_mul]
    ext x
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, ConjAct.ofConjAct_toConjAct]
    by_cases hx : x ∈ MulAction.fixedBy _ α g
    · simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def] at hx 
      rw [hx]
      apply symm
      rw [← Equiv.Perm.smul_def, ← MulAction.mem_fixedBy]
      exact (Equiv.Perm.mem_iff_ofSubtype_apply_mem u x).mp hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem u hx]
      apply Equiv.Perm.ofSubtype_apply_of_not_mem u
      intro hx'; apply hx
      simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def] at hx' ⊢
      simp only [EmbeddingLike.apply_eq_iff_eq] at hx' ; exact hx'
  · rw [MulAction.mem_stabilizer_iff]
    rw [ConjAct.smul_def]
    rw [mul_inv_eq_iff_eq_mul]
    simp only [ConjAct.ofConjAct_toConjAct]
    change Commute _ _
    rw [Commute.symm_iff]
    apply Finset.noncommProd_commute
    intro c hc
    rw [dif_pos hc]
    obtain ⟨m, hm⟩ := subgroup.mem_zpowers_iff.mp (v c hc).Prop
    rw [← hm]
    change Commute g (c ^ m)
    apply Commute.zpow_right
    rw [Commute.symm_iff]
    exact Equiv.Perm.self_mem_cycle_factors_commute g c hc

example {G : Type _} [Group G] (x : G) (hx : x ∈ (⊥ : Subgroup G)) : x = 1 := by
  refine' subgroup.mem_bot.mp hx

theorem commute_ofSubtype_disjoint {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a, ¬(p a ∧ q a)) (x : Equiv.Perm (Subtype p)) (y : Equiv.Perm (Subtype q)) :
    Commute x.ofSubtype y.ofSubtype :=
  by
  apply Equiv.Perm.Disjoint.commute
  intro a
  by_cases hx : p a
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem y]
    apply Or.intro_right; rfl
    exact not_and.mp (hpq a) hx
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem x hx]
    apply Or.intro_left; rfl
#align commute_of_subtype_disjoint commute_ofSubtype_disjoint

example {ι : Type _} (p : ι → Prop) (f : ∀ i, p i → Type _) (i j : ι) (hi : p i) (hj : p j)
    (h : i = j) : f i hi = f j hj := by simp_rw [h]

example {ι : Type _} [DecidableEq ι] (p : α → ι) (s : Finset ι)
    (f : ∀ i : ι, i ∈ s → Equiv.Perm ↥{a : α | p a = i}) (i j : ι) (hi : i ∈ s) (hj : j ∈ s)
    (h : i = j) : Equiv.Perm.ofSubtype (f j hj) = Equiv.Perm.ofSubtype (f i hi) := by subst h

def Equiv.Perm.ofPartitionFun {ι : Type _} [DecidableEq ι] (p : α → ι) (s : Finset ι) :
    (∀ i ∈ s, Equiv.Perm {a | p a = i}) → Equiv.Perm α := fun f =>
  s.noncommProd (fun i => dite (i ∈ s) (fun hi => (f i hi).ofSubtype) fun hi => 1)
    (by
      intro i hi j hj hij
      simp only [Finset.mem_coe] at hi hj 
      simp only [dif_pos hi, dif_pos hj]
      /- by_cases h : i = j,
              exfalso, exact hij h,
               -/
      -- case h : ¬ (i = j)
      convert commute_ofSubtype_disjoint _ (f i hi) (f j hj)
      intro x
      simp only [Set.mem_setOf_eq, not_and]
      intro h'i h'j; apply hij; rw [← h'i]; exact h'j)
#align equiv.perm.of_partition_fun Equiv.Perm.ofPartitionFun

def Equiv.Perm.ofPartition {ι : Type _} [Fintype ι] [DecidableEq ι] (p : α → ι) :
    (∀ i, Equiv.Perm {a | p a = i}) →* Equiv.Perm α
    where
  toFun u := Equiv.Perm.ofPartitionFun p Finset.univ fun i hi => u i
  map_one' := by
    rw [← Subgroup.mem_bot]
    apply Subgroup.noncommProd_mem
    intro i hi
    simp only [dif_pos hi]
    rw [Subgroup.mem_bot]
    convert map_one Equiv.Perm.ofSubtype
  map_mul' := by
    intro f g
    simp only [Equiv.Perm.ofPartitionFun]
    rw [← Finset.noncommProd_mul_distrib]
    apply Finset.noncommProd_congr rfl
    · intro x hx
      dsimp
      simp only [if_pos hx]
      apply map_mul
    · intro x hx y hy h
      simp only [Finset.mem_coe] at hx hy 
      simp only [dif_pos hx, dif_pos hy]
      apply commute_ofSubtype_disjoint
      simp only [Set.mem_setOf_eq, not_and]
      intro a h' h''; apply h; rw [← h', ← h'']
#align equiv.perm.of_partition Equiv.Perm.ofPartition

theorem Equiv.Perm.of_partition_coe_apply' {ι : Type _} [DecidableEq ι] (p : α → ι) (s : Finset ι)
    (u : ∀ i ∈ s, Equiv.Perm {x | p x = i}) (i : ι) (a : {x : α | p x = i}) :
    Equiv.Perm.ofPartitionFun p s u (a : α) = dite (i ∈ s) (fun hi => (u i hi) a) fun hi => a :=
  by
  simp only [Equiv.Perm.ofPartitionFun]
  induction' s using Finset.induction with j s hj ih
  -- empty
  simp only [Finset.noncommProd_empty, Equiv.Perm.coe_one, id.def, Finset.not_mem_empty, if_false]
  rw [dif_neg id]
  · -- insert
    rw [Finset.noncommProd_insert_of_not_mem s j _ _ hj]
    rw [Equiv.Perm.mul_apply]
    simp only [dif_pos (Finset.mem_insert_self j s)]
    split_ifs with h
    · rw [Finset.mem_insert] at h 
      cases' h with h1 h2
      · subst h1
        suffices : Equiv.Perm.ofSubtype (u i h) a = (u i h) a
        rw [← this]
        apply congr_arg
        specialize ih fun i hi => u i (Finset.mem_insert_of_mem hi)
        simp only [dif_neg hj] at ih 
        conv_rhs => rw [← ih]
        apply congr_arg₂ _ _ rfl
        apply Finset.noncommProd_congr rfl
        · intro k hk
          simp only [dif_pos hk, dif_pos (Finset.mem_insert_of_mem hk)]
        · rw [Equiv.Perm.ofSubtype_apply_of_mem]
          simp only [Subtype.coe_eta]; exact a.prop
      · specialize ih fun i hi => u i (Finset.mem_insert_of_mem hi)
        simp only [dif_pos h2] at ih 
        suffices : ∀ h' : j ∈ insert j s, Equiv.Perm.ofSubtype (u j h') ((u i h) a) = (u i h) a
        rw [← this _]
        apply congr_arg
        rw [← ih]
        apply congr_arg₂ _ _ rfl
        apply Finset.noncommProd_congr rfl
        · intro k hk
          simp only [dif_pos hk, dif_pos (Finset.mem_insert_of_mem hk)]
        · intro h'
          rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
          simp only [Set.mem_setOf_eq]; intro h''
          suffices : p ((u i h) a) = i
          apply hj; rw [← h'']; rw [this]; exact h2
          exact (u i h a).Prop
    · specialize ih fun i hi => u i (Finset.mem_insert_of_mem hi)
      simp only [Finset.mem_insert, not_or] at h 
      simp only [dif_neg h.2] at ih 
      suffices : ∀ h' : j ∈ insert j s, Equiv.Perm.ofSubtype (u j h') a = a
      convert this _
      conv_rhs => rw [← ih]
      apply congr_arg₂ _ _ rfl
      apply Finset.noncommProd_congr rfl
      · intro k hk
        simp only [dif_pos hk, dif_pos (Finset.mem_insert_of_mem hk)]
      · intro h'
        rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
        simp only [Set.mem_setOf_eq]
        intro h'
        suffices : p a = i; apply h.1
        rw [← h']; rw [this]
        exact a.prop
#align equiv.perm.of_partition_coe_apply' Equiv.Perm.of_partition_coe_apply'

theorem Equiv.Perm.ofPartition_coe_apply {ι : Type _} [Fintype ι] [DecidableEq ι] {p : α → ι}
    (u : ∀ i, Equiv.Perm {x | p x = i}) (i : ι) (a : {x : α | p x = i}) :
    Equiv.Perm.ofPartition p u (a : α) = (u i) a :=
  by
  dsimp [Equiv.Perm.ofPartition]
  rw [Equiv.Perm.of_partition_coe_apply' p Finset.univ fun i h => u i]
  simp only [dif_pos (Finset.mem_univ i)]
#align equiv.perm.of_partition_coe_apply Equiv.Perm.ofPartition_coe_apply

theorem Equiv.Perm.ofPartition_inj {ι : Type _} [Fintype ι] [DecidableEq ι] (p : α → ι) :
    Function.Injective (Equiv.Perm.ofPartition p) :=
  by
  intro u v h
  ext i a
  rw [← Equiv.Perm.ofPartition_coe_apply]
  rw [h]
  rw [Equiv.Perm.ofPartition_coe_apply]
#align equiv.perm.of_partition_inj Equiv.Perm.ofPartition_inj

theorem Equiv.Perm.ofPartition_range {ι : Type _} [Fintype ι] [DecidableEq ι] (p : α → ι)
    (f : Equiv.Perm α) : f ∈ (Equiv.Perm.ofPartition p).range ↔ p ∘ f = p :=
  by
  constructor
  · rintro ⟨u, rfl⟩
    ext a
    simp only [Function.comp_apply]
    have ha : a ∈ {x : α | p x = p a}; rw [Set.mem_setOf_eq]
    have : a = (⟨a, ha⟩ : {x : α | p x = p a}) := (Subtype.coe_mk a ha).symm
    rw [this]
    rw [Equiv.Perm.ofPartition_coe_apply]
    simp only [Subtype.coe_mk]
    exact (u (p a) ⟨a, ha⟩).Prop
  · intro h
    have h' : ∀ i a, a ∈ {x | p x = i} ↔ f a ∈ {x | p x = i} :=
      by
      intro i a; simp only [Set.mem_setOf_eq]
      rw [← Function.comp_apply p f a]; rw [h]
    let g : ∀ i, Equiv.Perm {x | p x = i} := fun i => f.subtype_perm (h' i)
    use g
    ext a
    have ha : a ∈ {x | p x = p a}; rw [Set.mem_setOf_eq]
    have : a = (⟨a, ha⟩ : {x : α | p x = p a}) := (Subtype.coe_mk a ha).symm
    rw [this]
    rw [Equiv.Perm.ofPartition_coe_apply]
    simp only [g]
    rw [Equiv.Perm.subtypePerm_apply]
    rfl
#align equiv.perm.of_partition_range Equiv.Perm.ofPartition_range

theorem Equiv.Perm.of_partition_card {ι : Type _} [Fintype ι] [DecidableEq ι] (p : α → ι) :
    Fintype.card {f : Equiv.Perm α | p ∘ f = p} =
      Finset.prod (⊤ : Finset ι) fun i => (Fintype.card {a | p a = i}).factorial :=
  by
  let φ := Equiv.Perm.ofPartition p
  let hφ_inj := Equiv.Perm.ofPartition_inj p
  let hφ_range := Equiv.Perm.ofPartition_range p
  suffices :
    Fintype.card (∀ i : ι, Equiv.Perm {a | p a = i}) = Fintype.card {f : Equiv.Perm α | p ∘ f = p}
  rw [← this]
  simp only [Fintype.card_pi, Set.coe_setOf, Finset.top_eq_univ, Fintype.card_perm]
  · rw [Fintype.card_eq]
    let φ' : (∀ i : ι, Equiv.Perm {a | p a = i}) → {f : Equiv.Perm α | p ∘ f = p} := fun u =>
      ⟨φ u, by
        simp only [Set.mem_setOf_eq]
        rw [← hφ_range _]; use u⟩
    have hφ' : Function.Bijective φ' := by
      constructor
      · -- injectivity
        intro u v
        simp only [φ', Subtype.mk_eq_mk]
        apply hφ_inj
      · -- surjectivity
        rintro ⟨f, hf⟩
        simp only [φ', Subtype.mk_eq_mk, ← MonoidHom.mem_range, hφ_range f]
        exact hf
    use Equiv.ofBijective φ' hφ'
#align equiv.perm.of_partition_card Equiv.Perm.of_partition_card

end CycleTypes

namespace OnCycleFactors

variable {α : Type _} [DecidableEq α] [Fintype α] (g : Equiv.Perm α)

theorem centralizer_le_stab_cycle_fact :
    MulAction.stabilizer (ConjAct (Equiv.Perm α)) g ≤
      MulAction.stabilizer (ConjAct (Equiv.Perm α)) (g.cycleFactorsFinset : Set (Equiv.Perm α)) :=
  by
  intro k
  simp only [MulAction.mem_stabilizer_iff]
  intro hk
  rw [← Finset.coe_smul_finset k _, ← Equiv.Perm.mem_cycle_factors_conj_eq, hk]
#align on_cycle_factors.centralizer_le_stab_cycle_fact OnCycleFactors.centralizer_le_stab_cycle_fact

/- instance mul_action_on_cycle_factors
/-   mul_action (mul_action.stabilizer (conj_act (equiv.perm α)) g)
  ((g.cycle_factors_finset) : set (equiv.perm α)) -/
:= (sub_mul_action_of_stabilizer
  (conj_act (equiv.perm α))
  ((g.cycle_factors_finset) : set (equiv.perm α))).mul_action
-/
def subMulActionOnCycleFactors :
    SubMulAction (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) (Equiv.Perm α)
    where
  carrier := (g.cycleFactorsFinset : Set (Equiv.Perm α))
  smul_mem' k c hc := by
    have := Equiv.Perm.mem_cycle_factors_conj_eq (↑k) g
    rw [mul_action.mem_stabilizer_iff.mp k.prop] at this 
    rw [this, Finset.coe_smul_finset]
    exact ⟨c, hc, rfl⟩
#align on_cycle_factors.sub_mul_action_on_cycle_factors OnCycleFactors.subMulActionOnCycleFactors

instance mulActionOnCycleFactors :
    MulAction (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
      (g.cycleFactorsFinset : Set (Equiv.Perm α)) :=
  (subMulActionOnCycleFactors g).MulAction
#align on_cycle_factors.mul_action_on_cycle_factors OnCycleFactors.mulActionOnCycleFactors

def φ :=
  MulAction.toPermHom (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (g.cycleFactorsFinset : Set (Equiv.Perm α))
#align on_cycle_factors.φ OnCycleFactors.φ

theorem φ_eq :
    ∀ (k : ConjAct (Equiv.Perm α)) (hk : k ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
      (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset),
      (φ g ⟨k, hk⟩ ⟨c, hc⟩ : Equiv.Perm α) = k • c :=
  by
  intro k hk c hc
  simp only [φ]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulAction.toPermHom_apply,
    MulAction.toPerm_apply]
  rfl
#align on_cycle_factors.φ_eq OnCycleFactors.φ_eq

theorem φ_eq' :
    ∀ (k : Equiv.Perm α) (hk : k ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
      (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset),
      (φ g ⟨ConjAct.toConjAct k, hk⟩ ⟨c, hc⟩ : Equiv.Perm α) = k * c * k⁻¹ :=
  by
  intro k hk c hc
  simp only [φ]
  rfl
#align on_cycle_factors.φ_eq' OnCycleFactors.φ_eq'

/-
lemma mem_range_φ (k : equiv.perm (g.cycle_factors_finset)) :
  k ∈ (φ g).range ↔ ∀ (c : g.cycle_factors_finset), (k c: equiv.perm α).support.card = (c : equiv.perm α).support.card :=
begin
  split,
  { simp only [monoid_hom.coe_range, monoid_hom.mem_range],
    rintro ⟨⟨k, hk⟩, rfl⟩,
    rintro ⟨c, hc⟩,
    simp only [function.comp_app, φ_eq, subtype.coe_mk],
    simp_rw conj_act.smul_def,
    simp only [equiv.perm.support_conj, finset.card_map], },
  { intro hk,
    obtain ⟨a, k1, _, hk1, hk2, _⟩ := is_surjective_aux g k _,
    use k1,
    { -- mem_stabilizer
      simp only [mul_action.mem_stabilizer_iff],
      simp only [has_smul.smul],
      change k1 * g * k1⁻¹ = g,
      simp only [← hk1, mul_inv_cancel_right], },
    { ext ⟨c, hc⟩ x,
      rw [φ_eq, ← hk2 ⟨c, hc⟩],
      refl, },
    exact λ c, (hk c).symm, },
end
 -/
/- lemma hφ_range : ((φ g).range : set (equiv.perm (g.cycle_factors_finset :
  set (equiv.perm α)))) = { k : equiv.perm (g.cycle_factors_finset) |
  ∀ (c : g.cycle_factors_finset), (k c: equiv.perm α).support.card = (c : equiv.perm α).support.card } :=
begin
  ext k,
  simp only [set_like.mem_coe, mem_range_φ],
  refl,
end
 -/
variable {g}

variable (a : g.cycleFactorsFinset → α)
  (ha : ∀ c : g.cycleFactorsFinset, a c ∈ (c : Equiv.Perm α).support)

variable {a}

theorem SameCycle.is_cycleOf (c : g.cycleFactorsFinset) {x} (hx : g.SameCycle (a c) x) :
    g.cycleOf x = c := by
  rw [Equiv.Perm.cycle_is_cycleOf (ha c) c.prop, Equiv.Perm.SameCycle.cycleOf_eq hx]
#align on_cycle_factors.same_cycle.is_cycle_of OnCycleFactors.SameCycle.is_cycleOf

theorem sameCycle_of_mem_support_iff (c : g.cycleFactorsFinset) {x} (hx : x ∈ g.support) :
    g.cycleOf x = c ↔ g.SameCycle (a c) x :=
  by
  rw [Equiv.Perm.cycle_is_cycleOf (ha c) c.prop]
  constructor
  · intro hx'
    apply And.left
    rw [← Equiv.Perm.mem_support_cycleOf_iff]
    rw [← hx']
    rw [Equiv.Perm.mem_support]
    rw [Equiv.Perm.cycleOf_apply_self]
    rw [← Equiv.Perm.mem_support]
    exact hx
  · intro hx; rw [same_cycle.is_cycle_of ha c hx]
    rw [Equiv.Perm.cycle_is_cycleOf (ha c) c.prop]
#align on_cycle_factors.same_cycle_of_mem_support_iff OnCycleFactors.sameCycle_of_mem_support_iff

theorem sameCycle_of_mem_support :
    ∀ x ∈ g.support, ∃ c : g.cycleFactorsFinset, g.SameCycle (a c) x :=
  by
  intro x hx
  have hcx : g.cycle_of x ∈ g.cycle_factors_finset :=
    equiv.perm.cycle_of_mem_cycle_factors_finset_iff.mpr hx
  use ⟨g.cycle_of x, hcx⟩
  rw [← same_cycle_of_mem_support_iff ha _ hx]
  rfl
#align on_cycle_factors.same_cycle_of_mem_support OnCycleFactors.sameCycle_of_mem_support

variable (a) {g}

def kf : Equiv.Perm g.cycleFactorsFinset → g.cycleFactorsFinset × ℤ → α := fun e ⟨c, i⟩ =>
  (g ^ i) (a (e c))
#align on_cycle_factors.Kf OnCycleFactors.kf

theorem kf_apply {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i : ℤ} :
    kf a e ⟨c, i⟩ = (g ^ i) (a (e c)) :=
  rfl
#align on_cycle_factors.Kf_apply OnCycleFactors.kf_apply

theorem kf_apply' {e e' : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i j : ℤ} :
    kf a (e' * e) ⟨c, i + j⟩ = (g ^ i) (kf a e' ⟨e c, j⟩) := by
  simp only [Kf_apply, zpow_add, Equiv.Perm.coe_mul]
#align on_cycle_factors.Kf_apply' OnCycleFactors.kf_apply'

variable {a}

theorem ha' (c : g.cycleFactorsFinset) : g.cycleOf (a c) = (c : Equiv.Perm α) :=
  (Equiv.Perm.cycle_is_cycleOf (ha c) c.Prop).symm
#align on_cycle_factors.ha' OnCycleFactors.ha'

-- was ha
theorem ha'2 (c : g.cycleFactorsFinset) : g (a c) ≠ a c :=
  by
  rw [← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, ha' ha c]
  exact c.prop
#align on_cycle_factors.ha'2 OnCycleFactors.ha'2

-- was ha''
theorem ha'3 (c : g.cycleFactorsFinset) (i : ℤ) : g.cycleOf ((g ^ i) (a c)) = c := by
  rw [Equiv.Perm.cycleOf_self_apply_zpow, ha' ha]
#align on_cycle_factors.ha'3 OnCycleFactors.ha'3

theorem haK1
    -- was haK
    (e : Equiv.Perm g.cycleFactorsFinset)
    (c : g.cycleFactorsFinset) (i : ℤ) : g.cycleOf (kf a e ⟨c, i⟩) = e c := by
  rw [Kf_apply, Equiv.Perm.cycleOf_self_apply_zpow,
    Equiv.Perm.cycle_is_cycleOf (ha (e c)) (e c).Prop]
#align on_cycle_factors.haK1 OnCycleFactors.haK1

theorem haK2 (e : Equiv.Perm g.cycleFactorsFinset) (c : g.cycleFactorsFinset) (i : ℤ) :
    g (kf a e ⟨c, i⟩) = kf a e ⟨c, i + 1⟩ := by
  rw [Kf_apply, Kf_apply, ← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm 1 i]
#align on_cycle_factors.haK2 OnCycleFactors.haK2

theorem haK3 (e : Equiv.Perm g.cycleFactorsFinset) (c d : g.cycleFactorsFinset) (i : ℤ)
    (hd : d = e c) : d (kf a e ⟨c, i⟩) = kf a e ⟨c, i + 1⟩ :=
  by
  -- Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) appartient au cycle de e c
  rw [hd]
  change (e c : Equiv.Perm α) _ = _
  rw [← haK1 ha e c i, Equiv.Perm.cycleOf_apply_self, haK2 ha]
#align on_cycle_factors.haK3 OnCycleFactors.haK3

theorem haK4 (e : Equiv.Perm g.cycleFactorsFinset) (c d : g.cycleFactorsFinset) (i : ℤ)
    (hd' : d ≠ e c) : d (kf a e ⟨c, i⟩) = kf a e ⟨c, i⟩ :=
  by
  suffices hdc : (d : Equiv.Perm α).Disjoint (e c : Equiv.Perm α)
  apply Or.resolve_right (equiv.perm.disjoint_iff_eq_or_eq.mp hdc (Kf a e ⟨c, i⟩))
  rw [← haK1 ha e c i]
  rw [Equiv.Perm.cycleOf_apply_self]
  rw [← Equiv.Perm.cycleOf_eq_one_iff]
  rw [haK1 ha e c i]
  apply Equiv.Perm.IsCycle.ne_one
  refine' (equiv.perm.mem_cycle_factors_finset_iff.mp _).1
  exact g
  exact (e c).Prop
  apply g.cycle_factors_finset_pairwise_disjoint d.prop (e c).Prop
  rw [Function.Injective.ne_iff Subtype.coe_injective]
  exact hd'
#align on_cycle_factors.haK4 OnCycleFactors.haK4

theorem haK5 (τ : Equiv.Perm g.cycleFactorsFinset) (x : α)
    (hx : ¬∃ cj : g.cycleFactorsFinset × ℤ, kf a 1 cj = x) :
    Function.extend (kf a 1) (kf a τ) id x = x := by
  simp only [Function.extend_apply' _ _ _ hx, id.def]
#align on_cycle_factors.haK5 OnCycleFactors.haK5

theorem haK6 (x : α) (hx : x ∉ g.support) (c : g.cycleFactorsFinset) : c x = x :=
  by
  change (c : Equiv.Perm α) x = x
  rw [← Equiv.Perm.not_mem_support]
  intro hx'
  exact hx (Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hx')
#align on_cycle_factors.haK6 OnCycleFactors.haK6

/-
lemma haK6 (x : α)
  (hx : ¬ (∃ (cj : g.cycle_factors_finset × ℤ), Kf a 1 cj = x))
  (c : g.cycle_factors_finset) : c x = x :=
begin
  by_contradiction, apply hx,
  suffices h' : x ∈ (c : equiv.perm α).support,
  suffices : g.same_cycle (a c) x,
  { obtain ⟨i, hi⟩ := this,
    use ⟨c, i⟩,
    rw [Kf_apply, ← hi, equiv.perm.coe_one, id.def], },

  apply and.left,
  rw ← equiv.perm.mem_support_cycle_of_iff,
  rw ha' ha c,
  exact h',

  rw equiv.perm.mem_support, exact h,
end
-/
theorem hkfg (e e' : Equiv.Perm g.cycleFactorsFinset)
    (hee' :
      ∀ c : g.cycleFactorsFinset,
        (e c : Equiv.Perm α).support.card = (e' c : Equiv.Perm α).support.card) :
    (kf a e').FactorsThrough (kf a e) :=
  by
  --    Kf e ci = Kf e dj → Kf e' ci = Kf e' dj,
  rintro ⟨c, i⟩ ⟨d, j⟩ He
  change (g ^ i) (a (e c)) = (g ^ j) (a (e d)) at He 
  change (g ^ i) (a (e' c)) = (g ^ j) (a (e' d))
  suffices hcd : c = d
  · rw [hcd] at He ⊢
    rw [g.zpow_eq_zpow_on_iff i j, ha' ha] at He 
    rw [g.zpow_eq_zpow_on_iff, ha' ha, ← hee' d]
    exact He
    · exact ha'2 ha (e' d)
    · exact ha'2 ha (e d)
  · -- d = c
    apply Equiv.injective e
    rw [← Subtype.coe_inj, ← ha'3 ha (e c) i, ← ha'3 ha (e d) j, He]
#align on_cycle_factors.hkfg OnCycleFactors.hkfg

variable (a)

noncomputable def k := fun τ => Function.extend (kf a 1) (kf a τ) id
#align on_cycle_factors.k OnCycleFactors.k

variable {a}

theorem k_apply (c : g.cycleFactorsFinset) (i : ℤ) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (kf a 1 ⟨c, i⟩) = kf a τ ⟨c, i⟩ :=
  by
  simp only [k]
  rw [Function.FactorsThrough.extend_apply (hkfg ha 1 τ _) id ⟨c, i⟩]
  · intro c; simp only [← hτ c, Equiv.Perm.coe_one, id.def]
#align on_cycle_factors.k_apply OnCycleFactors.k_apply

theorem k_apply_base (c : g.cycleFactorsFinset) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (a c) = a (τ c) :=
  k_apply ha c 0 hτ
#align on_cycle_factors.k_apply_base OnCycleFactors.k_apply_base

-- was k_apply'
theorem k_apply_of_not_mem_support {τ : Equiv.Perm g.cycleFactorsFinset} (x : α)
    (hx : x ∉ g.support) : k a τ x = x := by
  simp only [k]
  rw [Function.extend_apply']
  simp only [id.def]
  intro hyp
  obtain ⟨⟨c, i⟩, rfl⟩ := hyp
  apply hx
  change (g ^ i) (a c) ∈ g.support
  rw [Equiv.Perm.zpow_apply_mem_support]
  rw [Equiv.Perm.mem_support]
  exact ha'2 ha c
#align on_cycle_factors.k_apply_of_not_mem_support OnCycleFactors.k_apply_of_not_mem_support

theorem mem_support_iff_exists_kf (x : α) :
    x ∈ g.support ↔ ∃ (c : g.cycleFactorsFinset) (i : ℤ), x = kf a 1 ⟨c, i⟩ :=
  by
  constructor
  · intro hx
    rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff] at hx 
    use ⟨g.cycle_of x, hx⟩
    simp only [Kf_apply, Equiv.Perm.coe_one, id.def]
    specialize ha ⟨g.cycle_of x, hx⟩
    simp only [Subtype.coe_mk, Equiv.Perm.mem_support_cycleOf_iff] at ha 
    obtain ⟨i, hi⟩ := ha.1.symm; use i; exact hi.symm
  · rintro ⟨c, i, rfl⟩
    simp only [Kf_apply, Equiv.Perm.zpow_apply_mem_support, Equiv.Perm.coe_one, id.def]
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop
    exact ha c
#align on_cycle_factors.mem_support_iff_exists_Kf OnCycleFactors.mem_support_iff_exists_kf

theorem k_commute_zpow {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) (j : ℤ) :
    k a τ ∘ (g ^ j : Equiv.Perm α) = (g ^ j : Equiv.Perm α) ∘ k a τ :=
  by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · rw [mem_support_iff_exists_Kf ha] at hx 
    obtain ⟨c, i, rfl⟩ := hx
    suffices : ∀ e, Kf a e (c, j + i) = (g ^ j) (Kf a e (c, i))
    rw [← this 1]
    rw [k_apply ha c (j + i) hτ]
    rw [k_apply ha c i hτ]
    rw [← this τ]
    · intro e
      simpa only [mul_one, Equiv.Perm.coe_one, id.def] using @Kf_apply' _ _ _ g a 1 e c j i
  · rw [k_apply_of_not_mem_support ha x hx]
    rw [k_apply_of_not_mem_support ha ((g ^ j : Equiv.Perm α) x) _]
    rw [Equiv.Perm.zpow_apply_mem_support]
    exact hx
#align on_cycle_factors.k_commute_zpow OnCycleFactors.k_commute_zpow

theorem k_commute {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ ∘ g = g ∘ k a τ := by simpa only [zpow_one] using k_commute_zpow ha hτ 1
#align on_cycle_factors.k_commute OnCycleFactors.k_commute

theorem k_apply_gen (c : g.cycleFactorsFinset) (i : ℤ) {σ : Equiv.Perm g.cycleFactorsFinset}
    (hσ : ∀ c, (σ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card)
    {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (kf a σ ⟨c, i⟩) = kf a (τ * σ) ⟨c, i⟩ :=
  by
  simp only [Kf_apply]
  rw [← Function.comp_apply (k a τ)]
  rw [k_commute_zpow ha hτ]
  rw [Function.comp_apply]
  apply congr_arg
  dsimp
  suffices : ∀ (d) (τ : Equiv.Perm g.cycle_factors_finset), a (τ d) = Kf a 1 (τ d, 0)
  rw [this _ σ, k_apply ha (σ c) 0 hτ, ← Function.comp_apply τ σ c, ← Equiv.Perm.coe_mul,
    this _ (τ * σ)]
  rfl
  · intro d τ; rw [Kf_apply]; rfl
#align on_cycle_factors.k_apply_gen OnCycleFactors.k_apply_gen

theorem k_mul (σ : Equiv.Perm g.cycleFactorsFinset)
    (hσ : ∀ c, (σ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card)
    (τ : Equiv.Perm g.cycleFactorsFinset)
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a σ ∘ k a τ = k a (σ * τ) := by
  ext x
  simp only [Function.comp_apply]
  suffices hστ : ∀ c, ((σ * τ) c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf ha] at hx 
    obtain ⟨c, i, rfl⟩ := hx
    simp only [k_apply ha c i hτ, k_apply_gen ha c i hτ hσ, k_apply ha c i hστ]
  · simp only [k_apply_of_not_mem_support ha x hx]
  · intro c; rw [Equiv.Perm.coe_mul, Function.comp_apply, hσ, hτ]
#align on_cycle_factors.k_mul OnCycleFactors.k_mul

theorem k_one : k a 1 = id := by
  ext x
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf ha] at hx 
    obtain ⟨c, i, rfl⟩ := hx
    rw [k_apply ha c i]; rfl
    intro c; rfl
  simp only [id.def, k_apply_of_not_mem_support ha x hx]
#align on_cycle_factors.k_one OnCycleFactors.k_one

theorem k_bij {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    Function.Bijective (k a τ) :=
  by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine' And.intro _ rfl
  rw [Function.surjective_iff_hasRightInverse]
  use k a τ⁻¹
  rw [Function.rightInverse_iff_comp]
  rw [k_mul ha]; rw [mul_inv_self]; rw [k_one ha]
  exact hτ
  intro c; rw [← hτ (τ⁻¹ c), Equiv.Perm.apply_inv_self]
#align on_cycle_factors.k_bij OnCycleFactors.k_bij

theorem k_cycle_apply {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card)
    (c : g.cycleFactorsFinset) (x : α) : k a τ (c x) = (τ c) (k a τ x) :=
  by
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf ha] at hx 
    obtain ⟨d, j, rfl⟩ := hx
    by_cases hcd : c = d
    · rw [hcd]; rw [haK3 ha]; rw [k_apply ha _ _ hτ]
      dsimp
      rw [k_apply ha _ _ hτ]
      dsimp
      rw [← haK3 ha τ d (τ d) j rfl]
      simp only [Equiv.Perm.coe_one, id.def]
    · rw [haK4 ha]
      rw [k_apply ha _ _ hτ]
      dsimp
      rw [haK4 ha τ d (τ c) j _]
      rw [Function.Injective.ne_iff (Equiv.injective τ)]; exact hcd
      simpa only [Equiv.Perm.coe_one, id.def, Ne.def] using hcd
  · simp only [haK6 ha x hx, k_apply_of_not_mem_support ha x hx]
#align on_cycle_factors.k_cycle_apply OnCycleFactors.k_cycle_apply

theorem hφ_eq_card_of_mem_range {τ} (hτ : τ ∈ (φ g).range) :
    ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card :=
  by
  rintro ⟨c, hc⟩
  obtain ⟨⟨k, hk⟩, rfl⟩ := hτ
  simp only [φ_eq, Subtype.coe_mk, ConjAct.smul_def, Equiv.Perm.support_conj, Finset.card_map]
#align on_cycle_factors.hφ_eq_card_of_mem_range OnCycleFactors.hφ_eq_card_of_mem_range

noncomputable def φ'Fun {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    Equiv.Perm α :=
  Equiv.ofBijective (k a τ) (k_bij ha hτ)
#align on_cycle_factors.φ'_fun OnCycleFactors.φ'Fun

theorem φ'_mem_stabilizer {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    ConjAct.toConjAct (φ'Fun ha hτ) ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g :=
  by
  rw [MulAction.mem_stabilizer_iff]
  rw [ConjAct.smul_def]
  rw [ConjAct.ofConjAct_toConjAct]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Equiv.Perm.coe_mul]
  simp only [φ'_fun]
  simp only [Function.comp_apply, Equiv.ofBijective_apply]
  rw [← Function.comp_apply (k a τ)]
  rw [k_commute ha hτ]
#align on_cycle_factors.φ'_mem_stabilizer OnCycleFactors.φ'_mem_stabilizer

variable (g)

def iφ : Subgroup (Equiv.Perm g.cycleFactorsFinset)
    where
  carrier := {τ | ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_one, id.def, eq_self_iff_true, imp_true_iff]
  mul_mem' σ τ hσ hτ :=
    by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_mul, Function.comp_apply] at hσ hτ ⊢
    intro c
    rw [hσ]; rw [hτ]
  inv_mem' σ hσ :=
    by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_mul, Function.comp_apply] at hσ ⊢
    intro c
    rw [← hσ (σ⁻¹ c)]
    simp only [Equiv.Perm.apply_inv_self]
#align on_cycle_factors.Iφ OnCycleFactors.iφ

variable {g}

theorem mem_iφ_iff {τ : Equiv.Perm g.cycleFactorsFinset} :
    τ ∈ iφ g ↔ ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  simp only [Iφ]; rfl
#align on_cycle_factors.mem_Iφ_iff OnCycleFactors.mem_iφ_iff

noncomputable def φ' : iφ g →* MulAction.stabilizer (ConjAct (Equiv.Perm α)) g
    where
  toFun τhτ :=
    ⟨ConjAct.toConjAct (φ'Fun ha (mem_iφ_iff.mp τhτ.Prop)),
      φ'_mem_stabilizer ha (mem_iφ_iff.mp τhτ.Prop)⟩
  map_one' :=
    by
    simp only [Subgroup.coe_one, Subgroup.mk_eq_one_iff, MulEquivClass.map_eq_one_iff]
    ext x
    simp only [φ'_fun, k_one ha, Subtype.val_eq_coe, Subgroup.coe_one, Equiv.ofBijective_apply,
      Equiv.Perm.coe_one]
  map_mul' σ τ :=
    by
    simp only [Subgroup.coe_mul, Submonoid.mk_mul_mk, Subtype.mk_eq_mk, ← ConjAct.toConjAct_mul]
    apply congr_arg
    ext x
    simp only [φ'_fun, Equiv.ofBijective_apply, Subtype.val_eq_coe, Subgroup.coe_mul,
      Equiv.Perm.coe_mul, Function.comp_apply, ← k_mul ha _ σ.prop _ τ.prop]
#align on_cycle_factors.φ' OnCycleFactors.φ'

theorem hφ'_is_right_inverse : ∀ τ, (φ g) ((φ' ha) τ) = (τ : Equiv.Perm g.cycleFactorsFinset) :=
  by
  rintro ⟨τ, hτ⟩
  apply Equiv.Perm.ext
  rintro ⟨c, hc⟩
  simp only [φ', φ'_fun]; dsimp
  ext x
  rw [φ_eq g]
  rw [ConjAct.smul_def]; simp only [ConjAct.ofConjAct_toConjAct]
  apply congr_fun
  dsimp
  simp only [← Equiv.Perm.coe_mul]
  apply congr_arg
  rw [mul_inv_eq_iff_eq_mul]
  ext y
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.ofBijective_apply]
  exact k_cycle_apply ha hτ ⟨c, hc⟩ y
#align on_cycle_factors.hφ'_is_right_inverse OnCycleFactors.hφ'_is_right_inverse

theorem φ'_apply {τ} (hτ) (x) :
    (ConjAct.ofConjAct (φ' ha ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))) x = k a τ x :=
  rfl
#align on_cycle_factors.φ'_apply OnCycleFactors.φ'_apply

theorem coe_φ' {τ} (hτ) : k a τ = ConjAct.ofConjAct (φ' ha ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α)) :=
  rfl
#align on_cycle_factors.coe_φ' OnCycleFactors.coe_φ'

example (τ) (hτ) : Commute (ConjAct.ofConjAct (φ' ha ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))) g :=
  by
  rw [Commute, SemiconjBy]
  --  simp only [φ', φ'_fun],
  --  simp only [subgroup.coe_mk, monoid_hom.coe_mk, conj_act.of_conj_act_to_conj_act],
  -- simp only [equiv.perm.mul_def],
  rw [← Equiv.coe_inj]
  --  simp only [equiv.coe_trans],
  -- change (k a τ) ∘ g = g ∘ (k a τ),
  exact k_commute ha hτ

example (τ) (hτ) : Commute (ConjAct.ofConjAct (φ' ha ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))) g :=
  by
  rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
  rw [← MulAction.ConjAct.mem_stabilizer_iff]
  exact ((φ' ha) ⟨τ, hτ⟩).Prop

example (τ) (hτ) :
    (ConjAct.ofConjAct (φ' ha ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))).support ≤ g.support :=
  by
  intro x
  simp only [Equiv.Perm.mem_support, φ'_apply]
  intro hx' hx; apply hx'
  rw [← Equiv.Perm.not_mem_support] at hx 
  exact k_apply_of_not_mem_support ha x hx

example (τ) (hτ) : ConjAct.ofConjAct (φ' ha ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α)) ∘ a = a ∘ τ :=
  by
  ext c
  exact k_apply ha c 0 hτ

example (τ) (hτ) :
    ∀ c : g.cycleFactorsFinset,
      ConjAct.toConjAct (ConjAct.ofConjAct (φ' ha ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))) •
          (c : Equiv.Perm α) =
        τ c :=
  by
  intro c
  rw [ConjAct.toConjAct_ofConjAct]
  simp only [φ', φ'_fun]
  simp only [Subgroup.coe_mk, MonoidHom.coe_mk]
  rw [ConjAct.smul_def]
  simp only [ConjAct.ofConjAct_toConjAct]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  exact k_cycle_apply ha hτ c x

example (u v : Equiv.Perm α) (x : α) : u (v x) = (u * v) x := by rfl

example (τ) (hτ) (c : g.cycleFactorsFinset) (m n : ℕ) :
    (ConjAct.ofConjAct (φ' ha ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α)) ^ m)
        ((g ^ n : Equiv.Perm α) (a c)) =
      (g ^ n) (a ((τ ^ m) c)) :=
  by
  suffices :
    ∀ m n : ℕ, Commute (ConjAct.ofConjAct (φ' ha ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α)) ^ m) (g ^ n)
  simp only [Commute, SemiconjBy] at this 
  rw [← Equiv.Perm.mul_apply, this, Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq]
  induction' m with m hrec
  · simp only [pow_zero, Equiv.Perm.coe_one, id.def]
  · rw [pow_succ, Equiv.Perm.mul_apply]
    rw [hrec]
    rw [φ'_apply ha hτ]
    rw [k_apply_base ha _ hτ]; rw [pow_succ]; rw [Equiv.Perm.coe_mul]
  apply Commute.pow_pow
  rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
  rw [← MulAction.ConjAct.mem_stabilizer_iff]
  exact ((φ' ha) ⟨τ, hτ⟩).Prop

variable (g)

theorem exists_base_points :
    ∃ a : g.cycleFactorsFinset → α, ∀ c, a c ∈ (c : Equiv.Perm α).support :=
  by
  suffices hsupp_ne : ∀ c : g.cycle_factors_finset, (c : Equiv.Perm α).support.Nonempty
  use fun c => (hsupp_ne c).some
  intro c; exact (hsupp_ne c).choose_spec
  · intro c
    exact Equiv.Perm.support_of_cycle_nonempty (equiv.perm.mem_cycle_factors_finset_iff.mp c.prop).1
#align on_cycle_factors.exists_base_points OnCycleFactors.exists_base_points

variable {g}

theorem iφ_eq_range : iφ g = (φ g).range :=
  by
  obtain ⟨a, ha⟩ := exists_base_points g
  ext τ
  constructor
  · intro hτ; rw [MonoidHom.mem_range]
    use (φ' ha) ⟨τ, hτ⟩
    rw [hφ'_is_right_inverse, Subgroup.coe_mk]
  · rw [mem_Iφ_iff]; exact hφ_eq_card_of_mem_range
#align on_cycle_factors.Iφ_eq_range OnCycleFactors.iφ_eq_range

theorem hφ_mem_range_iff {τ} :
    τ ∈ (φ g).range ↔ ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  simp only [← Iφ_eq_range, mem_Iφ_iff]; rfl
#align on_cycle_factors.hφ_mem_range_iff OnCycleFactors.hφ_mem_range_iff

-- To get an automatic fintype instance, we view the lengths of the cycle to the fintype `fin (fintype.card α + 1)`
/-- The lengths of the cycles, as a fintype -/
def fsc : g.cycleFactorsFinset → Fin (Fintype.card α + 1) := fun c =>
  ⟨(c : Equiv.Perm α).support.card, Nat.lt_succ_iff.mpr (c : Equiv.Perm α).support.card_le_univ⟩
#align on_cycle_factors.fsc OnCycleFactors.fsc

theorem hφ_range' :
    ((φ g).range : Set (Equiv.Perm (g.cycleFactorsFinset : Set (Equiv.Perm α)))) =
      {τ : Equiv.Perm g.cycleFactorsFinset | fsc ∘ τ = fsc} :=
  by
  rw [← Iφ_eq_range]
  ext τ
  simp only [SetLike.mem_coe, mem_Iφ_iff]
  change _ ↔ fsc ∘ τ = fsc
  simp only [fsc]
  rw [Function.funext_iff]
  dsimp
  apply forall_congr'
  intro c
  rw [← Function.Injective.eq_iff Fin.val_injective]
  simp only [Fin.val_mk]
#align on_cycle_factors.hφ_range' OnCycleFactors.hφ_range'

theorem hφ_range_card' :
    Fintype.card (φ g).range = Fintype.card {k : Equiv.Perm g.cycleFactorsFinset | fsc ∘ k = fsc} :=
  by
  simp_rw [← hφ_range']
  simp only [SetLike.coe_sort_coe]
#align on_cycle_factors.hφ_range_card' OnCycleFactors.hφ_range_card'

example (l : List ℕ) (n : ℕ) (hn : ∀ i ∈ l, i < n) :
    ((Finset.range n).Prod fun i => (List.count i l).factorial) =
      (List.map (fun i : ℕ => (List.count i l).factorial) l.dedup).Prod :=
  by
  rw [← List.prod_toFinset]
  apply symm
  apply Finset.prod_subset_one_on_sdiff
  · intro i hi; rw [Finset.mem_range]; apply hn i
    simpa only [List.mem_toFinset, List.mem_dedup] using hi
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_range, List.mem_toFinset, List.mem_dedup] at hi 
    rw [List.count_eq_zero_of_not_mem hi.2]; exact Nat.factorial_zero
  · intro i hi; rfl
  exact List.nodup_dedup l

theorem Fintype.card_eq_count {ι : Type _} [DecidableEq ι] (f : ι → ℕ) (s : Finset ι) (n : ℕ) :
    Finset.card ({x ∈ s | f x = n}) = Multiset.count n (Multiset.map f s.val) :=
  by
  induction' s using Finset.induction with a s has ih
  simp only [Finset.sep_def, Finset.filter_true_of_mem, Finset.not_mem_empty, IsEmpty.forall_iff,
    imp_true_iff, Finset.card_empty, Finset.empty_val, Multiset.map_zero, Multiset.count_zero]
  -- simp only [set.coe_set_of, finset.insert_val],
  rw [Finset.insert_val_of_not_mem has]
  rw [Multiset.map_cons]
  rw [Multiset.count_cons]
  simp only [Finset.sep_def, Finset.filter_congr_decidable] at ih ⊢
  rw [Finset.filter_insert]
  rw [apply_ite Finset.card]
  rw [Finset.card_insert_of_not_mem fun h => has (Finset.mem_of_mem_filter a h)]
  by_cases h : f a = n
  rw [if_pos h, if_pos h.symm, ih]
  rw [if_neg h, if_neg (Ne.symm h), ih, add_zero]
#align fintype.card_eq_count Fintype.card_eq_count

theorem Finset.card_eq_count' {ι : Type _} [DecidableEq ι] (f : ι → ℕ) (s : Finset ι) (n : ℕ) :
    Fintype.card {x : s | f x = n} = Multiset.count n (Multiset.map f s.val) :=
  by
  rw [← Fintype.card_eq_count]
  rw [← Fintype.card_coe]
  apply Fintype.card_of_bijective _
  exact fun ⟨⟨x, hx⟩, hx'⟩ =>
    ⟨x, by
      simp only [Set.mem_setOf_eq] at hx' 
      simp only [Finset.sep_def, Finset.mem_filter]
      exact ⟨hx, hx'⟩⟩
  · constructor
    rintro ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ h
    simpa only [Subtype.mk_eq_mk] using h
    rintro ⟨x, hx⟩
    simp only [Finset.sep_def, Finset.mem_filter] at hx 
    use ⟨x, hx.1⟩; exact hx.2
#align finset.card_eq_count' Finset.card_eq_count'

@[to_additive]
theorem Multiset.prod_toFinset {α : Type _} {M : Type _} [DecidableEq α] [CommMonoid M]
    (f : α → M) : ∀ {m : Multiset α} (hm : m.Nodup), m.toFinset.Prod f = (m.map f).Prod :=
  by
  intro m hm
  induction' m using Multiset.induction with a m ih
  simp
  obtain ⟨not_mem, hm⟩ := multiset.nodup_cons.mp hm
  simp [Finset.prod_insert (mt multiset.mem_to_finset.mp not_mem), ih hm]
#align multiset.prod_to_finset Multiset.prod_toFinset
#align multiset.sum_to_finset Multiset.sum_toFinset

theorem hφ_range_card (m : Multiset ℕ) (hg : g.cycleType = m) :
    Fintype.card (φ g).range = (m.dedup.map fun n : ℕ => (m.count n).factorial).Prod :=
  by
  rw [hφ_range_card']
  rw [Equiv.Perm.of_partition_card]
  suffices hlc :
    ∀ n : Fin (Fintype.card α + 1),
      Fintype.card {a : g.cycle_factors_finset | fsc a = n} = m.count ↑n
  suffices hl_lt : ∀ i ∈ m, i < Fintype.card α + 1
  simp_rw [hlc]
  rw [Finset.top_eq_univ]
  rw [← Finset.prod_range fun i => (m.count i).factorial]
  rw [← Multiset.prod_toFinset]
  apply symm
  apply Finset.prod_subset_one_on_sdiff
  · intro i hi; rw [Finset.mem_range]; apply hl_lt
    simpa only [Multiset.mem_toFinset, Multiset.mem_dedup] using hi
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_range, Multiset.mem_toFinset, Multiset.mem_dedup] at hi
      ;
    simp only
    rw [Multiset.count_eq_zero_of_not_mem hi.2]
    exact Nat.factorial_zero
  · intro i hi; rfl
  exact m.nodup_dedup
  · intro i hi
    rw [Nat.lt_succ_iff]
    apply le_trans _ (Finset.card_le_univ g.support)
    apply Equiv.Perm.le_card_support_of_mem_cycleType
    rw [hg]; exact hi
  · rintro ⟨i, hi⟩
    rw [← hg]
    rw [Equiv.Perm.cycleType_def]
    simp only [Fin.val_mk]
    rw [← Fintype.card_eq_count (Finset.card ∘ Equiv.Perm.support) g.cycle_factors_finset i]
    rw [← Fintype.card_coe]
    let u :
      {x : g.cycle_factors_finset | fsc x = ⟨i, hi⟩} →
        {x ∈ g.cycle_factors_finset | (Finset.card ∘ Equiv.Perm.support) x = i} :=
      fun ⟨⟨x, hx⟩, hx'⟩ =>
      ⟨x, by
        simp only [Set.mem_setOf_eq, fsc] at hx' 
        simp only [Subtype.coe_mk, Fin.mk_eq_mk] at hx' 
        simp only [Finset.sep_def, Finset.mem_filter, Function.comp_apply]
        exact ⟨hx, hx'⟩⟩
    have : Function.Bijective u := by
      constructor
      rintro ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ h
      simpa only [u, Subtype.mk_eq_mk] using h
      rintro ⟨x, hx⟩
      simp only [Finset.sep_def, Finset.mem_filter, Function.comp_apply] at hx 
      use ⟨x, hx.1⟩
      simp only [fsc, Subtype.coe_mk, Fin.mk_eq_mk]; exact hx.2
    apply Fintype.card_of_bijective this
#align on_cycle_factors.hφ_range_card OnCycleFactors.hφ_range_card

-- noyau : commute with each cycle of g
theorem hφ_mem_ker_iff' (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈
        Subgroup.map (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).Subtype (φ g).ker ↔
      ∀ (t : Equiv.Perm α) (ht : t ∈ g.cycleFactorsFinset), z * t = t * z :=
  by
  constructor
  · intro hz
    rw [Subgroup.mem_map] at hz 
    obtain ⟨⟨k, hkK⟩, hk, hk'⟩ := hz
    simp only [MonoidHom.mem_ker] at hk 
    intro t ht
    rw [← mul_inv_eq_iff_eq_mul, ← MulAut.conj_apply, ← ConjAct.ofConjAct_toConjAct z, ←
      ConjAct.smul_eq_mulAut_conj _ t]
    rw [← hk']
    simp only [Subgroup.coeSubtype, Subgroup.coe_mk]
    simp only [← φ_eq g k hkK t ht, hk]
    rfl
  · intro H
    rw [Subgroup.mem_map]
    use ConjAct.toConjAct z
    · rw [MulAction.mem_stabilizer_iff]
      rw [ConjAct.smul_eq_mulAut_conj]
      rw [MulAut.conj_apply]
      rw [mul_inv_eq_iff_eq_mul]
      rw [ConjAct.ofConjAct_toConjAct]
      exact Equiv.Perm.commute_of_mem_cycles_factors_commute z g H
    simp only [MonoidHom.mem_ker]
    constructor
    · ext ⟨c, hc⟩
      rw [φ_eq']
      rw [H c hc]
      simp only [mul_inv_cancel_right, Equiv.Perm.coe_one, id.def, Subtype.coe_mk]
    · simp only [Subgroup.coeSubtype, Subgroup.coe_mk]
#align on_cycle_factors.hφ_mem_ker_iff' OnCycleFactors.hφ_mem_ker_iff'

/-
lemma hφ_mem_ker_iff' (z : equiv.perm α) :
  conj_act.to_conj_act z ∈
    subgroup.map (mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype (φ g).ker
  ↔  ∀ (s : equiv.perm α) (hs : s ∈ g.cycle_factors_finset),
    ∃ (hs' : ∀ (x : α), x ∈ s.support ↔ z x ∈ s.support),
      equiv.perm.subtype_perm z hs' ∈ subgroup.zpowers (equiv.perm.subtype_perm g (equiv.perm.mem_cycle_factors_finset_support g s hs)) :=
begin
  rw hφ_mem_ker_iff,
  split,
  { intros H c hc,
    exact (equiv.perm.centralizer_mem_cycle_factors_iff g z c hc).mp (H c hc), },
  { intros H c hc,
    exact (equiv.perm.centralizer_mem_cycle_factors_iff g z c hc).mpr (H c hc), },
end
 -/
-- un groupe symétrique x produit de groupes cycliques
theorem hφ_mem_ker_iff (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈
        Subgroup.map (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).Subtype (φ g).ker ↔
      ∀ (s : Equiv.Perm α) (hs : s ∈ g.cycleFactorsFinset),
        ∃ hs' : ∀ x : α, x ∈ s.support ↔ z x ∈ s.support,
          (Equiv.Perm.subtypePerm z hs').ofSubtype ∈ Subgroup.zpowers s :=
  by
  rw [hφ_mem_ker_iff']
  refine' forall_congr' _
  intro c
  refine' forall_congr' _
  intro hc
  rw [Equiv.Perm.centralizer_mem_cycle_factors_iff g z c hc]
#align on_cycle_factors.hφ_mem_ker_iff OnCycleFactors.hφ_mem_ker_iff

def ψAux (s : Finset (Equiv.Perm α)) (hs : s ⊆ g.cycleFactorsFinset) :
    (Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g) ×
        ∀ c ∈ s, Subgroup.zpowers (c : Equiv.Perm α)) →
      Equiv.Perm α :=
  fun uv :
    Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g) ×
      ∀ c ∈ s, Subgroup.zpowers (c : Equiv.Perm α) =>
  uv.fst.ofSubtype *
    s.noncommProd (fun c => dite (c ∈ s) (fun hc => uv.snd c hc) fun hc => 1) fun c hc d hd h =>
      by
      simp only [Finset.mem_coe] at hc hd 
      rw [dif_pos hc]; rw [dif_pos hd]
      obtain ⟨m, hc'⟩ := subgroup.mem_zpowers_iff.mp (uv.snd c hc).Prop
      obtain ⟨n, hd'⟩ := subgroup.mem_zpowers_iff.mp (uv.snd d hd).Prop
      rw [← hc', ← hd']
      apply Commute.zpow_zpow
      exact g.cycle_factors_finset_mem_commute (hs hc) (hs hd) h
#align on_cycle_factors.ψ_aux OnCycleFactors.ψAux

variable (g)

def ψ :=
  ψAux g.cycleFactorsFinset (Finset.Subset.refl g.cycleFactorsFinset)
#align on_cycle_factors.ψ OnCycleFactors.ψ

variable {g}

theorem hψ_1 (uv)
    -- (uv : (equiv.perm ((mul_action.fixed_by (equiv.perm α) α g))  × Π (c ∈ g.cycle_factors_finset), subgroup.zpowers (c : equiv.perm α)))
    (x : α)
    (hx : x ∈ MulAction.fixedBy _ α g) : ψ g uv x = uv.fst ⟨x, hx⟩ :=
  by
  simp only [ψ, ψ_aux, Equiv.Perm.mul_apply]
  rw [← Equiv.Perm.ofSubtype_apply_coe]
  apply congr_arg
  simp only [Subtype.coe_mk, ← Equiv.Perm.smul_def]
  rw [← MulAction.mem_stabilizer_iff]
  apply Subgroup.noncommProd_mem
  intro c hc
  simp only [dif_pos hc]
  rw [MulAction.mem_stabilizer_iff]
  simp only [Equiv.Perm.smul_def]
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def, ← Equiv.Perm.not_mem_support] at hx 
  simp only [← Equiv.Perm.not_mem_support]
  intro hx'; apply hx
  obtain ⟨m, hm⟩ := (uv.snd c hc).Prop; rw [← hm] at hx' 
  apply Equiv.Perm.mem_cycleFactorsFinset_support_le hc
  apply Equiv.Perm.support_zpow_le c m
  exact hx'
#align on_cycle_factors.hψ_1 OnCycleFactors.hψ_1

/- -- Useless
lemma hψ_2_aux {ι : Type*} [decidable_eq ι] (f : ι → equiv.perm α)
  (s : finset ι)
  (hs : ∀ (i ∈ s) (j ∈ s), commute (f i) (f j))
  (hs' : ∀ (i ∈ s) (j ∈ s), (f i).disjoint (f j))
  (a : α) (ha : ∀ (j ∈ s), a ∉ (f j).support) :
  s.noncomm_prod (λ i, f i) hs a = a :=
begin
  rw ← equiv.perm.smul_def,
  rw ← mul_action.mem_stabilizer_iff,
  apply subgroup.noncomm_prod_mem,
  intros i hi,
  rw mul_action.mem_stabilizer_iff, rw equiv.perm.smul_def,
  rw ← equiv.perm.not_mem_support,
  exact ha i hi,
end -/
theorem hψ_2 (uv) (x : α) (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset)
    (hx : c = g.cycleOf x) : ψ g uv x = (uv.snd c hc : Equiv.Perm α) x :=
  by
  revert uv x c hc hx
  suffices :
    ∀ (s : Finset (Equiv.Perm α)) (hs : s ⊆ g.cycle_factors_finset) (uvs) (x : α) (c : Equiv.Perm α)
      (hc : c ∈ g.cycle_factors_finset) (hx : c = g.cycle_of x),
      ψ_aux s hs uvs x = dite (c ∈ s) (fun h => (uvs.snd c h : Equiv.Perm α) x) fun h => x
  intro uv x c hc hx
  rw [ψ, this g.cycle_factors_finset Finset.Subset.rfl uv x c hc hx, dif_pos hc]
  intro s
  induction' s using Finset.induction with d s hds ih
  · intro hs uv x c hc hx
    simp only [ψ_aux, Finset.empty_subset, Finset.not_mem_empty, not_false_iff, dif_neg,
      Finset.noncommProd_empty, mul_one, Prod.forall, forall_forall_const, forall_true_left]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
    rw [← Ne.def, ← g.is_cycle_cycle_of_iff, ← hx]
    rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc 
    exact hc.1
  · rintro hs ⟨u, v⟩ x c hc hx
    have fixes_of_ne :
      ∀ d ∈ g.cycle_factors_finset,
        ∀ (k : Subgroup.zpowers d) (h : c ≠ d), (k : Equiv.Perm α) x = x :=
      by
      intro d hd k h
      obtain ⟨m, hm⟩ := k.prop
      rw [← hm]; rw [← Equiv.Perm.smul_def]; rw [← MulAction.mem_stabilizer_iff]
      apply Subgroup.zpow_mem
      rw [MulAction.mem_stabilizer_iff]; rw [Equiv.Perm.smul_def]
      apply
        Or.resolve_left
          (equiv.perm.disjoint_iff_eq_or_eq.mp (g.cycle_factors_finset_pairwise_disjoint hc hd h) x)
      rw [← Ne.def]
      rw [← Equiv.Perm.mem_support]
      rw [hx]
      rw [Equiv.Perm.mem_support_cycleOf_iff]
      constructor
      exact Equiv.Perm.SameCycle.refl g x
      rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
      rw [← hx]; exact hc
    simp only [ψ_aux]
    rw [Finset.noncommProd_insert_of_not_mem' _ _ _ _ hds]
    simp only [dif_pos (Finset.mem_insert_self d s)]
    rw [← mul_assoc]
    rw [Equiv.Perm.mul_apply]
    suffices :
      ∀ x ∈ s,
        (dite (x ∈ insert d s) (fun h => (v x h : Equiv.Perm α)) fun h => 1) =
          dite (x ∈ s) (fun h => (v x (Finset.mem_insert_of_mem h) : Equiv.Perm α)) fun h => 1
    rw [Finset.noncommProd_congr rfl this]
    specialize
      ih (subset_trans (Finset.subset_insert d s) hs)
        ⟨u, fun x h => v x (Finset.mem_insert_of_mem h)⟩
        ((v d (Finset.mem_insert_self d s) : Equiv.Perm α) x) c hc
    -- (hs (finset.mem_insert_self d s)),
    simp only [ψ_aux] at ih 
    rw [ih _]
    by_cases hcs : c ∈ s
    · simp only [dif_pos hcs, dif_pos (Finset.mem_insert_of_mem hcs)]
      apply congr_arg
      apply fixes_of_ne
      exact hs (Finset.mem_insert_self d s)
      -- c ≠ d
      intro h;
      apply hds; rw [← h]; exact hcs
    · -- by_cases : c ∉ s
      simp only [dif_neg hcs]
      by_cases hcd : c = d
      · rw [hcd]; simp only [dif_pos (Finset.mem_insert_self d s)]
      rw [dif_neg]
      apply fixes_of_ne
      exact hs (Finset.mem_insert_self d s)
      exact hcd
      -- c ∉ insert d s
      intro h;
      rw [Finset.mem_insert] at h 
      cases' h with h h
      exact hcd h
      exact hcs h
    · -- c = g.cycle_of ((v d _) x)
      by_cases h : c = d
      · obtain ⟨m, hm⟩ := (v d (Finset.mem_insert_self d s)).Prop
        rw [← hm]
        rw [← h]
        rw [hx]; rw [Equiv.Perm.cycleOf_zpow_apply_self]
        rw [Equiv.Perm.cycleOf_self_apply_zpow]
      rw [fixes_of_ne]
      exact hx
      exact hs (Finset.mem_insert_self d s)
      exact h
    · -- ∀ …
      intro k hks
      simp only [dif_pos hks, dif_pos (Finset.mem_insert_of_mem hks)]
#align on_cycle_factors.hψ_2 OnCycleFactors.hψ_2

variable (g)

theorem hψ_inj : Function.Injective (ψ g) :=
  by
  intro uv uv' h
  rw [Prod.ext_iff]; constructor
  · ext ⟨x, hx⟩; rw [← hψ_1 uv x hx]; rw [← hψ_1 uv' x hx]; rw [h]
  · ext c hc x
    by_cases hx : c = g.cycle_of x
    · rw [← hψ_2 uv x c hc hx]; rw [← hψ_2 uv' x c hc hx]; rw [h]
    · obtain ⟨m, hm⟩ := subgroup.mem_zpowers_iff.mp (uv.snd c hc).Prop
      obtain ⟨n, hn⟩ := subgroup.mem_zpowers_iff.mp (uv'.snd c hc).Prop
      rw [← hm]; rw [← hn]
      suffices ∀ n : ℤ, (c ^ n) x = x by rw [this n]; rw [this m]
      suffices c x = x by
        change c • x = x at this 
        rw [← MulAction.mem_stabilizer_iff] at this 
        intro n
        change c ^ n • x = x
        rw [← MulAction.mem_stabilizer_iff]
        apply Subgroup.zpow_mem _ this
      · rw [← Equiv.Perm.not_mem_support]; intro hx'
        apply hx; exact Equiv.Perm.cycle_is_cycleOf hx' hc
#align on_cycle_factors.hψ_inj OnCycleFactors.hψ_inj

theorem hφ_ker_eq_ψ_range (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈
        Subgroup.map (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).Subtype (φ g).ker ↔
      z ∈ Set.range (ψ g) :=
  by
  rw [hφ_mem_ker_iff]
  rw [Set.mem_range]
  constructor
  · intro Hz
    have hu :
      ∀ x : α,
        x ∈ MulAction.fixedBy (Equiv.Perm α) α g ↔ z x ∈ MulAction.fixedBy (Equiv.Perm α) α g :=
      by
      intro x
      simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
      simp only [← Equiv.Perm.not_mem_support]
      rw [not_iff_not]
      constructor
      · intro hx
        let hx' := id hx
        rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff] at hx' 
        obtain ⟨Hz'⟩ := Hz (g.cycle_of x) hx'
        specialize Hz' x
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hx'
        rw [← Hz']
        rw [Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hx⟩
      · intro hzx
        let hzx' := id hzx
        rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff] at hzx' 
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hzx'
        obtain ⟨Hz'⟩ := Hz (g.cycle_of (z x)) hzx'
        rw [Hz' x]
        rw [Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hzx⟩
    let u := Equiv.Perm.subtypePerm z hu
    let v : ∀ c : Equiv.Perm α, c ∈ g.cycle_factors_finset → ↥(Subgroup.zpowers c) := fun c hc =>
      ⟨Equiv.Perm.ofSubtype (z.subtype_perm (Classical.choose (Hz c hc))),
        Classical.choose_spec (Hz c hc)⟩
    use ⟨u, v⟩
    ext x
    by_cases hx : x ∈ g.support
    · rw [hψ_2 ⟨u, v⟩ x (g.cycle_of x) _ rfl]
      simp only [Subgroup.coe_mk]
      rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
      rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]; exact hx
      rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]; exact hx
    · rw [Equiv.Perm.not_mem_support, ← Equiv.Perm.smul_def, ← MulAction.mem_fixedBy] at hx 
      rw [hψ_1 ⟨u, v⟩ x hx]
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
  · rintro ⟨⟨u, v⟩, h⟩
    intro c hc
    suffices hs' : ∀ x : α, x ∈ c.support ↔ z x ∈ c.support
    use hs'
    suffices : (z.subtype_perm hs').ofSubtype = v c hc
    rw [this]; apply SetLike.coe_mem
    · ext x
      by_cases hx : x ∈ c.support
      · rw [Equiv.Perm.ofSubtype_apply_of_mem]
        simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
        rw [← h]
        rw [hψ_2 ⟨u, v⟩ x]
        exact Equiv.Perm.cycle_is_cycleOf hx hc
        exact hx
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
        apply symm; rw [← Equiv.Perm.not_mem_support]
        obtain ⟨m, hm⟩ := (v c hc).Prop; rw [← hm]
        intro hx'; apply hx
        exact Equiv.Perm.support_zpow_le c m hx'
        exact hx
    · intro x
      suffices :
        ∀ (d : Equiv.Perm α) (hd : d ∈ g.cycle_factors_finset), x ∈ d.support → z x ∈ d.support
      constructor
      exact this c hc
      · intro hzx
        by_cases hx : x ∈ g.support
        · have hx'' : x ∈ (g.cycle_of x).support :=
            by
            rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]
            exact hx
          have hc' := equiv.perm.cycle_of_mem_cycle_factors_finset_iff.mpr hx
          suffices : c = g.cycle_of x; rw [this]; exact hx''
          specialize this (g.cycle_of x) hc' hx''
          by_contra h
          simp only [Equiv.Perm.mem_support] at this hzx 
          cases'
            equiv.perm.disjoint_iff_eq_or_eq.mp (g.cycle_factors_finset_pairwise_disjoint hc hc' h)
              (z x) with
            h1 h2
          exact hzx h1
          exact this h2
        · exfalso
          let hzx' := Equiv.Perm.mem_cycleFactorsFinset_support_le hc hzx
          apply equiv.perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hc hzx)
          rw [← Equiv.Perm.smul_def, ← MulAction.mem_fixedBy]
          simp only [Equiv.Perm.not_mem_support, ← Equiv.Perm.smul_def, ← MulAction.mem_fixedBy] at
            hx 
          rw [← h]
          rw [hψ_1 ⟨u, v⟩ x hx]
          apply Subtype.mem
      · intro d hd
        simp only [Equiv.Perm.mem_support]
        intro hx
        rw [← h]; rw [hψ_2 ⟨u, v⟩ x d hd]
        obtain ⟨m, hm⟩ := (v d hd).Prop; rw [← hm]
        intro hx'; apply hx
        simp only [← Equiv.Perm.mul_apply] at hx' 
        have : d * d ^ m = d ^ m * d := Commute.self_zpow d m
        rw [this, Equiv.Perm.mul_apply] at hx' 
        simp only [EmbeddingLike.apply_eq_iff_eq] at hx' 
        exact hx'
        rw [← Equiv.Perm.mem_support] at hx 
        exact Equiv.Perm.cycle_is_cycleOf hx hd
#align on_cycle_factors.hφ_ker_eq_ψ_range OnCycleFactors.hφ_ker_eq_ψ_range

theorem hψ_range_card' : Fintype.card (Set.range (ψ g)) = Fintype.card (φ g).ker := by
  classical
  let u :
    ↥(Set.range (ψ g)) →
      ↥(φ
            g).ker :=-- (subgroup.map (mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype (φ g).ker)
  fun ⟨z, hz⟩ => by
    rw [← hφ_ker_eq_ψ_range g] at hz 
    suffices : ConjAct.toConjAct z ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g
    use ⟨ConjAct.toConjAct z, this⟩
    have hK : Function.Injective (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).Subtype
    apply Subgroup.subtype_injective
    rw [← Subgroup.mem_map_iff_mem hK]
    simp only [Subgroup.coeSubtype, Subgroup.coe_mk]
    exact hz
    · obtain ⟨u, ⟨hu, hu'⟩⟩ := hz
      rw [← hu']; exact u.prop
  suffices : Function.Bijective u
  exact Fintype.card_of_bijective this
  constructor
  · -- injectivity
    rintro ⟨z, hz⟩ ⟨w, hw⟩ hzw
    simpa only [Subtype.mk_eq_mk, MulEquiv.apply_eq_iff_eq] using hzw
  · -- surjectivity
    rintro ⟨w, hw⟩
    use ConjAct.ofConjAct ((MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).Subtype w)
    rw [← hφ_ker_eq_ψ_range]
    simp only [Subgroup.coeSubtype, ConjAct.toConjAct_ofConjAct, Subgroup.mem_map,
      SetLike.coe_eq_coe, exists_prop, exists_eq_right, hw]
    simp only [Subgroup.coeSubtype, ConjAct.toConjAct_ofConjAct, Subtype.mk_eq_mk, SetLike.eta]
#align on_cycle_factors.hψ_range_card' OnCycleFactors.hψ_range_card'

theorem Equiv.Perm.card_fixedBy (m : Multiset ℕ) (hg : g.cycleType = m) :
    Fintype.card (MulAction.fixedBy (Equiv.Perm α) α g) = Fintype.card α - m.Sum :=
  by
  rw [← hg, Equiv.Perm.sum_cycleType, ← Finset.card_compl]
  simp only [Fintype.card_ofFinset, Set.mem_compl_iff, Finset.mem_coe, Equiv.Perm.mem_support,
    Classical.not_not]
  apply congr_arg
  ext x
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def, Finset.mem_filter, Finset.mem_univ,
    true_and_iff, Finset.mem_compl, Equiv.Perm.mem_support, Classical.not_not]
#align on_cycle_factors.equiv.perm.card_fixed_by OnCycleFactors.Equiv.Perm.card_fixedBy

theorem Fintype.card_pfun (p : Prop) [Decidable p] (β : p → Type _) [∀ hp, Fintype (β hp)] :
    Fintype.card (∀ hp : p, β hp) = dite p (fun h => Fintype.card (β h)) fun h => 1 :=
  by
  by_cases hp : p
  · simp only [dif_pos hp]
    rw [Fintype.card_eq]
    apply Nonempty.intro
    refine' Equiv.piSubsingleton (fun a' : p => β a') hp
  · simp only [dif_neg hp]
    rw [Fintype.card_eq_one_iff]
    have : ∀ h : p, β h := fun h => False.ndrec (β h) (hp h)
    use this
    intro u; ext h; exfalso; exact hp h
#align on_cycle_factors.fintype.card_pfun OnCycleFactors.Fintype.card_pfun

variable {g}

theorem hψ_range_card (m : Multiset ℕ) (hg : g.cycleType = m) :
    Fintype.card (Set.range (ψ g)) = (Fintype.card α - m.Sum).factorial * m.Prod :=
  by
  rw [Set.card_range_of_injective (hψ_inj g)]
  rw [Fintype.card_prod]
  rw [Fintype.card_perm]
  rw [Fintype.card_pi]
  apply congr_arg₂ (· * ·)
  · -- fixed points
    apply congr_arg
    exact equiv.perm.card_fixed_by g m hg
  · rw [← Finset.prod_compl_mul_prod g.cycle_factors_finset, ← hg]
    suffices :
      (g.cycle_factors_finsetᶜ.Prod fun i : Equiv.Perm α =>
          Fintype.card (i ∈ g.cycle_factors_finset → ↥(Subgroup.zpowers i))) =
        1
    rw [this, one_mul]
    · -- on g.cycle_factors_finset
      simp only [Equiv.Perm.cycleType, Finset.prod]
      apply congr_arg
      ext n
      simp only [Multiset.count_map]
      apply congr_arg
      simp only [← Finset.filter_val]; apply congr_arg
      ext a
      simp only [Finset.mem_filter]
      rw [fintype.card_pfun]
      by_cases ha : a ∈ g.cycle_factors_finset
      · simp only [dif_pos ha]
        rw [← orderOf_eq_card_zpowers]
        rw [Equiv.Perm.IsCycle.orderOf]
        rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at ha ; exact ha.1
      · simp only [ha, false_and_iff]
    · -- on g.cycle_factors_finsetᶜ
      apply Finset.prod_eq_one
      intro c hc
      rw [Finset.mem_compl] at hc 
      rw [fintype.card_pfun, dif_neg hc]
#align on_cycle_factors.hψ_range_card OnCycleFactors.hψ_range_card

-- Should one parenthesize the product ?
/-- Cardinality of a centralizer in `equiv.perm α` of a given `cycle_type` -/
theorem Equiv.Perm.conj_stabilizer_card (g : Equiv.Perm α) (m : Multiset ℕ) (hg : g.cycleType = m) :
    Fintype.card (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) =
      (Fintype.card α - m.Sum).factorial * m.Prod *
        (m.dedup.map fun n : ℕ => (m.count n).factorial).Prod :=
  by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (φ g).ker]
  rw [Fintype.card_congr (QuotientGroup.quotientKerEquivRange (φ g)).toEquiv]
  rw [hφ_range_card m hg]
  rw [mul_comm]
  apply congr_arg₂ (· * ·) _ rfl
  rw [← hψ_range_card m hg]
  rw [hψ_range_card']
#align on_cycle_factors.equiv.perm.conj_stabilizer_card OnCycleFactors.Equiv.Perm.conj_stabilizer_card

theorem Group.conj_class_eq_conj_orbit {G : Type _} [Group G] (g : G) :
    {k : G | IsConj g k} = MulAction.orbit (ConjAct G) g :=
  by
  ext k
  simp only [Set.mem_setOf_eq, isConj_iff, MulAction.mem_orbit_iff, ConjAct.smul_def]
  constructor
  rintro ⟨c, hc⟩
  use ConjAct.toConjAct c; simp only [hc, ConjAct.ofConjAct_toConjAct]
  rintro ⟨x, hx⟩
  use ConjAct.ofConjAct x; simp only [hx]
#align on_cycle_factors.group.conj_class_eq_conj_orbit OnCycleFactors.Group.conj_class_eq_conj_orbit

theorem Equiv.Perm.conj_class_card_mul_eq (g : Equiv.Perm α) (m : Multiset ℕ)
    (hg : g.cycleType = m) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} * (Fintype.card α - m.Sum).factorial * m.Prod *
        (m.dedup.map fun n : ℕ => (m.count n).factorial).Prod =
      (Fintype.card α).factorial :=
  by
  classical
  simp_rw [group.conj_class_eq_conj_orbit g]
  simp only [mul_assoc]
  rw [mul_comm]
  simp only [← mul_assoc]
  rw [← equiv.perm.conj_stabilizer_card g m hg]
  rw [mul_comm]
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Equiv.Perm α)) g]
  rw [ConjAct.card, Fintype.card_perm]
#align on_cycle_factors.equiv.perm.conj_class_card_mul_eq OnCycleFactors.Equiv.Perm.conj_class_card_mul_eq

theorem Multiset.prod_pos {R : Type _} [StrictOrderedCommSemiring R] [Nontrivial R] (m : Multiset R)
    (h : ∀ a ∈ m, (0 : R) < a) : 0 < m.Prod :=
  by
  induction' m using Multiset.induction with a m ih
  · simp
  · rw [Multiset.prod_cons]
    exact
      mul_pos (h _ <| Multiset.mem_cons_self _ _)
        (ih fun a ha => h a <| Multiset.mem_cons_of_mem ha)
#align on_cycle_factors.multiset.prod_pos OnCycleFactors.Multiset.prod_pos

/-- Cardinality of a conjugacy class in `equiv.perm α` of a given `cycle_type` -/
theorem Equiv.Perm.conj_class_card (g : Equiv.Perm α) (m : Multiset ℕ) (hg : g.cycleType = m) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} =
      (Fintype.card α).factorial /
        ((Fintype.card α - m.Sum).factorial * m.Prod *
          (m.dedup.map fun n : ℕ => (m.count n).factorial).Prod) :=
  by
  rw [← equiv.perm.conj_class_card_mul_eq g m hg]
  rw [Nat.div_eq_of_eq_mul_left _]
  simp only [← mul_assoc]
  -- This is the cardinal of the centralizer
  rw [← equiv.perm.conj_stabilizer_card g m hg]
  refine' Fintype.card_pos
#align on_cycle_factors.equiv.perm.conj_class_card OnCycleFactors.Equiv.Perm.conj_class_card

variable (α)

theorem Equiv.Perm.card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filterₓ fun g : Equiv.Perm α => g.cycleType = m).card *
        ((Fintype.card α - m.Sum).factorial * m.Prod *
          (m.dedup.map fun n : ℕ => (m.count n).factorial).Prod) =
      ite (m.Sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) (Fintype.card α).factorial 0 :=
  by
  split_ifs with hm hm
  · -- nonempty case
    obtain ⟨g, hg⟩ := equiv.perm_with_cycle_type_nonempty_iff.mp hm
    suffices :
      (finset.univ.filter fun h : Equiv.Perm α => h.cycleType = m) =
        finset.univ.filter fun h : Equiv.Perm α => IsConj g h
    rw [this]
    rw [← Fintype.card_coe]
    simp only [Equiv.permWithCycleType, Finset.mem_filter] at hg 
    rw [← equiv.perm.conj_class_card_mul_eq g m hg.2]
    simp only [Fintype.card_coe, ← Set.toFinset_card, mul_assoc]
    apply congr_arg₂ _
    · apply congr_arg
      ext
      simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff, Set.mem_toFinset,
        Set.mem_setOf_eq]
    rfl
    ext h;
    simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff, Set.mem_toFinset, Set.mem_setOf_eq]
    rw [isConj_comm]; rw [Equiv.Perm.isConj_iff_cycleType_eq]
    simp only [Equiv.permWithCycleType, Finset.mem_filter] at hg 
    rw [hg.2]
  · convert MulZeroClass.zero_mul _
    rw [Finset.card_eq_zero]
    rw [← Finset.isEmpty_coe_sort]
    rw [← not_nonempty_iff]
    intro h; apply hm
    simp only [Finset.nonempty_coe_sort] at h 
    rw [Equiv.permWithCycleType_nonempty_iff]
    exact h
#align on_cycle_factors.equiv.perm.card_of_cycle_type_mul_eq OnCycleFactors.Equiv.Perm.card_of_cycleType_mul_eq

/-- Cardinality of the set of `equiv.perm α` of given `cycle_type` -/
theorem Equiv.Perm.card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filterₓ fun g : Equiv.Perm α => g.cycleType = m).card =
      if m.Sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a then
        (Fintype.card α).factorial /
          ((Fintype.card α - m.Sum).factorial * m.Prod *
            (m.dedup.map fun n : ℕ => (m.count n).factorial).Prod)
      else 0 :=
  by
  split_ifs with hm hm
  · -- nonempty case
    obtain ⟨g, hg⟩ := equiv.perm_with_cycle_type_nonempty_iff.mp hm
    simp only [Equiv.permWithCycleType, Finset.mem_filter] at hg 
    rw [← equiv.perm.conj_class_card_mul_eq g m hg.2]
    simp only [mul_assoc]
    simp only [Fintype.card_coe, ← Set.toFinset_card, mul_assoc]
    rw [Nat.div_eq_of_eq_mul_left _]
    apply congr_arg₂
    · apply congr_arg
      ext
      simp only [Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ,
        true_and_iff]
      rw [isConj_comm, Equiv.Perm.isConj_iff_cycleType_eq, hg.2]
    rfl
    -- This is the cardinal of the centralizer
    simp only [← mul_assoc]
    rw [← equiv.perm.conj_stabilizer_card g m hg.2]
    refine' Fintype.card_pos
  · rw [Finset.card_eq_zero, ← Finset.isEmpty_coe_sort, ← not_nonempty_iff]
    simpa only [Finset.nonempty_coe_sort, Equiv.permWithCycleType_nonempty_iff] using hm
#align on_cycle_factors.equiv.perm.card_of_cycle_type OnCycleFactors.Equiv.Perm.card_of_cycleType

theorem AlternatingGroup.of_cycleType_eq (m : Multiset ℕ) :
    Finset.map ⟨Subgroup.subtype (alternatingGroup α), Subgroup.subtype_injective _⟩
        (Finset.univ.filterₓ fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m) =
      ite (Even (m.Sum + m.card)) (Finset.univ.filterₓ fun g : Equiv.Perm α => g.cycleType = m) ∅ :=
  by
  split_ifs with hm hm
  · ext g
    -- split,
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hg; rw [Finset.mem_map] at hg 
      obtain ⟨⟨k, hk⟩, hk', rfl⟩ := hg
      apply And.intro (Finset.mem_univ _)
      simp only [Finset.mem_filter, Finset.mem_univ, Subgroup.coe_mk, true_and_iff] at hk' 
      simp only [Subgroup.coeSubtype, Function.Embedding.coeFn_mk, Subgroup.coe_mk]
      exact hk'
    · rintro ⟨_, hg⟩
      simp only [Subgroup.coeSubtype, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and_iff, Function.Embedding.coeFn_mk, exists_prop]
      use g
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hg, Even.neg_one_pow hm]
      simp only [Subgroup.coe_mk, Subgroup.coeSubtype]
      exact ⟨hg, rfl⟩
  · rw [Finset.eq_empty_iff_forall_not_mem]
    intro g hg
    simp only [Subgroup.coeSubtype, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and_iff, Function.Embedding.coeFn_mk, exists_prop] at hg 
    obtain ⟨⟨k, hk⟩, hkm, rfl⟩ := hg
    rw [← Nat.odd_iff_not_even] at hm 
    simp only [Subgroup.coe_mk] at hkm 
    simpa [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hkm, Odd.neg_one_pow hm, ←
      Units.eq_iff] using hk
#align on_cycle_factors.alternating_group.of_cycle_type_eq OnCycleFactors.AlternatingGroup.of_cycleType_eq

theorem AlternatingGroup.card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filterₓ fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card *
        ((Fintype.card α - m.Sum).factorial *
          (m.Prod * (m.dedup.map fun n : ℕ => (m.count n).factorial).Prod)) =
      ite ((m.Sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.Sum + m.card))
        (Fintype.card α).factorial 0 :=
  by
  split_ifs with hm hm
  -- by_cases hm : (m.sum ≤ fintype.card α ∧ ∀ a ∈ m, 2 ≤ a),
  -- cases nat.even_or_odd (m.sum + m.card) with hm' hm',
  · -- m is an even cycle_type
    rw [← Finset.card_map]
    rw [alternating_group.of_cycle_type_eq]
    rw [if_pos]
    have := equiv.perm.card_of_cycle_type_mul_eq α m
    simp only [mul_assoc] at this 
    rw [this]
    rw [if_pos]
    exact hm.1
    exact hm.2
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map]
    rw [alternating_group.of_cycle_type_eq]
    rw [apply_ite Finset.card]
    rw [Finset.card_empty]
    rw [not_and_or] at hm 
    by_cases hm' : Even (m.sum + m.card)
    rw [if_pos]
    rw [equiv.perm.card_of_cycle_type]
    rw [if_neg]
    exact MulZeroClass.zero_mul _
    cases' hm with hm hm; exact hm; exfalso; exact hm hm'
    exact hm'
    rw [if_neg]; exact MulZeroClass.zero_mul _; exact hm'
#align on_cycle_factors.alternating_group.card_of_cycle_type_mul_eq OnCycleFactors.AlternatingGroup.card_of_cycleType_mul_eq

theorem AlternatingGroup.card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filterₓ fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card =
      if (m.Sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.Sum + m.card) then
        (Fintype.card α).factorial /
          ((Fintype.card α - m.Sum).factorial *
            (m.Prod * (m.dedup.map fun n : ℕ => (m.count n).factorial).Prod))
      else 0 :=
  by
  split_ifs with hm hm
  -- by_cases hm : (m.sum ≤ fintype.card α ∧ ∀ a ∈ m, 2 ≤ a),
  -- cases nat.even_or_odd (m.sum + m.card) with hm' hm',
  · -- m is an even cycle_type
    rw [← Finset.card_map]
    rw [alternating_group.of_cycle_type_eq]
    rw [if_pos]
    rw [equiv.perm.card_of_cycle_type α m]
    rw [if_pos]
    simp only [mul_assoc]
    exact hm.1
    exact hm.2
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map]
    rw [alternating_group.of_cycle_type_eq]
    rw [apply_ite Finset.card]
    rw [Finset.card_empty]
    rw [not_and_or] at hm 
    by_cases hm' : Even (m.sum + m.card)
    rw [if_pos]
    rw [equiv.perm.card_of_cycle_type]
    rw [if_neg]
    cases' hm with hm hm; exact hm; exfalso; exact hm hm'
    exact hm'
    rw [if_neg]; exact hm'
#align on_cycle_factors.alternating_group.card_of_cycle_type OnCycleFactors.AlternatingGroup.card_of_cycleType

variable {α}

/- TODO !
Lorsque G est un groupe fini, H un sous-groupe d'indice 2,
la classe de conjugaison dans G d'un élément g ∈ H
C_H(g) ⬝ Z_H(g) = card H
C_G(g) ⬝ Z_G(g) = card G = 2 card H
Si Z_G(g) ≤ H, alors Z_H(g) = Z_G(g), donc C_G(g) = 2 ⬝ C_H(g)
sinon, Z_H(g) est d'indice 2 dans Z_G(g) et C_G(g) = C_H(g)
-/
/-
/-- Cardinality of a centralizer in `alternating_group α` of a given `cycle_type`-/
theorem alternating_group.conj_stabilizer_card (g : alternating_group α) (m : multiset ℕ)
  (hg : (g : equiv.perm α).cycle_type = m) :
  nat.card (mul_action.stabilizer (conj_act (alternating_group α)) g) =
    (((fintype.card α - m.sum).factorial
    * (fintype.card α - m.sum).factorial
    * m.prod * (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod))
    / (ite ((∀ i ∈ m, odd i) ∧ m.sum + 1 ≥ fintype.card α) 2 1) := sorry
-/
/-

lemma sign_of_lift (g : equiv.perm α) (τ: equiv.perm (g.cycle_factors_finset))
  (H : ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.card = ((τ c) : equiv.perm α).support.card)
  (a : g.cycle_factors_finset → α) (k : equiv.perm α)
    (ha : ∀ (c : g.cycle_factors_finset), a c ∈ (c : equiv.perm α).support)
    (hgk : g * k = k * g)
    (hkc : ∀ (c : g.cycle_factors_finset), (conj_act.to_conj_act k) • (c : equiv.perm α) = τ c)
    (hka : k ∘ a = a ∘ τ) :
  let hτ_supp_ne : ∀ (d : equiv.perm (g.cycle_factors_finset)) (hd : d ∈ τ.cycle_factors_finset), d.support.nonempty := λ d hd, equiv.perm.support_of_cycle_nonempty (equiv.perm.mem_cycle_factors_finset_iff.mp hd).left
  in let fτn : equiv.perm (g.cycle_factors_finset) → ℕ := λ d, dite (d ∈ τ.cycle_factors_finset) (λ hd, (hτ_supp_ne d hd).some.val.support.card) (λ hd, 0)
  in k.sign = τ.cycle_factors_finset.prod (λ d, d.sign ^ (fτn d)) :=
  begin
  /- chaque cycle de τ donne lieu à des cycles de k en nombre égal au cardinal du support commun des éléments du cycle

    cycle (c1 ... cr), où les ci sont des cycles de g
   -/
  intros hτ_supp_ne fτn,
  /- let fτg : τ.cycle_factors_finset → g.cycle_factors_finset := λ d, (hτ_supp_ne d).some,
  let fgn : g.cycle_factors_finset → ℕ := λ c, c.val.support.card,
  let fτn := fgn ∘ fτg, -/
  have : ∀ (d : equiv.perm g.cycle_factors_finset) (hd : d ∈ τ.cycle_factors_finset)
    (c : g.cycle_factors_finset) (hc: c ∈ d.support), c.val.support.card = fτn d,
  begin
  { intros d hd c hc,
    suffices : ∃ (k : ℕ), (d ^ k) (hτ_supp_ne d hd).some = c,
    obtain ⟨k, rfl⟩ := this,
    rw equiv.perm.pow_apply_mem_support at hc,
    induction k with k hk,
    { dsimp only [fτn],
      rw dif_pos,
      simp only [subtype.val_eq_coe, pow_zero, equiv.perm.coe_one, id.def], },
    { rw [pow_succ, equiv.perm.mul_apply],
      suffices : d _ = τ _,
      rw this,
      rw ← hk,
      apply symm, exact H _,
      convert equiv.perm.cycle_of_apply_self _ _,
      refine equiv.perm.cycle_is_cycle_of _ hd,
      rw equiv.perm.pow_apply_mem_support, exact hc, },
    apply equiv.perm.is_cycle.exists_pow_eq ,
    exact (equiv.perm.mem_cycle_factors_finset_iff.mp hd).left,
    exact equiv.perm.mem_support.mp (hτ_supp_ne d hd).some_spec,
    exact equiv.perm.mem_support.mp hc, },
  end,

  sorry,
end

-/
example (g c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) (a : α) (ha : a ∈ g.support) :
    a ∈ c.support ↔ c = g.cycleOf a := by
  constructor
  · intro ha'
    exact Equiv.Perm.cycle_is_cycleOf ha' hc
  · intro hc
    rw [hc, Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
    simpa only [Equiv.Perm.mem_support] using ha

theorem sign_ψ (s : Finset (Equiv.Perm α)) (hs : s ⊆ g.cycleFactorsFinset)
    (uv : Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g))
    (k : ∀ c ∈ s, Subgroup.zpowers (c : Equiv.Perm α)) :
    (OnCycleFactors.ψAux s hs ⟨uv, k⟩).sign =
      uv.sign *
        s.Prod fun i =>
          Equiv.Perm.sign
            (dite (i ∈ s) (fun hc : i ∈ s => (k i hc : Equiv.Perm α)) fun hc : i ∉ s => 1) :=
  by
  dsimp only [ψ_aux]
  simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_ofSubtype]
  rw [Finset.noncommProd_map]
  rw [Finset.noncommProd_eq_prod]
#align on_cycle_factors.sign_ψ OnCycleFactors.sign_ψ

end OnCycleFactors


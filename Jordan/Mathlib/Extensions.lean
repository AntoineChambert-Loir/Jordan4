/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.extensions
-/
import Jordan.Mathlib.ULift
-- import Jordan.Mathlib.Cardinal

-- import Mathlib.Tactic.Lift
import Mathlib.Data.Finite.Basic
import Mathlib.SetTheory.Cardinal.Finite

section Extensions

open Function.Embedding Nat

open scoped Classical

variable {α : Type _}

example (h q : Prop) : h → ¬h → q :=
  absurd

/-- Given a nat.card inequality, get an embedding from a fin _ -/
theorem gimme_some {m : ℕ} (hα : ↑m ≤ PartENat.card α) : Nonempty (Fin m ↪ α) := by
  suffices Nonempty (ULift (Fin m) ↪ α) by
    obtain ⟨x'⟩ := this;
    use Equiv.ulift.symm.toEmbedding.trans x'
    apply Function.Embedding.injective
  rw [← Cardinal.le_def, Cardinal.mk_fintype, Fintype.card_ulift, Fintype.card_fin]
  exact Iff.mp Cardinal.natCast_le_toPartENat_iff hα

theorem gimme_some_equiv {m : ℕ} [Fintype α] (hα : m = Fintype.card α) : Nonempty (Fin m ≃ α) := by
  exact ⟨(Fintype.equivFinOfCardEq hα.symm).symm⟩



theorem equiv_fin_of_partENat_card_eq {m : ℕ} (hα : PartENat.card α = m) :
    Nonempty (Fin m ≃ α) := by
  cases' fintypeOrInfinite α with h h -- <;> skip
  · simp only [PartENat.card_eq_coe_fintype_card, PartENat.natCast_inj] at hα
    exact ⟨(Fintype.equivFinOfCardEq hα).symm⟩
  · rw [PartENat.card_eq_top_of_infinite] at hα
    exfalso
    apply PartENat.natCast_ne_top m
    rw [hα]

/-- Given an embedding and a strict nat.card inequality, get another element  -/
theorem gimme_another {m : ℕ} (f : Fin m → α) (hα : ↑m < PartENat.card α) :
    ∃ a : α, a ∉ Set.range f := by
  rw [← Set.ne_univ_iff_exists_not_mem]
  intro h
  rw [← not_le] at hα
  apply hα
  rw [← PartENat.card_congr (Equiv.Set.univ α), ← h]
  unfold PartENat.card
  rw [Cardinal.toPartENat_le_natCast_iff]
  convert Cardinal.mk_range_le
  swap
  exact fun n ↦ f (n.down)
  ext a
  simp only [Set.mem_range, ULift.exists]

/-- Extend a fin embedding by another element -/
theorem may_extend_with {n : ℕ} (x : Fin n ↪ α) (a : α) (ha : a ∉ Set.range x.toFun) :
    ∃ x' : Fin n.succ ↪ α,
      (Fin.castLEEmb n.le_succ).trans x' = x ∧ x' ⟨n, n.lt_succ_self⟩ = a := by
  let p := fun i : Fin n.succ => i.val < n
  let f : {i : Fin n.succ | i.val < n} → α := fun i => x.toFun (Fin.castLT i.val i.prop)
  let f' : {i : Fin n.succ | ¬p i} ↪ α := {
    toFun := fun ⟨_, _⟩ => a
    inj' := by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ _
      simp only [Subtype.mk_eq_mk, Fin.ext_iff]
      rw [Nat.eq_of_lt_succ_of_not_lt i.prop hi, Nat.eq_of_lt_succ_of_not_lt j.prop hj] }
  use {
    toFun := fun i => if hi : p i then f ⟨i, hi⟩ else f' ⟨i, hi⟩
    inj' := by
      apply  Function.Injective.dite p
      · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
        rw [Subtype.mk_eq_mk]
        apply Fin.ext
        rw [← Fin.coe_castLT i _]; rw [← Fin.coe_castLT j _]
        rw [x.inj' hij]
      · exact Function.Embedding.injective f'
      · intros -- x x' hx hx'
        simp only [Set.coe_setOf, Set.mem_setOf_eq, toFun_eq_coe, coeFn_mk, ne_eq]
        intro h
        apply ha
        refine ⟨_, h⟩ }
  constructor
  · ext ⟨i, hi⟩
    simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, coeFn_mk]
    rw [dite_eq_iff]
    apply Or.intro_left; use hi; rfl
  · simp only [gt_iff_lt, Set.coe_setOf, Set.mem_setOf_eq, toFun_eq_coe,
    coeFn_mk, lt_self_iff_false, ↓reduceDite, p, f, f']



/-- Extend an embedding from Fin given a PartENat.card inequality -/
theorem may_extend {m n : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ PartENat.card α) (x : Fin m ↪ α) :
    ∃ x' : Fin n ↪ α, (Fin.castLEEmb hmn).trans x' = x :=
  by
  induction' n with n hrec
  · simp only [Nat.zero_eq, nonpos_iff_eq_zero] at hmn
    let w : Fin 0 ↪ α := Function.Embedding.ofIsEmpty
    use w; ext ⟨i, hi⟩
    exfalso; rw [hmn] at hi
    exact Nat.not_lt_zero i hi
  · cases Nat.eq_or_lt_of_le hmn with
    -- case where m = n.succ
    | inl h =>
      use (Equiv.toEmbedding (Fin.castOrderIso h.symm).toEquiv).trans x
      ext ⟨i, hi⟩
      simp
    -- case where m < n.succ
    | inr h =>
      obtain ⟨y, hy⟩ :=
        hrec (Nat.le_of_lt_succ h) (le_trans (PartENat.coe_le_coe.mpr (le_succ n)) hα)
      obtain ⟨a, ha⟩ :=
        gimme_another y (lt_of_lt_of_le (PartENat.coe_lt_coe.mpr (Nat.lt_succ_self n)) hα)
      obtain ⟨x', hx', _⟩ := may_extend_with y a ha
      use x'; rw [← hy]; rw [← hx']
      ext ⟨i, hi⟩; rfl

/-- Join two disjoint embeddings from Fin _ types -/
theorem may_extend_with' {m n k : ℕ} {s : Set α} (z : Fin k ↪ s) (h : n = m + k)
    (x : Fin m ↪ (sᶜ : Set α)) :
    ∃ x' : Fin n ↪ α,
      (Fin.castLEEmb (le_trans le_self_add (le_of_eq (Eq.symm h)))).trans x' =
          x.trans (subtype (sᶜ)) ∧
      (Fin.natAddEmb m).trans ((Fin.castOrderIso h.symm).toEquiv.toEmbedding.trans x') =
          z.trans (subtype s) := by
  let h' := Eq.trans h (add_comm m k)
  let p := fun i : Fin n => i.val < m
  let f : {i : Fin n | p i} → α := fun i => x.toFun (Fin.castLT i.val i.prop)
  let g : {i : Fin n | ¬p i} → α := fun i =>
    z.toFun (Fin.subNat m (Fin.castOrderIso h' i.val) (by simpa [h] using not_lt.mp (Subtype.mem i)))
  use {
    toFun := fun i => if hi : p i then f ⟨i, hi⟩ else g ⟨i, hi⟩
    inj' := by
      refine Function.Injective.dite p ?_ ?_ ?_
      · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
        simpa only [Subtype.mk_eq_mk, Fin.ext_iff] using x.inj' (Subtype.coe_injective hij)
      · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
        simp only [Subtype.mk_eq_mk]
        apply (Fin.castOrderIso h').injective
        rw [not_lt] at hi hj
        have hi' : m ≤ (Fin.castOrderIso h') i := by simp only [Fin.coe_orderIso_apply]; exact hi
        have hj' : m ≤ (Fin.castOrderIso h') j := by simp only [Fin.coe_orderIso_apply]; exact hj
        let hij' := z.inj' (Subtype.coe_injective hij)
        simp only at hij'
        rw [← Fin.addNat_subNat hi', ← Fin.addNat_subNat hj', hij']
      · intro i j hi hj hij
        suffices f ⟨i, hi⟩ ∉ s by
          apply this
          rw [hij]
          simp only [Set.coe_setOf, Set.mem_setOf_eq, Fin.castOrderIso_apply,
            toFun_eq_coe, Subtype.coe_prop, g]
        simp only [f, ← Set.mem_compl_iff, Subtype.coe_prop] }
  constructor
  · ext ⟨i, hi⟩
    simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, coeFn_mk]
    rw [dite_eq_iff]
    apply Or.intro_left; use hi; rfl
  · ext ⟨j, hj⟩
    simp only [gt_iff_lt, Set.coe_setOf, Set.mem_setOf_eq, toFun_eq_coe, Fin.castOrderIso_apply,
      trans_apply, Fin.natAddEmb_apply, Fin.natAdd_mk, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
      Fin.cast_mk, coeFn_mk, add_lt_iff_neg_left, not_lt_zero', ↓reduceDite, Fin.subNat_mk,
      add_tsub_cancel_left, p, f, g, subtype]

end Extensions

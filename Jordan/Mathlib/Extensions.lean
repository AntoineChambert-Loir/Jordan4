/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.extensions
-/
import Mathbin.Tactic.Lift
import Oneshot.ForMathlib.Ulift
import Oneshot.ForMathlib.Cardinal
import Mathbin.Data.Finite.Basic
import Mathbin.SetTheory.Cardinal.Finite

section Extensions

open Function.Embedding Nat

open scoped Classical

variable {α : Type _}

example (h q : Prop) : h → ¬h → q :=
  absurd

/-- Given a nat.card inequality, get an embedding from a fin _ -/
theorem gimme_some {m : ℕ} (hα : ↑m ≤ PartENat.card α) : ∃ x : Fin m ↪ α, True :=
  by
  suffices ∃ x' : ULift (Fin m) ↪ α, True by obtain ⟨x'⟩ := this;
    use equiv.ulift.symm.to_embedding.trans x'
  rw [exists_true_iff_nonempty, ← Cardinal.le_def]
  simp only [Cardinal.mk_fintype, Fintype.card_ulift, Fintype.card_fin]
  cases lt_or_ge (Cardinal.mk α) Cardinal.aleph0
  · obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 h
    rw [hn]; simp only [Cardinal.natCast_le]
    unfold PartENat.card at hα ; rw [hn] at hα 
    simpa only [Cardinal.toPartENat_cast, PartENat.coe_le_coe] using hα
  · refine' le_trans _ h
    apply le_of_lt
    exact Cardinal.nat_lt_aleph0 m
#align gimme_some gimme_some

theorem gimme_some_equiv {m : ℕ} [Fintype α] (hα : m = Fintype.card α) : Nonempty (Fin m ≃ α) := by
  use (Fintype.equivFinOfCardEq hα.symm).symm
#align gimme_some_equiv gimme_some_equiv

theorem equiv_fin_of_partENat_card_eq {m : ℕ} (hα : PartENat.card α = m) : Nonempty (α ≃ Fin m) :=
  by
  cases' fintypeOrInfinite α with h h <;> skip
  · simp only [PartENat.card_eq_coe_fintype_card, PartENat.natCast_inj] at hα 
    use Fintype.equivFinOfCardEq hα
  · rw [PartENat.card_eq_top_of_infinite] at hα 
    exfalso; apply PartENat.natCast_ne_top m; rw [hα]
#align equiv_fin_of_part_enat_card_eq equiv_fin_of_partENat_card_eq

/-- Given an embedding and a strict nat.card inequality, get another element  -/
theorem gimme_another {m : ℕ} (x : Fin m → α) (hα : ↑m < PartENat.card α) :
    ∃ a : α, a ∉ Set.range x := by
  rw [← not_forall]
  intro h
  apply (lt_iff_not_ge _ _).mp hα
  let hx := Cardinal.mk_range_le_lift
  rw [Set.eq_univ_of_forall h] at hx 
  simp only [Cardinal.mk_univ, Cardinal.lift_uzero, Cardinal.mk_fin, Cardinal.lift_natCast] at hx 
  cases' lt_or_ge (Cardinal.mk α) Cardinal.aleph0 with hα' hα'
  · obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 hα'
    unfold PartENat.card; rw [hn]
    simp only [Cardinal.toPartENat_cast, ge_iff_le, PartENat.coe_le_coe]
    simpa only [hn, Cardinal.lift_natCast, Cardinal.natCast_le] using hx
  · exfalso
    apply (lt_iff_not_ge _ _).mp (Cardinal.nat_lt_aleph0 m)
    exact le_trans hα' hx
#align gimme_another gimme_another

/-- Extend a fin embedding by another element -/
theorem may_extend_with {n : ℕ} (x : Fin n ↪ α) (a : α) (ha : a ∉ Set.range x.toFun) :
    ∃ x' : Fin n.succ ↪ α,
      (-- (∀ (i : fin n.succ) (hi : i.val < n), x' i = x ⟨i, hi⟩)
                  Fin.castLE
                  n.le_succ).toEmbedding.trans
            x' =
          x ∧
        x' ⟨n, n.lt_succ_self⟩ = a :=
  by
  let p := fun i : Fin n.succ => i.val < n
  let f : {i : Fin n.succ | i.val < n} → α := fun i => x.to_fun (Fin.castLT i.val i.Prop)
  let f' : {i : Fin n.succ | ¬p i} → α := fun ⟨i, hi⟩ => a
  use fun i => if hi : p i then f ⟨i, hi⟩ else f' ⟨i, hi⟩
  · refine' Function.Injective.dite p _ _ _
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      rw [Subtype.mk_eq_mk]
      apply Fin.ext
      rw [← Fin.coe_castLT i _]; rw [← Fin.coe_castLT j _]
      rw [x.inj' hij]
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [Subtype.mk_eq_mk, Fin.eq_iff_veq]
      rw [Nat.eq_of_lt_succ_of_not_lt i.prop hi, Nat.eq_of_lt_succ_of_not_lt j.prop hj]
    · intro _ _ _ _
      change x.to_fun _ ≠ a
      intro h; apply ha; use ⟨_, h⟩
  constructor
  · ext ⟨i, hi⟩
    simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, coe_fn_mk]
    rw [dite_eq_iff]
    apply Or.intro_left; use hi; rfl
  · simp only [not_lt, coe_fn_mk, dif_neg]
#align may_extend_with may_extend_with

example (m n : ℕ) (h : m ≤ n) : (m : PartENat) ≤ n :=
  part_enat.coe_le_coe.mpr h

/-- Extend an embedding from fin given a nat.card inequality -/
theorem may_extend {m n : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ PartENat.card α) (x : Fin m ↪ α) :
    ∃ x' : Fin n ↪ α, (Fin.castLE hmn).toEmbedding.trans x' = x :=
  by
  induction' n with n hrec
  · simp only [Nat.zero_eq, nonpos_iff_eq_zero] at hmn 
    let w : Fin 0 ↪ α := Function.Embedding.ofIsEmpty
    use w; ext ⟨i, hi⟩
    exfalso; rw [hmn] at hi 
    exact Nat.not_lt_zero i hi
  · cases Nat.eq_or_lt_of_le hmn
    -- case where m = n.succ
    · use (Equiv.toEmbedding (Fin.castIso h.symm).toEquiv).trans x
      ext ⟨i, hi⟩
      simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, Equiv.toEmbedding_apply,
        RelIso.coe_fn_toEquiv, Fin.castIso_mk]
    -- case where m < n.succ
    · obtain ⟨y, hy⟩ :=
        hrec (Nat.le_of_lt_succ h) (le_trans (part_enat.coe_le_coe.mpr (le_succ n)) hα)
      obtain ⟨a, ha⟩ :=
        gimme_another y (lt_of_lt_of_le (part_enat.coe_lt_coe.mpr (Nat.lt_succ_self n)) hα)
      obtain ⟨x', hx', hx'a⟩ := may_extend_with y a ha
      use x'; rw [← hy]; rw [← hx']
      ext ⟨i, hi⟩; rfl
#align may_extend may_extend

/-- Join two disjoint embeddings from fin _ types -/
theorem may_extend_with' {m n k : ℕ} {s : Set α} (z : Fin k ↪ ↥s) (h : n = m + k)
    (x : Fin m ↪ ↥(sᶜ)) :-- let h' : n = k + m := eq.trans h (add_comm m k) in
    ∃ x' : Fin n ↪ α,
      (Fin.castLE (le_trans le_self_add (le_of_eq (Eq.symm h)))).toEmbedding.trans x' =
          x.trans (Subtype (sᶜ)) ∧
        (Fin.natAdd m).toEmbedding.trans ((Fin.castIso h.symm).toEquiv.toEmbedding.trans x') =
          z.trans (Subtype s) :=
  by
  let h' := Eq.trans h (add_comm m k)
  let p := fun i : Fin n => i.val < m
  let f : {i : Fin n | p i} → α := fun i => x.to_fun (Fin.castLT i.val i.Prop)
  let g : {i : Fin n | ¬p i} → α := fun i =>
    z.to_fun (Fin.subNat m (Fin.castIso h' i.val) (by simpa [h] using not_lt.mp (Subtype.mem i)))
  use fun i => if hi : p i then f ⟨i, hi⟩ else g ⟨i, hi⟩
  · refine' Function.Injective.dite p _ _ _
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simpa only [Subtype.mk_eq_mk, Fin.eq_iff_veq] using x.inj' (Subtype.coe_injective hij)
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [Subtype.mk_eq_mk]
      apply (Fin.castIso h').Injective
      rw [not_lt] at hi hj 
      have hi' : m ≤ (Fin.castIso h') i := by simp only [Fin.coe_castIso, Fin.coe_eq_val]; exact hi
      have hj' : m ≤ (Fin.castIso h') j := by simp only [Fin.coe_castIso, Fin.coe_eq_val]; exact hj
      let hij' := z.inj' (Subtype.coe_injective hij)
      simp only at hij' 
      rw [← Fin.addNat_subNat hi', ← Fin.addNat_subNat hj', hij']
    · intro i j hi hj hij
      suffices f ⟨i, hi⟩ ∉ s by apply this; rw [hij]; simp only [Subtype.coe_prop]
      simp only [← Set.mem_compl_iff, Subtype.coe_prop]
  constructor
  · ext ⟨i, hi⟩
    simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, coe_fn_mk]
    rw [dite_eq_iff]
    apply Or.intro_left; use hi; rfl
  · ext ⟨j, hj⟩
    simp only [not_lt, le_add_iff_nonneg_right, zero_le, trans_apply, RelEmbedding.coe_toEmbedding,
      Fin.natAdd_mk, Equiv.toEmbedding_apply, RelIso.coe_fn_toEquiv, Fin.castIso_mk, coe_fn_mk,
      dif_neg, Function.Embedding.coe_subtype]
    change ↑(z.to_fun _) = _
    simp only [Fin.castIso_mk, add_tsub_cancel_left, Fin.subNat_mk, to_fun_eq_coe]
#align may_extend_with' may_extend_with'

end Extensions


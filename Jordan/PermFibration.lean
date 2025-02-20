import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Set.Card

/-  Subgroup of `Equiv.Perm α` preserving a fibration `p : α → ι` , by Junyan Xu -/

variable {α ι : Type*} {p : α → ι}

open Equiv MulAction

local instance  : MulAction (Equiv.Perm α) (α → ι) := arrowAction

lemma arrowAction.mem_stabilizer_iff {g : Perm α} :
    g ∈ stabilizer (Perm α) p ↔ p ∘ g = p := by rw [eq_comm, ← g.comp_symm_eq]; rfl

def φ_invFun (g : ∀ i, Perm {a | p a = i}) (a : α) : α := g (p a) ⟨a, rfl⟩

lemma φ_invFun_eq (g : ∀ i, Perm {a | p a = i}) {a : α} {i : ι} (h : p a = i) :
    φ_invFun g a = g i ⟨a, h⟩ := by subst h; rfl

lemma comp_φ_invFun (g : ∀ i, Perm {a | p a = i}) (a : α) : p (φ_invFun g a) = p a :=
  (g (p a) ⟨a, rfl⟩).prop

def φ_invFun_equiv (g : ∀ i, Perm {a | p a = i}) : Perm α where
  toFun := φ_invFun g
  invFun := φ_invFun (fun i ↦ (g i).symm)
  left_inv a := by
    rw [φ_invFun_eq _ (comp_φ_invFun g a)]
    exact congr_arg Subtype.val ((g <| p a).left_inv _)
  right_inv a := by
    rw [φ_invFun_eq _ (comp_φ_invFun _ a)]
    exact congr_arg Subtype.val ((g <| p a).right_inv _)

variable (p)

def Φ : stabilizer (Perm α) p ≃* (∀ i, Perm {a | p a = i}) where
  toFun g i := Perm.subtypePerm g fun a ↦ by
    simp only [Set.mem_setOf_eq]
    rw [← Function.comp_apply (f := p), arrowAction.mem_stabilizer_iff.mp g.prop]
  invFun g := ⟨φ_invFun_equiv g, by
    ext a; exact comp_φ_invFun (fun i ↦ (g i).symm) a⟩
  left_inv g := rfl
  right_inv g := by ext i a; apply φ_invFun_eq
  map_mul' g h := rfl

#exit


import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-  Subgroup of `Equiv.Perm α` preserving a fibration `p : α → ι` -/

variable {α ι : Type*} {p : α → ι}

open Equiv MulAction

local instance  : MulAction (Equiv.Perm α) (α → ι) := arrowAction

lemma arrowAction.mem_stabilizer_iff {g : Perm α} :
    g ∈ stabilizer (Perm α) p ↔ p ∘ g = p := by
  rw [MulAction.mem_stabilizer_iff]
  change p ∘ (g⁻¹ : Perm α) = p ↔ _
  constructor
  all_goals {
    intro h
    conv_lhs => rw [← h]
    ext a
    simp only [Function.comp_apply, Equiv.Perm.inv_apply_self, Equiv.Perm.apply_inv_self] }

def Φ : stabilizer (Perm α) p ≃* ((i : ι) → Perm {a | p a = i}) := {
  toFun := fun g i ↦ by
    apply Perm.subtypePerm g
    intro a
    simp only [Set.mem_setOf_eq]
    rw [← Function.comp_apply (f := p), arrowAction.mem_stabilizer_iff.mp g.prop]
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := fun g h ↦ by
    ext i
    dsimp }

def φ : stabilizer (Perm α) p →* ((i : ι) → Perm {a | p a = i}) := {
  toFun := fun g i ↦ by
    apply Perm.subtypePerm g
    intro a
    simp only [Set.mem_setOf_eq]
    rw [← Function.comp_apply (f := p), arrowAction.mem_stabilizer_iff.mp g.prop]
  map_one' := by
    simp only [Set.coe_setOf, Set.mem_setOf_eq, OneMemClass.coe_one, Perm.subtypePerm_one]
    ext
    rfl
  map_mul' := fun g h ↦ by
    ext i
    dsimp }

def φ_invFun : ((i : ι) → Perm {a | p a = i}) → α → α :=
  fun g a ↦ g (p a) (⟨a, by simp only [Set.mem_setOf_eq]⟩ : {x | p x = p a})


lemma comp_φ_invFun (g : (i : ι) → Perm {a | p a = i}) (a) : p (φ_invFun g a) = p a := by
  unfold φ_invFun
  simp only [Set.mem_setOf_eq, Set.coe_setOf]
  exact (g (p a) (⟨a, by simp only [Set.mem_setOf_eq]⟩ : {x | p x = p  a})).prop

lemma φ'Fun_apply (g : ((i : ι) → Perm {a | p a = i})) (i : ι) (a : {x | p x = i}) :
    φ'Fun g a = g i a := by
  unfold φ'Fun
  simp only [Set.mem_setOf_eq, Set.coe_setOf]
  let h := a.prop
  simp only [Set.mem_setOf_eq] at h
  congr 2
  rw [h]
  simp only [Set.mem_setOf_eq]




lemma φ'Fun.mul (g h : (i : ι) → Perm {a | p a = i}) (a : α) :
    φ'Fun g (φ'Fun h a) = φ'Fun (g * h) a := by
  unfold φ'Fun


def φ' (g : (i : ι) → Perm {a | p a = i}) : Perm α :=  {
  toFun := φ'Fun g
  invFun := φ'Fun g⁻¹
  left_inv := by
    intro a
    unfold φ'Fun
    simp only [Set.mem_setOf_eq, Set.coe_setOf, Pi.inv_apply]
    let h := comp_φ'Fun g a
    unfold φ'Fun at h
    simp only [Set.mem_setOf_eq, Set.coe_setOf] at h

    sorry
  right_inv := sorry

}

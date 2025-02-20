/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module equivariant_map
-/

import Jordan.Mathlib.Set

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.GroupTheory.GroupAction.Hom

/-! Complements on equivariant maps

In this file, we add some complements to the theory
of equivariant maps by adding some pointwise lemmas.

-/


/-- The map of monoids underlying a `MulActionHom` -/
@[nolint unusedArguments]
def MulActionHom.toMap {M N α β : Type*}
  [SMul M α] [SMul N β] {φ : M → N} (_ : α →ₑ[φ] β) : M → N := φ

open scoped Pointwise

variable {α β M N : Type*} {φ : M → N} [SMul M α] [SMul N β]

variable {f : α →ₑ[φ] β}

namespace Set

open MulActionHom

/-- Image of translated set under an action -/
@[simp]
theorem image_smul_setₑ (m : M) (s : Set α) : f '' (m • s) = φ m • f '' s := by
  change f.toFun '' ((fun a => m • a) '' s) = (fun b => φ m • b) '' (f.toFun '' s)
  simp only [Set.image_image]
  apply Set.image_congr
  intro a _; rw [f.map_smul']

variable {β₁ : Type _} [SMul M β₁] {f₁ : α →[M] β₁}

theorem image_smul_set (m : M) (s : Set α) : f₁ '' (m • s) = m • f₁ '' s := by simp

/-- Translation of preimage is contained in preimage of translation -/
theorem preimage_smul_setₑ_le {m : M} (t : Set β) : m • f ⁻¹' t ⊆ f ⁻¹' (φ m • t) := by
  rintro x ⟨y, hy, rfl⟩
  -- was exact ⟨f y, hy, by rw [map_smul]⟩
  -- why doesn't map_smul work anymore??
  refine ⟨f y, hy, (by rw [map_smulₛₗ])⟩

theorem preimage_smul_set_le {m : M} (t : Set β₁) : m • f₁ ⁻¹' t ⊆ f₁ ⁻¹' (m • t) :=
  preimage_smul_setₑ_le t

/-- When the action is bijective, preimage of translation equals translation of preimage -/
theorem preimage_smul_setₑ' {m : M} (hmα : Function.Bijective fun a : α => m • a)
    (hmβ : Function.Bijective fun b : β => φ m • b) (t : Set β) : f ⁻¹' (φ m • t) = m • f ⁻¹' t := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, yt, hy⟩
    dsimp at hy
    obtain ⟨x', hx' : m • x' = x⟩ := hmα.surjective x
    refine ⟨x',  ?_, hx'⟩
    simp only [← hx', map_smulₛₗ] at hy
    simp only [mem_preimage]
    rw [← hmβ.injective hy]; exact yt
  exact preimage_smul_setₑ_le t

theorem preimage_smul_set' {m : M} (hmα : Function.Bijective fun a : α => m • a)
    (hmβ : Function.Bijective fun b : β₁ => m • b) (t : Set β₁) : f₁ ⁻¹' (m • t) = m • f₁ ⁻¹' t :=
  preimage_smul_setₑ' hmα hmβ t

section Group

variable {M N : Type _} [Group M] [Group N] {φ : M → N}

variable {α β : Type _} [MulAction M α] [MulAction N β]

variable {f : α →ₑ[φ] β}

open scoped Pointwise

/-- For an equivariant map between group actions,
preimage of translation equals translation of preimage -/
theorem preimage_smul_setₑ {m : M} (t : Set β) : f ⁻¹' (φ m • t) = m • f ⁻¹' t :=
  preimage_smul_setₑ' (MulAction.bijective m) (MulAction.bijective (φ m)) t

variable {β₁ : Type _} [MulAction M β₁] {f₁ : α →[M] β₁}

theorem preimage_smul_set {m : M} (t : Set β₁) : f₁ ⁻¹' (m • t) = m • f₁ ⁻¹' t :=
  preimage_smul_set' (MulAction.bijective m) (MulAction.bijective m) t

end Group

end Set

section Pretransitivity

open MulAction

variable {M : Type _} [Group M] {α : Type _} [MulAction M α]

variable {N β : Type _} [Group N] [MulAction N β]

theorem isPretransitive.of_surjective_map {φ : M → N} {f : α →ₑ[φ] β} (hf : Function.Surjective f)
    (h : IsPretransitive M α) : IsPretransitive N β :=
  by
  apply MulAction.IsPretransitive.mk
  intro x y; let h_eq := h.exists_smul_eq
  obtain ⟨x', rfl⟩ := hf x
  obtain ⟨y', rfl⟩ := hf y
  obtain ⟨g, rfl⟩ := h_eq x' y'
  use φ g; simp only [map_smulₛₗ]

theorem isPretransitive.of_bijective_map_iff {φ : M → N} {f : α →ₑ[φ] β}
    (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPretransitive M α ↔ IsPretransitive N β :=
  by
  constructor
  apply isPretransitive.of_surjective_map hf.surjective
  · intro hN
    -- let hN_heq := hN.exists_smul_eq,
    apply IsPretransitive.mk
    intro x y
    obtain ⟨k, hk⟩ := exists_smul_eq N (f x) (f y)
    obtain ⟨g, rfl⟩ := hφ k
    use g
    apply hf.injective
    simp only [hk, map_smulₛₗ]

end Pretransitivity

#exit

/-- Equivariant maps -/
structure EquivariantMap {M N : Type _}
  (φ : outParam (M → N)) (α : Type _) (β : Type _) [SMul M α] [SMul N β] where
  /-- an equivariant map is a map -/
  toFun : α → β
  /-- An equivariant map commutes with `SMul.smul` -/
  map_smul' : ∀ (m : M) (a : α), toFun (m • a) = φ m • toFun a

/-- In the presence of `SMul : M α` and `SMul N β`,
  f : α →ₑ[φ] β` means that `f : α → β` is an equivariant map
  with respect to `φ : M → N` -/
notation:25 α " →ₑ[" φ:25 "] " β:0 => EquivariantMap φ α β

/-- In the presence of `SMul : M α` and `SMul M β`,
  f : α →[M] β` means that `f : α → β` is an equivariant map -/
notation:25 α " →[" M:25 "] " β:0 => EquivariantMap (@id M) α β


/-- Equivariant maps (unbundled version) -/
structure IsEquivariantMap {M N α β : Type _} [SMul M α] [SMul N β]
  (φ : outParam (M → N)) (f : α → β) : Prop where
  /-- An equivariant map commutes with `SMul.smul` -/
  map_smul : ∀ (m : M) (a : α), f (m • a) = φ m • f a

-- ACL : I don't understand this, and this does not work as intended!
/-- `EquivariantMapClass F α β` states that `F` is a type of equivariant maps.
You should declare an instance of this typeclass when you extend `EquivariantMap`.
-/
class EquivariantMapClass (F : Type _) (M N : outParam (Type _))
  (φ : outParam (M → N)) (α β : outParam (Type _))
   [SMul M α] [SMul N β]
  extends DFunLike F α fun _ => β where
  /-- An equivariant map commutes with `SMul.smul` -/
  map_smul : ∀ (f : F) (m : M) (a : α), f (m • a) = φ m • f a

/-- Predicate stating that a map is equivariant -/
theorem IsEquivariant {α β M N : Type _} {φ : M → N} [SMul M α] [SMul N β]
  (f : α →ₑ[φ] β) : IsEquivariantMap φ f.toFun :=
  ⟨f.map_smul'⟩

namespace EquivariantMap

section SMul

variable {α β M N : Type _} {φ : outParam (M → N)} [SMul M α] [SMul N β]

/-- The map on scalars underlying an equivariant map -/
def toSmulMap (_ : α →ₑ[φ] β) := φ

-- ACL : I copied a few of them from `group_theory.hom.group_action.lean` and `linear_map.lean`
-- but I don't really know what I'm doing
/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →ₑ[φ] β) fun _ => α → β :=
  ⟨EquivariantMap.toFun⟩

/-
@[simp]
theorem toFun_eq_coe {f : α →ₑ[φ] β} : f.toFun = (f : α → β) :=
  rfl
-/

@[simp]
theorem map_smul (f : α →ₑ[φ] β) (m : M) (a : α) : f (m • a) = φ m • f a :=
  f.map_smul' m a

@[ext]
theorem ext : ∀ {f g : α →ₑ[φ] β}, (∀ a, f a = g a) → f = g
  | ⟨f, _⟩, ⟨g, _⟩, H => by congr 1 with a; exact H a

theorem ext_iff {f g : α →ₑ[φ] β} : f = g ↔ ∀ a, f a = g a :=
  ⟨fun H a => by rw [H], ext⟩

protected theorem congr_fun {f g : α →ₑ[φ] β} (h : f = g) (a : α) : f a = g a :=
  h ▸ rfl

/-- Copy of a `equivariant_map` with a new `to_fun` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (f : α →ₑ[φ] β) (f' : α → β) (h : f' = ⇑f) : α →ₑ[φ] β
    where
  toFun := f'
  map_smul' := h.symm ▸ f.map_smul'

initialize_simps_projections EquivariantMap (toFun → apply)

/- @[simp]
theorem coe_mk {φ : M → N} (f : α → β) (h) :
  ((EquivariantMap.mk f h : α →ₑ[φ] β) : α → β) = f := rfl
 -/

/- Why does this not work ?
theorem coe_injective : @function.injective (α →ₑ[φ] β) (α → β) coe_fn :=
fun_like.coe_injective

protected lemma congr_arg {x x' : α} {f : α →ₑ[φ] β} : x = x' → f x = f x' :=
fun_like.congr_arg f
-/



/-- Two equal maps on scalars give rise to an equivariant map for identity -/
def ofEq {φ' : M → N} (h : φ = φ') (f : α →ₑ[φ] β) : α →ₑ[φ'] β
    where
  toFun := f.toFun
  map_smul' m a := h ▸ f.map_smul' m a

@[simp]
theorem ofEq_coe {φ' : M → N} (h : φ = φ') (f : α →ₑ[φ] β) :
  (f.ofEq h).toFun = f.toFun := rfl

@[simp]
theorem ofEq_apply {φ' : M → N} (h : φ = φ') (f : α →ₑ[φ] β) (a : α) :
  (f.ofEq h) a = f a :=
  rfl

variable (M)

/-- The identity map as an equivariant map. -/
protected def id : α →[M] α :=
  ⟨id, fun _ _ => rfl⟩

@[simp]
theorem id_apply (a : α) : EquivariantMap.id M a = a :=
  rfl

@[simp] -- porting note : remove norm_cast
theorem id_coe : ((EquivariantMap.id M : α →[M] α) : α → α) = id := rfl

variable {M}

section Composition

variable {P γ : Type _} [SMul P γ] {ψ : N → P}

/-- Composition of equivariant maps -/
def comp (g : β →ₑ[ψ] γ) (f : α →ₑ[φ] β) : α →ₑ[ψ ∘ φ] γ :=
  ⟨g ∘ f, fun m a =>
    calc
      g (f (m • a)) = g (φ m • f a) := by rw [f.map_smul]
      _ = ψ (φ m) • g (f a) := g.map_smul _ _⟩

@[simp]
theorem comp_apply (g : β →ₑ[ψ] γ) (f : α →ₑ[φ] β) (a : α) : g.comp f a = g (f a) :=
  rfl

@[simp]
theorem id_comp (f : α →ₑ[φ] β) :
    ((EquivariantMap.id N).comp f).ofEq (Function.id_comp φ) = f :=
  ext fun x => by rw [ofEq_apply, comp_apply, id_apply]

@[simp]
theorem comp_id (f : α →ₑ[φ] β) :
    (f.comp (EquivariantMap.id M)).ofEq (Function.id_comp φ) = f :=
  ext fun x => by rw [ofEq_apply, comp_apply, id_apply]

variable {Q δ : Type _} [SMul Q δ] {χ : P → Q}

@[simp]
theorem comp_assoc (h : γ →ₑ[χ] δ) (g : β →ₑ[ψ] γ) (f : α →ₑ[φ] β) :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl

end Composition

section Inverse

variable {φ' : N → M}

/-- The inverse of a bijective equivariant map is equivariant with
respect to any right inverse of the scalar map -/
@[simps]
def inverse (f : α →ₑ[φ] β) (g : β → α)
    (k₂ : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : β →ₑ[φ'] α
    where
  toFun := g
  map_smul' n b := calc
      g (n • b) = g (φ (φ' n) • f (g b)) := by rw [k₂, h₂]
      _ = g (f (φ' n • g b)) := by rw [f.map_smul]
      _ = φ' n • g b := by rw [h₁]

/-- Inverse composed with map is identity (if the map on scalars is bijective) -/
theorem inverse_comp
    (f : α →ₑ[φ] β) (g : β → α)
    (k₁ : Function.LeftInverse ψ φ) (k₂ : Function.RightInverse ψ φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    ((f.inverse g k₂ h₁ h₂).comp f).ofEq (Function.LeftInverse.id k₁) = EquivariantMap.id M :=
  ext fun a => by rw [ofEq_apply, comp_apply, inverse_apply, id_coe, id.def, h₁]

/-- Map composed with inverse is identity -/
@[simp]
theorem comp_inverse (f : α →ₑ[φ] β) (g : β → α)
     (k₂ : Function.RightInverse ψ φ)
     (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    (f.comp (f.inverse g k₂ h₁ h₂)).ofEq (Function.RightInverse.id k₂) = EquivariantMap.id N :=
  ext fun a => by rw [ofEq_apply, comp_apply, inverse_apply, id_coe, id.def, h₂]

-- Necessary ?
@[simp]
theorem inverse_inverse
    {f : α →ₑ[φ] β} {g : β → α}
    (k₁ : Function.LeftInverse ψ φ) (k₂ : Function.RightInverse ψ φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    (f.inverse g k₂ h₁ h₂).inverse f k₁ h₂ h₁ = f :=
  ext fun b => by simp only [inverse_apply]
-- 
end Inverse

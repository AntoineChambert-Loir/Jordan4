/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Antoine Chambert-Loir

! This file was ported from Lean 3 source module algebra.hom.group_action
! leanprover-community/mathlib commit e7bab9a85e92cf46c02cb4725a7be2f04691e3a7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GroupRingAction.Basic
import Mathlib.Algebra.Module.Basic

/-!
# Equivariant homomorphisms

## Main definitions

* `MulActionSemiHom φ X Y`, the type of equivariant functions from `X` to `Y`, where `φ : M → N` is a morphism of monoids, `M` acting on the type `X` and `N` acting on the type of `Y`.
* `DistribMulActionSemiHom φ A B`, 
  the type of equivariant additive monoid homomorphisms from `A` to `B`, 
  where `φ : M → N` is a morphism of monoids, 
  `M` acting on the additive monoid `A` and `N` acting on the additive monoid of `B`
* `MulSemiringActionHom φ R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `φ : M → N` is a morphism of monoids,
  `M` acting on the ring `R` and `N` acting on the ring `S`.

The above types have corresponding classes:
* `SMulSemiHomClass F φ X Y` states that `F` is a type of bundled `X → Y` homs
  which are  `φ`-equivariant
* `DistribMulActionSemiHomClass F φ A B` states that `F` is a type of bundled `A → B` homs
  preserving the additive monoid structure and `φ`-equivariant
* `MulSemiringActionSemiHomClass F φ R S` states that `F` is a type of bundled `R → S` homs
  preserving the ring structure and `φ`-equivariant

## Notations

* `X →ₑ[φ] Y` is `MulActionHom φ X Y`.
* `A →ₑ+[φ] B` is `DistribMulActionHom φ A B`.
* `R →ₑ+*[φ] S` is `MulSemiringActionHom φ R S`.

-/

section CompTriple


/-- Class of composing triples -/
class CompTriple  {M N P : Type _}
  (φ : M → N) (ψ : N → P) (χ : M → P) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

instance comp_id {N P : Type _} (ψ : N → P) :
  CompTriple (@id N) ψ ψ := {comp_eq := rfl} 

instance id_comp {M N : Type _} (φ : M → N) :
  CompTriple φ (@id N) φ := {comp_eq := rfl}

instance comp {M N P : Type _}
  (φ : M → N) (ψ : N → P) :
  CompTriple φ ψ  (ψ.comp φ) := {comp_eq := rfl}

end CompTriple

section CompTripleClass

/-- Class of composing triples -/
class CompTripleClass (F : Type _) {M N P : outParam (Type _)}
  (φ : outParam (M → N)) (ψ : outParam (N → P)) (χ : outParam (M → P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTripleClass.comp_eq

namespace CompTripleClass

lemma comp_id (F : Type _) {N P : outParam (Type _)} (ψ : outParam (N → P)) :
  CompTripleClass F (@id N) ψ ψ := {comp_eq := rfl} 

lemma id_comp (F : Type _) {M N : outParam (Type _)} (φ : outParam (M → N)) :
  CompTripleClass F φ (@id N) φ := {comp_eq := rfl}

lemma comp (F : Type _) {M N P : outParam (Type _)}
  (φ : outParam (M → N)) (ψ : outParam (N → P)) :
  CompTripleClass F φ ψ  (ψ.comp φ) := {comp_eq := rfl}

end CompTripleClass

assert_not_exists Submonoid

variable {M' : Type _} {N' : Type _} {P' : Type _}
variable (φ' : M' → N') (ψ' : N' → P') (χ' : M' → P')
variable (X : Type _) [SMul M' X]
variable (Y : Type _) [SMul N' Y]
variable (Z : Type _) [SMul P' Z]
variable (M : Type _) [Monoid M]
variable (N : Type _) [Monoid N]
variable (A : Type _) [AddMonoid A] [DistribMulAction M A]
variable (A' : Type _) [AddGroup A'] [DistribMulAction M A']
variable (B : Type _) [AddMonoid B] [DistribMulAction M B]
variable (B' : Type _) [AddGroup B'] [DistribMulAction M B']
variable (C : Type _) [AddMonoid C] [DistribMulAction M C]
variable (R : Type _) [Semiring R] [MulSemiringAction M R]
variable (R' : Type _) [Ring R'] [MulSemiringAction M R']
variable (S : Type _) [Semiring S] [MulSemiringAction M S]
variable (S' : Type _) [Ring S'] [MulSemiringAction M S']
variable (T : Type _) [Semiring T] [MulSemiringAction M T]

/-- Equivariant functions. -/
-- Porting note: This linter does not exist yet
-- @[nolint has_nonempty_instance]
structure MulActionSemiHom where
  /-- The underlying function. -/
  toFun : X → Y
  /-- The proposition that the function preserves the action. -/
  map_smul' : ∀ (m : M') (x : X), toFun (m • x) = (φ' m) • toFun x

/- Porting note: local notation given a name, conflict with Algebra.Hom.GroupAction
 see https://github.com/leanprover/lean4/issues/2000 -/
@[inherit_doc]
notation:25 (name := «MulActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => MulActionSemiHom φ X Y

/-- `SMulSemiHomClass F φ X Y` states that `F` is a type of morphisms which are `φ`-equivariant

You should extend this class when you extend `MulActionSemiHom`. -/
class SMulSemiHomClass (F : Type _) {M N : outParam (Type _)}
(φ : outParam (M → N)) (X Y : outParam (Type _)) [SMul M X] [SMul N Y] extends
  FunLike F X fun _ => Y where
  /-- The proposition that the function preserves the action. -/
  map_smul : ∀ (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)
#align smul_hom_class SMulSemiHomClass

/- porting note: Removed a @[nolint dangerousInstance] for SMulSemiHomClass
 not dangerous due to outParam -/

export SMulSemiHomClass (map_smul)

attribute [simp] map_smul

-- porting note: removed has_coe_to_fun instance, coercions handled differently now
#noalign mul_action_hom.has_coe_to_fun

instance : SMulSemiHomClass (X →ₑ[φ'] Y) φ' X Y
    where
  coe := MulActionSemiHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_smul := MulActionSemiHom.map_smul'

namespace MulActionSemiHom

variable {φ' X Y}

/- porting note: inserted following def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group -/
/-- Turn an element of a type `F` satisfying `SMulSemiHomClass F M X Y` 
  into an actual `MulActionSemiHom`. 
  This is declared as the default coercion from `F` to `MulActionSemiHom M X Y`. -/
@[coe]
def _root_.SMulSemiHomClass.toMulActionSemiHom [SMul M' X] [SMul N' Y]
[SMulSemiHomClass F φ' X Y] (f : F) :
    X →ₑ[φ'] Y where
   toFun := FunLike.coe f
   map_smul' := map_smul f

/-- Any type satisfying `SMulSemiHomClass` can be cast into `MulActionSemiHom` via
  `SMulSemiHomClass.toMulActionSemiHom`. -/
instance [SMul M' X] [SMul N' Y] [SMulSemiHomClass F φ' X Y] : CoeTC F (X →ₑ[φ'] Y) :=
  ⟨SMulSemiHomClass.toMulActionSemiHom⟩

protected theorem map_smul (f : X →ₑ[φ'] Y) (m : M') (x : X) : f (m • x) = (φ' m) • f x :=
  map_smul f m x
#align mul_action_hom.map_smul MulActionSemiHom.map_smul

@[ext]
theorem ext {f g : X →ₑ[φ'] Y} : (∀ x, f x = g x) → f = g :=
  FunLike.ext f g
#align mul_action_hom.ext MulActionSemiHom.ext

theorem ext_iff {f g : X →ₑ[φ'] Y} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_action_hom.ext_iff MulActionSemiHom.ext_iff

protected theorem congr_fun {f g : X →ₑ[φ'] Y} (h : f = g) (x : X) : f x = g x :=
  FunLike.congr_fun h _
#align mul_action_hom.congr_fun MulActionSemiHom.congr_fun

variable (φ' M' N')

/-- The identity map as an equivariant map. -/
protected def id : X →ₑ[@id M'] X :=
  ⟨id, fun _ _ => rfl⟩
#align mul_action_hom.id MulActionSemiHom.id

@[simp]
theorem id_apply (x : X) : MulActionSemiHom.id M' x = x :=
  rfl
#align mul_action_hom.id_apply MulActionSemiHom.id_apply

variable {M M' N' Z}

variable {φ' ψ' χ'}

/-- Composition of two equivariant maps. -/
def comp --  [CompTriple φ' ψ' χ']
  (g : Y →ₑ[ψ'] Z) (f : X →ₑ[φ'] Y) : X →ₑ[ψ' ∘ φ'] Z :=
  ⟨g ∘ f, fun m x =>
    calc
      g (f (m • x)) = g (φ' m • f x) := by rw [f.map_smul]
      _ = ψ' (φ' m) • g (f x) := g.map_smul _ _ ⟩
-- to have another target
--      _ = (ψ' ∘ φ') m • g (f x) := rfl
--      _ = χ' m • g (f x) := by rw [κ.comp_eq] 
#align mul_action_hom.comp MulActionSemiHom.comp

@[simp]
theorem comp_apply --  [CompTriple φ' ψ' χ']
  (g : Y →ₑ[ψ'] Z) (f : X →ₑ[φ'] Y) (x : X) : (g.comp f : X →ₑ[ψ' ∘ φ'] Z) x = g (f x) :=
  rfl
#align mul_action_hom.comp_apply MulActionSemiHom.comp_apply

@[simp]
theorem id_comp (f : X →ₑ[φ'] Y) : (MulActionSemiHom.id N').comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align mul_action_hom.id_comp MulActionSemiHom.id_comp

@[simp]
theorem comp_id (f : X →ₑ[φ'] Y) : f.comp (MulActionSemiHom.id M') = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align mul_action_hom.comp_id MulActionSemiHom.comp_id

variable {A B}
variable {φ₁' : N' → M'}

/-- The inverse of a bijective equivariant map is equivariant. -/
@[simps]
def inverse (f : X →ₑ[φ'] Y) (g : Y → X) (k : Function.RightInverse φ₁' φ') 
  (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Y →ₑ[φ₁'] X
    where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g ((φ' (φ₁' m)) • f (g x)) := by rw [k]
      _ = g (f (φ₁' m • g x)) := by rw [f.map_smul]
      _ = φ₁' m • g x := by rw [h₁]
#align mul_action_hom.inverse_to_fun MulActionSemiHom.inverse_toFun
#align mul_action_hom.inverse MulActionSemiHom.inverse

end MulActionSemiHom

/-- If actions of `M` and `N` on `α` commute, then for `c : M`, `(c • · : α → α)` is an `N`-action
homomorphism. -/
@[simps]
def SMulCommClass.toMulActionSemiHom {M} (N α : Type _) [SMul M α] [SMul N α] [SMulCommClass M N α]
    (c : M) : α →[N] α where
  toFun := (c • ·)
  map_smul' := smul_comm _

/-- Equivariant additive monoid homomorphisms. -/
structure DistribMulActionHom extends A →[M] B, A →+ B
#align distrib_mul_action_hom DistribMulActionHom

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
add_decl_doc DistribMulActionHom.toAddMonoidHom
#align distrib_mul_action_hom.to_add_monoid_hom DistribMulActionHom.toAddMonoidHom

/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
add_decl_doc DistribMulActionHom.toMulActionHom
#align distrib_mul_action_hom.to_mul_action_hom DistribMulActionHom.toMulActionHom

/- Porting note: local notation given a name, conflict with Algebra.Hom.Freiman
 see https://github.com/leanprover/lean4/issues/2000 -/
@[inherit_doc]
notation:25 (name := «DistribMulActionHomLocal≺»)
  A " →+[" M:25 "] " B:0 => DistribMulActionHom M A B

/-- `DistribMulActionHomClass F M A B` states that `F` is a type of morphisms preserving
the additive monoid structure and scalar multiplication by `M`.

You should extend this class when you extend `DistribMulActionHom`. -/
class DistribMulActionHomClass (F : Type _) (M A B : outParam <| Type _) [Monoid M] [AddMonoid A]
  [AddMonoid B] [DistribMulAction M A] [DistribMulAction M B] extends SMulHomClass F M A B,
  AddMonoidHomClass F A B
#align distrib_mul_action_hom_class DistribMulActionHomClass

/- porting note: Removed a @[nolint dangerousInstance] for
DistribMulActionHomClass.toAddMonoidHomClass not dangerous due to `outParam`s -/

namespace DistribMulActionHom

/- porting note: TODO decide whether the next two instances should be removed
Coercion is already handled by all the HomClass constructions I believe -/
-- instance coe : Coe (A →+[M] B) (A →+ B) :=
--   ⟨toAddMonoidHom⟩
-- #align distrib_mul_action_hom.has_coe DistribMulActionHom.coe

-- instance coe' : Coe (A →+[M] B) (A →[M] B) :=
--   ⟨toMulActionHom⟩
-- #align distrib_mul_action_hom.has_coe' DistribMulActionHom.coe'

-- porting note: removed has_coe_to_fun instance, coercions handled differently now

#noalign distrib_mul_action_hom.has_coe
#noalign distrib_mul_action_hom.has_coe'
#noalign distrib_mul_action_hom.has_coe_to_fun

instance : DistribMulActionHomClass (A →+[M] B) M A B
    where
  coe m := m.toFun
  coe_injective' f g h := by
    rcases f with ⟨tF, _, _⟩; rcases g with ⟨tG, _, _⟩
    cases tF; cases tG; congr
  map_smul m := m.map_smul'
  map_zero := DistribMulActionHom.map_zero'
  map_add := DistribMulActionHom.map_add'

variable {M A B}
/- porting note: inserted following def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group -/
/-- Turn an element of a type `F` satisfying `SMulHomClass F M X Y` into an actual
`MulActionHom`. This is declared as the default coercion from `F` to `MulActionHom M X Y`. -/
@[coe]
def _root_.DistribMulActionHomClass.toDistribMulActionHom [DistribMulActionHomClass F M A B]
  (f : F) : A →+[M] B :=
  { (f : A →+ B),  (f : A →[M] B) with }

/-- Any type satisfying `SMulHomClass` can be cast into `MulActionHom` via
  `SMulHomClass.toMulActionHom`. -/
instance [DistribMulActionHomClass F M A B] : CoeTC F (A →+[M] B) :=
  ⟨DistribMulActionHomClass.toDistribMulActionHom⟩

@[simp]
theorem toFun_eq_coe (f : A →+[M] B) : f.toFun = f := rfl
#align distrib_mul_action_hom.to_fun_eq_coe DistribMulActionHom.toFun_eq_coe

@[norm_cast]
theorem coe_fn_coe (f : A →+[M] B) : ⇑(f : A →+ B) = f :=
  rfl
#align distrib_mul_action_hom.coe_fn_coe DistribMulActionHom.coe_fn_coe

@[norm_cast]
theorem coe_fn_coe' (f : A →+[M] B) : ⇑(f : A →[M] B) = f :=
  rfl
#align distrib_mul_action_hom.coe_fn_coe' DistribMulActionHom.coe_fn_coe'

@[ext]
theorem ext {f g : A →+[M] B} : (∀ x, f x = g x) → f = g :=
  FunLike.ext f g
#align distrib_mul_action_hom.ext DistribMulActionHom.ext

theorem ext_iff {f g : A →+[M] B} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align distrib_mul_action_hom.ext_iff DistribMulActionHom.ext_iff

protected theorem congr_fun {f g : A →+[M] B} (h : f = g) (x : A) : f x = g x :=
  FunLike.congr_fun h _
#align distrib_mul_action_hom.congr_fun DistribMulActionHom.congr_fun

theorem toMulActionHom_injective {f g : A →+[M] B} (h : (f : A →[M] B) = (g : A →[M] B)) :
    f = g := by
  ext a
  exact MulActionHom.congr_fun h a
#align distrib_mul_action_hom.to_mul_action_hom_injective DistribMulActionHom.toMulActionHom_injective

theorem toAddMonoidHom_injective {f g : A →+[M] B} (h : (f : A →+ B) = (g : A →+ B)) : f = g := by
  ext a
  exact FunLike.congr_fun h a
#align distrib_mul_action_hom.to_add_monoid_hom_injective DistribMulActionHom.toAddMonoidHom_injective

protected theorem map_zero (f : A →+[M] B) : f 0 = 0 :=
  map_zero f
#align distrib_mul_action_hom.map_zero DistribMulActionHom.map_zero

protected theorem map_add (f : A →+[M] B) (x y : A) : f (x + y) = f x + f y :=
  map_add f x y
#align distrib_mul_action_hom.map_add DistribMulActionHom.map_add

protected theorem map_neg (f : A' →+[M] B') (x : A') : f (-x) = -f x :=
  map_neg f x
#align distrib_mul_action_hom.map_neg DistribMulActionHom.map_neg

protected theorem map_sub (f : A' →+[M] B') (x y : A') : f (x - y) = f x - f y :=
  map_sub f x y
#align distrib_mul_action_hom.map_sub DistribMulActionHom.map_sub

protected theorem map_smul (f : A →+[M] B) (m : M) (x : A) : f (m • x) = m • f x :=
  map_smul f m x
#align distrib_mul_action_hom.map_smul DistribMulActionHom.map_smul

variable (M)
/-- The identity map as an equivariant additive monoid homomorphism. -/
protected def id : A →+[M] A :=
  ⟨.id _, rfl, fun _ _ => rfl⟩
#align distrib_mul_action_hom.id DistribMulActionHom.id

@[simp]
theorem id_apply (x : A) : DistribMulActionHom.id M x = x := by
  rfl
#align distrib_mul_action_hom.id_apply DistribMulActionHom.id_apply

variable {M C}

-- porting note:  `simp` used to prove this, but now `change` is needed to push past the coercions
instance : Zero (A →+[M] B) :=
  ⟨{ (0 : A →+ B) with map_smul' := fun m _ => by change (0 : B) = m • (0 : B); rw [smul_zero]}⟩

instance : One (A →+[M] A) :=
  ⟨DistribMulActionHom.id M⟩

@[simp]
theorem coe_zero : ⇑(0 : A →+[M] B) = 0 :=
  rfl
#align distrib_mul_action_hom.coe_zero DistribMulActionHom.coe_zero

@[simp]
theorem coe_one : ⇑(1 : A →+[M] A) = id :=
  rfl
#align distrib_mul_action_hom.coe_one DistribMulActionHom.coe_one

theorem zero_apply (a : A) : (0 : A →+[M] B) a = 0 :=
  rfl
#align distrib_mul_action_hom.zero_apply DistribMulActionHom.zero_apply

theorem one_apply (a : A) : (1 : A →+[M] A) a = a :=
  rfl
#align distrib_mul_action_hom.one_apply DistribMulActionHom.one_apply

instance : Inhabited (A →+[M] B) :=
  ⟨0⟩

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : B →+[M] C) (f : A →+[M] B) : A →+[M] C :=
  { MulActionHom.comp (g : B →[M] C) (f : A →[M] B),
    AddMonoidHom.comp (g : B →+ C) (f : A →+ B) with }
#align distrib_mul_action_hom.comp DistribMulActionHom.comp

@[simp]
theorem comp_apply (g : B →+[M] C) (f : A →+[M] B) (x : A) : g.comp f x = g (f x) :=
  rfl
#align distrib_mul_action_hom.comp_apply DistribMulActionHom.comp_apply

@[simp]
theorem id_comp (f : A →+[M] B) : (DistribMulActionHom.id M).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align distrib_mul_action_hom.id_comp DistribMulActionHom.id_comp

@[simp]
theorem comp_id (f : A →+[M] B) : f.comp (DistribMulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align distrib_mul_action_hom.comp_id DistribMulActionHom.comp_id

/-- The inverse of a bijective `DistribMulActionHom` is a `DistribMulActionHom`. -/
@[simps]
def inverse (f : A →+[M] B) (g : B → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B →+[M] A :=
  { (f : A →+ B).inverse g h₁ h₂, (f : A →[M] B).inverse g h₁ h₂ with toFun := g }
#align distrib_mul_action_hom.inverse DistribMulActionHom.inverse

section Semiring

variable {R M'}
variable [AddMonoid M'] [DistribMulAction R M']

@[ext]
theorem ext_ring {f g : R →+[R] M'} (h : f 1 = g 1) : f = g := by
  ext x
  rw [← mul_one x, ← smul_eq_mul R, f.map_smul, g.map_smul, h]
#align distrib_mul_action_hom.ext_ring DistribMulActionHom.ext_ring

theorem ext_ring_iff {f g : R →+[R] M'} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩
#align distrib_mul_action_hom.ext_ring_iff DistribMulActionHom.ext_ring_iff

end Semiring

end DistribMulActionHom

/-- If `DistribMulAction` of `M` and `N` on `A` commute, then for each `c : M`, `(c • ·)` is an
`N`-action additive homomorphism. -/
@[simps]
def SMulCommClass.toDistribMulActionHom {M} (N A : Type _) [Monoid N] [AddMonoid A]
    [DistribSMul M A] [DistribMulAction N A] [SMulCommClass M N A] (c : M) : A →+[N] A :=
  { SMulCommClass.toMulActionHom N A c, DistribSMul.toAddMonoidHom _ c with
    toFun := (c • ·) }

/-- Equivariant ring homomorphisms. -/
-- Porting note: This linter does not exist yet
-- @[nolint has_nonempty_instance]
structure MulSemiringActionHom extends R →+[M] S, R →+* S
#align mul_semiring_action_hom MulSemiringActionHom

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc MulSemiringActionHom.toRingHom
#align mul_semiring_action_hom.to_ring_hom MulSemiringActionHom.toRingHom

/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
add_decl_doc MulSemiringActionHom.toDistribMulActionHom
#align mul_semiring_action_hom.to_distrib_mul_action_hom MulSemiringActionHom.toDistribMulActionHom

/- Porting note: local notation given a name, conflict with Algebra.Hom.Freiman
 see https://github.com/leanprover/lean4/issues/2000 -/
@[inherit_doc]
notation:25 (name := «MulSemiringActionHomLocal≺»)
  R " →+*[" M:25 "] " S:0 => MulSemiringActionHom M R S

/-- `MulSemiringActionHomClass F M R S` states that `F` is a type of morphisms preserving
the ring structure and scalar multiplication by `M`.

You should extend this class when you extend `MulSemiringActionHom`. -/
class MulSemiringActionHomClass (F : Type _) (M R S : outParam <| Type _) [Monoid M] [Semiring R]
  [Semiring S] [DistribMulAction M R] [DistribMulAction M S] extends
  DistribMulActionHomClass F M R S, RingHomClass F R S
#align mul_semiring_action_hom_class MulSemiringActionHomClass

/- porting note: Removed a @[nolint dangerousInstance] for MulSemiringActionHomClass.toRingHomClass
 not dangerous due to outParam -/

namespace MulSemiringActionHom

/- porting note: TODO decide whether the next two instances should be removed
Coercion is already handled by all the HomClass constructions I believe -/
-- @[coe]
-- instance coe : Coe (R →+*[M] S) (R →+* S) :=
--   ⟨toRingHom⟩
-- #align mul_semiring_action_hom.has_coe MulSemiringActionHom.coe

-- @[coe]
-- instance coe' : Coe (R →+*[M] S) (R →+[M] S) :=
--   ⟨toDistribMulActionHom⟩
-- #align mul_semiring_action_hom.has_coe' MulSemiringActionHom.coe'

-- porting note: removed has_coe_to_fun instance, coercions handled differently now

#noalign mul_semiring_action_hom.has_coe
#noalign mul_semiring_action_hom.has_coe'
#noalign mul_semiring_action_hom.has_coe_to_fun

instance : MulSemiringActionHomClass (R →+*[M] S) M R S
    where
  coe m := m.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨tF, _, _⟩, _, _⟩; rcases g with ⟨⟨tG, _, _⟩, _, _⟩
    cases tF; cases tG; congr
  map_smul m := m.map_smul'
  map_zero m := m.map_zero'
  map_add m := m.map_add'
  map_one := MulSemiringActionHom.map_one'
  map_mul := MulSemiringActionHom.map_mul'

variable {M R S}

/- porting note: inserted following def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group -/
/-- Turn an element of a type `F` satisfying `MulSemiringActionHomClass F M R S` into an actual
`MulSemiringActionHom`. This is declared as the default coercion from `F` to
`MulSemiringActionHom M X Y`. -/
@[coe]
def _root_.MulSemiringActionHomClass.toMulSemiringActionHom [MulSemiringActionHomClass F M R S]
  (f : F) : R →+*[M] S :=
 { (f : R →+* S),  (f : R →+[M] S) with }

/-- Any type satisfying `MulSemiringActionHomClass` can be cast into `MulSemiringActionHom` via
  `MulSemiringActionHomClass.toMulSemiringActionHom`. -/
instance [MulSemiringActionHomClass F M R S] : CoeTC F (R →+*[M] S) :=
  ⟨MulSemiringActionHomClass.toMulSemiringActionHom⟩

@[norm_cast]
theorem coe_fn_coe (f : R →+*[M] S) : ⇑(f : R →+* S) = f :=
  rfl
#align mul_semiring_action_hom.coe_fn_coe MulSemiringActionHom.coe_fn_coe

@[norm_cast]
theorem coe_fn_coe' (f : R →+*[M] S) : ⇑(f : R →+[M] S) = f :=
  rfl
#align mul_semiring_action_hom.coe_fn_coe' MulSemiringActionHom.coe_fn_coe'

@[ext]
theorem ext {f g : R →+*[M] S} : (∀ x, f x = g x) → f = g :=
  FunLike.ext f g
#align mul_semiring_action_hom.ext MulSemiringActionHom.ext

theorem ext_iff {f g : R →+*[M] S} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_semiring_action_hom.ext_iff MulSemiringActionHom.ext_iff

protected theorem map_zero (f : R →+*[M] S) : f 0 = 0 :=
  map_zero f
#align mul_semiring_action_hom.map_zero MulSemiringActionHom.map_zero

protected theorem map_add (f : R →+*[M] S) (x y : R) : f (x + y) = f x + f y :=
  map_add f x y
#align mul_semiring_action_hom.map_add MulSemiringActionHom.map_add

protected theorem map_neg (f : R' →+*[M] S') (x : R') : f (-x) = -f x :=
  map_neg f x
#align mul_semiring_action_hom.map_neg MulSemiringActionHom.map_neg

protected theorem map_sub (f : R' →+*[M] S') (x y : R') : f (x - y) = f x - f y :=
  map_sub f x y
#align mul_semiring_action_hom.map_sub MulSemiringActionHom.map_sub

protected theorem map_one (f : R →+*[M] S) : f 1 = 1 :=
  map_one f
#align mul_semiring_action_hom.map_one MulSemiringActionHom.map_one

protected theorem map_mul (f : R →+*[M] S) (x y : R) : f (x * y) = f x * f y :=
  map_mul f x y
#align mul_semiring_action_hom.map_mul MulSemiringActionHom.map_mul

protected theorem map_smul (f : R →+*[M] S) (m : M) (x : R) : f (m • x) = m • f x :=
  map_smul f m x
#align mul_semiring_action_hom.map_smul MulSemiringActionHom.map_smul

variable (M)

/-- The identity map as an equivariant ring homomorphism. -/
protected def id : R →+*[M] R :=
  ⟨.id _, rfl, (fun _ _ => rfl)⟩
#align mul_semiring_action_hom.id MulSemiringActionHom.id

@[simp]
theorem id_apply (x : R) : MulSemiringActionHom.id M x = x :=
  rfl
#align mul_semiring_action_hom.id_apply MulSemiringActionHom.id_apply

variable {M T}

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : S →+*[M] T) (f : R →+*[M] S) : R →+*[M] T :=
  { DistribMulActionHom.comp (g : S →+[M] T) (f : R →+[M] S),
    RingHom.comp (g : S →+* T) (f : R →+* S) with }
#align mul_semiring_action_hom.comp MulSemiringActionHom.comp

@[simp]
theorem comp_apply (g : S →+*[M] T) (f : R →+*[M] S) (x : R) : g.comp f x = g (f x) :=
  rfl
#align mul_semiring_action_hom.comp_apply MulSemiringActionHom.comp_apply

@[simp]
theorem id_comp (f : R →+*[M] S) : (MulSemiringActionHom.id M).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align mul_semiring_action_hom.id_comp MulSemiringActionHom.id_comp

@[simp]
theorem comp_id (f : R →+*[M] S) : f.comp (MulSemiringActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align mul_semiring_action_hom.comp_id MulSemiringActionHom.comp_id

end MulSemiringActionHom

-- import Mathlib.Tactic.Default
import Mathlib.Control.ULift
import Mathlib.Logic.Equiv.Defs

namespace ULift

universe u v w

variable {α : Type u} {β : Type v}

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem comp_uLift_eq_uLift_comp {f : α → β} : 
    Equiv.ulift ∘ ULift.map f = f ∘ Equiv.ulift :=
  rfl
#align ulift.comp_ulift_eq_uift_comp ULift.comp_uLift_eq_uLift_comp

/-
Note : this involves 4 universes :

comp_ulift_eq_ulift_comp.{u_1 u_2 u_3 u_4} :
  ⇑equiv.ulift.{u_4 u_2} ∘ ulift.map.{u_1 u_2 u_3 u_4} ?M_3 = ?M_3 ∘ ⇑equiv.ulift.{u_3 u_1}

A discussion with Eric Rodriguez
suggested to make them explicit, so as to have only 3.
If w is another universe, one could write :

lemma comp_ulift_eq_ulift_comp {f : α → β} :
equiv.ulift.{w v} ∘ (ulift.map.{u v w} f) =
  f ∘ equiv.ulift.{w u} := rfl

-- comp_ulift_eq_ulift_comp.{u_1 u_2 u_3} :
--  ⇑equiv.ulift.{u_3 u_2} ∘ ulift.map.{u_1 u_2 u_3 u_3} ?M_3 = ?M_3 ∘ ⇑equiv.ulift.{u_3 u_1}

but then the remaining of the file does not compile anymore. -/
theorem surjective_iff_surjective {f : α → β} :
    Function.Surjective (ULift.map f) ↔ Function.Surjective f := by
  rw [← Equiv.comp_surjective, comp_uLift_eq_uLift_comp, Equiv.surjective_comp]
#align ulift.surjective_iff_surjective ULift.surjective_iff_surjective

theorem injective_iff_injective {f : α → β} :
    Function.Injective (ULift.map f) ↔ Function.Injective f := by
  rw [← Equiv.comp_injective, comp_uLift_eq_uLift_comp, Equiv.injective_comp]
#align ulift.injective_iff_injective ULift.injective_iff_injective

theorem bijective_iff_bijective {f : α → β} :
    Function.Bijective (ULift.map f) ↔ Function.Bijective f := by
  rw [← Equiv.comp_bijective, comp_uLift_eq_uLift_comp, Equiv.bijective_comp]
#align ulift.bijective_iff_bijective ULift.bijective_iff_bijective

/- Alternative lemma, but the proof requires 4 lines :

lemma bijective_iff_bijective' {f : α → β} :
  function.bijective f ↔ function.bijective (ulift.map f) :=
begin
    unfold function.bijective,
    rw [surjective_iff_surjective, injective_iff_injective],
end

-/
end ULift


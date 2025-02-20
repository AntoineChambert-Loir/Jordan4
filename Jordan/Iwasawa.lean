/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Jordan.Primitive

/-! # Iwasawa criterion for simplicity

- `IwasawaStructure`
the structure underlying the Iwasawa criterion for simplicity

- `commutator_le_of_Iwasawa` and `is_simple_of_Iwasawa`
give two versions of the Iwasawa criterion

-/

section Iwasawa

open scoped BigOperators Pointwise

variable (M : Type _) [Group M] (α : Type*) [MulAction M α]

/-- The structure underlying the Iwasawa criterion -/
structure IwasawaStructure where
/-- The subgroups of the Iwasawa structure -/
  T : α → Subgroup M
/-- The commutativity property of the subgroups -/
  is_comm : ∀ x : α, (T x).IsCommutative
/-- The conjugacy property of the subgroups -/
  is_conj : ∀ g : M, ∀ x : α, T (g • x) = MulAut.conj g • T x
/-- The subgroups generate the group -/
  is_generator : iSup T = ⊤

/- Variante de la structure d'Iwasawa :
* M action primitive sur α
* a : α
* A := T a, sous-groupe commutatif de G
* g • a = a → mul_aut.conj g A = A
* stabilizer M a ≤ normalizer A
* subgroup.normal_closure A = ⊤

Ou encore : (?)
* A : subgroup M, commutative
* normalizer A maximal
* subgroup.normal_closure A = ⊤

-/
variable {M α}

/-- The Iwasawa criterion : If a quasiprimitive action of a group G on X
  has an Iwasawa structure, then any normal subgroup that acts nontrivially
  contains the group of commutators. -/
theorem commutator_le_iwasawa (is_qprim : IsQuasipreprimitive M α) (IwaS : IwasawaStructure M α)
    {N : Subgroup M} (nN : N.Normal) (hNX : MulAction.fixedPoints N α ≠ ⊤) : commutator M ≤ N := by
  have is_transN := is_qprim.pretransitive_of_normal nN hNX
  have ntα : Nontrivial α := isnontrivial_of_nontrivial_action hNX
  obtain a : α := Nontrivial.to_nonempty.some
  refine' contains_commutators_of N nN (IwaS.T a) _ (IwaS.is_comm a)
  -- by contains_commutators_of, it suffices to prove that N ⊔ IwaS.T x = ⊤
  rw [eq_top_iff, ← IwaS.is_generator, iSup_le_iff]
  intro x
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq N a x
  rw [Subgroup.smul_def, IwaS.is_conj g a]
  rintro _ ⟨k, hk, rfl⟩
  have hg' : ↑g ∈ N ⊔ IwaS.T a := Subgroup.mem_sup_left (Subtype.mem g)
  have hk' : k ∈ N ⊔ IwaS.T a := Subgroup.mem_sup_right hk
  exact (N ⊔ IwaS.T a).mul_mem ((N ⊔ IwaS.T a).mul_mem hg' hk') ((N ⊔ IwaS.T a).inv_mem hg')

/-- The Iwasawa criterion for simplicity -/
theorem is_simple_iwasawa
    (is_nontrivial : Nontrivial M) (is_perfect : commutator M = ⊤)
    (is_qprim : IsQuasipreprimitive M α) (is_faithful : FaithfulSMul M α)
    (IwaS : IwasawaStructure M α) : IsSimpleGroup M := by
  apply IsSimpleGroup.mk
  intro N nN
  cases or_iff_not_imp_left.mpr (commutator_le_iwasawa is_qprim IwaS nN) with
  | inl h =>
    refine' Or.inl (N.eq_bot_iff_forall.mpr fun n hn => _)
    apply is_faithful.eq_of_smul_eq_smul
    intro x
    rw [one_smul]
    exact Set.eq_univ_iff_forall.mp h x ⟨n, hn⟩
   | inr h => exact Or.inr (top_le_iff.mp (le_trans (ge_of_eq is_perfect) h))

end Iwasawa

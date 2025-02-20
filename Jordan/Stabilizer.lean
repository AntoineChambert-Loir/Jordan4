/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module stabilizer
-/
import Jordan.SubMulActions
import Jordan.MultipleTransitivity
import Mathbin.GroupTheory.GroupAction.Defs

-- import group_theory.group_action.fixing_subgroup
-- import group_theory.group_action.fixing_subgroup
-- import group_theory.group_action.sub_mul_action
-- import group_theory.group_action.sub_mul_action
open scoped Pointwise

open MulAction

variable (G : Type _) [Group G] {α : Type _} [MulAction G α]

/- The goal is to easify the proof of the following result and,
above all, make it useful :
namely, if we know something about the action of (stabilizer G s) on s,
for example that it is (pre)primitive.
-/
example (s : Set α) (B : Set α) (hB : IsBlock G B) : IsBlock (stabilizer G s) (B ∩ s) :=
  by
  rw [is_block.def_one] at hB ⊢
  rintro ⟨g, hg : g • s = s⟩
  change g • (B ∩ s) = B ∩ s ∨ Disjoint (g • (B ∩ s)) (B ∩ s)
  rw [Set.smul_set_inter, hg]
  cases' hB g with hB_eq hB_dis
  · apply Or.intro_left; rw [hB_eq]
  · apply Or.intro_right
    apply Disjoint.inter_right; apply Disjoint.inter_left; exact hB_dis

-- In a first try, I had used this lemma which seems to be useful.
theorem stabilizer_smul_mem_iff (s : Set α) (g : G) (hg : g ∈ stabilizer G s) (x : α) :
    g • x ∈ s ↔ x ∈ s := by
  rw [mem_stabilizer_iff] at hg
  rw [← hg, Set.smul_mem_smul_set_iff, hg]
#align stabilizer_smul_mem_iff stabilizer_smul_mem_iff

/- However, it does not seem easy to use this result later on,
because (stabilizer G s) has not be given its action on s.
An intermediate step is the following example. -/
example (s : Set α) [DecidablePred s] (B : Set α) (hB : IsBlock (Equiv.Perm α) B) :
    IsBlock (Equiv.Perm s) (coe ⁻¹' B : Set s) :=
  by
  rw [is_block.def_one] at hB ⊢
  intro g
  suffices : ∃ k : stabilizer (Equiv.Perm α) s, ∀ x : s, coe (g • x) = (k : Equiv.Perm α) • (x : α)
  obtain ⟨k, hk⟩ := this
  suffices : g • coe ⁻¹' B = coe ⁻¹' (k • B); rw [this]
  cases' hB k with hB_eq hB_dis
  · change k • B = B at hB_eq
    apply Or.intro_left; rw [hB_eq]
  · apply Or.intro_right
    refine' Disjoint.preimage coe hB_dis
  -- g • (coe ⁻¹' B) = coe ⁻¹' (k • B),
  · ext
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
    suffices : ↑(g⁻¹ • x) = k⁻¹ • ↑x; rw [this]
    set y := g⁻¹ • x
    have hy : x = g • y := by rw [smul_inv_smul]
    rw [eq_inv_smul_iff, hy, hk y]
    rfl
  -- ∃ (k : stabilizer G s), ∀ (x : s) , coe(g • x) = (k : equiv.perm α) • (x : α))
  · have : g.of_subtype ∈ stabilizer (Equiv.Perm α) s :=
      by
      rw [mem_stabilizer_iff]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [Equiv.Perm.smul_def]
        rw [← Subtype.coe_mk y hy]
        rw [Equiv.Perm.ofSubtype_apply_coe]
        rw [← Equiv.Perm.smul_def]; simp only [Subtype.coe_prop]
      · intro hx
        let y := g⁻¹ • (⟨x, hx⟩ : s)
        use y
        constructor
        exact y.prop
        rw [Equiv.Perm.smul_def, Equiv.Perm.ofSubtype_apply_coe, ← Equiv.Perm.smul_def]
        rw [smul_inv_smul]
        rfl
    use g.of_subtype
    · exact this
    · intro x
      simp only [Equiv.Perm.smul_def, Subgroup.coe_mk]
      change _ = g.of_subtype • ↑x
      rw [Equiv.Perm.smul_def]
      rw [Equiv.Perm.ofSubtype_apply_coe]

/- This is not so satisfactory. In fact, what the previous proofs do, is emulating
the proof of
`is_block_preimage :
  ∀ (j : α →ₑ[φ] β) {B : set β}, is_block H β → is_block G (⇑j ⁻¹' B)`
in the presence of `mul_action G α` and `mul_action H β`,
with `φ : G → H`.
Let us try to use it, rather than reproving it.
We need to introduce adequate equivariant maps between `mul_action`s.

The point is that we don't have a natural map
`equiv.perm s → G`, but we have obvious maps
`stabilizer G s → equiv.perm s` and `stabilizer G s → G`
so we'll have to do it in two steps.

The second, `stabilizer G s → G` is just inclusion, but
the first map is best done via the natural `mul_action` of
`stabilizer G s` on `s` and `to_perm`  -/
/-- The instance that makes the stabilizer of a set acting on that set -/
instance SMul.stabilizer (s : Set α) : SMul (↥(stabilizer G s)) ↥s
    where smul := fun ⟨g, hg⟩ ⟨x, hx⟩ =>
    ⟨g • x, by
      rw [← mem_stabilizer_iff.mp hg]
      exact Set.smul_mem_smul_set hx⟩
#align has_smul.stabilizer SMul.stabilizer

@[simp]
theorem SMul.stabilizer_def (s : Set α) (g : stabilizer G s) (x : s) :
    coe (g • x) = (g : G) • (x : α) :=
  by
  rw [← Subtype.coe_eta g g.prop]
  rw [← Subtype.coe_eta x x.prop]
  rfl
#align has_smul.stabilizer_def SMul.stabilizer_def

/-- The mul_action of stabilizer a set on that set -/
instance MulAction.ofStabilizer' (s : Set α) : MulAction (stabilizer G s) s
    where
  one_smul := fun ⟨x, hx⟩ => by
    rw [← Subtype.coe_inj, SMul.stabilizer_def, Subgroup.coe_one, one_smul]
  mul_smul := fun ⟨g, hg⟩ ⟨k, hk⟩ ⟨x, hx⟩ =>
    by
    rw [← Subtype.coe_inj, Submonoid.mk_mul_mk]
    simp only [SMul.stabilizer_def, Subtype.coe_mk, MulAction.mul_smul]
#align mul_action.of_stabilizer' MulAction.ofStabilizer'

theorem MulAction.of_stabilizer_def' (s : Set α) (g : stabilizer G s) (x : s) :
    (g : G) • (x : α) = g • (x : α) :=
  rfl
#align mul_action.of_stabilizer_def' MulAction.of_stabilizer_def'

theorem MulAction.of_stabilizer_set_def' (s : Set α) (g : stabilizer G s) (t : Set α) :
    (g : G) • t = g • t := by rfl
#align mul_action.of_stabilizer_set_def' MulAction.of_stabilizer_set_def'

theorem Equiv.Perm.ofSubtype.mem_stabilizer (s : Set α) [DecidablePred s] (g : Equiv.Perm ↥s) :
    Equiv.Perm.ofSubtype g ∈ stabilizer (Equiv.Perm α) s :=
  by
  rw [mem_stabilizer_iff]
  ext; constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Equiv.Perm.smul_def]
    rw [Equiv.Perm.ofSubtype_apply_of_mem g hy]
    simp only [Subtype.coe_prop]
  · intro hx
    suffices : ∃ y : s, (⟨x, hx⟩ : ↥s) = g • y
    obtain ⟨⟨y, hy⟩, hxy⟩ := this
    use (⟨y, hy⟩ : ↥s)
    rw [← Subtype.coe_mk x hx, hxy]
    simp only [hy, Equiv.Perm.ofSubtype_apply_of_mem, Subtype.coe_mk, Equiv.Perm.smul_def,
      eq_self_iff_true, and_self_iff]
    obtain ⟨y⟩ := Equiv.surjective g (⟨x, hx⟩ : ↥s)
    use y; simp only [← h, Equiv.Perm.smul_def]
#align equiv.perm.of_subtype.mem_stabilizer Equiv.Perm.ofSubtype.mem_stabilizer

-- So let's do it !
example (s : Set α) [DecidablePred s] (B : Set α) (hB : IsBlock (Equiv.Perm α) B) :
    IsBlock (Equiv.Perm s) (coe ⁻¹' B : Set s) :=
  by
  let φ : stabilizer (Equiv.Perm α) s → Equiv.Perm s := to_perm
  let j : s →ₑ[φ] s :=
    { toFun := id
      map_smul' := fun g x => rfl }
  rw [← Set.image_id (coe ⁻¹' B)]
  apply is_block_image j
  -- surjectivity of φ,
  · intro g
    use Equiv.Perm.ofSubtype g
    apply Equiv.Perm.ofSubtype.mem_stabilizer
    · ext ⟨x, hx⟩
      simp only [hx, Equiv.Perm.ofSubtype_apply_of_mem, to_perm_apply, SMul.stabilizer_def,
        Subtype.coe_mk, Equiv.Perm.smul_def]
  apply Function.Bijective.injective
  apply Function.bijective_id
  let ψ : stabilizer (Equiv.Perm α) s → Equiv.Perm α := coe
  let k : s →ₑ[ψ] α :=
    { toFun := coe
      map_smul' := fun g x => by simp }
  apply is_block_preimage k hB

-- To prove the required surjectivity
variable (α)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def equivariantMapId : α →[G] α where
  toFun := id
  map_smul' g x := rfl
#align equivariant_map_id equivariantMapId

variable {α}

def equivariantMapOfStabilizerCoe (s : Set α) [DecidablePred s] :
    let φ : stabilizer G s → G := coe
    s →ₑ[φ] α
    where
  toFun := coe
  map_smul' g x := by simp
#align equivariant_map_of_stabilizer_coe equivariantMapOfStabilizerCoe

def equivariantMapOfStabilizerToPerm (s : Set α) [DecidablePred s] :
    let φ : stabilizer G s → Equiv.Perm s := toPerm
    s →ₑ[φ] s
    where
  toFun := id
  map_smul' g x := rfl
#align equivariant_map_of_stabilizer_to_perm equivariantMapOfStabilizerToPerm

theorem surjective_of_stabilizer_smul (s : Set α) [DecidablePred s] :
    Function.Surjective (equivariantMapOfStabilizerToPerm (Equiv.Perm α) s).toSmulMap :=
  by
  intro g
  use g.of_subtype
  · rw [mem_stabilizer_iff]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Equiv.Perm.smul_def]
      rw [← Subtype.coe_mk y hy]
      rw [Equiv.Perm.ofSubtype_apply_coe]
      rw [← Equiv.Perm.smul_def]; simp only [Subtype.coe_prop]
    · intro hx
      let y := g⁻¹ • (⟨x, hx⟩ : s)
      use y
      constructor
      exact y.prop
      rw [Equiv.Perm.smul_def, Equiv.Perm.ofSubtype_apply_coe, ← Equiv.Perm.smul_def]
      rw [smul_inv_smul]
      rfl
  · ext
    rw [equivariantMapOfStabilizerToPerm, EquivariantMap.toSmulMap]
    simp only [Equiv.Perm.smul_def, Equiv.Perm.ofSubtype_apply_coe, to_perm_apply,
      SMul.stabilizer_def, Subgroup.coe_mk]
#align surjective_of_stabilizer_smul surjective_of_stabilizer_smul

example (s : Set α) [DecidablePred s] (B : Set α) (hB : IsBlock (Equiv.Perm α) B) :
    IsBlock (Equiv.Perm s) (coe ⁻¹' B : Set s) :=
  by
  rw [← Set.image_id (coe ⁻¹' B)]
  apply is_block_image (equivariantMapOfStabilizerToPerm (Equiv.Perm α) s)
  apply surjective_of_stabilizer_smul
  apply Function.Bijective.injective
  apply Function.bijective_id
  apply is_block_preimage (equivariantMapOfStabilizerCoe (Equiv.Perm α) s) hB

/- This is much clearer.
But we want a general purpose lemma that can serve for
other groups than `equiv.perm s`
 -/
theorem Le.isBlock {H K : Subgroup G} (hHK : H ≤ K) {B : Set α} (hfB : IsBlock K B) : IsBlock H B :=
  by
  rw [is_block.def_one]; rintro ⟨g, hg⟩
  simpa only using is_block.def_one.mp hfB ⟨g, hHK hg⟩
#align le.is_block Le.isBlock

theorem isBlock_of_top (H : Subgroup G) {B : Set α} (hB : IsBlock H B) (hH : H = ⊤) : IsBlock G B :=
  by
  rw [is_block.def_one] at hB ⊢
  intro g
  refine' hB ⟨g, _⟩
  rw [hH]; apply Subgroup.mem_top
#align is_block_of_top isBlock_of_top

theorem isBlock_preimage_coe (s : Set α) [DecidablePred s] (H : Subgroup (Equiv.Perm s))
    -- (hH : ∀ g ∈ H, ∃ (k : stabilizer G s), (to_perm k: equiv.perm s) = g)
    (hH : H ≤ Subgroup.map (MulAction.toPermHom (stabilizer G s) s) ⊤)
    (B : Set α) (hB : IsBlock G B) : IsBlock H (coe ⁻¹' B : Set s) :=
  by
  apply Le.isBlock
  exact hH
  let φ : stabilizer G s → Subgroup.map (MulAction.toPermHom (stabilizer G s) s) ⊤ := fun u =>
    ⟨to_perm_hom (stabilizer G s) s u, by
      simp only [Subgroup.mem_map, Subgroup.mem_top, exists_true_left, exists_apply_eq_apply]⟩
  let j : s →ₑ[φ] s :=
    { toFun := id
      map_smul' := fun g x => rfl }
  rw [← Set.image_id (coe ⁻¹' B)]
  apply is_block_image j
  · rintro ⟨g, hg⟩
    obtain ⟨k, hk, rfl⟩ := hg
    use k; rfl
  apply Function.Bijective.injective
  apply Function.bijective_id
  let ψ : stabilizer G s → G := coe
  let k : s →ₑ[ψ] α :=
    { toFun := coe
      map_smul' := fun g x => by simp only [SMul.stabilizer_def] }
  apply is_block_preimage k hB
#align is_block_preimage_coe isBlock_preimage_coe

example (s : Set α) [DecidablePred s] (B : Set α) (hB : IsBlock (Equiv.Perm α) B) :
    IsBlock (Equiv.Perm s) (coe ⁻¹' B : Set s) :=
  by
  apply isBlock_of_top
  refine' isBlock_preimage_coe (Equiv.Perm α) s ⊤ _ B hB
  · intro g _
    obtain ⟨k, hk⟩ := surjective_of_stabilizer_smul s g
    use k
    rw [← hk]
    simp only [Subgroup.coe_top, Set.mem_univ, to_perm_hom_apply, true_and_iff]
    rfl
  rfl

theorem surjective_of_stabilizer_smul' [DecidableEq α] [Fintype α] (s : Set α) [DecidablePred s]
    (hsc : 2 ≤ Fintype.card (sᶜ : Set α)) :
    Function.Surjective (equivariantMapOfStabilizerToPerm (alternatingGroup α) s).toSmulMap :=
  by
  skip
  have : ∃ a b : (sᶜ : Set α), a ≠ b := by rw [← Fintype.one_lt_card_iff]; exact hsc
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := this; simp at hab
  let k := Equiv.swap a b
  have hk_sign : k.sign = -1; simp only [Equiv.Perm.sign_swap', hab, if_false]
  have hk_apply : ∀ x ∈ s, k x = x := by
    intro x hx
    refine' Equiv.swap_apply_of_ne_of_ne _ _
    intro hxa; rw [Set.mem_compl_iff] at ha ; apply ha; rw [← hxa]; exact hx
    intro hxb; rw [Set.mem_compl_iff] at hb ; apply hb; rw [← hxb]; exact hx
  have hk_mem : k ∈ stabilizer (Equiv.Perm α) s :=
    by
    rw [mem_stabilizer_iff]
    suffices k • s ≤ s by
      apply le_antisymm
      exact this
      intro x hx
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp only [Equiv.swap_inv]
      -- equiv.perm.smul_def],
      apply this
      simp [hx]
      use x; apply And.intro hx; simp
    · intro x; rintro ⟨y, hy, rfl⟩
      rw [Equiv.Perm.smul_def, hk_apply y hy]
      exact hy
  intro g
  have hg : g.of_subtype ∈ stabilizer (Equiv.Perm α) s :=
    by
    rw [mem_stabilizer_iff]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Equiv.Perm.smul_def]
      rw [← Subtype.coe_mk y hy]
      rw [Equiv.Perm.ofSubtype_apply_coe]
      rw [← Equiv.Perm.smul_def]; simp only [Subtype.coe_prop]
    · intro hx
      let y := g⁻¹ • (⟨x, hx⟩ : s)
      use y
      constructor
      exact y.prop
      rw [Equiv.Perm.smul_def, Equiv.Perm.ofSubtype_apply_coe, ← Equiv.Perm.smul_def]
      rw [smul_inv_smul]
      rfl
  use ite (g.sign = 1) g.of_subtype (g.of_subtype * k)
  · simp only [Equiv.Perm.mem_alternatingGroup]
    by_cases hg_sign : g.sign = 1
    simp only [hg_sign, eq_self_iff_true, if_true, Equiv.Perm.sign_ofSubtype]
    simp only [hg_sign, hk_sign, if_false, Equiv.Perm.sign_mul, Equiv.Perm.sign_ofSubtype, mul_neg,
      mul_one]
    · cases Int.units_eq_one_or (Equiv.Perm.sign g)
      exfalso; exact hg_sign h
      rw [h]; apply neg_neg
  · by_cases hg_sign : g.sign = 1
    simp only [hg_sign, eq_self_iff_true, if_true]
    exact hg
    simp only [hg_sign, if_false]
    dsimp at hk_mem hg ⊢
    change (g.of_subtype * k) • s = s
    rw [MulAction.mul_smul, hk_mem, hg]
  · ext
    rw [equivariantMapOfStabilizerToPerm, EquivariantMap.toSmulMap]
    simp only [to_perm_apply, SMul.stabilizer_def, Subgroup.coe_mk]
    by_cases hg_sign : g.sign = 1 <;> simp only [hg_sign, eq_self_iff_true, if_true, if_false]
    -- ⟨⇑equiv.perm.of_subtype g, _⟩ • ↑x = ↑(⇑g x)
    change Equiv.Perm.ofSubtype g ↑x = ↑(g x)
    rw [Equiv.Perm.ofSubtype_apply_coe]
    -- ⟨⇑equiv.perm.of_subtype g * k, _⟩ • ↑x = ↑(⇑g x)
    change (Equiv.Perm.ofSubtype g * k) • ↑x = ↑(g x)
    rw [MulAction.mul_smul]
    simp only [Equiv.Perm.smul_def]
    rw [hk_apply, Equiv.Perm.ofSubtype_apply_coe]
    exact x.prop
#align surjective_of_stabilizer_smul' surjective_of_stabilizer_smul'

example [DecidableEq α] [Fintype α] (s : Set α) [DecidablePred s]
    (hsc : 2 ≤ Fintype.card (sᶜ : Set α)) (B : Set α) (hB : IsBlock (alternatingGroup α) B) :
    IsBlock (Equiv.Perm s) (coe ⁻¹' B : Set s) :=
  by
  apply isBlock_of_top
  refine' isBlock_preimage_coe (alternatingGroup α) s ⊤ _ B hB
  · intro g _
    obtain ⟨k, hk⟩ := surjective_of_stabilizer_smul' s hsc g
    use k
    rw [← hk]
    simp only [Subgroup.coe_top, Set.mem_univ, to_perm_hom_apply, true_and_iff]
    rfl
  rfl

-- We might wish a more general lemma
variable {G}

theorem isBlock_preimage_comap {H : Type _} [Group H] {β : Type _} [MulAction H β] {φ : H →* G}
    (f : β →ₑ[φ] α) (K : Subgroup G) (L : Subgroup H) (hHK : L ≤ K.comap φ) {B : Set α}
    (hB : IsBlock K B) : IsBlock L (f ⁻¹' B) :=
  by
  apply Le.isBlock; exact hHK
  let f' : β →ₑ[MonoidHom.subgroupComap φ K] α :=
    { toFun := f
      map_smul' := fun ⟨m, hm⟩ x => by
        change f (m • x) = _; rw [f.map_smul]
        apply congr_arg; rfl }
  apply MulAction.isBlock_preimage f' hB
#align is_block_preimage_comap isBlock_preimage_comap

example (s : Set α) [DecidablePred s] (B : Set α) (hB : IsBlock (Equiv.Perm α) B) :
    IsBlock (Equiv.Perm s) (coe ⁻¹' B : Set s) :=
  by
  rw [← Set.image_id (coe ⁻¹' B)]
  apply is_block_image (equivariantMapOfStabilizerToPerm (Equiv.Perm α) s)
  apply surjective_of_stabilizer_smul
  apply Function.Bijective.injective
  apply Function.bijective_id
  apply is_block_preimage (equivariantMapOfStabilizerCoe (Equiv.Perm α) s) hB

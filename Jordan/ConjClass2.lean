import Oneshot.ConjClassCount
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.Algebra.Group.Semiconj
import Oneshot.IndexNormal
import Oneshot.EquivariantMap

variable {G : Type _} [Group G] (H : Subgroup G)

theorem Subgroup.relindex_swap {G : Type _} [Group G] (H K : Subgroup G) :
    H.relindex K * K.index = K.relindex H * H.index :=
  by
  rw [← Subgroup.inf_relindex_right H, Subgroup.relindex_mul_index (inf_le_right : H ⊓ K ≤ K)]
  rw [← Subgroup.inf_relindex_right K, Subgroup.relindex_mul_index (inf_le_right : K ⊓ H ≤ H)]
  rw [inf_comm]
#align subgroup.relindex_swap Subgroup.relindex_swap

theorem Subgroup.Nat.card_eq_mul' (H K : Subgroup G) (hK : 0 < K.index) :
    Nat.card K = H.relindex K * Nat.card (K.subgroupOf H) :=
  by
  rw [mul_comm]
  rw [← mul_left_inj' (ne_of_gt hK)]
  rw [Subgroup.card_mul_index K]
  rw [mul_assoc]
  rw [← Subgroup.card_mul_index H]
  rw [← Subgroup.card_mul_index (K.subgroup_of H)]
  simp only [mul_assoc]
  apply congr_arg₂ (· * ·) rfl
  apply Subgroup.relindex_swap
#align subgroup.nat.card_eq_mul' Subgroup.Nat.card_eq_mul'

theorem ConjAct.stabilizer_eq_comap (g : H) :
    Subgroup.comap
        (ConjAct.toConjAct.toMonoidHom.comp (H.Subtype.comp ConjAct.ofConjAct.toMonoidHom) :
          ConjAct H →* ConjAct G)
        (MulAction.stabilizer (ConjAct G) (g : G)) =
      MulAction.stabilizer (ConjAct H) g :=
  by
  ext k
  induction' k using ConjAct.rec with k
  simp only [Subgroup.mem_comap, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Subgroup.coeSubtype,
    Function.comp_apply, MulAction.mem_stabilizer_iff]
  simp only [ConjAct.ofConjAct_toConjAct, ConjAct.smul_def]
  rw [← Subtype.coe_inj]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
#align conj_act.stabilizer_eq_comap ConjAct.stabilizer_eq_comap

theorem mem_zpowers_centralizer_iff (h k : G) :
    k ∈ (Subgroup.zpowers h).centralizer ↔ h * k = k * h :=
  by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  intro H
  apply H h; exact Subgroup.mem_zpowers h
  intro H
  intro g hg
  rw [Subgroup.zpowers_eq_closure] at hg 
  apply Subgroup.closure_induction hg
  · intro x hx; simp only [Set.mem_singleton_iff] at hx ; rw [hx]; exact H
  · rw [one_mul, mul_one]
  · intro x y hx hy; rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  · intro x hx; rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_assoc, mul_inv_self, mul_one]
#align mem_zpowers_centralizer_iff mem_zpowers_centralizer_iff

theorem Subgroup.relindex_of_index_two (K : Subgroup G) (hH : H.index = 2) :
    ¬K ≤ H → H.relindex K = 2 := by
  intro hK
  haveI : Subgroup.Normal H := Subgroup.normal_of_index_eq_two hH
  suffices : H.relindex K = 1 ∨ H.relindex K = 2
  cases' this with h1 h2
  · exfalso; apply hK; rw [← Subgroup.relindex_eq_one]; exact h1
  · exact h2
  apply Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two
  rw [← Subgroup.relindex_sup_left]
  rw [← hH]
  refine' Subgroup.relindex_dvd_index_of_normal H (H ⊔ K)
#align subgroup.relindex_of_index_two Subgroup.relindex_of_index_two

theorem MulAction.card_orbit_eq_stabilizer_index {G : Type _} [Group G] [Fintype G] {X : Type _}
    [Fintype X] [MulAction G X] (x : X) :
    Nat.card (MulAction.orbit G x) = (MulAction.stabilizer G x).index := by
  classical
  simp only [Nat.card_eq_fintype_card]
  apply Nat.eq_of_mul_eq_mul_left (_ : 0 < Fintype.card (MulAction.stabilizer G x))
  rw [mul_comm]
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group]
  rw [mul_comm]
  rw [Subgroup.index_mul_card]
  refine' Fintype.card_pos
#align mul_action.card_orbit_eq_stabilizer_index MulAction.card_orbit_eq_stabilizer_index

theorem MulAction.card_orbit_of_subgroup {G : Type _} [Group G] [Fintype G] {X : Type _} [Fintype X]
    [MulAction G X] (H : Subgroup G) (x : X) :
    (Subgroup.map (Subgroup.subtype H) (MulAction.stabilizer H x)).relindex
          (MulAction.stabilizer G x) *
        Nat.card (MulAction.orbit G x) =
      H.index * Nat.card (MulAction.orbit H x) :=
  by
  classical
  simp only [MulAction.card_orbit_eq_stabilizer_index]
  rw [Subgroup.relindex_mul_index]
  rw [mul_comm]
  rw [Subgroup.index_map]
  simp only [Subgroup.ker_subtype, sup_bot_eq, Subgroup.subtype_range]
  rw [Subgroup.map_le_iff_le_comap]
  intro h
  rw [Subgroup.mem_comap]
  simp only [MulAction.mem_stabilizer_iff]
  exact id
#align mul_action.card_orbit_of_subgroup MulAction.card_orbit_of_subgroup

theorem MulAction.card_orbit_of_equivariant {G : Type _} [Group G] [Fintype G] {X : Type _}
    [Fintype X] [MulAction G X] {H : Type _} [Group H] [Fintype H] {Y : Type _} [Fintype Y]
    [MulAction H Y] (φ : H →* G) (f : Y →ₑ[φ] X) (y : Y) (hy : φ.ker ≤ MulAction.stabilizer H y) :
    (Subgroup.map φ (MulAction.stabilizer H y)).relindex (MulAction.stabilizer G (f y)) *
        Nat.card (MulAction.orbit G (f y)) =
      φ.range.index * Nat.card (MulAction.orbit H y) :=
  by
  classical
  simp only [MulAction.card_orbit_eq_stabilizer_index]
  rw [Subgroup.relindex_mul_index]
  rw [mul_comm]
  rw [Subgroup.index_map]
  simp only [Subgroup.ker_subtype, sup_bot_eq, Subgroup.subtype_range, sup_of_le_left hy]
  rw [Subgroup.map_le_iff_le_comap]
  intro h
  rw [Subgroup.mem_comap]
  simp only [MulAction.mem_stabilizer_iff]
  intro h'
  rw [← f.map_smul h y, h']
#align mul_action.card_orbit_of_equivariant MulAction.card_orbit_of_equivariant

example [Fintype G] (hH : H.index = 2) (K : Subgroup (ConjAct G)) :
    (H.map (ConjAct.toConjAct.toMonoidHom : G →* ConjAct G)).relindex K = 1 :=
  by
  rw [← Subgroup.map_comap_eq_self_of_surjective _ K]
  --  suffices : K = subgroup.map conj_act.to_conj_act.to_monoid_hom (subgroup.comap conj_act.of_conj_act.to_monoid_hom K),
  -- rw this,
  rw [← Subgroup.relindex_comap]
  rw [Subgroup.comap_map_eq_self_of_injective]
  rw [Subgroup.relindex_eq_one]
  sorry
  exact conj_act.to_conj_act.injective
  exact conj_act.of_conj_act.surjective

theorem Subgroup.conj_class_card_of_index [Fintype G] (g : H) :
    (H.map (ConjAct.toConjAct.toMonoidHom : G →* ConjAct G)).relindex
          (MulAction.stabilizer (ConjAct G) (g : G)) *
        Nat.card (MulAction.orbit (ConjAct G) (g : G)) =
      H.index * Nat.card (MulAction.orbit (ConjAct H) g) :=
  by
  classical
  let φ : ConjAct H →* ConjAct G :=
    (conj_act.to_conj_act.to_monoid_hom.comp H.subtype).comp conj_act.of_conj_act.to_monoid_hom
  let f : H →ₑ[φ] G :=
    { toFun := H.subtype.to_fun
      map_smul' := fun m a => by simp [φ, ConjAct.smul_def] }
  suffices hφ : φ.range.index = H.index
  rw [← hφ]
  rw [← MulAction.card_orbit_of_equivariant φ f g _]
  apply congr_arg₂ (· * ·) _ rfl
  dsimp [f]
  rw [← Subgroup.inf_relindex_right]
  apply congr_arg₂ Subgroup.relindex _ rfl
  · rw [← ConjAct.stabilizer_eq_comap]
    dsimp only [φ]
    simp only [← Subgroup.map_map, ← Subgroup.comap_comap]
    rw [Subgroup.map_comap_eq]
    apply le_antisymm
    · intro k
      rw [Subgroup.mem_inf]
      rintro ⟨hk, hk'⟩
      rw [Subgroup.mem_map] at hk 
      obtain ⟨h, hH, rfl⟩ := hk
      rw [Subgroup.mem_map]
      use h
      rw [Subgroup.mem_map]
      use (⟨h, hH⟩ : H)
      constructor
      rw [Subgroup.mem_inf]
      constructor
      rw [MonoidHom.mem_range]
      use ConjAct.toConjAct (⟨h, hH⟩ : H)
      simp only [MulAction.mem_stabilizer_iff] at hk' ⊢
      simp only [MulEquiv.coe_toMonoidHom, ConjAct.ofConjAct_toConjAct]
      simp only [Subgroup.comap_subtype]
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_comap]
      exact hk'
      rfl
    · intro k hk
      rw [Subgroup.mem_map] at hk 
      obtain ⟨h, hh, rfl⟩ := hk
      rw [Subgroup.mem_map] at hh 
      obtain ⟨k, hk, rfl⟩ := hh
      rw [Subgroup.mem_inf] at hk 
      simp only [Subgroup.mem_comap] at hk 
      constructor
      simp only [Subgroup.coeSubtype, MulEquiv.coe_toMonoidHom, Subgroup.coe_toSubmonoid,
        Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, MulEquiv.apply_eq_iff_eq, exists_eq_right,
        SetLike.coe_mem]
      exact hk.2
  suffices : φ.ker = ⊥
  rw [this]
  exact bot_le
  rw [MonoidHom.ker_eq_bot_iff]
  simp only [φ, MonoidHom.coe_comp]
  rw [Function.Injective.of_comp_iff _]
  exact conj_act.of_conj_act.injective
  rw [Function.Injective.of_comp_iff _]
  exact H.subtype_injective
  exact conj_act.to_conj_act.injective
  dsimp only [φ]
  rw [MonoidHom.range_eq_map, ← Subgroup.map_map, Subgroup.index_map]
  rw [Subgroup.map_top_of_surjective _]
  simp only [top_sup_eq, Subgroup.index_top, one_mul]
  rw [MonoidHom.range_eq_map, ← Subgroup.map_map, Subgroup.index_map]
  rw [← mul_one H.index]
  apply congr_arg₂ (· * ·)
  apply congr_arg
  have : H = H ⊔ ⊥ := by rw [sup_bot_eq]
  conv_rhs => rw [this]
  apply congr_arg₂ (· ⊔ ·)
  rw [← MonoidHom.range_eq_map]
  exact Subgroup.subtype_range H
  rw [MonoidHom.ker_eq_bot_iff]
  exact conj_act.to_conj_act.injective
  rw [Subgroup.index_eq_one]
  rw [MonoidHom.range_top_iff_surjective]
  exact conj_act.to_conj_act.surjective
  exact conj_act.to_conj_act.surjective
#align subgroup.conj_class_card_of_index Subgroup.conj_class_card_of_index

open scoped Classical

example (hH : H.index = 2) [Fintype G] (g : H) :
    (if MulAction.stabilizer (ConjAct G) (g : G) ≤ H then 2 else 1) *
        Fintype.card (MulAction.orbit (ConjAct H) g) =
      Fintype.card (MulAction.orbit (ConjAct G) (g : G)) :=
  by
  suffices :
    Fintype.card (MulAction.stabilizer (ConjAct G) (g : G)) =
      ite (MulAction.stabilizer (ConjAct G) (g : G) ≤ H) 1 2 *
        Fintype.card (MulAction.stabilizer (ConjAct H) g)
  rw [← mul_left_inj' _]
  -- nat.eq_of_mul_eq_mul_left  _,
  rw [mul_assoc]
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ (g : G)]
  rw [this]
  simp only [mul_assoc]; rw [mul_comm]; rw [← mul_assoc]
  rw [ConjAct.card]
  rw [← Subgroup.index_mul_card H]
  rw [hH]
  simp only [← mul_assoc]; rw [mul_comm]
  nth_rw 3 [mul_comm]
  simp only [mul_assoc]
  -- rw mul_comm (fintype.card ↥(mul_action.stabilizer (conj_act ↥H) g)),
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group]
  -- rw mul_comm,
  simp only [← mul_assoc]
  apply congr_arg₂ _ _ rfl
  by_cases hg : MulAction.stabilizer (ConjAct G) (g : G) ≤ H
  · simp only [if_pos hg, mul_one]
  · simp only [if_neg hg, one_mul]
  exact Fintype.card_ne_zero
  simp_rw [ConjAct.stabilizer_eq_centralizer]
  rw [← Nat.card_eq_fintype_card]
  rw [Subgroup.Nat.card_eq_mul' H]
  apply congr_arg₂
  · split_ifs with hK
    rw [Subgroup.relindex_eq_one]; exact hK
    exact Subgroup.relindex_of_index_two _ _ hH hK
  · rw [Nat.card_eq_fintype_card]
    apply Fintype.card_congr'
    apply congr_arg coeSort
    · ext k
      rw [Subgroup.mem_subgroupOf]
      simp only [mem_zpowers_centralizer_iff]
      simp only [← Subgroup.coe_mul]; rw [Subtype.coe_inj]
  rw [zero_lt_iff]; exact Subgroup.index_ne_zero_of_finite

variable {α : Type _} [Fintype α] [DecidableEq α]

variable (g : Equiv.Perm α)

theorem kerφ_le_alternating_iff (g : Equiv.Perm α) (m : Multiset ℕ) (hg : g.cycleType = m) :
    MulAction.stabilizer (ConjAct (Equiv.Perm α)) g ≤ alternatingGroup α ↔
      (∀ i ∈ m, Odd i) ∧ m.Sum + 1 ≥ Fintype.card α ∧ ∀ i, m.count i ≤ 1 :=
  by
  rw [SetLike.le_def]
  simp_rw [Equiv.Perm.mem_alternatingGroup]
  constructor
  · intro h
    suffices h_odd; suffices h_fixed; suffices h_count
    constructor; exact h_odd
    constructor; exact h_fixed; exact h_count
    · -- ∀ i, m.count i ≤ 1
      rw [← Multiset.nodup_iff_count_le_one, ← hg, Equiv.Perm.cycleType_def]
      rw [Multiset.nodup_map_iff_inj_on g.cycle_factors_finset.nodup]
      simp only [Function.comp_apply, ← Finset.mem_def]
      by_contra hm
      push_neg at hm 
      obtain ⟨c, hc, d, hd, hm, hm'⟩ := hm
      let τ : Equiv.Perm g.cycle_factors_finset := Equiv.swap ⟨c, hc⟩ ⟨d, hd⟩
      obtain ⟨a, ha⟩ := OnCycleFactors.exists_base_points g
      suffices hτ : τ ∈ OnCycleFactors.iφ g
      let kk := OnCycleFactors.φ' ha ⟨τ, hτ⟩
      let k : Equiv.Perm α := ConjAct.ofConjAct ↑kk
      -- obtain ⟨a, k, ha, hk1, hk2, hka, hksup⟩ := is_surjective_aux g τ _,
      have hk1 : k * g = g * k := by rw [← Equiv.coe_inj]; exact OnCycleFactors.k_commute ha hτ
      have hk2 : ∀ c : g.cycle_factors_finset, ConjAct.toConjAct k • (c : Equiv.Perm α) = τ c :=
        by
        intro c
        rw [ConjAct.smul_def]
        simp only [ConjAct.ofConjAct_toConjAct]
        rw [mul_inv_eq_iff_eq_mul]
        ext x
        exact OnCycleFactors.k_cycle_apply ha hτ c x
      have hka : k ∘ a = a ∘ τ := by ext c; exact OnCycleFactors.k_apply ha c 0 hτ
      have hksup : k.support ≤ g.support := by
        intro x
        simp only [Equiv.Perm.mem_support]
        intro hx' hx; apply hx'
        rw [← Equiv.Perm.not_mem_support] at hx 
        exact OnCycleFactors.k_apply_of_not_mem_support ha x hx
      suffices hsign_k : k.sign = -1
      · rw [h _, ← Units.eq_iff] at hsign_k ; exact Int.noConfusion hsign_k
        exact kk.prop
      · /- prouver que k est le produit des transpositions à support disjoint
                  [(g ^ n) (a c), (g ^ n) (a d)], pour 0 ≤ n < c.support.card
                  mais il va suffire de remarquer que k ^ 2 = 1, et de contrôler son support -/
        suffices k.cycle_type = Multiset.replicate c.support.card 2
          by
          rw [Equiv.Perm.sign_of_cycleType]; rw [this]
          simp only [Multiset.sum_replicate, Algebra.id.smul_eq_mul, Multiset.card_replicate]
          rw [Odd.neg_one_pow]
          rw [Nat.odd_add']
          simp only [h_odd c.support.card
              (by rw [← hg, Equiv.Perm.cycleType_def, Multiset.mem_map]; exact ⟨c, hc, rfl⟩),
            true_iff_iff]
          rw [mul_comm]; apply even_two_mul
        -- on_cycle_count.same_cycle_of_mem_support
        have hk_apply :
          ∀ (c : g.cycle_factors_finset) (m n : ℕ),
            (k ^ m) ((g ^ n : Equiv.Perm α) (a c)) = (g ^ n) (a ((τ ^ m) c)) :=
          by
          suffices : ∀ m n : ℕ, Commute (k ^ m) (g ^ n)
          intro c m n
          simp only [Commute, SemiconjBy] at this 
          rw [← Equiv.Perm.mul_apply, this, Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq]
          induction' m with m hrec
          · simp only [pow_zero, Equiv.Perm.coe_one, id.def]
          · rw [pow_succ, Equiv.Perm.mul_apply]
            rw [hrec]
            rw [OnCycleFactors.φ'_apply ha hτ]
            rw [OnCycleFactors.k_apply_base ha _ hτ]
            rw [pow_succ]; rw [Equiv.Perm.coe_mul]
          apply Commute.pow_pow
          rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
          rw [← MulAction.ConjAct.mem_stabilizer_iff]
          exact kk.prop
        suffices ∀ i ∈ k.cycle_type, i = 2
          by
          rw [← Multiset.eq_replicate_card] at this 
          rw [this]
          apply congr_arg₂ _ _ rfl
          have this' := Equiv.Perm.sum_cycleType k
          rw [this] at this' 
          simp only [Multiset.sum_replicate, Algebra.id.smul_eq_mul] at this' 
          rw [← mul_left_inj']; rw [this']
          suffices this2 : k.support = c.support ∪ d.support
          rw [this2]; rw [Finset.card_union_eq _]
          suffices this3 : d.support.card = c.support.card
          rw [this3]; rw [mul_two]
          exact hm.symm
          rw [← Equiv.Perm.disjoint_iff_disjoint_support]
          by_contra hcd; apply hm'
          exact Set.Pairwise.eq g.cycle_factors_finset_pairwise_disjoint hc hd hcd
          · -- k.support = c.support ∪ d.support
            ext x
            constructor
            · intro hx
              --              obtain ⟨cx, hcx, hcx'⟩ := hsame_cycle x (hksup hx),
              obtain ⟨cx, hcx⟩ := OnCycleFactors.sameCycle_of_mem_support ha x (hksup hx)
              -- have hcx' := (on_cycle_factors.same_cycle_of_mem_support' ha cx (hksup hx)).mpr hcx,
              have hxcx : x ∈ (cx : Equiv.Perm α).support :=
                by
                rw [← OnCycleFactors.SameCycle.is_cycleOf ha cx hcx]
                -- rw ← (on_cycle_factors.same_cycle_of_mem_support' ha cx (hksup hx)).mpr hcx,
                rw [Equiv.Perm.mem_support_cycleOf_iff]
                constructor; rfl; exact hksup hx
              suffices : c = cx ∨ d = cx
              rw [Finset.mem_union]
              cases' this with hccx hdcx
              · apply Or.intro_left; rw [hccx]; exact hxcx
              · apply Or.intro_right; rw [hdcx]; exact hxcx
              · obtain ⟨n, hn, hnx⟩ := hcx.exists_pow_eq'
                rw [Equiv.Perm.mem_support, ← hnx] at hx 
                specialize hk_apply cx 1
                simp only [pow_one] at hk_apply 
                rw [hk_apply] at hx 
                rw [Function.Injective.ne_iff (Equiv.injective _)] at hx 
                have hx' : τ cx ≠ cx := ne_of_apply_ne a hx
                rw [← Equiv.Perm.mem_support] at hx' 
                simp only [τ] at hx' 
                rw [Equiv.Perm.support_swap _] at hx' 
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx' 
                cases' hx' with hx' hx'
                · apply Or.intro_left; rw [← Subtype.coe_inj] at hx' ; rw [hx']; rfl
                · apply Or.intro_right; rw [← Subtype.coe_inj] at hx' ; rw [hx']; rfl
                intro h; rw [← Subtype.coe_inj] at h ; apply hm'; exact h
            · intro hx
              -- obtain ⟨cx, hcx, hcx'⟩ := hsame_cycle x _,
              obtain ⟨cx, hcx⟩ := OnCycleFactors.sameCycle_of_mem_support ha x _
              have hcx' := OnCycleFactors.SameCycle.is_cycleOf ha cx hcx
              obtain ⟨n, hn, hnx⟩ := Equiv.Perm.SameCycle.exists_pow_eq' hcx
              specialize hk_apply cx 1
              simp only [pow_one] at hk_apply 
              rw [← hnx, Equiv.Perm.mem_support, hk_apply]
              rw [Function.Injective.ne_iff (Equiv.injective _)]
              intro haτcx_eq_acx; dsimp at haτcx_eq_acx 
              have : ¬Equiv.Perm.Disjoint (cx : Equiv.Perm α) (τ cx : Equiv.Perm α) :=
                by
                rw [Equiv.Perm.disjoint_iff_support_disjoint]
                rw [Finset.not_disjoint_iff]
                use a cx
                apply And.intro (ha cx)
                rw [← haτcx_eq_acx]; exact ha (τ cx)
              have this' :=
                (Set.Pairwise.eq g.cycle_factors_finset_pairwise_disjoint cx.prop (τ cx).Prop
                    this).symm
              rw [Subtype.coe_inj] at this' 
              rw [← Equiv.Perm.not_mem_support] at this' 
              rw [Equiv.Perm.support_swap _] at this' 
              simp only [Finset.mem_insert, Finset.mem_singleton] at this' 
              apply this'
              simp only [← Subtype.coe_inj, Subtype.coe_mk, ← hcx']
              rw [Finset.mem_union] at hx 
              cases' hx with hx hx
              · apply Or.intro_left
                exact (Equiv.Perm.cycle_is_cycleOf hx hc).symm
              · apply Or.intro_right
                exact (Equiv.Perm.cycle_is_cycleOf hx hd).symm
              · intro h; simp only [← Subtype.coe_inj, Subtype.coe_mk] at h 
                exact hm' h
              · rw [Finset.mem_union] at hx ; cases' hx with hx hx
                exact Equiv.Perm.mem_cycleFactorsFinset_support_le hc hx
                exact Equiv.Perm.mem_cycleFactorsFinset_support_le hd hx
          norm_num
        -- ∀ i ∈ k.cycle_type, i = 2
        suffices hk2 : orderOf k = 2
        · have hk2' : Nat.Prime (orderOf k); rw [hk2]; exact Nat.prime_two
          obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hk2'
          intro i hi
          rw [hn, hk2, Multiset.mem_replicate] at hi 
          exact hi.right
        apply orderOf_eq_prime
        · -- k ^ 2 = 1,
          ext x
          simp only [Equiv.Perm.coe_one, id.def]
          by_cases hx : x ∈ g.support
          · -- obtain ⟨cx, hcx, hcx'⟩ := hsame_cycle x hx,
            obtain ⟨cx, hcx⟩ := OnCycleFactors.sameCycle_of_mem_support ha x hx
            -- have hcx' := on_cycle_factors.same_cycle.is_cycle_of ha cx hcx,
            obtain ⟨n, hn, rfl⟩ := hcx.exists_pow_eq'
            rw [hk_apply cx 2 n]
            apply congr_arg
            apply congr_arg
            suffices hτ2 : τ ^ 2 = 1
            rw [hτ2, Equiv.Perm.coe_one, id.def]
            rw [pow_two]; rw [Equiv.swap_mul_self]
          · -- lorsque x ∉ g.support
            rw [← Equiv.Perm.not_mem_support]
            intro hx'; apply hx
            apply hksup
            apply Equiv.Perm.support_pow_le k 2
            exact hx'
        intro hk
        specialize hk2 ⟨c, hc⟩
        simp only [hk, ConjAct.toConjAct_one, Subtype.coe_mk, one_smul, Equiv.swap_apply_left] at
          hk2 
        exact hm' hk2
      · simp only [τ]
        intro x
        by_cases hx : x = ⟨c, hc⟩
        · rw [hx, Equiv.swap_apply_left]; exact hm.symm
        by_cases hx' : x = ⟨d, hd⟩
        · rw [hx', Equiv.swap_apply_right]; exact hm
        · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
    · -- m.sum + 1 ≥ fintype.card α
      rw [ge_iff_le]; rw [← not_lt]; intro hm
      rw [Nat.lt_iff_add_one_le] at hm 
      rw [add_assoc] at hm 
      change m.sum + 2 ≤ _ at hm 
      suffices 1 < Fintype.card (MulAction.fixedBy (Equiv.Perm α) α g)
        by
        obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
        let k := OnCycleFactors.ψ g ⟨Equiv.swap a b, fun d hd => 1⟩
        suffices k.sign ≠ 1 by
          apply this
          apply h
          change ConjAct.toConjAct k ∈ _
          apply Subgroup.map_subtype_le
          rw [OnCycleFactors.hφ_ker_eq_ψ_range]
          exact Set.mem_range_self _
        suffices k = Equiv.swap a b by
          rw [this, Equiv.Perm.sign_swap]
          intro h'; rw [← Units.eq_iff] at h' 
          simpa only [← Units.eq_iff] using h
          intro hab'; apply hab
          rw [← Subtype.coe_inj]; exact hab'
        · simp only [k, OnCycleFactors.ψ, OnCycleFactors.ψAux]
          simp only [Subgroup.coe_one, dite_eq_ite, if_t_t, Equiv.Perm.ofSubtype_swap_eq,
            mul_right_eq_self]
          rw [Finset.noncommProd_eq_pow_card]; rw [one_pow]
          intro x hx; rfl
      · rw [OnCycleFactors.Equiv.Perm.card_fixedBy g m hg]
        rw [add_comm] at hm 
        rw [Nat.lt_iff_add_one_le, Nat.le_sub_iff_right _]
        exact hm
        rw [← hg, Equiv.Perm.sum_cycleType]; exact Finset.card_le_univ _
    · -- all cycle lengths are odd
      intro i hi
      rw [← hg] at hi 
      rw [Equiv.Perm.cycleType_def g, Multiset.mem_map] at hi 
      obtain ⟨c, hc, rfl⟩ := hi
      rw [← Finset.mem_def] at hc 
      have Hc_cycle : c.is_cycle := by rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc ;
        exact hc.left
      let k := OnCycleFactors.ψ g ⟨1, fun d hd => ite (c = d) ⟨d, Subgroup.mem_zpowers d⟩ 1⟩
      suffices c.sign = 1 by
        rw [Equiv.Perm.IsCycle.sign Hc_cycle] at this 
        rw [Nat.odd_iff_not_even]
        rw [← neg_one_pow_eq_one_iff_even _]
        intro this'; rw [this'] at this 
        simpa [← Units.eq_iff, Units.val_one, Units.coe_neg_one] using this
        intro h; simpa [← Units.eq_iff, Units.val_one, Units.coe_neg_one] using h
      suffices k = c by
        rw [← this]; apply h
        change ConjAct.toConjAct k ∈ _
        apply Subgroup.map_subtype_le
        rw [OnCycleFactors.hφ_ker_eq_ψ_range]
        exact Set.mem_range_self _
      -- k = c
      simp only [k, OnCycleFactors.ψ, OnCycleFactors.ψAux]
      simp only [dite_eq_ite, map_one, one_mul]
      suffices h_eq : g.cycle_factors_finset = {c} ∪ g.cycle_factors_finset \ {c}
      rw [@Finset.noncommProd_congr _ _ _ _ _ _ (fun x => ite (x = c) c 1) h_eq]
      rw [Finset.noncommProd_union_of_disjoint Finset.disjoint_sdiff]
      conv_rhs => rw [← mul_one c]
      apply congr_arg₂ (· * ·)
      rw [Finset.noncommProd_singleton, if_pos rfl]
      rw [Finset.noncommProd_eq_pow_card]
      exact one_pow _
      · intro i hi; rw [if_neg]
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi ; exact hi.right
      · intro x hx
        rw [if_pos]
        · simp only [Finset.union_sdiff_self_eq_union, Finset.mem_union, Finset.mem_singleton] at hx 
          by_cases hxc : c = x
          rw [if_pos hxc]; dsimp only; rw [if_pos hxc.symm]; rw [hxc]; rfl
          rw [if_neg hxc]; dsimp only; simp only [if_neg (Ne.symm hxc), Subgroup.coe_one]
        rw [Finset.union_sdiff_of_subset] at hx ; exact hx
        simp only [Finset.singleton_subset_iff]; exact hc
      · rw [Finset.union_sdiff_of_subset]
        rw [Finset.singleton_subset_iff]; exact hc
  · rintro ⟨h_odd, h_fixed, h_count⟩ x hx
    suffices hx' : x ∈ Set.range (OnCycleFactors.ψ g)
    obtain ⟨⟨y, uv⟩, rfl⟩ := set.mem_range.mp hx'
    simp only [OnCycleFactors.ψ, OnCycleFactors.ψAux]
    simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_ofSubtype]
    convert mul_one _
    · rw [Finset.noncommProd_map]
      rw [Finset.noncommProd_eq_prod]
      apply Finset.prod_eq_one
      intro c hc
      rw [dif_pos hc]
      let hc' := (uv c hc).Prop
      rw [Subgroup.mem_zpowers_iff] at hc' 
      obtain ⟨k, hkc⟩ := hc'
      rw [← hkc]
      simp only [map_zpow]
      suffices : Equiv.Perm.sign c = 1; rw [this]; simp only [one_zpow]
      rw [Equiv.Perm.IsCycle.sign, Odd.neg_one_pow, neg_neg]
      apply h_odd; rw [← hg]; rw [Equiv.Perm.cycleType_def]
      rw [Multiset.mem_map]
      use c; apply And.intro hc; rfl
      rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc 
      exact hc.left
    · apply symm
      suffices : y = 1
      rw [this]; exact Equiv.Perm.sign_one
      rw [← Equiv.Perm.card_support_le_one]
      apply le_trans (Finset.card_le_univ _)
      rw [OnCycleFactors.Equiv.Perm.card_fixedBy g m hg]
      rw [tsub_le_iff_left]; exact h_fixed
    -- x ∈ set.range (on_cycle_factors.ψ g)
    rw [← OnCycleFactors.hφ_ker_eq_ψ_range]
    suffices : (OnCycleFactors.φ g).ker = ⊤
    rw [this]
    simp only [Subgroup.mem_map, Subgroup.mem_top, Subgroup.coeSubtype, exists_true_left]
    exact ⟨⟨x, hx⟩, rfl⟩
    -- (on_cycle_factors.φ g).ker = ⊤
    rw [eq_top_iff]
    intro y _
    suffices (OnCycleFactors.φ g).range = ⊥
      by
      rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← this, MonoidHom.mem_range]
      exact ⟨y, rfl⟩
    rw [eq_bot_iff]
    intro z
    rw [← OnCycleFactors.iφ_eq_range]; rw [Subgroup.mem_bot]
    intro hz
    apply Equiv.ext
    intro c
    rw [← Multiset.nodup_iff_count_le_one, ← hg, Equiv.Perm.cycleType_def,
      Multiset.nodup_map_iff_inj_on (Equiv.Perm.cycleFactorsFinset g).Nodup] at h_count 
    rw [Equiv.Perm.coe_one, id.def, ← Subtype.coe_inj]
    exact h_count (z c) (z c).Prop c c.prop (hz c)
#align kerφ_le_alternating_iff kerφ_le_alternating_iff

theorem Equiv.Perm.is_cycle_eq_cycleOf_iff (g c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset)
    (x : α) : c = g.cycleOf x ↔ x ∈ c.support :=
  by
  constructor
  · intro hcx
    rw [Equiv.Perm.mem_support, hcx, Equiv.Perm.cycleOf_apply_self, Ne.def, ←
      Equiv.Perm.cycleOf_eq_one_iff, ← hcx]
    exact Equiv.Perm.IsCycle.ne_one (equiv.perm.mem_cycle_factors_finset_iff.mp hc).left
  · intro hx; exact Equiv.Perm.cycle_is_cycleOf hx hc
#align equiv.perm.is_cycle_eq_cycle_of_iff Equiv.Perm.is_cycle_eq_cycleOf_iff

example (g c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) (x y : α) (hx : x ∈ c.support) :
    g.SameCycle x y ↔ y ∈ c.support :=
  by
  rw [(Equiv.Perm.is_cycle_eq_cycleOf_iff g c hc x).mpr hx]
  rw [Equiv.Perm.mem_support_cycleOf_iff, iff_self_and]
  intro
  exact Equiv.Perm.mem_cycleFactorsFinset_support_le hc hx

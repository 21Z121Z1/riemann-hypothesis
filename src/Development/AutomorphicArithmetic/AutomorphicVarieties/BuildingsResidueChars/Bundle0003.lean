import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.KrullDimQuotientLeCardOfRadicalParameters
section
open IsLocalRing

theorem UpperTheory.krullDim_quotient_le_card_of_radical_parameters :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (q : Ideal B) (κ : Type) [Finite κ] (x : κ → B), (∀ k, x k ∈ maximalIdeal B) → (∀ p : Ideal B, p.IsPrime → q ≤ p → (∀ k, x k ∈ p) → maximalIdeal B ≤ p) → ringKrullDim (B ⧸ q) ≤ Nat.card κ := by
  intro B _ _ _ q κ _ x hx h
  classical
  by_cases hq : q = ⊤
  · subst hq
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  haveI : Nontrivial (B ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hq
  haveI : IsLocalRing (B ⧸ q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let s : Set (B ⧸ q) := Set.range (fun k => Ideal.Quotient.mk q (x k))
  have hs : s.Finite := Set.finite_range _
  have hmin : maximalIdeal (B ⧸ q) ∈ (Ideal.span s).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact map_nonunit (Ideal.Quotient.mk q) _ (hx k)
    · rintro P ⟨hP, hsP⟩ _
      have h1 : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk q) := by
        refine h _ (Ideal.comap_isPrime _ _) ?_ ?_
        · intro a ha
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
          exact P.zero_mem
        · intro k
          exact hsP (Ideal.subset_span ⟨k, rfl⟩)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply h1
      rw [mem_maximalIdeal] at hy ⊢
      exact fun hu => hy (hu.map _)
  have h2 := Ideal.height_le_card_of_mem_minimalPrimes_span hs hmin
  have h3 : s.ncard ≤ Nat.card κ := by
    rw [← Set.ncard_univ, show s = (fun k => Ideal.Quotient.mk q (x k)) '' Set.univ from Set.image_univ.symm]
    exact Set.ncard_image_le Set.finite_univ
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have h4 : (maximalIdeal (B ⧸ q)).height ≤ (Nat.card κ : ℕ∞) := h2.trans (by exact_mod_cast h3)
  exact_mod_cast h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LeSpanIntegralValuedOfGaloisStable
section
private theorem UpperTheory.exists_mul_eq_algebraMap_of_galois_fixed (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ]
    [Algebra.IsAlgebraic O ℂ] (z : ℂ) (hz : ∀ γ : ℂ ≃ₐ[O] ℂ, γ z = z) :
    ∃ a b : O, b ≠ 0 ∧ algebraMap O ℂ b * z = algebraMap O ℂ a := by
  letI : Algebra (FractionRing O) ℂ := FractionRing.liftAlgebra O ℂ
  haveI : IsScalarTower O (FractionRing O) ℂ := FractionRing.isScalarTower_liftAlgebra O ℂ
  haveI : Algebra.IsAlgebraic (FractionRing O) ℂ :=
    Algebra.IsAlgebraic.extendScalars (FaithfulSMul.algebraMap_injective O (FractionRing O))
  haveI : CharZero (FractionRing O) := RingHom.charZero (algebraMap (FractionRing O) ℂ)
  haveI : Algebra.IsSeparable (FractionRing O) ℂ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsAlgClosure (FractionRing O) ℂ := ⟨inferInstance, inferInstance⟩
  haveI : Normal (FractionRing O) ℂ := inferInstance
  haveI : IsGalois (FractionRing O) ℂ := ⟨⟩
  have hmem : z ∈ Set.range (algebraMap (FractionRing O) ℂ) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed z).2 (fun f => hz (f.restrictScalars O))
  obtain ⟨q, rfl⟩ := hmem
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) q
  refine ⟨a, b, nonZeroDivisors.ne_zero b.2, ?_⟩
  show algebraMap O ℂ b * algebraMap (FractionRing O) ℂ (IsLocalization.mk' (FractionRing O) a b) =
    algebraMap O ℂ a
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) ℂ (b : O),
    IsScalarTower.algebraMap_apply O (FractionRing O) ℂ a, ← map_mul, mul_comm,
    IsLocalization.mk'_spec]

theorem UpperTheory.le_span_integralValued_of_galoisStable :
    ∀ (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ] [Algebra.IsAlgebraic O ℂ] (X : Type) [Finite X] (I : Submodule ℂ (X → ℂ)), (∀ γ : ℂ ≃ₐ[O] ℂ, ∀ x ∈ I, (fun g => γ (x g)) ∈ I) → I ≤ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
  intro O _ _ _ _ _ X _ I hI
  classical
  haveI := Fintype.ofFinite X
  have hfix : ∀ x ∈ I, (∀ γ : ℂ ≃ₐ[O] ℂ, (fun g => γ (x g)) = x) →
      x ∈ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
    intro x hx hγ
    have hc : ∀ g, ∃ a b : O, b ≠ 0 ∧ algebraMap O ℂ b * x g = algebraMap O ℂ a :=
      fun g => UpperTheory.exists_mul_eq_algebraMap_of_galois_fixed O (x g) (fun γ => congrFun (hγ γ) g)
    choose a b hb hab using hc
    have hB : algebraMap O ℂ (∏ g, b g) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun g _ =>
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O ℂ)).2 (hb g))
    have hmem : algebraMap O ℂ (∏ g, b g) • x ∈
        Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
      apply Submodule.subset_span
      refine ⟨I.smul_mem _ hx, fun g => ⟨a g * ∏ h ∈ Finset.univ.erase g, b h, ?_⟩⟩
      show algebraMap O ℂ (a g * ∏ h ∈ Finset.univ.erase g, b h) = algebraMap O ℂ (∏ g, b g) * x g
      rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ g)]
      simp only [map_mul, ← hab g]
      ring
    have h2 := Submodule.smul_mem _ (algebraMap O ℂ (∏ g, b g))⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hB, one_smul] at h2
  have key : ∀ n : ℕ, ∀ y ∈ I, (Finset.univ.filter (fun g => y g ≠ 0)).card ≤ n →
      y ∈ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
    intro n
    induction n with
    | zero =>
      intro y hy hc
      have hy0 : y = 0 := by
        funext g
        by_contra h
        have := Finset.card_pos.2
          ⟨g, (by simpa using h : g ∈ Finset.univ.filter (fun g => y g ≠ 0))⟩
        omega
      rw [hy0]
      exact Submodule.zero_mem _
    | succ n ih =>
      intro y hy hc
      by_cases h0 : y = 0
      · rw [h0]
        exact Submodule.zero_mem _
      obtain ⟨g0, hg0⟩ : ∃ g, y g ≠ 0 := by
        by_contra h
        push_neg at h
        exact h0 (funext h)
      obtain ⟨x, hx⟩ : ∃ x : X → ℂ, x = (y g0)⁻¹ • y := ⟨_, rfl⟩
      have hxI : x ∈ I := by
        rw [hx]
        exact I.smul_mem _ hy
      have hxg0 : x g0 = 1 := by
        rw [hx]
        simp [hg0]
      have hsupp : ∀ g, x g = 0 ↔ y g = 0 := by
        intro g
        rw [hx]
        simp [hg0]
      have hyx : y = y g0 • x := by
        rw [hx, smul_smul, mul_inv_cancel₀ hg0, one_smul]
      by_cases hall : ∀ γ : ℂ ≃ₐ[O] ℂ, (fun g => γ (x g)) = x
      · rw [hyx]
        exact Submodule.smul_mem _ _ (hfix x hxI hall)
      · push_neg at hall
        obtain ⟨γ, hγ⟩ := hall
        obtain ⟨d, hd⟩ : ∃ d : X → ℂ, d = (fun g => γ (x g)) - x := ⟨_, rfl⟩
        have hdI : d ∈ I := by
          rw [hd]
          exact I.sub_mem (hI γ x hxI) hxI
        have hd0 : d ≠ 0 := by
          rw [hd]
          exact sub_ne_zero.2 hγ
        obtain ⟨g1, hg1⟩ : ∃ g, d g ≠ 0 := by
          by_contra h
          push_neg at h
          exact hd0 (funext h)
        have hdsupp : ∀ g, y g = 0 → d g = 0 := by
          intro g hg
          rw [hd]
          simp [(hsupp g).2 hg]
        have hdg0 : d g0 = 0 := by
          rw [hd]
          simp [hxg0]
        have hy1 : y g1 ≠ 0 := fun e => hg1 (hdsupp g1 e)
        have hdcard : (Finset.univ.filter (fun g => d g ≠ 0)).card ≤ n := by
          have hsub : Finset.univ.filter (fun g => d g ≠ 0) ⊆
              (Finset.univ.filter (fun g => y g ≠ 0)).erase g0 := by
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun e => hg (e ▸ hdg0), fun e => hg (hdsupp g e)⟩
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem
            (show g0 ∈ Finset.univ.filter (fun g => y g ≠ 0) by simp [hg0])
          omega
        have hdW := ih d hdI hdcard
        obtain ⟨y', hy'⟩ : ∃ y' : X → ℂ, y' = y - (y g1 / d g1) • d := ⟨_, rfl⟩
        have hy'I : y' ∈ I := by
          rw [hy']
          exact I.sub_mem hy (I.smul_mem _ hdI)
        have hy'card : (Finset.univ.filter (fun g => y' g ≠ 0)).card ≤ n := by
          have hsub : Finset.univ.filter (fun g => y' g ≠ 0) ⊆
              (Finset.univ.filter (fun g => y g ≠ 0)).erase g1 := by
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, ?_⟩
            · rintro rfl
              apply hg
              rw [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hg1, sub_self]
            · intro e
              apply hg
              rw [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e, hdsupp g e, mul_zero, sub_zero]
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem
            (show g1 ∈ Finset.univ.filter (fun g => y g ≠ 0) by simp [hy1])
          omega
        have hy'W := ih y' hy'I hy'card
        have hyy : y = y' + (y g1 / d g1) • d := by
          rw [hy', sub_add_cancel]
        rw [hyy]
        exact Submodule.add_mem _ hy'W (Submodule.smul_mem _ _ hdW)
  intro y hy
  exact key _ y hy le_rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ResidueIsIntegralOfAlgebraicOverDvr
section
private theorem UpperTheory.algebraic_over_finite_field_integral (k L : Type) [Field k] [Finite k] [Field L] [Algebra k L]
    (y : L) (h : IsAlgebraic k y) : IsIntegral ℤ y := by
  have hi : IsIntegral k y := h.isIntegral
  haveI : FiniteDimensional k (IntermediateField.adjoin k {y}) := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin k {y}) := Module.finite_of_finite k
  let g : ℕ → IntermediateField.adjoin k {y} := fun n =>
    ⟨y ^ (n + 1), pow_mem (IntermediateField.mem_adjoin_simple_self k y) _⟩
  obtain ⟨m, n, hmn, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have hpow : y ^ (m + 1) = y ^ (n + 1) := congrArg Subtype.val hg
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · refine ⟨Polynomial.X ^ (n + 1) - Polynomial.X ^ (m + 1), Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X_pow]
      exact_mod_cast Nat.succ_lt_succ hlt
    · simp [hpow]
  · refine ⟨Polynomial.X ^ (m + 1) - Polynomial.X ^ (n + 1), Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X_pow]
      exact_mod_cast Nat.succ_lt_succ hlt
    · simp [hpow]

open Polynomial in
theorem UpperTheory.residue_isIntegral_of_algebraic_over_dvr :
    ∀ (A K : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] [Field K] (V : ValuationSubring K) (f : A →+* V), Function.Injective f → IsLocalHom f → ∀ x : V, (∃ p : Polynomial A, p ≠ 0 ∧ p.eval₂ (V.subtype.comp f) x = 0) → IsIntegral ℤ (IsLocalRing.residue V x) := by
  intro A K _ _ _ _ _ V f hf _ x hx
  classical
  obtain ⟨p, hp0, hpx⟩ := hx
  letI : NormalizationMonoid A := UniqueFactorizationMonoid.normalizationMonoid.toNormalizationMonoid
  letI : NormalizedGCDMonoid A := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  have hV : Polynomial.eval₂ f x p = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero]
    exact (Polynomial.hom_eval₂ p f V.subtype x).trans hpx
  set q := p.primPart with hq
  have hcont : f p.content ≠ 0 := by
    intro h0
    apply hp0
    rw [← Polynomial.content_eq_zero_iff]
    exact hf (h0.trans (map_zero f).symm)
  have hqx : Polynomial.eval₂ f x q = 0 := by
    have e := Polynomial.eq_C_content_mul_primPart p
    rw [e, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hV
    exact (mul_eq_zero.1 hV).resolve_left hcont
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hqbar : q.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C π ∣ q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi : IsLocalRing.residue A (q.coeff i) = 0 := by
        rw [← Polynomial.coeff_map, h0, Polynomial.coeff_zero]
      rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hi
      exact hi
    exact hπ.not_isUnit (Polynomial.isPrimitive_primPart p π hdvd)
  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) :=
    (IsLocalRing.ResidueField.map f).toAlgebra
  have halg : IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.residue V x) := by
    refine ⟨q.map (IsLocalRing.residue A), hqbar, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have e : (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue A) =
        (IsLocalRing.residue V).comp f := by
      ext a
      exact IsLocalRing.ResidueField.map_residue f a
    rw [e, ← Polynomial.hom_eval₂, hqx, map_zero]
  exact UpperTheory.algebraic_over_finite_field_integral (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) _ halg
end


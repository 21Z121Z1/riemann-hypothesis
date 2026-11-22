import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0047

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitHeightBoundLogDiscriminantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicit_height_bound_log_discriminant : ∀ (f r : ℕ) (L n g h rd P : ℝ), 2 ≤ f → 2 ≤ r → 1 ≤ L → (f : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp L → 1 ≤ rd → Real.log rd ≤ 2 * L → 0 < n → Real.log n ≤ 2 * f * (r : ℝ) ^ 2 * Real.log g → Real.log g ≤ 30 * L → 0 < h → Real.log h ≤ f * Real.log rd + 2 * f * Real.log (1 + f * Real.log rd) → 0 ≤ P → P ≤ 2 ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * √r → n * (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ (f * r ^ 2) * (h * 3 ^ (2 * f) * ((3 : ℝ) ^ (2 * f * r ^ 2) * rd ^ ((f : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * P ^ f)) ≤ Real.exp (119 * (f * (r : ℝ) ^ 2 * L)) := by
  first | exact @GlobalTheory.CovTop.VolUp.mass_bound_numbers_le_exp | exact GlobalTheory.CovTop.VolUp.mass_bound_numbers_le_exp | (intros; apply GlobalTheory.CovTop.VolUp.mass_bound_numbers_le_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAlgHomAdjoinIntegralRootStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ → ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 → ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω, ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))), ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  first | exact @GlobalTheory.extend_alg_hom_adjoin_integral_root | exact GlobalTheory.extend_alg_hom_adjoin_integral_root | (intros; apply GlobalTheory.extend_alg_hom_adjoin_integral_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendLinearIndependentDifferentialsStatement
section
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_linear_independent_differentials : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.FiniteType R B] (d : ℕ) (ι : Type) (x : ι → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (x i)) → ∃ (t : Fin d → B) (e : ι ↪ Fin d), (∀ i, t (e i) = x i) ∧ LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) := by
  first | exact @GlobalTheory.kaehler_baseChange_independent_extend | exact GlobalTheory.kaehler_baseChange_independent_extend | (intros; apply GlobalTheory.kaehler_baseChange_independent_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePoints
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.factor_closedImmersion_of_affine_points :
    ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X),
      (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) →
      ∃ z : T ⟶ Z, z ≫ i = g := by
  intro X Z T i hi g h
  let 𝒰 := T.affineCover
  have hj : ∀ j, ∃ y : 𝒰.X j ⟶ Z, y ≫ i = 𝒰.f j ≫ g := fun j => h _ (𝒰.f j)
  choose y hy using hj
  have hc : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ y a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ y b := by
    intro a b
    rw [← cancel_mono i, Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms y hc, ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hy]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAdicCompletionSpan
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem faithfullyFlat_adicCompletion_span (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (t : R) (ht : t ∈ maximalIdeal R) :
    Module.FaithfullyFlat R (AdicCompletion (Ideal.span {t}) R) := by
  haveI : Module.Flat R (AdicCompletion (Ideal.span {t}) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hm]
  have hle : Ideal.span {t} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).2 ht
  have hmax := AdicCompletion.isMaximal_map_of_le (Ideal.span {t}) (maximalIdeal R) hle
    (Submodule.fg_span_singleton t)
  intro h
  apply hmax.ne_top
  have e := Ideal.smul_top_eq_map (S := AdicCompletion (Ideal.span {t}) R) (maximalIdeal R)
  rw [h] at e
  apply Submodule.restrictScalars_injective R
  rw [← e]; rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem exists_integral_point (A R C : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing R] [CommRing C] [Algebra R C] (ρ : R →+* A) (hint : Algebra.IsIntegral R C)
    (s : C →+* FractionRing A) (hs : s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) :
    ∃ g : C →+* A, (algebraMap A (FractionRing A)).comp g = s ∧ g.comp (algebraMap R C) = ρ := by
  set K := FractionRing A
  have hmem : ∀ c : C, s c ∈ (algebraMap A K).range := by
    intro c
    obtain ⟨p, hp, hpc⟩ := hint.isIntegral c
    have hi : IsIntegral A (s c) := by
      refine ⟨p.map ρ, hp.map ρ, ?_⟩
      rw [Polynomial.eval₂_map, ← hs, ← Polynomial.hom_eval₂, hpc, map_zero]
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
    exact ⟨a, ha⟩
  let e := RingEquiv.ofBijective (algebraMap A K).rangeRestrict
    ⟨fun x y h => IsFractionRing.injective A K (congrArg Subtype.val h),
     (algebraMap A K).rangeRestrict_surjective⟩
  let g : C →+* A := e.symm.toRingHom.comp (s.codRestrict _ hmem)
  have hg : (algebraMap A K).comp g = s := by
    ext c
    have : e (g c) = s.codRestrict _ hmem c := by simp [g]
    exact congrArg Subtype.val this
  refine ⟨g, hg, ?_⟩
  ext r
  apply IsFractionRing.injective A K
  have := congrArg (fun f => f r) hs
  simp only [RingHom.comp_apply] at this
  change (algebraMap A K) (g (algebraMap R C r)) = _
  rw [← this, ← hg, RingHom.comp_apply]
  rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem mem_pow_of_mul_mem_pow (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R)
    (a : A) (ha : a ≠ 0) : ∀ (n : ℕ) (r : R), algebraMap A R a * r ∈ Ideal.span {t ^ n} →
      r ∈ Ideal.span {t ^ n} := by
  have hρa : ρ (algebraMap A R a) = a := by
    simpa using congrArg (fun f => f a) hρ
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r hr
    have hr1 : algebraMap A R a * r ∈ RingHom.ker ρ := by
      rw [hker, Ideal.mem_span_singleton]
      exact (dvd_pow_self t (Nat.succ_ne_zero n)).trans (Ideal.mem_span_singleton.1 hr)
    rw [RingHom.mem_ker, map_mul, hρa] at hr1
    have hr0 : r ∈ Ideal.span {t} := by
      rw [← hker, RingHom.mem_ker]
      exact (mul_eq_zero.1 hr1).resolve_left ha
    obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton.1 hr0
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hr
    have h2 : algebraMap A R a * r' = t ^ n * q := by
      have : t * (algebraMap A R a * r') = t * (t ^ n * q) := by
        rw [pow_succ] at hq
        linear_combination hq
      have h3 : t * (algebraMap A R a * r' - t ^ n * q) = 0 := by rw [mul_sub, this, sub_self]
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h3)
    have := ih r' (Ideal.mem_span_singleton.2 ⟨q, h2⟩)
    obtain ⟨q', rfl⟩ := Ideal.mem_span_singleton.1 this
    exact Ideal.mem_span_singleton.2 ⟨q', by ring⟩

theorem torsionFree_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.TorsionFreeOver A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow] at hm
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
  exact mem_pow_of_mul_mem_pow A R ρ hρ t hker ht a ha n r hm

end GlobalTheory.GoodEtaleSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAppOfIsAffineHomFlatSurjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faithfullyFlat_app_of_isAffineHom_flat_surjective' : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p → IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by
  first | exact @GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective | exact GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective | (intros; apply GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivIntegralMulKernelApplyStatement
section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fderiv_integral_mul_kernel_apply' : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] {U : Set V}, IsOpen U → ∀ {α : V → ℂ}, Continuous α → HasCompactSupport α → tsupport α ⊆ U → ∀ {K : V × V → ℂ}, ContDiffOn ℝ ∞ K (U ×ˢ U) → ∀ {x : V}, x ∈ U → ∀ v : V, fderiv ℝ (fun x' => ∫ y, α y * K (x', y) ∂ν) x v = ∫ y, α y * fderiv ℝ (fun x' => K (x', y)) x v ∂ν := by
  first | exact @GlobalTheory.fderiv_integral_mul_kernel_apply | exact GlobalTheory.fderiv_integral_mul_kernel_apply | (intros; apply GlobalTheory.fderiv_integral_mul_kernel_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLocalizationAwaySpanFinsetStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (N : Submodule R' A'), N.FG → ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  first | exact @GlobalTheory.fg_localizationAway_span_finset | exact GlobalTheory.fg_localizationAway_span_finset | (intros; apply GlobalTheory.fg_localizationAway_span_finset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCosineExplicitFormula
section
open MeasureTheory
open scoped ComplexOrder ENNReal

set_option autoImplicit false

namespace GlobalTheory.FibCos

theorem cos_fs_moebius (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (x : ℂ)
    (hx : 1 + G 1 0 / G 0 0 * x ≠ 0) :
    GlobalTheory.FibCos.cos G x = 1 / (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ∧
    GlobalTheory.FibCos.fs G x = ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 *
      (1 / (Real.pi * (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ^ 2)) := by
  have h00 : (0 : ℂ) < G 0 0 := hG.diag_pos
  have hdet : (0 : ℂ) < G.det := hG.det_pos
  obtain ⟨ha, ha'⟩ := Complex.pos_iff.mp h00
  obtain ⟨hD, -⟩ := Complex.pos_iff.mp hdet
  have h01 : G 0 1 = (starRingEnd ℂ) (G 1 0) := (hG.isHermitian.apply 0 1).symm
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have hGa : G 0 0 = (a : ℂ) := by
    apply Complex.ext
    · simp [ha_def]
    · simp [← ha']
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set u : ℝ := ‖1 + G 1 0 / G 0 0 * x‖ ^ 2 with hu_def
  set s : ℝ := ‖x‖ ^ 2 with hs_def
  have hu : 0 < u := by positivity
  have hs : 0 ≤ s := by positivity
  have hnum : ‖G 0 0 + x * G 1 0‖ ^ 2 = a ^ 2 * u := by
    have : G 0 0 + x * G 1 0 = (a : ℂ) * (1 + G 1 0 / G 0 0 * x) := by
      rw [hGa]; field_simp
    rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hDe : D = a * (G 1 1).re - ((G 1 0).re ^ 2 + (G 1 0).im ^ 2) := by
    rw [hD_def, Matrix.det_fin_two, h01, hGa]
    simp
    ring
  have hn : nrm G x = a * u + D / a * s := by
    have h1 : a * nrm G x = a ^ 2 * u + D * s := by
      rw [← hnum, hDe, hs_def, nrm, h01, hGa]
      simp only [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    field_simp
    linarith
  have hc : ‖(Real.sqrt D / a : ℂ)‖ ^ 2 = D / a ^ 2 := by
    rw [norm_div, div_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, Real.sq_sqrt hD.le]
  have hy : ‖(Real.sqrt D / a : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2 = D / a ^ 2 * s / u := by
    rw [norm_div, norm_mul, div_pow, mul_pow, hc]
  have hd : ‖(Real.sqrt D / a : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 = D / a ^ 2 / u ^ 2 := by
    rw [norm_div, norm_pow, div_pow, hc]
  have hpi := Real.pi_pos
  rw [hy, hd]
  constructor
  · rw [cos, hnum, hn, ← ha_def]
    field_simp
  · rw [fs, hn, ← hD_def]
    field_simp

end GlobalTheory.FibCos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDenseAffineChartPrimesStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_annihilator_primes_inter_fibre : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by
  first | exact @GlobalTheory.fibre_dense_affine_chart_primes | exact GlobalTheory.fibre_dense_affine_chart_primes | (intros; apply GlobalTheory.fibre_dense_affine_chart_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreGoingDownTensorStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_le_comap_of_goingDown_tensor : ∀ (S A C : Type) [CommRing S] [CommRing A] [CommRing C] [Algebra S A] [Algebra S C]
    (u : Ideal (TensorProduct S A C)) [u.IsPrime] (Q₁ : Ideal C) [Q₁.IsPrime],
    Q₁ ≤ u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) →
    Q₁.comap (algebraMap S C) = u.comap (algebraMap S (TensorProduct S A C)) →
    ∃ Q : Ideal (TensorProduct S A C), Q.IsPrime ∧ Q ≤ u ∧
      Q.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) = Q₁ ∧
      Q.comap (algebraMap A (TensorProduct S A C)) = u.comap (algebraMap A (TensorProduct S A C)) := by
  first | exact @GlobalTheory.fibre_going_down_tensor | exact GlobalTheory.fibre_going_down_tensor | (intros; apply GlobalTheory.fibre_going_down_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCardTorsionQuotSmulTopLePowFinrankStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_card_torsion_quot_smul_top_le_pow_finrank : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] (I J : Ideal R), I.IsMaximal → Finite (R ⧸ I) → J ≠ ⊥ → Finite {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ∧ Nat.card {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ≤ Nat.card (R ⧸ I) ^ Module.finrank R M := by
  first | exact @GlobalTheory.TorsionCount.torsion_card | exact GlobalTheory.TorsionCount.torsion_card | (intros; apply GlobalTheory.TorsionCount.torsion_card <;> assumption)
end


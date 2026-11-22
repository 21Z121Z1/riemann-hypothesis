import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCompactMatrixEntryAbsSumSublevel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0003
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealPlaceMeasures
section
noncomputable section

namespace GlobalTheory.RealPlaceMeasuresProof

open MeasureTheory FourierTransform Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal NNReal

theorem selfDual_of_map {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure V) (hμ : μ.IsAddHaarMeasure) (β : V → V → ℝ) (hs : ∀ x y, β x y = β y x)
    (T : V ≃L[ℝ] E) (R : V → E) (hRm : MeasurableEmbedding R)
    (hR : ∀ x y, β x y = inner ℝ (T x) (R y)) (a b : ℝ≥0) (hab : a * b = 1)
    (hT : μ.map T = a • (volume : Measure E)) (hRv : μ.map R = b • (volume : Measure E)) :
    SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((β x y : ℝ) : ℂ))) := by
  have gen : ∀ (S : V → E) (c : ℝ≥0), c ≠ 0 → MeasurableEmbedding S →
      μ.map S = c • (volume : Measure E) →
      (∀ g : E → ℂ, ∫ x, g (S x) ∂μ = ((c : ℝ) : ℂ) * ∫ w, g w) ∧
      ∀ g : E → ℂ, Integrable (fun x => g (S x)) μ ↔ Integrable g := by
    intro S c hc he h
    refine ⟨fun g => ?_, fun g => ?_⟩
    · rw [← he.integral_map, h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    · have := he.integrable_map_iff (μ := μ) (g := g)
      rw [h] at this
      refine this.symm.trans ?_
      exact integrable_smul_measure (by exact_mod_cast hc) ENNReal.coe_ne_top
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab
  have hb : b ≠ 0 := right_ne_zero_of_mul_eq_one hab
  obtain ⟨haI, haG⟩ := gen T a ha T.toHomeomorph.measurableEmbedding hT
  obtain ⟨hbI, hbG⟩ := gen R b hb hRm hRv
  have ha' : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  have hab' : ((a : ℝ) : ℂ) * ((b : ℝ) : ℂ) = 1 := by exact_mod_cast hab
  have key : ∀ (Φ : V → ℂ) (y : V),
      ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((β x y : ℝ) : ℂ)) ∂μ =
        ((a : ℝ) : ℂ) * 𝓕⁻ (fun w => Φ (T.symm w)) (R y) := by
    intro Φ y
    rw [Real.fourierInv_eq', ← haI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul, hR]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  refine ⟨hμ, fun Φ hc hsup hF z => ?_⟩
  have hi : Integrable Φ μ := hc.integrable_of_hasCompactSupport hsup
  simp only [key Φ] at hF ⊢
  have hf : Integrable (fun w => Φ (T.symm w)) := by
    rw [← haG]; simpa using hi
  have hF' : Integrable (𝓕⁻ (fun w => Φ (T.symm w))) := by
    rw [← hbG]
    simpa [← mul_assoc, ha'] using hF.const_mul ((a : ℝ) : ℂ)⁻¹
  have h1 : 𝓕⁻ (fun w => Φ (T.symm w)) = 𝓕 (fun w => Φ (T.symm (-w))) :=
    Real.fourierInv_eq_fourier_comp_neg _
  have h2 : 𝓕⁻ (𝓕 (fun w => Φ (T.symm (-w)))) = fun w => Φ (T.symm (-w)) :=
    Continuous.fourierInv_fourier_eq (by fun_prop) hf.comp_neg (h1 ▸ hF')
  have h3 := congrFun h2 (T z)
  rw [← h1, Real.fourierInv_eq'] at h3
  simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply] at h3
  rw [← h3, ← one_mul (∫ v : E, _), ← hab', mul_assoc ((a : ℝ) : ℂ), ← hbI, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul]
  rw [hs y z, hR, real_inner_comm, mul_assoc ((a : ℝ) : ℂ)]
  congr 1
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem selfDual_line {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    SelfDual (volume : Measure ℝ)
      (fun t s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (t * s) : ℝ) : ℂ))) := by
  rcases hε with rfl | rfl
  · exact selfDual_of_map volume inferInstance (fun t s => 1 * (t * s)) (fun x y => by ring)
      (ContinuousLinearEquiv.refl ℝ ℝ) id MeasurableEmbedding.id (fun x y => by simp [mul_comm])
      1 1 (one_mul 1) (by simp) (by simp)
  · exact selfDual_of_map volume inferInstance (fun t s => -1 * (t * s)) (fun x y => by ring)
      (ContinuousLinearEquiv.refl ℝ ℝ) Neg.neg (Homeomorph.neg ℝ).measurableEmbedding
      (fun x y => by simp [mul_comm]) 1 1 (one_mul 1) (by simp) (by simp)

theorem selfDual_dx {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (P Q : ℕ) :
    SelfDual (PerpendicularEmbedding.dx P Q) (fun x y : PerpendicularEmbedding.Sp P Q =>
      Complex.exp (2 * Real.pi * Complex.I *
        ((ε * (2 * (PerpendicularEmbedding.herm x y).re) : ℝ) : ℂ))) := by
  obtain ⟨u, hu1, hu2⟩ : ∃ u : Fin P ⊕ Fin Q → (ℂ ≃ₗᵢ[ℝ] ℂ),
      (∀ i z, u (Sum.inl i) z = ε * z) ∧ ∀ i z, u (Sum.inr i) z = -(ε * z) := by
    rcases hε with rfl | rfl
    · exact ⟨Sum.elim (fun _ => .refl ℝ ℂ) (fun _ => .neg ℝ), by simp, by simp⟩
    · exact ⟨Sum.elim (fun _ => .neg ℝ) (fun _ => .refl ℝ ℂ), by simp, by simp⟩
  let T : PerpendicularEmbedding.Sp P Q ≃L[ℝ] EuclideanSpace ℂ (Fin P ⊕ Fin Q) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin P ⊕ Fin Q => ℂ).symm
  let S : EuclideanSpace ℂ (Fin P ⊕ Fin Q) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin P ⊕ Fin Q) :=
    LinearIsometryEquiv.piLpCongrRight 2 u
  have hT : MeasurePreserving T volume volume :=
    (show MeasurePreserving T.toHomeomorph.toMeasurableEquiv.symm volume volume from
      GlobalTheory.volume_preserving_ofLp_complex (Fin P ⊕ Fin Q)).symm _
  have hST : MeasurePreserving (S ∘ T) volume volume := S.measurePreserving.comp hT
  have h2 : MeasurableEmbedding fun w : EuclideanSpace ℂ (Fin P ⊕ Fin Q) => (2 : ℝ) • w :=
    (Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero).measurableEmbedding
  refine selfDual_of_map _ (GlobalTheory.RealPlaceCompare.isAddHaar_dx P Q)
    (fun x y => ε * (2 * (PerpendicularEmbedding.herm x y).re))
    (fun x y => by rw [← GlobalTheory.RealPlaceCompare.herm_star x y]; simp) T
    ((fun w => (2 : ℝ) • w) ∘ (S ∘ T))
    (h2.comp (S.toHomeomorph.measurableEmbedding.comp T.toHomeomorph.measurableEmbedding))
    (fun x y => ?_) (2 ^ (P + Q)) (2 ^ (P + Q))⁻¹ (mul_inv_cancel₀ (by positivity)) ?_ ?_
  · simp only [Function.comp, PiLp.inner_apply, Fintype.sum_sum_type,
      PerpendicularEmbedding.herm, Complex.sub_re, Complex.re_sum]
    have e : ∀ i, S (T y) i = u i (y i) := fun i => rfl
    have e' : ∀ i, T x i = x i := fun i => rfl
    simp only [e', Complex.inner, mul_sub, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp [e, hu1, hu2] <;> ring
  · rw [PerpendicularEmbedding.dx, Measure.map_smul, hT.map_eq]
    ext s hs
    simp [ENNReal.smul_def]
  · rw [← Measure.map_map h2.measurable hST.measurable, PerpendicularEmbedding.dx, Measure.map_smul, hST.map_eq,
      Measure.map_smul, Measure.map_addHaar_smul _ two_ne_zero,
      GlobalTheory.finrank_real_euclideanSpace_complex, smul_smul, ENNReal.smul_def]
    congr 1
    rw [abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.coe_inv (by positivity)]
    simp only [Fintype.card_sum, Fintype.card_fin, ENNReal.ofReal_ofNat, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
    generalize P + Q = n
    rw [two_mul, pow_add, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem selfDualReal : PerpendicularEmbedding.SelfDualReal := fun _ hε =>
  ⟨selfDual_dx hε, selfDual_line hε⟩

theorem realPlaceMeasures : ActionCoordinates.RealPlaceMeasures :=
  GlobalTheory.RealPlaceCompare.typings_agree.2.2.2.1
    ⟨selfDualReal, GlobalTheory.SphereMassProof.sphereMass, GlobalTheory.CompactDualQuot.compactDualQuotient⟩

end GlobalTheory.RealPlaceMeasuresProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryFourfoldLatticePreservesRationalVectors
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatDesc

theorem unitary_maps_rational : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  intro D cc δ B hcc u hidx v
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) with hM
  set n := Formalism.L2.Th1.H.relIdx S M with hn

  have h1 : ∀ x ∈ M, n • x ∈ S := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨x, hx⟩ : M)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set y := B.γ₀.g.symm v with hy
  obtain ⟨t, ht, hint⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.exists_nat_mul D.host.E (Finset.univ.image y)
  set N := Ideal.absNorm cc with hNdef
  have hN : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hw₀ : δ * (N : ℂ) ∈ lamOf D cc δ := by
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K), hNc, ?_⟩
    simp
  have hm : (δ * (N : ℂ)) • emb4 D (t • y) ∈ Formalism.L2.Th1.H.pow4 B.lamM :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀ fun a => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different (by
      have := hint _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
      simpa using this)
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hg : B.gC (emb4 D (t • y)) = (t : ℂ) • V := by
    rw [show B.gC (emb4 D (t • y)) = _ from B.gC_spec (t • y), map_nsmul, hy, LinearEquiv.apply_symm_apply]
    funext w
    simp [hV]
  have hmem : (δ * (N : ℂ) * (t : ℂ)) • u V ∈ M := by
    refine ⟨B.gC ((δ * (N : ℂ)) • emb4 D (t • y)), ⟨_, hm, rfl⟩, ?_⟩
    show u (B.gC _) = _
    rw [map_smul, hg, smul_smul, map_smul]
  have hS' := h1 _ hmem
  rw [hS, Formalism.L2.Th1.H.mem_stdLat] at hS'
  have hc : ∀ w, ∃ c ∈ cc, ((n • ((δ * (N : ℂ) * (t : ℂ)) • u V)) w) = δ * D.host.φ₀ (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) :=
    fun w => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 (hS' w))
  choose c _ hc using hc
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨fun w => ((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)), ?_⟩
  funext w
  have h := hc w
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at h
  have e : D.host.φ₀ (((((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)) : D.host.K)) : D.host.E)
      = D.host.φ₀ (((c w : 𝓞 D.host.K) : D.host.K) : D.host.E) / ((n : ℂ) * (N : ℂ) * (t : ℂ)) := by
    push_cast
    rw [map_div₀, map_mul, map_mul, map_natCast, map_natCast, map_natCast]
  rw [e, eq_div_iff (mul_ne_zero (mul_ne_zero hnC hNC) htC)]
  apply mul_left_cancel₀ hδ
  rw [← h]
  ring

end GlobalTheory.LatDesc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedAdjoinSqrtOfNotMem
section
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Polynomial

theorem GlobalTheory.unramified_adjoin_sqrt_of_not_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : 𝓞 (maximalRealSubfield L)) (δ : L), δ ^ 2 = ((a : maximalRealSubfield L) : L) → δ ∉ maximalRealSubfield L → ∀ w : HeightOneSpectrum (𝓞 L), 2 * a ∉ (w.under (𝓞 (maximalRealSubfield L))).asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  intro L _ _ _ a δ hδ hδK w ha

  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    exact (RingOfIntegers.isIntegral_coe a).algebraMap
  let d : 𝓞 L := ⟨δ, hint⟩
  have hd : algebraMap (𝓞 L) L d = δ := rfl
  have hdA : IsIntegral (𝓞 (maximalRealSubfield L)) d := Algebra.IsIntegral.isIntegral d
  have hδR : IsIntegral (maximalRealSubfield L) δ := Algebra.IsIntegral.isIntegral δ
  have hsq : d ^ 2 = algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, hd, hδ, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L) L]
    rfl

  have hfin : Module.finrank (maximalRealSubfield L) L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hdegK : (minpoly (maximalRealSubfield L) δ).natDegree = 2 := by
    refine le_antisymm (hfin ▸ minpoly.natDegree_le δ) ?_
    rw [minpoly.two_le_natDegree_iff hδR]
    rintro ⟨x, hx⟩
    exact hδK (hx ▸ x.2)
  have hdeg : (minpoly (𝓞 (maximalRealSubfield L)) d).natDegree = 2 := by
    rw [← hdegK, ← hd, minpoly.isIntegrallyClosed_eq_field_fractions (maximalRealSubfield L) L hdA,
      (minpoly.monic hdA).natDegree_map]

  have hpoly : minpoly (𝓞 (maximalRealSubfield L)) d = X ^ 2 - C a := by
    have hm : (X ^ 2 - C a : (𝓞 (maximalRealSubfield L))[X]).Monic := monic_X_pow_sub_C a two_ne_zero
    have hroot : aeval d (X ^ 2 - C a) = 0 := by
      rw [map_sub, aeval_X_pow, aeval_C, hsq, sub_self]
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hdA) hm
      (minpoly.isIntegrallyClosed_dvd hdA hroot) ?_).symm
    rw [hdeg, natDegree_X_pow_sub_C]

  have hadj : Algebra.adjoin (maximalRealSubfield L) {algebraMap (𝓞 L) L d} = ⊤ := by
    have htop : IntermediateField.adjoin (maximalRealSubfield L) {δ} = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_le le_top (by
        rw [IntermediateField.finrank_top', hfin, IntermediateField.adjoin.finrank hδR, hdegK])
    rw [hd, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hδR.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]

  have hmem : 2 * d ∈ differentIdeal (𝓞 (maximalRealSubfield L)) (𝓞 L) := by
    have := aeval_derivative_mem_differentIdeal (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L) L d hadj
    simpa [hpoly, derivative_X_pow, one_add_one_eq_two, map_ofNat] using this

  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  have h2d : 2 * d ∈ w.asIdeal := Ideal.dvd_iff_le.mp hdvd hmem
  have h4a : algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) (2 * (2 * a)) ∈ w.asIdeal := by
    have := w.asIdeal.mul_mem_left (2 * d) h2d
    convert this using 1
    rw [map_mul, map_mul, map_ofNat, ← hsq]
    ring
  have h4a' : 2 * (2 * a) ∈ (w.under (𝓞 (maximalRealSubfield L))).asIdeal := h4a
  rcases (w.under (𝓞 (maximalRealSubfield L))).isPrime.mem_or_mem h4a' with h | h
  · exact ha (Ideal.mul_mem_right a _ h)
  · exact ha h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationComplexConjOfNotSplit
section
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitOfSquare

private theorem valued_v_algebraMap_adicCompletion_foundation {F : Type} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x :=
  u.valuedAdicCompletion_eq_valuation' x

theorem exists_valuation_lt_one {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) (a : F) (ha : a ≠ 0)
    (h : IsSquare (algebraMap F (u.adicCompletion F) a)) : ∃ c : F, u.valuation F (1 / 4 - c ^ 2 * a) < 1 := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply ha
    simpa using hs
  obtain ⟨π, hπ⟩ := u.valuation_exists_uniformizer F
  have hπ1 : u.valuation F π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set h2 : u.adicCompletion F := algebraMap F (u.adicCompletion F) 2⁻¹ with hh2
  set p : u.adicCompletion F := algebraMap F (u.adicCompletion F) π with hp
  have hp0 : p ≠ 0 := (map_ne_zero _).mpr hπ0
  have hvp : Valued.v p < 1 := by rw [hp, valued_v_algebraMap_adicCompletion_foundation]; exact hπ1
  have hI := Valued.isOpen_integer (u.adicCompletion F)
  have hcont : Continuous (fun y : u.adicCompletion F => (y * s - h2) * p⁻¹) :=
    ((continuous_id.mul continuous_const).sub continuous_const).mul continuous_const
  obtain ⟨c, hc⟩ := (u.denseRange_algebraMap F).exists_mem_open (hI.preimage hcont) ⟨h2 * s⁻¹, by
    simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff]
    rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self, zero_mul, map_zero]
    exact zero_le⟩
  refine ⟨c, ?_⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff] at hc
  set y := algebraMap F (u.adicCompletion F) c
  set z := y * s - h2 with hz_def
  have hz : Valued.v z < 1 := by
    calc Valued.v z = Valued.v (z * p⁻¹) * Valued.v p := by
          rw [← map_mul, inv_mul_cancel_right₀ hp0]
      _ ≤ 1 * Valued.v p := by gcongr
      _ < 1 := by rw [one_mul]; exact hvp
  have hhalf : h2 + h2 = 1 := by
    rw [hh2, ← map_add, ← map_one (algebraMap F (u.adicCompletion F))]
    congr 1
    norm_num
  have hkey : algebraMap F (u.adicCompletion F) (1 / 4 - c ^ 2 * a) = -z * (1 + z) := by
    have e1 : (1 / 4 : F) = 2⁻¹ * 2⁻¹ := by norm_num
    rw [e1, map_sub, map_mul, map_mul, map_pow, hs, ← hh2]
    rw [hz_def]
    linear_combination (h2 - y * s) * hhalf
  rw [← valued_v_algebraMap_adicCompletion_foundation, hkey]
  have h1z : Valued.v (1 + z) ≤ 1 := by
    calc Valued.v (1 + z) ≤ max (Valued.v (1 : u.adicCompletion F)) (Valued.v z) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := by rw [map_one]; exact max_le le_rfl hz.le
  calc Valued.v (-z * (1 + z)) = Valued.v z * Valued.v (1 + z) := by
        rw [map_mul, Valuation.map_neg]
    _ ≤ Valued.v z * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact hz

theorem valuation_complexConj_of_not_split {L : Type} [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)) (hw : ¬ IsSplitAt w) (y : L) :
    w.valuation L (IsCMField.complexConj L y) = w.valuation L y := by
  set σ : L ≃+* L := (IsCMField.complexConj L).toRingEquiv with hσ
  have hne : w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) ≠ ⊥ := by
    intro hbot
    apply w.ne_bot
    rw [eq_bot_iff] at hbot ⊢
    intro x hx
    have hx' : (RingOfIntegers.mapRingEquiv σ).symm x ∈
        w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) := by
      rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      exact hx
    have h0 := hbot hx'
    rw [Ideal.mem_bot] at h0 ⊢
    simpa using h0
  obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 L),
      w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) :=
    ⟨⟨_, Ideal.comap_isPrime _ _, hne⟩, rfl⟩
  have hfix : ∀ x : 𝓞 (maximalRealSubfield L),
      RingOfIntegers.mapRingEquiv σ (algebraMap _ (𝓞 L) x) = algebraMap _ (𝓞 L) x := by
    intro x
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingEquiv_apply]
    have hx : ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x : 𝓞 L) : L) =
        algebraMap (maximalRealSubfield L) L (x : maximalRealSubfield L) := rfl
    rw [hx]
    exact (IsCMField.complexConj L).commutes _
  have hsame : w' = w := by
    by_contra hne'
    apply hw
    refine ⟨w', hne', ?_⟩
    ext x
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, hw', hfix]
  have key := GlobalTheory.QNorm.valuation_of_eq_comap σ w w' hw' y
  rw [hsame] at key
  exact key.symm

theorem isSplitAt_of_isSquare : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : maximalRealSubfield L) (δ : L), δ ^ 2 = a → δ ∉ maximalRealSubfield L → ∀ w : HeightOneSpectrum (𝓞 L), IsSquare (algebraMap (maximalRealSubfield L) ((w.under (𝓞 (maximalRealSubfield L))).adicCompletion (maximalRealSubfield L)) a) → IsSplitAt w := by
  intro L _ _ _ a δ hδ hδL w hsq
  by_contra hw
  set u := w.under (𝓞 (maximalRealSubfield L)) with hu
  have ha : a ≠ 0 := by
    rintro rfl
    apply hδL
    have h0 : δ = 0 := by simpa using hδ
    rw [h0]
    exact zero_mem _
  obtain ⟨c, hc⟩ := exists_valuation_lt_one u a ha hsq
  have hconj : IsCMField.complexConj L δ = -δ := by
    have h1 : (IsCMField.complexConj L δ) ^ 2 = δ ^ 2 := by
      rw [← map_pow, hδ, IsCMField.complexConj_apply_eq_self]
    have h2 : IsCMField.complexConj L δ ≠ δ := fun h =>
      hδL ((IsCMField.complexConj_eq_self_iff L δ).mp h)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact absurd h h2
    · exact h
  set x : L := 2⁻¹ + (c : L) * δ with hx
  have hcc : IsCMField.complexConj L (c : L) = c := IsCMField.complexConj_apply_eq_self L c
  have hx' : IsCMField.complexConj L x = 2⁻¹ - (c : L) * δ := by
    rw [hx, map_add, map_mul, hcc, hconj, map_inv₀, map_ofNat]
    ring
  have hsum : x + IsCMField.complexConj L x = 1 := by
    rw [hx', hx]
    ring
  have hprod : x * IsCMField.complexConj L x =
      algebraMap (maximalRealSubfield L) L (1 / 4 - c ^ 2 * a) := by
    rw [hx', hx]
    simp only [map_sub, map_mul, map_pow, map_div₀, map_one, map_ofNat]
    change _ = 1 / 4 - (c : L) ^ 2 * (a : L)
    linear_combination (-(c : L) ^ 2) * hδ
  have : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  have hlt : w.valuation L (x * IsCMField.complexConj L x) < 1 := by
    rw [hprod, ← HeightOneSpectrum.valuation_liesOver L u w]
    exact pow_lt_one₀ zero_le hc (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal u.ne_bot)
  have heq := valuation_complexConj_of_not_split w hw x
  rw [map_mul, heq] at hlt
  have hx1 : w.valuation L x < 1 := by
    by_contra hge
    push Not at hge
    exact absurd hlt (not_lt.mpr (one_le_mul hge hge))
  have hadd := Valuation.map_add (w.valuation L) x (IsCMField.complexConj L x)
  rw [hsum, map_one, heq, max_self] at hadd
  exact absurd (lt_of_le_of_lt hadd hx1) (lt_irrefl 1)

end GlobalTheory.SplitOfSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightAdmissibleSmallSharesAtPoint
section
noncomputable section

namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem weightAdmissible_smallShares_at_point {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (h : AuxBlock8.admW D L X K) :
    ChW_at X K := by
  have h3 := h.2.2
  unfold AuxBlock8.WReq at h3
  unfold ChW_at
  refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) h3
  split_ifs <;> ring

end GlobalTheory.EX.DQ

end
end


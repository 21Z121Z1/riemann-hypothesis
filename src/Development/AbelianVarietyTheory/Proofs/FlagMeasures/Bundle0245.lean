import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsDiscrEqSqOfUnramifiedCmExtension
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem abs_discr_eq_abs_discr_sq_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
  intro F E _ _ _ _ _ σ hcm hu
  have hd := (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hu
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hd, Ideal.absNorm_top, one_mul, hcm.2.2.1] at h1
  have h2 : (((discr E).natAbs : ℕ) : ℝ) = (((discr F).natAbs ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
  simpa [Nat.cast_natAbs] using h2

end GlobalTheory.SnMass.VolN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsNormInverseDifferentIdealPowEqDiscr
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem absNorm_dInv_eq_abs_discr_pow_inv :
    ∀ (K : Type) [Field K] [NumberField K] (j : ℕ),
      (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  intro K _ _ j

  rw [dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm (K := K),
    NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs]
  push_cast
  rw [inv_pow]

end GlobalTheory.SnMass.VolN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AddFundamentalDomainMeasureEqOfCountable
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem addFundamentalDomains_measure_eq : ∀ {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (L : Submodule ℤ V) [Countable L] (D D' : Set V), MeasurableSet D → MeasurableSet D' → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D') → μ D = μ D' := by
  intro V _ _ _ μ _ L _ D D' hD hD' hu hu'
  let G : AddSubgroup V := L.toAddSubgroup
  haveI : Countable G := inferInstanceAs (Countable L)
  have key : ∀ E : Set V, MeasurableSet E → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ E) →
      IsAddFundamentalDomain G E μ := by
    intro E hE hEu
    refine IsAddFundamentalDomain.mk' hE.nullMeasurableSet ?_
    intro x
    obtain ⟨l, ⟨hlL, hlE⟩, huniq⟩ := hEu x
    refine ⟨⟨l, hlL⟩, ?_, ?_⟩
    · show (l : V) + x ∈ E
      rwa [add_comm]
    · rintro ⟨g, hg⟩ hgE
      have hgE' : x + g ∈ E := by
        have : (g : V) + x ∈ E := hgE
        rwa [add_comm]
      exact Subtype.ext (huniq g ⟨hg, hgE'⟩)
  exact (key D hD hu).measure_eq (key D' hD' hu')

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIndependentOfQuotientMeasure
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SnMass.AmpUniq

theorem isQuotMeas_smul {k r : ℕ} {μG μR ν : Measure (Mt k r)} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : IsQuotMeas μG (c • μR) ν) : IsQuotMeas μG μR (c • ν) := by
  intro f hf
  rw [h f hf]
  simp only [lintegral_smul_measure, smul_eq_mul]
  exact lintegral_const_mul' _ _ hc

theorem equiv_N {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {Φ : Mat k r → Wp}
    (hπ : IsURepOn (UWset k r z) π) (hΦ : IsSPsiEquiv z ψ π Φ) {n : Mat k r} (hn : n ∈ Nset k r)
    {x : Mat k r} (hx : x ∈ GG k r) : Φ (n * x) = ψ n • Φ x := by
  have h1 : (1 : Mat k r) ∈ UWset k r z := (isClosedSub_UWset (k := k) (r := r) z).2.2.1
  have e := hΦ 1 h1 n hn x hx
  rw [hπ.1.1, one_mul, ContinuousLinearMap.one_apply] at e
  exact e

theorem amp_uniq : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (cN : ℝ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → (∀ n ∈ Nset k r, ‖ψ n‖ = 1 ∧ ‖ψ' n‖ = 1) → IsSPsiEquiv z ψ π Φ → IsSPsiEquiv z' ψ' π' Φ' → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → ∀ (γ : Mat k r) (μG μR ν ν' : Measure (Mt k r)) (t : ℝ), γ ∈ GG k r → (∀ ρ ∈ Rset k r γ, ψ (γ * ρ * γ⁻¹) = ψ' ρ) → IsHaarOn (GG k r) μG → IsHaarOn (Rset k r γ) μR → 0 < t → IsQuotMeas μG μR ν → IsQuotMeas μG (ENNReal.ofReal t • μR) ν' → ampJ ν cN Φ Φ' γ = (t : ℂ) • ampJ ν' cN Φ Φ' γ := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ z z' ψ ψ' π π' Φ Φ' cN _ _ _ _ hπ hπ' hψ hΦ hΦ' hc hc' γ μG μR ν ν' t hγ
    hψγ hG hR ht hν hν'
  obtain ⟨hRc, hRu⟩ := GlobalTheory.T.unipotentRadical_inter_conjugate_closed_unimodular k r γ hγ
  have hν₂ : IsQuotMeas μG μR (ENNReal.ofReal t • ν') := isQuotMeas_smul ENNReal.ofReal_ne_top hν'
  have hGm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := (isClosedSub_GG (k := k) (r := r)).2.2.2.1
  let F : Mat k r → (Wq →L[ℂ] Wp) := fun g => (innerSL ℂ (Φ' g)).smulRight (Φ (γ * g))
  have hFc : ContinuousOn F (GG k r) := by
    have h1 : ContinuousOn (fun g => innerSL ℂ (Φ' g)) (GG k r) :=
      (innerSL ℂ).continuous.comp_continuousOn hc'
    have h2 : ContinuousOn (fun g => Φ (γ * g)) (GG k r) :=
      hc.comp (continuous_const.mul continuous_id).continuousOn fun g hg => hGm γ hγ g hg
    exact (ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂.comp_continuousOn (h1.prodMk h2)
  have hFi : ∀ ρ ∈ Rset k r γ, ∀ x ∈ GG k r, F (ρ * x) = F x := by
    intro ρ hρ x hx
    have hρN : ρ ∈ Nset k r := hρ.1
    have hρc : γ * ρ * γ⁻¹ ∈ Nset k r := hρ.2
    have e1 : Φ' (ρ * x) = ψ' ρ • Φ' x := equiv_N hπ' hΦ' hρN hx
    have e2 : γ * (ρ * x) = γ * ρ * γ⁻¹ * (γ * x) := by
      rw [show γ * ρ * γ⁻¹ * (γ * x) = γ * ρ * (γ⁻¹ * γ) * x by simp only [Matrix.mul_assoc],
        Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hγ), Matrix.mul_one, Matrix.mul_assoc]
    have e3 : Φ (γ * (ρ * x)) = ψ' ρ • Φ (γ * x) := by
      rw [e2, equiv_N hπ hΦ hρc (hGm γ hγ x hx), hψγ ρ hρ]
    have hn : ‖ψ' ρ‖ = 1 := (hψ ρ hρN).2
    ext w
    simp only [F, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, e1, e3, inner_smul_left,
      smul_smul]
    congr 1
    calc (starRingEnd ℂ) (ψ' ρ) * inner ℂ (Φ' x) w * ψ' ρ
        = ((starRingEnd ℂ) (ψ' ρ) * ψ' ρ) * inner ℂ (Φ' x) w := by ring
      _ = inner ℂ (Φ' x) w := by rw [Complex.conj_mul', hn]; simp
  have key := (GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary k r (Rset k r γ) μG μR ν (ENNReal.ofReal t • ν') hRc hG hR (hRu μR hR) hν hν₂
    (Wq →L[ℂ] Wp) F hFc hFi).2
  rw [integral_smul_measure, ENNReal.toReal_ofReal ht.le] at key
  change (cN : ℂ)⁻¹ • ∫ x, F (Matrix.of x) ∂ν = (t : ℂ) • ((cN : ℂ)⁻¹ • ∫ x, F (Matrix.of x) ∂ν')
  rw [key, Complex.coe_smul, smul_comm]

end GlobalTheory.SnMass.AmpUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalStandardSide
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.KernelRe

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det := ((uHGroup _ _ hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r := ((uHGroup _ _ hpk_unit).2.2 a ha).2

def lmulEquiv (a : Mat k r) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := lmulM a x
  invFun x := lmulM a⁻¹ x
  left_inv x := by
    show (a⁻¹ * (a * Matrix.of x) : Mat k r) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]
  right_inv x := by
    show (a * (a⁻¹ * Matrix.of x) : Mat k r) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
  measurable_toFun := Continuous.measurable (α := Mt k r) (γ := Mt k r)
    (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  measurable_invFun := Continuous.measurable (α := Mt k r) (γ := Mt k r)
    (continuous_const.matrix_mul (continuous_id (X := Mat k r)))

theorem rconv_eq_translate {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    (μG : Measure (Mt k r)) (e : Mat k r → ℂ) (W : Mat k r → Wp) (hμ : IsHaarOn (GG k r) μG)
    {y : Mat k r} (hy : y ∈ GG k r) :
    rconv μG e W y = ∫ g, e (y⁻¹ * Matrix.of g) • W (Matrix.of g) ∂μG := by
  have hyu : IsUnit y⁻¹.det := GG_unit (GG_inv hy)
  have hmap : μG.map (lmulM y⁻¹) = μG := hμ.2.2.2 _ (GG_inv hy)
  have hme : MeasurableEmbedding (lmulM (k := k) (r := r) y⁻¹) :=
    (lmulEquiv y⁻¹ hyu).measurableEmbedding
  unfold rconv
  conv_lhs => rw [← hmap]
  rw [hme.integral_map]
  congr 1; funext g
  show e (Matrix.of (lmulM y⁻¹ g)) • W (y * Matrix.of (lmulM y⁻¹ g)) = _
  show e (y⁻¹ * Matrix.of g) • W (y * (y⁻¹ * Matrix.of g)) = _
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GG_unit hy), Matrix.one_mul]

theorem kernel_rconv : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g))) ν ∧ rconv μG (eFun μG σ w) W y = (d : ℂ) • ∫ g, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) ∂ν := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν W hWG hWν hW hL2 y hy
  obtain ⟨hz, hT, hπ, hμS, _⟩ := hSide
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have hun := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hμS
  have hμG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hWeil := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hμG hμS hun hν
  have hFint : Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG :=
    GlobalTheory.T.integrable_besselCoefficient_smul_equivariant k r σ w a μG d z c π μS hStd ⟨hz, hT, hπ, hμS, inferInstance⟩ ν hν W hWG hWν hW hL2 y hy
  obtain ⟨hI, hEq⟩ := hWeil.2.2.2.1 Wp _ hFint
  have hae : ∀ᵐ x ∂ν, (∫ s, star (coef σ w w (y⁻¹ * Matrix.of (lmulM (Matrix.of s) x))) •
      W (Matrix.of (lmulM (Matrix.of s) x)) ∂μS) =
      be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
    have h0 : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
      rw [ae_iff]; simpa using hWeil.2.1
    filter_upwards [h0] with x hx
    exact GlobalTheory.T.bessel_inner_integral_eq_form k r σ w a μG d z c π μS hStd ⟨hz, hT, hπ, hμS, inferInstance⟩ W hW y hy x hx
  have hfd : fdegH μG σ w = d :=
    GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality k r σ μG d w hStd.2.2.2.2.2.1 (by
      intro h0; have := hStd.2.2.2.1; rw [h0, norm_zero] at this; exact zero_ne_one this)
  refine ⟨hI.congr hae, ?_⟩
  rw [rconv_eq_translate μG _ W hμG hy]
  have hfun : (fun g : Mt k r => eFun μG σ w (y⁻¹ * Matrix.of g) • W (Matrix.of g)) =
      fun g => (d : ℂ) • (star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) := by
    funext g; simp only [eFun, hfd, coef, smul_smul]
  rw [hfun, integral_smul, hEq, integral_congr_ae hae]

end GlobalTheory.SgInf.KernelRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmExtensionConjMemInverseDifferentIdealPow
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.SnMass.VolN

variable {E : Type} [Field E] [NumberField E]

theorem ringEquiv_mem_one (e : E ≃+* E) {x : E} (hx : x ∈ (1 : Submodule (𝓞 E) E)) :
    e x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [Submodule.mem_one] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  have hy : IsIntegral ℤ (e (algebraMap (𝓞 E) E y)) :=
    (RingOfIntegers.isIntegral_coe y).map (e : E →+* E).toIntAlgHom
  exact ⟨⟨_, hy⟩, rfl⟩

theorem ringEquiv_mem_dual (e : E ≃+* E) {x : E}
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    e x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))] at hx ⊢
  intro a ha
  have ha' : e.symm a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at ha ⊢
    exact ringEquiv_mem_one e.symm ha
  have h := hx _ ha'
  let f : E ≃ₐ[ℚ] E := AlgEquiv.ofRingEquiv (f := e) (fun q => map_ratCast e q)
  have key : Algebra.traceForm ℚ E (e x) a = Algebra.traceForm ℚ E x (e.symm a) := by
    simp only [Algebra.traceForm_apply]
    have : e x * a = f (x * e.symm a) := by
      rw [map_mul]
      show e x * a = e x * e (e.symm a)
      rw [RingEquiv.apply_symm_apply]
    rw [this, Algebra.trace_eq_of_algEquiv]
  rw [key]; exact h

theorem ringEquiv_mem_pow (e : E ≃+* E) (M : Submodule (𝓞 E) E) (hM : ∀ x ∈ M, e x ∈ M) :
    ∀ (j : ℕ) (x : E), x ∈ M ^ j → e x ∈ M ^ j := by
  intro j
  induction j with
  | zero => intro x hx; rw [pow_zero] at hx ⊢; exact ringEquiv_mem_one e hx
  | succ j ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]; exact Submodule.mul_mem_mul (ih m hm) (hM n hn)
    · rw [map_add]; exact Submodule.add_mem _ ha hb

theorem ringEquiv_mem_dInv (e : E ≃+* E) (j : ℕ) (x : E) (hx : x ∈ dInv E j) : e x ∈ dInv E j := by
  have hd : ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  rw [dInv, hd, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow] at hx ⊢
  exact ringEquiv_mem_pow e _ (fun y hy => ringEquiv_mem_dual e hy) j x hx

theorem conj_mem_dInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) (x : E), x ∈ dInv E j → σ x ∈ dInv E j := by
  intro F E _ _ _ _ _ σ _ j x hx
  have hb : Function.Bijective ((σ : E →+* E).toRatAlgHom) := AlgHom.bijective _
  exact ringEquiv_mem_dInv (RingEquiv.ofBijective (σ : E →+* E) hb) j x hx

end GlobalTheory.SnMass.VolN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerNormalFormBlockUnitriangularStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular : ∀ (k r : ℕ) (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ → Rset k r g₀ = Set.range (fun x : UTin β → ℂ => uEmb k r (upperIn β x)) ∧ IsClosedSub k r (Rset k r g₀) ∧ IsHaarOn (Rset k r g₀) (lebR k r β) ∧ IsUnimod (Rset k r g₀) (lebR k r β) ∧ IsNormal k r β g₀⁻¹ ∧ (lebR k r β).map (conjM g₀) = lebR k r β := by
  first | exact @GlobalTheory.Amp.StabNormal.stabiliser_normal | exact GlobalTheory.Amp.StabNormal.stabiliser_normal | (intros; apply GlobalTheory.Amp.StabNormal.stabiliser_normal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowDivLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_inverseDifferentPow_div_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * (dInv E t')⁻¹) c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  first | exact @GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div | exact GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div | (intros; apply GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowMulLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_inverseDifferentPow_mul_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * dInv E t') c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  first | exact @GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | exact GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | (intros; apply GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeQuotientOfRealIdentity
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem covolQuotient_real (d : ℝ) (f t : ℕ) (hd : 1 ≤ d) :
    ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2) =
      ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) *
        ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ))) := by
  have hd0 : 0 < d := by linarith
  have hd0' : d ≠ 0 := hd0.ne'
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd0.le

  have h1 : d ^ (1 / 2 - 2 * (t : ℝ)) = Real.sqrt d / d ^ (2 * t) := by
    rw [Real.rpow_sub hd0, Real.sqrt_eq_rpow]
    congr 1
    exact_mod_cast Real.rpow_natCast d (2 * t)
  rw [Real.sqrt_sq hd0.le, h1]
  calc ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * d
      = ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * (Real.sqrt d * Real.sqrt d) := by rw [hs]
    _ = _ := by
        rw [← pow_mul, show 2 * (2 * t) = 2 * t + 2 * t by ring, pow_add]
        field_simp

theorem covolQuotient_arith : ∀ (d c : ℝ) (f t : ℕ) (m : ℝ≥0∞), 1 ≤ d → 0 < c →
    ENNReal.ofReal (((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2)) =
      ENNReal.ofReal ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) * m →
    ENNReal.ofReal ((2 * c) ^ f) * m = ENNReal.ofReal (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by
  intro d c f t m hd hc h
  have hd0 : 0 < d := by linarith
  have hY : 0 < (d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d :=
    mul_pos (mul_pos (inv_pos.mpr (pow_pos hd0 _)) (by norm_num)) (Real.sqrt_pos.mpr hd0)
  have hZ : 0 ≤ (2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hd0.le _)

  rw [covolQuotient_real d f t hd, ENNReal.ofReal_mul hY.le] at h
  have hm : m = ENNReal.ofReal ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ))) :=
    ((ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hY).ne' ENNReal.ofReal_ne_top).mp h).symm
  rw [hm, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) f)]
  congr 1
  have h2 : (2 : ℝ) ^ f * (2⁻¹ : ℝ) ^ f = 1 := by rw [← mul_pow]; norm_num
  calc (2 * c) ^ f * ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ)))
      = ((2 : ℝ) ^ f * (2⁻¹ : ℝ) ^ f) * (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by ring
    _ = d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f := by rw [h2, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DelSqIrreducibleUnitaryStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delSq_unitary_stable_and_irreducible : ∀ (n : ℕ) (lam : DomWeight n), FiniteDimensional ℂ (delSq ℂ n lam) ∧ delSq ℂ n lam = nablaSq ℂ n lam ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ delSq ℂ n lam, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam) ∧ ∀ U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ), U ≤ delSq ℂ n lam → (∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ p ∈ U, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ U) → U = ⊥ ∨ U = delSq ℂ n lam := by
  first | exact @GlobalTheory.WeylUnitary.delSq_irreducible_unitary | exact GlobalTheory.WeylUnitary.delSq_irreducible_unitary | (intros; apply GlobalTheory.WeylUnitary.delSq_irreducible_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesLowestKTypeUnitUnitaryFormalDegree
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.RowLev

theorem isDS_lowUnit_unitary_fdegOf : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  intro n ε lam H _ _ σ h
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hvS, hv, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · have hle : S ≤ lowKSub ε lam σ := le_sSup hS
      exact hle (S.smul_mem _ hvS)
  · intro x a b
    have hx : uMat x ∈ UJset ε := x.2
    let f : H →ₗᵢ[ℂ] H := ⟨(σ (uMat x) : H →ₗ[ℂ] H), hU.2.1 _ hx⟩
    exact f.inner_map_map a b
  · intro c d w hc hw hF
    obtain ⟨hd, hI⟩ := hF
    have h1 := (hI w w w w).2
    have hc' : (0 : ℝ) < (c : ℝ) := hc
    have hww : ⟪w, w⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hpt : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g))
        = fun g => ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hpt, integral_smul_measure, integral_complex_ofReal, hww, ENNReal.coe_toReal,
      Complex.real_smul] at h1
    have h2 : (c : ℝ) * ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 * 1 / d := by
      exact_mod_cast h1
    have h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / ((c : ℝ) * d) := by
      field_simp at h2 ⊢
      linarith
    unfold fdegOf
    rw [h3, hw]
    simp

end GlobalTheory.RowLev
end


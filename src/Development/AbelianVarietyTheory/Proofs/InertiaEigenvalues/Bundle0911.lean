import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0899
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.InertPlacesGoodSet
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0898
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0900
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0901

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergKernelZeroCoeffTwoCentralChars
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

open GlobalTheory.ThetaPoisson GlobalTheory.RSTheta GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix

noncomputable section

namespace GlobalTheory.RSResidue

theorem rsHat_zero_props_two : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → ∀ (φ φ' : Sm E a), φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω → φ'.1 ∈ GlobalTheory.Petersson.bddForms E a ω' → ∀ (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E), Continuous (fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ (∃ C : ℝ, ∀ g, ‖GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0‖ ≤ C) ∧ (∀ (γ : GL (Fin a) E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) 0 = GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ ∀ (z : Neutral.B1.Ideles E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (GeneralLinearGroup.scalar (Fin a) z * g) 0 = ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
  intro E _ _ _ a ω ω' hω hω' φ φ' h h' ℓ Φ hΦ J η
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hc' : ∀ g, rsHat ℓ φ.1 φ'.1 Φ J η g 0 = (∫ u, rsInf ℓ φ.1 φ'.1 Φ g u ∂infMeasure E a) * c := hc
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hc']
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc', norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ g
    have e : rsPsi ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y =>
      rsPsi_ratGL_mul ℓ h.2.1 h'.2.1 Φ J η γ g y
    simp only [rsHat, e]
  · intro z g
    have e : ∀ u, rsInf ℓ φ.1 φ'.1 Φ (GeneralLinearGroup.scalar (Fin a) z * g) u =
        ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * rsInf ℓ φ.1 φ'.1 Φ g u := fun u => by
      simp only [rsInf, mul_assoc (GeneralLinearGroup.scalar (Fin a) z) g, h.2.2.1, h'.2.2.1, map_mul]
      ring
    rw [hc', hc', funext e, integral_const_mul]
    ring

end GlobalTheory.RSResidue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralPoleRapidKernelSpan
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSThetaLimR

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mspanR_le_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) :
    GlobalTheory.JSW.mspanR π ≤ bddForms E a ω := by
  rw [← GlobalTheory.JSW.rspan_eq_mspanR]
  exact GlobalTheory.JSW.rspan_le (fun φ hφ => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ)
    (fun F hF h => mul_right_mem_bddForms hF h) (fun F hF X _ ν _ k γ hk => GlobalTheory.JSW.kerInf_mem_bddForms hF hk)

theorem mem_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {φ : Sm E a}
    (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) : φ.1 ∈ bddForms E a ω :=
  hφ.elim (fun h => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ h)
    (fun h => mspanR_le_bddForms hω hπ h)

theorem mem_rsm {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) :
    φ ∈ GlobalTheory.RSThetaLowM.rsm π := by
  change φ.1 ∈ GlobalTheory.JSW.mspanR π
  rcases hφ with h | h
  · rw [← GlobalTheory.JSW.rspan_eq_mspanR]; exact GlobalTheory.JSW.mem_rspan h
  · exact h

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem resConst_ne_zero {Φ : (Fin a → Cinf E) → ℂ} (hΦ1 : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ2 : HasCompactSupport Φ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (hpos : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (hne : Φ ≠ 0) :
    ((finiteMeasurePi E (latt a J)).toReal : ℂ) * ∫ x, Φ x ∂infMeasure E a ≠ 0 := by
  have hv : (finiteMeasurePi E (latt a J)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
    ⟨((isOpen_latt J).measure_pos _ ⟨0, fun i => (idealFiniteAdeles J).zero_mem⟩).ne',
      (isCompact_latt J).measure_lt_top.ne⟩
  refine mul_ne_zero (Complex.ofReal_ne_zero.2 hv) ?_
  have e : (fun u => Φ u) = fun u => (((Φ u).re : ℝ) : ℂ) := funext fun u => Complex.ext rfl (by simp [(hpos u).2])
  obtain ⟨x, hx⟩ : ∃ x, Φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hre : (Φ x).re ≠ 0 := fun h0 => hx (Complex.ext h0 (hpos x).2)
  have hpos' : 0 < ∫ u, (Φ u).re ∂(volume : Measure (Fin a → Cinf E)) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (Complex.continuous_re.comp hΦ1.continuous)
      (hΦ2.comp_left Complex.zero_re) (fun u => (hpos u).1) hre
  rw [e, integral_complex_ofReal, infMeasure, integral_smul_measure]
  refine Complex.ofReal_ne_zero.2 (smul_ne_zero ?_ hpos'.ne')
  simp

theorem setIntegral_rsHat_zero_of_bdd {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ1 : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦ2 : HasCompactSupport Φ) (hΦ3 : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕' μ) {ω : HChar E} (hω : ω.IsUnitary) {φ φ' : Sm E a}
    (hb : φ.1 ∈ bddForms E a ω) (hb' : φ'.1 ∈ bddForms E a ω) :
    ∫ g in 𝓕', adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 ∂μ =
      (((finiteMeasurePi E (latt a J)).toReal : ℂ) * ∫ x, Φ x ∂infMeasure E a) *
        ∫ g in 𝓕', φ.1 g * conj (φ'.1 g) ∂μ := by
  have hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ := ⟨hΦ1, hΦ2, hΦ3⟩
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  haveI : IsFiniteMeasure (μ.restrict 𝓕') :=
    ⟨by rw [Measure.restrict_apply_univ, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]; exact measure_lt_top _ _⟩
  haveI : SFinite (infMeasure E a) := by unfold infMeasure; infer_instance
  obtain ⟨C, hC⟩ := hb.2.2.2
  obtain ⟨D, hD⟩ := hb'.2.2.2
  have hΦi : Integrable Φ (infMeasure E a) := by
    unfold infMeasure
    exact (hΦ1.continuous.integrable_of_hasCompactSupport hΦ2).smul_measure (by simp)
  have hi : Integrable (fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2)
      ((μ.restrict 𝓕').prod (infMeasure E a)) := by
    refine ((integrable_const (C * D)).mul_prod hΦi.norm).mono'
      (continuous_rsInf hb.1 hb'.1 hΦ1.continuous hΦ3).aestronglyMeasurable (.of_forall fun p => ?_)
    simp only [rsInf, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1)))
      (norm_nonneg _)
  have hx : ∀ x, ∫ g in 𝓕', rsInf ℓ φ.1 φ'.1 Φ g x ∂μ = (∫ g in 𝓕', φ.1 g * conj (φ'.1 g) ∂μ) * Φ x := by
    intro x
    simp only [rsInf]
    rw [integral_mul_const]
    congr 1
    exact GlobalTheory.RSResidue.setIntegral_mul_right h𝓕 (f := fun g => φ.1 g * conj (φ'.1 g))
      (GlobalTheory.Petersson.leftInv_mul_conj hω hb hb') _
  simp only [GlobalTheory.RSResidue.rsHat_zero J η φ φ' hΦ]
  rw [integral_mul_const, integral_integral_swap hi]
  simp only [hx, integral_const_mul]
  ring

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem theta_integral_low_mspanR {ℓ : Fin a} {π π' : CuspSub E a} (hπ : π.IsUnitary) (hπ' : π'.IsUnitary)
    {φ φ' : Sm E a} (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) (hφ' : φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π')
    (hc : Continuous φ.1) (hc' : Continuous φ'.1) {Φ : (Fin a → Cinf E) → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hcs : HasCompactSupport Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    (∀ x : ℝ, 1 < x →
      IntegrableOn (fun g : GA E a =>
        (∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ))) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ ∧
      IntegrableOn (fun g : GA E a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ))) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ ∧
      ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ)) ∂μ =
        ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ +
        ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ) ∧
    Continuous fun x : ℝ => ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ := by
  have h := mem_rsm hφ
  have h' := mem_rsm hφ'
  have hT : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ := ⟨hΦ, hcs, hs⟩
  obtain ⟨-, -, b3⟩ := GlobalTheory.RSThetaLowM.partB_entire J η hπ hπ' h h' hc hc' hT h𝓕
  simp only [Complex.ofReal_cpow (ideleModule E _).2.le, Complex.ofReal_sub, Complex.ofReal_one]
  exact ⟨fun x hx => ⟨(GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).1,
      GlobalTheory.RSThetaLowM.integrableOn_partA J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx,
      (GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).2⟩,
    b3.continuous.comp Complex.continuous_ofReal⟩

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

theorem theta_integral_pole_mspanR : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → (∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ) ∧ Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 (c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ)) := by
  intro E _ _ _ a ℓ Φ hΦ hc hs J η μ _ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨K, hKdef⟩ : ∃ K : ℂ, K = ((GroundTheory.Automorphic.GJMatrix.finiteMeasurePi E (GlobalTheory.ThetaPoisson.latt a J)).toReal : ℂ) * ∫ x, Φ x ∂GlobalTheory.ThetaPoisson.infMeasure E a := ⟨_, rfl⟩
  have hK0 : (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → K ≠ 0 := fun h1 h2 => hKdef ▸ resConst_ne_zero hΦ hc J h1 h2
  have had : ((a : ℝ) * (Module.finrank ℚ E : ℝ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 ℓ.pos)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  refine ⟨((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ)) * K,
    fun h1 h2 => mul_ne_zero (Complex.ofReal_ne_zero.2 (one_div_ne_zero had)) (hK0 h1 h2), ?_⟩
  intro π π' ω hω hπ hπ' φ φ' hφ hφ'
  have hu : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ⟩
  have hu' : π'.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ'⟩
  have hb := mem_bddForms hω hπ hφ
  have hb' := mem_bddForms hω hπ' hφ'
  obtain ⟨u1, u2, u3, -⟩ := GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π' hu hu' φ φ' hφ hφ' Φ hΦ.continuous hc hs J η μ 𝓕 h𝓕
  obtain ⟨l1, l2⟩ := theta_integral_low_mspanR hu hu' hφ hφ' hb.1 hb'.1 hΦ hc hs J η h𝓕
  obtain ⟨f1, f2, f3⟩ := GlobalTheory.RSResidue.rsHat_zero_props hω hb hb' ⟨hΦ, hc, hs⟩ J η
  have hres := GlobalTheory.T.tendsto_residueTerm_rankinSelberg_innerProduct E a ℓ.pos μ 𝓕 𝓕' h𝓕 h𝓕' _ f1 f2 f3
  rw [setIntegral_rsHat_zero_of_bdd hΦ hc hs J η h𝓕' hω hb hb', ← hKdef] at hres
  have hδc : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)
  have hδ0 : ∀ g : GA E a, 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) := fun g => (ideleModule E _).2
  have hT : MeasurableSet {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} := (isClosed_le hδc continuous_const).measurableSet
  have hsum : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) = ∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := fun g =>
    GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η φ.1 φ'.1 hs g
  have hint : ∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ := by
    intro x hx
    have iLo : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
      simp only [hsum]; exact (l1 x hx).1
    have iHi : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ))
        (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ := by
      simp only [Complex.ofReal_cpow (hδ0 _).le]; exact u3 x
    refine (iLo.union iHi).mono_set fun g hg => ?_
    by_cases h : (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, (not_le.1 h).le⟩
  refine ⟨hint, ?_⟩

  set U : ℝ → ℂ := fun x => ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ with hU
  set B : ℝ → ℂ := fun x => ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ with hB
  have hsplit : ∀ x : ℝ, 1 < x → ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ =
      ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ + B x + U x := by
    intro x hx
    rw [← integral_inter_add_diff hT (hint x hx)]
    congr 1
    simp only [hsum]
    exact (l1 x hx).2.2

  set M : ℝ := ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
    (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (2 : ℝ) ∂μ with hM
  have hUb : ∀ x : ℝ, x ≤ 2 → ‖U x‖ ≤ M := by
    intro x hx2
    refine norm_integral_le_of_norm_le ((u2 2).mono_set fun g hg => ⟨hg.1, by have h := hg.2; simp only [Set.mem_setOf_eq, not_le] at h ⊢; exact h.le⟩) ?_
    refine (ae_restrict_of_ae_restrict_of_subset (Set.diff_subset_compl _ _) (ae_restrict_mem hT.compl)).mono
      fun g hg => ?_
    have h1 : 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
      have h := hg; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at h; exact h.le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hδ0 g).le _)]
    exact mul_le_mul (norm_tsum_le_tsum_norm (u1 g)) (Real.rpow_le_rpow_of_exponent_le h1 hx2)
      (Real.rpow_nonneg (hδ0 g).le _) (tsum_nonneg fun _ => norm_nonneg _)
  have hx1 : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝 1) (𝓝 ((((1 : ℝ) - 1 : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have tB : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * B x) (𝓝[>] 1) (𝓝 0) := by
    simpa using hx1.mul ((l2.tendsto 1).mono_left nhdsWithin_le_nhds)
  have tU : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * U x) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => ‖((x - 1 : ℝ) : ℂ)‖ * M) ?_
      (by have h := hx1.norm.mul_const M; rwa [norm_zero, zero_mul] at h)
    filter_upwards [Ioc_mem_nhdsGT (one_lt_two : (1 : ℝ) < 2)] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hUb x hx.2) (norm_nonneg _)
  have tot := (hres.add tB).add tU
  rw [add_zero, add_zero, mul_assoc] at *
  refine tot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [hsplit x hx]
  ring

end GlobalTheory.RSThetaLimR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfNonThickLetter
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowNT

theorem logb_le_of_le_four_exp {l x large₂ : ℝ} (hl : 11 ≤ l) (hLg : 0 ≤ large₂) (hx0 : 0 ≤ x)
    (hx : x ≤ 4 * Real.exp large₂) : Real.logb l x ≤ 3 + large₂ := by
  rcases hx0.eq_or_lt with h | hpos
  · subst h; simp; linarith
  have hlogl : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h4 : Real.log x ≤ Real.log 4 + large₂ := by
    have := Real.log_le_log hpos hx
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have h43 : Real.log 4 ≤ 3 := by have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  unfold Real.logb
  rcases le_or_gt (Real.log x) 0 with hn | hp
  · have : Real.log x / Real.log l ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn (by linarith)
    linarith
  · have : Real.log x / Real.log l ≤ Real.log x := div_le_self hp.le hlogl
    linarith

theorem lift_shape_le {l H hB e : ℝ} (hl : 11 ≤ l) (hB1 : 1 ≤ hB) (hH0 : 0 ≤ H) (hH : H ≤ 2 * hB)
    (he : e ≤ 23 * (1 + H / l + (1 + Real.logb l (H + 1)))) :
    e ≤ 69 * (1 + hB / l + Real.logb l hB) := by
  have hl1 : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have h1 : H / l ≤ 2 * hB / l := div_le_div_of_nonneg_right hH hl0.le
  have h2 : Real.logb l (H + 1) ≤ Real.logb l (3 * hB) :=
    Real.logb_le_logb_of_le hl1 (by linarith) (by linarith)
  have h3 : Real.logb l (3 * hB) = Real.logb l 3 + Real.logb l hB :=
    Real.logb_mul (by norm_num) (by linarith)
  have h4 : Real.logb l 3 ≤ 1 := by
    have := Real.logb_le_logb_of_le hl1 (show (0:ℝ) < 3 by norm_num) (show (3:ℝ) ≤ l by linarith)
    rwa [Real.logb_self_eq_one hl1] at this
  have h5 : 0 ≤ Real.logb l hB := Real.logb_nonneg hl1 hB1
  have h6 : 0 ≤ hB / l := div_nonneg (by linarith) hl0.le
  have h7 : 2 * hB / l = 2 * (hB / l) := by ring
  linarith

theorem bound_real {l n r m h w η S lg band e' hB wP eta₃ Sc large₂ ind cE : ℝ}
    (hl : 11 ≤ l) (hn : 0 ≤ n) (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hh : h ≤ hB) (hw : w ≤ wP) (hη : η ≤ eta₃) (hS : S ≤ Sc) (h0w : 0 ≤ w) (h0η : 0 ≤ η)
    (h0S : 0 ≤ S) (h0h : 0 ≤ h) (hlg : lg ≤ 3 + large₂) (hLg : 1 ≤ large₂) (hband : band ≤ ind)
    (hind0 : 0 ≤ ind) (he : e' ≤ 69 * cE) (hcE : 0 ≤ cE) :
    320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) + 320 * n * m * e' ≤
      368 * ((n + 1) * r * (hB / l ^ 2)) +
        2082 * ((n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) + 22365 * (n * m * cE) := by
  have hl0 : 0 < l := by linarith
  have hA : 0 ≤ (n + 1) * r := mul_nonneg (by linarith) hr
  have e1 : h / l ^ 2 ≤ hB / l ^ 2 := div_le_div_of_nonneg_right hh (by positivity)
  have e2 : (w + η) / l ≤ (wP + eta₃) / l := div_le_div_of_nonneg_right (by linarith) hl0.le
  have e3 : η * band ≤ eta₃ * ind := by
    have hb0 : 0 ≤ band ∨ band < 0 := le_or_gt 0 band
    rcases hb0 with hb0 | hb0
    · exact mul_le_mul hη hband hb0 (by linarith)
    · have : η * band ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0η hb0.le
      have : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
      linarith
  have e4 : 0 ≤ (wP + eta₃) / l := div_nonneg (by linarith) hl0.le
  have e5 : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
  have e6 : 0 ≤ hB / l ^ 2 := div_nonneg (by linarith) (by positivity)
  have hbr : h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band ≤
      hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) := by
    nlinarith
  have k1 : 320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) ≤
      320 * ((n + 1) * r) * (hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) := by
    rw [mul_assoc 320 (n + 1) r]
    exact mul_le_mul_of_nonneg_left hbr (by positivity)
  have k2 : 320 * n * m * e' ≤ 320 * n * m * (69 * cE) :=
    mul_le_mul_of_nonneg_left he (by positivity)
  have hf : 0 ≤ (n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) :=
    mul_nonneg hA (by linarith)
  have hH : 0 ≤ (n + 1) * r * (hB / l ^ 2) := mul_nonneg hA e6
  have hM : 0 ≤ n * m * cE := by positivity
  nlinarith

end GlobalTheory.NLink.RowNT

namespace GlobalTheory.NLink.RowNT

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)), ArcLiftingSetup.aux₃ D HW F 320 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordsNT Wd → RowL i r ρ π w hw Cx (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  intro D L P HW F C₂ i r ρ π w hw Cx hG Wd h17 h54 hpar h11 hπ hb hbox hN
  intro T₁ T₂ Fm h2 h1 hF
  classical
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hcA := caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hG hb.unram (by omega)
  have hT := h17 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG hb.unram
  have hS := GlobalTheory.Survey.InertPlacesGoodSet.setting_of_wordsNT (by omega) hb hN inferInstance T₁ T₂ Fm h2 h1 hF
  have hX := (hT (by rw [hp]; exact h11) T₁ T₂ Fm Wd.b Wd.w Wd.S Wd.η Wd.m Wd.up Wd.sz Wd.Mi Wd.hi hS
    hN.w20 hN.η20 hN.twenty_words_le_b hN.some_nt).1 hN.alt
  rw [hp] at hX
  have hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have hnl : Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) = TwistedPlaces.nLam D w := by
    have e : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.2 hb.unram
    rw [e]
    exact hb.deg
  have hO := h54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁ Wd.Mi Wd.hi
    (hb.t1 T₁ h1).1 (hb.t1 T₁ h1).2.2
  have hl : (11 : ℝ) ≤ (D.nd.l i : ℝ) := by exact_mod_cast h11
  have hb1 : (1 : ℝ) ≤ L.sc.b := TwistedPlaces.one_le_b L
  have hSc := L.Sc_pos
  have hEt := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hB1 : (1 : ℝ) ≤ TwistedPlaces.hB L := by unfold TwistedPlaces.hB; linarith
  have hB2 : TwistedPlaces.hB L ≤ 2 * L.sc.b := by unfold TwistedPlaces.hB; unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hpar; linarith
  have hHm : (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ 2 * TwistedPlaces.hB L := by
    have hfl : LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi ≤ ⌊2 * TwistedPlaces.hB L⌋₊ := by
      unfold LiftingTheory.Hmax
      apply Finset.sup_le
      intro k _
      apply Nat.le_floor
      exact hbox.box_le _
    calc (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ (⌊2 * TwistedPlaces.hB L⌋₊ : ℝ) := by exact_mod_cast hfl
      _ ≤ 2 * TwistedPlaces.hB L := Nat.floor_le (by linarith)
  have he : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
      69 * coreE L (D.nd.l i) := by
    have hO' : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
        23 * (1 + (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) / ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p +
          (1 + Real.logb ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p
            ((LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) + 1))) := hO.1 hcA
    rw [hp] at hO'
    unfold coreE
    exact GlobalTheory.NLink.RowNT.lift_shape_le hl hB1 (Nat.cast_nonneg _) hHm hO'
  have hh : (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) ≤ TwistedPlaces.hB L := by
    have hwb : (Wd.w : ℝ) ≤ Wd.b := by have := hN.w20; exact_mod_cast (by omega : Wd.w ≤ Wd.b)
    have hle := hb.h_le
    unfold TruncatedSeriesCountingBounds.hB
    split_ifs
    · push_cast; linarith
    · push_cast; have : (0:ℝ) ≤ Wd.η := Nat.cast_nonneg _; linarith
  have hlg : Real.logb (D.nd.l i : ℝ) (2 * (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤ 3 + TwistedPlaces.large₂ L := by
    apply GlobalTheory.NLink.RowNT.logb_le_of_le_four_exp hl (by linarith [TwistedPlaces.L_ge_one L]) (by positivity)
    rw [← TwistedPlaces.b_eq]; linarith
  have hband : ((if TruncatedSeriesCountingBounds.Band (D.nd.l i) Wd.b Wd.S Wd.η Wd.sz
        (Real.logb (↑(D.nd.l i)) (2 * ↑(TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz))) 320 then 1 else 0) : ℝ) ≤
      (if bandOf L HW 320 i r ρ w then 1 else 0) := by
    split_ifs with hx hy
    · exact le_rfl
    · exact absurd ⟨h11, π, hπ, hw, Cx, hG, Wd, hb, hbox, hN, hx⟩ hy
    · norm_num
    · exact le_rfl
  have key := GlobalTheory.NLink.RowNT.bound_real (l := (D.nd.l i : ℝ)) (n := (TwistedPlaces.nLam D w : ℝ))
    (r := (D.R.r : ℝ)) (m := (D.R.m : ℝ)) hl (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hh hb.w_le hb.η_le hb.S_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hlg (TwistedPlaces.L_ge_one L) hband (by split_ifs <;> norm_num) he
    (by unfold coreE; have := Real.logb_nonneg (by linarith : (1:ℝ) < D.nd.l i) hB1
        have : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) := div_nonneg (by linarith) (by linarith)
        linarith)
  obtain ⟨mm, k, e1, e2, e3⟩ := hX
  refine ⟨mm, k, e1, e2, e3.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))⟩
  have hnlR : ((Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast hnl
  have hrkR : ((Module.finrank ↥Cx.LL.1 T₂.V : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  have hmR : ((Wd.m : ℕ) : ℝ) = (D.R.m : ℝ) := by exact_mod_cast hb.m_eq
  rw [hnlR, hrkR, hmR]
  simp only [bdCD, coreH, coreF, coreM, flat, rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃]
  refine le_trans key (le_of_eq ?_)
  norm_num

end GlobalTheory.NLink.RowNT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterLabel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.PendOf.tame_lab_mu : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ChiTOk D P.cf → ∀ S : Reading P.T, IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu ∧ ∃ (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧ labAt hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) := by
  intro hP hDZ hL D P hchi S hS i k v hw
  obtain ⟨u, hu0, hunit, hrep⟩ := GlobalTheory.T.exists_globalInteger_congr_tameGenerator_character D k v
  have hrep' : NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u := by
    obtain ⟨ϖ, π, h1, h2, h3, h4⟩ := hrep
    exact ⟨D.nd.plOm.1 (D.naut.plGw k v), D.nd.plOm.2 (D.naut.plGw k v), D.ntypes.tg_mem k v, ϖ, π, h1, h2, h3,
      by rw [zpow_one]; exact h4⟩
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  obtain ⟨c, hc, hcv⟩ := hchi k v j u hu0 hrep'
  have htame := GlobalTheory.T.split_character_tame hL D P S hS i k v hw
  refine ⟨htame, (S i _ hw).mu_ok.1, c, hc, GlobalTheory.T.tame_uniformizer_power hDZ hL D P.ty.grp k v _ _ htame u hu0 hrep c ?_⟩
  rw [GlobalTheory.T.split_character_unit_value hL D P S hS i k v hw j (by simp only [j]; omega) u hu0 hunit]
  exact hcv.symm
end


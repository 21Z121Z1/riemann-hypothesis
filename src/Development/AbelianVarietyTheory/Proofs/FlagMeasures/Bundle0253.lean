import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitalIntegralEqInvDegSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Formalism.FormalDegreeBessel.Bundle0002
import Formalism.PeriodIntegrals.Bundle0022
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsDiscrEqSqOfUnramifiedCmExtensionStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_discr_eq_sq_of_unramified_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
  first | exact @GlobalTheory.SnMass.VolN.abs_discr_eq_abs_discr_sq_of_unramified | exact GlobalTheory.SnMass.VolN.abs_discr_eq_abs_discr_sq_of_unramified | (intros; apply GlobalTheory.SnMass.VolN.abs_discr_eq_abs_discr_sq_of_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsNormInverseDifferentIdealPowEqDiscrStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr : ∀ (K : Type) [Field K] [NumberField K] (j : ℕ), (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  first | exact @GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv | exact GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv | (intros; apply GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AddFundamentalDomainMeasureEqOfCountableStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addFundamentalDomain_measure_eq_of_countable : ∀ {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (L : Submodule ℤ V) [Countable L] (D D' : Set V), MeasurableSet D → MeasurableSet D' → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D') → μ D = μ D' := by
  first | exact @GlobalTheory.addFundamentalDomains_measure_eq | exact GlobalTheory.addFundamentalDomains_measure_eq | (intros; apply GlobalTheory.addFundamentalDomains_measure_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIndependentOfQuotientMeasureStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselAmplitude_eq_smul_of_rescaled_stabilizerHaar : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (cN : ℝ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → (∀ n ∈ Nset k r, ‖ψ n‖ = 1 ∧ ‖ψ' n‖ = 1) → IsSPsiEquiv z ψ π Φ → IsSPsiEquiv z' ψ' π' Φ' → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → ∀ (γ : Mat k r) (μG μR ν ν' : Measure (Mt k r)) (t : ℝ), γ ∈ GG k r → (∀ ρ ∈ Rset k r γ, ψ (γ * ρ * γ⁻¹) = ψ' ρ) → IsHaarOn (GG k r) μG → IsHaarOn (Rset k r γ) μR → 0 < t → IsQuotMeas μG μR ν → IsQuotMeas μG (ENNReal.ofReal t • μR) ν' → ampJ ν cN Φ Φ' γ = (t : ℂ) • ampJ ν' cN Φ Φ' γ := by
  first | exact @GlobalTheory.SnMass.AmpUniq.amp_uniq | exact GlobalTheory.SnMass.AmpUniq.amp_uniq | (intros; apply GlobalTheory.SnMass.AmpUniq.amp_uniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalEquivariantUnipotentCharacter
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem Afun_isSPsiEquiv : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu v hv ξ
  intro h hh m hm g hg
  have hRep : IsURepOn (GG k r) σ := hStd.2.1
  have hDec : Decay σ (DD σ w) a := hStd.2.2.2.2.2.2.2.1
  have hz : inWb k r z := hSide.1
  have hT : 0 < Tz k r z := hSide.2.1
  have hπ : IsURepOn (UWset k r z) π := hSide.2.2.1
  have hCl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have hSsub : Sset k r z ⊆ GG k r := hCl.2.2.2.1.1
  have hhm : h * m ∈ Sset k r z := ⟨h, hh, m, hm, rfl⟩
  have hstab := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hRep).1
  have hgu : σ g u ∈ DD σ w := hstab g hg u hu
  have hmul : σ (h * m * g) = (σ (h * m)).comp (σ g) := hRep.1.2 _ (hSsub hhm) _ hg
  have hD1 := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H)
    (fun g hg v hv => hstab g hg v hv) hDec (σ g u) hgu v hv).2.1 (h * m) hhm
  have hPi := ((GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ).1 h hh m hm).2
  unfold Afun
  rw [hmul, ContinuousLinearMap.comp_apply, hD1.1, hPi]
  rfl

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalStandardSideStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_functional_standard_side : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g))) ν ∧ rconv μG (eFun μG σ w) W y = (d : ℂ) • ∫ g, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) ∂ν := by
  first | exact @GlobalTheory.SgInf.KernelRe.kernel_rconv | exact GlobalTheory.SgInf.KernelRe.kernel_rconv | (intros; apply GlobalTheory.SgInf.KernelRe.kernel_rconv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapPairingBound
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DatumOfPeriods

section

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma dsigW_eq (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ w v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v)
    rw [ih]; rfl

lemma isBesselMapSm_smul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {l : H → Wp}
    (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π l) (a : ℂ) :
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun v => a • l v) := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun g hg m hm v hv => ?_, ‖a‖ * C, Ws, h4, fun v hv => ?_⟩
  · simp only [h1 v hv w hw, smul_add]
  · simp only [h2 c v hv]; rw [smul_comm]
  · simp only [h3 g hg m hm v hv, map_smul]; rw [smul_comm]
  · simp only [dsigW_eq, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h5 v hv) (norm_nonneg _)

lemma l2SG_sqrt_smul_eq_ofReal_mul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (n : ℕ) (c : ℝ)
    (h : l2SG ν F = ENNReal.ofReal c) :
    l2SG ν (fun g => ((Real.sqrt n : ℝ) : ℂ) • F g) = ENNReal.ofReal (c * n) := by
  have e : ∀ y : Wp, ((‖((Real.sqrt n : ℝ) : ℂ) • y‖₊ : ℝ≥0∞)) ^ 2 = (n : ℝ≥0∞) * (‖y‖₊ : ℝ≥0∞) ^ 2 := by
    intro y
    have : ‖((Real.sqrt n : ℝ) : ℂ)‖₊ ^ 2 = (n : NNReal) := by
      apply NNReal.eq
      simp [Real.sq_sqrt, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [nnnorm_smul, ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, this, ENNReal.coe_natCast]
  unfold l2SG at h ⊢
  simp only [e]
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n), h, mul_comm c, ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ENNReal.ofReal_natCast]

end

theorem exists_goodS : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDS (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  intro hH D τ w w' θ W lam R _ l l' dd _ _ hR hl hl' hdd hn hn'
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨P, hP, hD⟩ := hR.2
  have hD' : Formalism.MainNotions.S.IsDS (epsSH D.R) lam (fun g => R.σ (P⁻¹ * g * P)) := hD
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ hD' _ (D.s.cdScale_pos _ (epsSH D.R))
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hD'
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hvs : v ∈ R.sm :=
    ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK _ _ _ lam R hR P hP S hS.1 hS.2.1).1 v hvS).2
  refine ⟨{ H := R.H, σ := R.σ, B := fun x => ((Real.sqrt (Module.finrank ℂ W.Wp : ℕ) : ℝ) : ℂ) • l x,
            B' := fun x => ((Real.sqrt (Module.finrank ℂ W.Wq : ℕ) : ℝ) : ℂ) • l' x,
            v0 := v, cN := ‖v‖ ^ 2 / dd, deg := d },
    hR.1, hR.2, isBesselMapSm_smul hl _, isBesselMapSm_smul hl' _, hvs, hv0, ⟨P, hP, ?_⟩,
    div_pos (pow_pos (norm_pos_iff.2 hv0) 2) hdd, l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn v hvs),
    l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn' v hvs), P, hP.1, hd⟩
  exact (le_sSup (s := {S | IsKTypeOf (epsSH D.R) (fun g => R.σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (epsSH D.R) lam) S}) hS) hvS

end GlobalTheory.DatumOfPeriods
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitalIntegralEqInvDegSmulStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselOrbitalIntegral_eq_inv_deg_smul : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∀ γ ∈ Greg k r z z', Integrable (fun p : Mt k r × Mt k r => coef σ w₀' w₀ (Matrix.of (act2 γ p)) • rk1 (PiS (psiGen k r z c) π (Matrix.of p.1)⁻¹ ξ) (PiS (psiGen k r z' c') π' (Matrix.of p.2)⁻¹ ξ')) (μS.prod μS') ∧ Integrable (fun x : Mt k r => rk1 ((Afun (psiGen k r z c) π μS σ w w₀ ξ) (Matrix.of x)) ((Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') (γ⁻¹ * Matrix.of x))) μG ∧ OO μG (Afun (psiGen k r z c) π μS σ w w₀ ξ) (Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') γ = (d : ℂ)⁻¹ • Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ w₀' w₀ ξ ξ' γ := by
  first | exact @GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint | exact GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint | (intros; apply GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupIntegralEqInnerBesselForm
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.SInt

theorem sint_eq_inner_be : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∫ t, ⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS = ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ
  have hURep : IsURepOn (GG k r) σ := hStd.2.1
  have hDecay : Decay σ (DD σ w : Set H) a := hStd.2.2.2.2.2.2.2.1
  obtain ⟨hz, hT, hπ, hHaar, -⟩ := id hSide
  have hstab : ∀ g ∈ GG k r, ∀ u ∈ (DD σ w : Set H), σ g u ∈ (DD σ w : Set H) :=
    (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hURep).1
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hstab hDecay v hv v hv).1
  let f : Mt k r → (Wp →L[ℂ] Wp) := fun s =>
    coef σ v v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hL : ∀ A, L A = ⟪ξ, A ξ⟫_ℂ := fun A => rfl
  have hRHS : ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ = ∫ s, L (f s) ∂μS := by
    rw [← hL]; exact (L.integral_comp_comm hint).symm
  have hunim : μS.map invM = μS := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hHaar).2
  have hmeas : AEStronglyMeasurable (fun s => L (f s)) μS :=
    L.continuous.comp_aestronglyMeasurable hint.aestronglyMeasurable
  have hsub : ∀ᵐ t ∂μS, Matrix.of t ∈ Sset k r z := ae_iff.2 hHaar.2.2.1
  have hchange : ∫ s, L (f s) ∂μS = ∫ t, L (f (invM t)) ∂μS := by
    conv_lhs => rw [← hunim]
    exact integral_map measurable_invM.aemeasurable (by rw [hunim]; exact hmeas)
  rw [hRHS, hchange]
  refine integral_congr_ae ?_
  filter_upwards [hsub] with t ht
  have hGG : Matrix.of t ∈ GG k r := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT).2.2.2.1.1 ht
  have hu : IsUnit (Matrix.of t : Mat k r).det :=
    ((uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.2 _ hGG).1
  have hadj := ((GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ).2.2.1 _ ht).2
  simp only [hL, f, coef, of_invM, Matrix.nonsing_inv_nonsing_inv _ hu,
    ContinuousLinearMap.smul_apply, inner_smul_right]
  rw [← hadj, ContinuousLinearMap.adjoint_inner_left]

end GlobalTheory.SgInf.SInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliDiscreteSeriesInfChar
section
namespace GlobalTheory

theorem capelliDiscreteSeriesInfChar : PI.DSInfCharCap.DSInfCharCap :=
  CompanionTheory.D.DSIC.discrete_series_infinitesimal_character

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliTransportUnitaryConj
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

private theorem list_prod_ofFn_sum_eq_sum_prod {A : Type*} [Semiring A] {ι : Type*} [Fintype ι] :
    ∀ {t : ℕ} (f : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, f k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_sum_eq_sum_prod (fun k => f k.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    simp [Fin.consEquiv, List.ofFn_succ]

private theorem list_prod_ofFn_smul_eq_prod_smul {A : Type*} [Semiring A] [Algebra ℂ A] :
    ∀ {t : ℕ} (r : Fin t → ℂ) (x : Fin t → A),
      (List.ofFn fun k => r k • x k).prod = (∏ k, r k) • (List.ofFn x).prod
  | 0, r, x => by simp
  | t + 1, r, x => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_smul_eq_prod_smul (fun k => r k.succ) (fun k => x k.succ),
      smul_mul_smul_comm, Fin.prod_univ_succ, List.ofFn_succ (f := x), List.prod_cons]

private theorem Tm_conj_eq_sum_conj_Tm {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (v : ℂ) (a b : Fin n) :
    Formalism.REAL.Tm (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) v a b =
      ∑ c, ∑ d, (P c a * Q b d) • Formalism.REAL.Tm E v c d := by
  have h1 : ∑ c, P c a * Q b c = if a = b then 1 else 0 := by
    have := congrFun (congrFun hQP b) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show (∑ c, P c a * Q b c) = ∑ c, Q b c * P c a from
      Finset.sum_congr rfl fun c _ => mul_comm _ _, this]
    by_cases h : a = b <;> simp [h, eq_comm]
  simp only [Formalism.REAL.Tm, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  congr 1
  rw [← Finset.sum_smul, h1]
  by_cases h : a = b <;> simp [h]

private theorem sum_sign_mul_prod_eq_zero_of_not_bijective {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → Fin n)
    (hr : ¬ Function.Bijective r) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (r k) (σ k) = 0 := by
  have := Matrix.det_mul_aux (M := Pᵀ) (N := Matrix.of fun _ _ => (1 : ℂ)) hr
  simpa [Matrix.transpose_apply] using this

private theorem sum_sign_mul_prod_perm_eq_sign_mul_det {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (τ : Equiv.Perm (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (τ k) (σ k) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * Matrix.det P := by
  rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulRight τ)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, Equiv.Perm.coe_mul,
    Function.comp_apply, Matrix.transpose_apply]
  rw [show (∏ k, P (τ k) (ρ (τ k))) = ∏ j, P j (ρ j) from Equiv.prod_comp τ (fun j => P j (ρ j))]
  ring

private theorem sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective {M : Type*} [AddCommMonoid M] {n : ℕ} (g : (Fin n → Fin n) → M)
    (h : ∀ r, ¬ Function.Bijective r → g r = 0) :
    ∑ r, g r = ∑ τ : Equiv.Perm (Fin n), g τ := by
  let e : Equiv.Perm (Fin n) ↪ (Fin n → Fin n) := ⟨fun τ => τ, DFunLike.coe_injective⟩
  rw [show (∑ τ : Equiv.Perm (Fin n), g τ) = ∑ r ∈ Finset.univ.map e, g r from
    (Finset.sum_map Finset.univ e g).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  apply h r
  intro hb
  exact hr (Finset.mem_map.2 ⟨Equiv.ofBijective r hb, Finset.mem_univ _, rfl⟩)

private theorem qminor_eq_zero_of_not_bijective {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (u : ℂ) (s : Fin n → Fin n) (hs : ¬ Function.Bijective s) :
    Formalism.REAL.qminor E id s u = 0 := by
  have hni : ¬ Function.Injective s := fun hi => hs (Finite.injective_iff_bijective.mp hi)
  obtain ⟨p, q, hsq, hpq⟩ : ∃ p q, s p = s q ∧ p ≠ q := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨p, q, h1, h2⟩ := hni
    exact ⟨p, q, h1, h2⟩
  have hsw : s ∘ Equiv.swap p q = s := by
    funext i
    simp only [Function.comp_apply]
    rcases eq_or_ne i p with rfl | hip
    · simp [hsq]
    rcases eq_or_ne i q with rfl | hiq
    · simp [hsq]
    · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]
  have h := Formalism.REAL.qSkewCol A n n E hE id s (Equiv.swap p q) u
  rw [hsw, Equiv.Perm.sign_swap hpq] at h
  set x := Formalism.REAL.qminor E id s u
  have h2 : x + x = 0 := by
    nth_rewrite 2 [h]
    simp
  calc x = (1 / 2 : ℂ) • (x + x) := by rw [← two_smul ℂ x, smul_smul]; norm_num
    _ = 0 := by rw [h2, smul_zero]

private theorem qdet_conj_eq_qdet_of_mul_eq_one {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (u : ℂ) :
    Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u = Formalism.REAL.qdet E u := by
  classical
  have hsg : ∀ (z : ℤ) (x : A), (z : A) * x = (z : ℂ) • x := fun z x => by
    rw [Algebra.smul_def, map_intCast]
  have ha : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d)
        (u - (k : ℂ)) (id (σ k)) (id k)).prod =
        ∑ r : Fin n → Fin n, ∑ s : Fin n → Fin n, (∏ k, (P (r k) (σ k) * Q k (s k))) •
          (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod := by
    intro σ
    simp only [id, Tm_conj_eq_sum_conj_Tm E P Q hQP]
    rw [list_prod_ofFn_sum_eq_sum_prod (fun k c => ∑ d, (P c (σ k) * Q k d) • Formalism.REAL.Tm E (u - (k : ℂ)) c d)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [list_prod_ofFn_sum_eq_sum_prod (fun k d => (P (r k) (σ k) * Q k d) • Formalism.REAL.Tm E (u - (k : ℂ)) (r k) d)]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact list_prod_ofFn_smul_eq_prod_smul (fun k => P (r k) (σ k) * Q k (s k))
      (fun k => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k))
  have hq : ∀ s : Fin n → Fin n, Formalism.REAL.qminor E id s u =
      ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) •
        (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (τ k) (s k)).prod := by
    intro s
    unfold Formalism.REAL.qminor
    exact Finset.sum_congr rfl fun τ _ => hsg _ _
  have hs : ∀ s : Fin n → Fin n,
      ∑ r : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, (P (r k) (σ k) * Q k (s k))) •
          (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod =
        (∏ k, Q k (s k)) • (Matrix.det P • Formalism.REAL.qminor E id s u) := by
    intro s
    have hD : ∀ r : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, (P (r k) (σ k) * Q k (s k))) =
          (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (r k) (σ k)) *
            ∏ k, Q k (s k) := by
      intro r
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => by rw [Finset.prod_mul_distrib, mul_assoc]
    simp_rw [hD]
    rw [sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective _ (fun r hr => by rw [sum_sign_mul_prod_eq_zero_of_not_bijective P r hr, zero_mul, zero_smul])]
    simp_rw [sum_sign_mul_prod_perm_eq_sign_mul_det P]
    rw [hq s, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hL : Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u =
      ∑ s : Fin n → Fin n, (∏ k, Q k (s k)) • (Matrix.det P • Formalism.REAL.qminor E id s u) := by
    have step : Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u =
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) *
          ∑ r : Fin n → Fin n, ∑ s : Fin n → Fin n, (∏ k, (P (r k) (σ k) * Q k (s k))) •
            (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod := by
      unfold Formalism.REAL.qdet Formalism.REAL.qminor
      exact Finset.sum_congr rfl fun σ _ => by rw [ha σ]
    rw [step]
    simp_rw [← hs]
    simp only [Finset.sum_smul, Finset.mul_sum, Finset.smul_sum, hsg, smul_smul]
    first
      | exact Finset.sum_comm
      | exact Eq.trans Finset.sum_comm (Finset.sum_congr rfl fun r _ => Finset.sum_comm)
      | exact Eq.trans Finset.sum_comm (Eq.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm) Finset.sum_comm)
  have hperm : ∀ τ : Equiv.Perm (Fin n),
      Formalism.REAL.qminor E id τ u = ((Equiv.Perm.sign τ : ℤ) : ℂ) • Formalism.REAL.qdet E u := by
    intro τ
    have h := Formalism.REAL.qSkewCol A n n E hE id id τ u
    rw [hsg] at h
    exact h
  have hdetQ : ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, Q k (τ k) =
      Matrix.det Q := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  have hscal : ∑ τ : Equiv.Perm (Fin n), (∏ k, Q k (τ k)) *
      (Matrix.det P * ((Equiv.Perm.sign τ : ℤ) : ℂ)) = 1 := by
    rw [show (1 : ℂ) = Matrix.det P * Matrix.det Q by rw [← Matrix.det_mul, hPQ, Matrix.det_one],
      ← hdetQ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hL, sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective _ (fun s hs => by rw [qminor_eq_zero_of_not_bijective E hE u s hs, smul_zero, smul_zero])]
  simp_rw [hperm, smul_smul]
  rw [← Finset.sum_smul, hscal, one_smul]

theorem capelli_transport_conj : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  intro n ε E _ _ H P Q F u g hQP hPQ hH hF hg
  have hx : Formalism.REAL.inUJ ε (P * g * Q) := Formalism.QuantumDeterminants.ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x₀, hx₀⟩ := Formalism.QuantumDeterminants.io_rep_mk hF
  have hA := Formalism.QuantumDeterminants.ioh_qminor_rep (Formalism.QuantumDeterminants.ioh_repr (ε := ε) (E := E) P Q) id id u hx₀
  have hB := Formalism.QuantumDeterminants.io_qminor_rep (ε := ε) id id u hx₀
  have hkey : Formalism.REAL.qminor (Formalism.QuantumDeterminants.iohE ε E P Q) id id u =
      Formalism.REAL.qminor (Formalism.QuantumDeterminants.ioE ε E) id id u :=
    qdet_conj_eq_qdet_of_mul_eq_one (Formalism.QuantumDeterminants.ioE ε E) (Formalism.QuantumDeterminants.io_gl ε E) P Q hQP hPQ u
  have h1 := Formalism.QuantumDeterminants.ioh_qminor ε H P Q hQP hPQ hH (id : Fin n → Fin n) id u F g
  show Formalism.QuantumDeterminants.qminorOp (Formalism.QuantumDeterminants.EabH H) id id u F g =
    Formalism.QuantumDeterminants.qminorOp (Formalism.REAL.EabV ε) id id u (fun x => F (Q * x * P)) (P * g * Q)
  rw [h1, hA _ hx, hB _ hx, hkey]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmExtensionConjMemInverseDifferentIdealPowStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) (x : E), x ∈ dInv E j → σ x ∈ dInv E j := by
  first | exact @GlobalTheory.SnMass.VolN.conj_mem_dInv | exact GlobalTheory.SnMass.VolN.conj_mem_dInv | (intros; apply GlobalTheory.SnMass.VolN.conj_mem_dInv <;> assumption)
end


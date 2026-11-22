import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0270
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0253
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationRankOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsGoodSplitPrimeCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalData
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpSides

open Filter Topology GlobalTheory.CWDeriv

variable {k r : ℕ}

theorem cwCont_of {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    {σ : Mat k r → (H →L[ℂ] H)} {Bm : H → Wp} (h : IsCWCont (k := k) (r := r) σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ Bm := by
  have e : ∀ (w : List (Mat k r)) (v : H),
      dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
    intro w v
    induction w with
    | nil => rfl
    | cons X w ih => show dsig σ X _ = PI.UpqRep.dsig σ X _; rw [ih]; rfl
  unfold IsCWCont at h
  simp only [e] at h
  exact h

theorem continuousOn_orbit {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (R : BranchingSupport.Rep k r)
    (hR : R.IsDS ε mu) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V)
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v)
    (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm) {v : R.H} (hv : v ∈ R.sm) :
    ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) := by
  have hD : DerFacts R := fun X hX =>
    ⟨fun _ hv => ⟨DerivedAction.dsig_smooth hR.2 hX hv, DerivedAction.hasDerivAt_dsig hX hv⟩,
      fun _ hv _ hw => DerivedAction.dsig_skew hR.2 hX hv hw⟩
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hB0 : Bm 0 = 0 := by simpa using hs 0 0 h0
  intro g hg
  have h1 := cw_tendsto hB (l := 𝓝[GG k r] g) (u := fun x => (1 : ℂ) • (R.σ x v - R.σ g v) - 0)
    (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact sm_comb 1 (hsm x hx) (hsm g hg) h0)
    (by
      intro W hW
      have h2 : Tendsto _ (𝓝[GG k r] g) _ :=
        (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW) g hg).tendsto
      have hW0 : PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0 = 0 := by
        have h := dsigW_comb hD W hW 0 h0 h0 h0
        simp only [zero_smul, zero_sub, neg_zero] at h
        rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h
        simpa using h
      rw [← tendsto_sub_nhds_zero_iff] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [dsigW_comb hD W hW 1 (hsm x hx) (hsm g hg) h0, hW0, one_smul, sub_zero])
  refine tendsto_sub_nhds_zero_iff.mp (h1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [lin_comb ha hs 1 (hsm x hx) (hsm g hg) h0, hB0, one_smul, sub_zero]

theorem isHaarOn_smul {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) {x : ℝ} (hx : 0 < x) :
    IsHaarOn S (ENNReal.ofReal x • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun h0 => h2 ?_, by rw [Measure.smul_apply, h3, smul_zero], fun s hs => by
    rw [Measure.map_smul, h4 s hs]⟩
  · exact inferInstanceAs (SigmaFinite (x.toNNReal • μ))
  · have h1 := Measure.measure_univ_eq_zero.2 h0
    rw [Measure.smul_apply, smul_eq_mul] at h1
    exact Measure.measure_univ_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (ENNReal.ofReal_pos.2 hx).ne')

theorem haarLie_eq (x : ℝ) :
    haarLie (Nset k r) (ENNReal.ofReal x) =
      ENNReal.ofReal (x * 2 ^ (r * (k + 1) + r * (r - 1))) • lebN k r := by
  have h := GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue k r
  unfold haarLie at h ⊢
  rw [one_smul] at h
  rw [h, smul_smul, mul_comm x, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
    mul_comm (ENNReal.ofReal x)]
  simp

theorem oneSide_of {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Wp →L[ℂ] Wp)} {c : ℂ}
    {μG μW νS : Measure (Mt k r)} {Bm : H → Wp} {v₀ : H} {cN x : ℝ} (hx : 0 < x)
    (hlam : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) (hG : IsHaarOn (GG k r) μG) (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) (ENNReal.ofReal x))) νS)
    (hB : IsBesselMapSm z (psi k r z c) σ π Bm) (hv : v₀ ∈ smoothVecs (k := k) (r := r) σ) (hc : 0 < cN)
    (hl : l2SG νS (fun g => Bm (σ g v₀)) = ENNReal.ofReal (cN * Module.finrank ℂ Wp)) :
    OneSide z π (psi k r z c) μG μW (ENNReal.ofReal (x * 2 ^ (r * (k + 1) + r * (r - 1))) • lebN k r) νS
      (fun g => Bm (σ g v₀)) cN := by
  let R : BranchingSupport.Rep k r := ⟨H, σ⟩
  have hR : R.IsDS ε lam := ⟨hlam, hσ⟩
  obtain ⟨e1, e2, e3⟩ := (GlobalTheory.Amp.Schur.type_irred_and_avg k r z π hz hT).1 u hπ
  rw [haarLie_eq] at hq
  refine ⟨hz, hT, e1, e2, e3, hG, hW, hW1, isHaarOn_smul (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r) (by positivity), hq,
    fun n _ => by unfold psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _, fun a ha m hm g hg => ?_,
    continuousOn_orbit R hR Bm hB.1 hB.2.1 (cwCont_of hB.2.2.2) hv, hc, hl⟩
  have ham : a * m ∈ GG k r := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r a ha.1).2.2 m hm.1
  have h1 := PI.UnitaryGroupMassFormula.CapelliEig.Hecke_multiplication k r ε lam H σ hσ _ ham g hg
  have h2 := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ v₀ hv g hg
  show Bm (σ (a * m * g) v₀) = _
  rw [h1]
  exact hB.2.2.1 a ha m hm _ h2

theorem oneSide_of_good : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → OneSide W.z W.π (psiS D W.z) W.μG W.μW (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS' A.Φ' A.cN := by
  intro D τ w w' θ W lam A hv hθ hT hT' hW hA
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩ := hW
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10, -⟩ := hA
  rw [w12] at w13 w14
  have hx : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := by positivity
  exact ⟨oneSide_of hx a1 a2 w3 (w5 ▸ hT) w1 w7 w8 w9 w13 a3 a5 a8 a9,
    oneSide_of hx a1 a2 w4 (w6 ▸ hT') w2 w7 w10 w11 w14 a4 a5 a8 a10⟩

end GlobalTheory.AmpSides
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelProjectorOnLine
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.ProjLine

theorem mul_mem_GG_iff {k r : ℕ} {s x : Mat k r} (hs : s ∈ GG k r) : s * x ∈ GG k r ↔ x ∈ GG k r := by
  simp only [GG, UH, Set.mem_setOf_eq] at hs ⊢
  have e : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * (sᴴ * Hpk k r * s) * x := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hs]

theorem Sset_subset_GG {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) : Sset k r z ⊆ GG k r := by
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact (mul_mem_GG_iff hh.1).2 hm.1

theorem isClosed_GG (k r : ℕ) : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} := by
  have hc : Continuous fun x : Mat k r => xᴴ * Hpk k r * x :=
    ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq (X := Mt k r) hc continuous_const

theorem rankOneInnerOperator_self_apply {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (x y : Wp) :
    rk1 y x x = ((‖x‖ ^ 2 : ℝ) : ℂ) • y := by
  rw [rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]; push_cast; rfl

theorem inner_rankOneInnerOperator_self {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (x : Wp) :
    ⟪x, rk1 x x x⟫_ℂ = (((‖x‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [rankOneInnerOperator_self_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have e : ((‖x‖ : ℝ) : ℂ) = (RCLike.ofReal ‖x‖ : ℂ) := rfl
  push_cast
  rw [← e]; ring

theorem ae_mem_GG {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μG μS ν : Measure (Mt k r)}
    (hG : IsHaarOn (GG k r) μG) (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS ν) :
    ∀ᵐ x ∂ν, (Matrix.of x : Mat k r) ∈ GG k r := by
  set B : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∉ GG k r} with hBdef
  have hB : MeasurableSet B := (isClosed_GG k r).measurableSet.compl
  have h0 := hq (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hG.2.2.1] at h0
  have hc : μS Set.univ ≠ 0 := by
    intro h; exact hS.2.1 (Measure.measure_univ_eq_zero.1 h)
  have hle : ∀ x, B.indicator (fun _ => μS Set.univ) x ≤
      ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      calc μS Set.univ = ∫⁻ _, 1 ∂μS := (lintegral_one).symm
        _ ≤ _ := by
          apply lintegral_mono_ae
          have hnull : ∀ᵐ s ∂μS, (Matrix.of s : Mat k r) ∈ Sset k r z := by
            rw [ae_iff]; simpa using hS.2.2.1
          filter_upwards [hnull] with s hs
          have hmem : (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∈ B := by
            show ¬ ((Matrix.of s * Matrix.of x : Mat k r) ∈ GG k r)
            intro h; exact hx ((mul_mem_GG_iff (Sset_subset_GG z hs)).1 h)
          rw [Set.indicator_of_mem hmem]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have hmul : μS Set.univ * ν B = 0 := by
    rw [← lintegral_indicator_const hB]
    exact le_antisymm ((lintegral_mono hle).trans h0.symm.le) (zero_le)
  have hνB : ν B = 0 := (mul_eq_zero.1 hmul).resolve_left hc
  rw [ae_iff]; simpa [hBdef] using hνB

theorem projector_line : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l → (∀ u ∈ DD σ w, l2SG ν (fun x => l (σ x u)) = ENNReal.ofReal (‖u‖ ^ 2 / d)) ∧ (∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x ∈ GG k r, Afun (psiGen k r z c) π μS σ w v ξ x = ⟪l v, ξ⟫_ℂ • l (σ x w)) ∧ ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, rconv μG (eFun μG σ w) W y = ((d : ℂ) * ∫ g, ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ ∂ν) • l (σ y w) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hq l hl
  have hG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hU : IsURepOn (GG k r) σ := hStd.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  have hS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hae := ae_mem_GG hG hS hq
  have hstab := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU).1
  obtain ⟨_, ⟨v0, hv0, hlv0⟩, hbe⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨_, _, hmem, heq, _, _⟩ :=
      GlobalTheory.T.norm_identity_besselCoefficient_quotient k r σ w a μG d z c π μS hStd hSide ν hq u hu u hu v0 hv0 (l v0)
    set A : Mt k r → Wp := fun x => Afun (psiGen k r z c) π μS σ u v0 (l v0) (Matrix.of x) with hAdef
    set L : Mt k r → Wp := fun x => l (σ (Matrix.of x) u) with hLdef
    set N : ℝ := ‖l v0‖ ^ 2 with hNdef
    have hN : 0 < N := by positivity
    have hAL : ∀ᵐ x ∂ν, A x = (N : ℂ) • L x := by
      filter_upwards [hae] with x hx
      simp only [hAdef, hLdef, Afun]
      rw [hbe _ (hstab _ hx _ hu) _ hv0, rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]
      simp [hNdef]
    have hnA : ∀ᵐ x ∂ν, ‖A x‖ ^ 2 = N ^ 2 * ‖L x‖ ^ 2 := by
      filter_upwards [hAL] with x hx
      rw [hx, norm_smul, Complex.norm_real, Real.norm_of_nonneg hN.le, mul_pow]
    have hIA : Integrable (fun x => ‖A x‖ ^ 2) ν := hmem.integrable_norm_pow two_ne_zero
    have hIL : Integrable (fun x => ‖L x‖ ^ 2) ν := by
      have : (fun x => ‖L x‖ ^ 2) =ᵐ[ν] fun x => (N ^ 2)⁻¹ * ‖A x‖ ^ 2 := by
        filter_upwards [hnA] with x hx
        rw [hx, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
      exact (hIA.const_mul _).congr this.symm
    have hbevv : ⟪l v0, be (psiGen k r z c) π μS σ v0 v0 (l v0)⟫_ℂ = ((N ^ 2 : ℝ) : ℂ) := by
      rw [hbe _ hv0 _ hv0, inner_rankOneInnerOperator_self]
    have hintA : ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * (‖u‖ ^ 2 / d) := by
      have h1 : ∫ x, ⟪A x, A x⟫_ℂ ∂ν = ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [inner_self_eq_norm_sq_to_K]; push_cast; rfl
      have h2 := heq
      rw [hbevv, inner_self_eq_norm_sq_to_K u] at h2
      have h3 : ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((N ^ 2 * (‖u‖ ^ 2 / d) : ℝ) : ℂ) := by
        rw [← h1]; refine h2.trans ?_
        have e : ((‖u‖ : ℝ) : ℂ) = (RCLike.ofReal ‖u‖ : ℂ) := rfl
        push_cast
        rw [← e]; ring
      exact_mod_cast h3
    have hintL : ∫ x, ‖L x‖ ^ 2 ∂ν = ‖u‖ ^ 2 / d := by
      have : ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * ∫ x, ‖L x‖ ^ 2 ∂ν := by
        rw [← integral_const_mul]; exact integral_congr_ae hnA
      rw [this] at hintA
      exact mul_left_cancel₀ (by positivity) hintA
    unfold l2SG
    rw [← hintL, ofReal_integral_eq_lintegral_ofReal hIL (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  · intro v hv ξ x hx
    simp only [Afun]
    rw [hbe _ (mem_DD σ w hx) _ hv, rankOneInnerOperator_apply]
  · intro W hW1 hW2 hEq hL2 y hy
    obtain ⟨_, hconv⟩ := GlobalTheory.T.bessel_functional_standard_side k r σ w a μG d z c π μS hStd hSide ν hq W hW1 hW2 hEq hL2 y hy
    rw [hconv]
    have h : ∀ᵐ g ∂ν, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) =
        ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ • l (σ y w) := by
      filter_upwards [hae] with g hg
      rw [hbe _ (mem_DD σ w hy) _ (mem_DD σ w hg), rankOneInnerOperator_apply]
    rw [integral_congr_ae h, integral_smul_const, smul_smul]

end GlobalTheory.SgInf.ProjLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupportStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_data_support : Hyps → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  first | exact @GlobalTheory.CellOrbInt.orbInt_integrable | exact GlobalTheory.CellOrbInt.orbInt_integrable | (intros; apply GlobalTheory.CellOrbInt.orbInt_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationRankOneStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classification_rank_one : (∀ ε : Fin 1 → Bool, ClassS ε) ∧ ClassU 0 := by
  first | exact @GlobalTheory.DSSU.Triv.classS_one_classU_zero | exact GlobalTheory.DSSU.Triv.classS_one_classU_zero | (intros; apply GlobalTheory.DSSU.Triv.classS_one_classU_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOneAvoiding
section
open NumberField Polynomial

namespace GlobalTheory.LargeSplitPrime

theorem exists_degree_one_avoiding (N : Type) [Field N] [NumberField N] (m : ℤ) (hm : m ≠ 0) :
    ∃ P : Ideal (𝓞 N), P.IsMaximal ∧ (m : 𝓞 N) ∉ P ∧ Function.Surjective (Int.castRingHom (𝓞 N ⧸ P)) := by
  obtain ⟨θ, d, hd, -, hden⟩ := GlobalTheory.SW.SplitPrime.exists_prim_den N
  by_cases hθ : θ = 0
  · refine GlobalTheory.SW.SplitPrime.exists_degree_one (1 : 𝓞 N) one_ne_zero d hd (fun a => ?_) m hm
    obtain ⟨g, hg⟩ := hden a
    refine ⟨C (g.coeff 0), ?_⟩
    rw [hg, hθ, aeval_C, aeval_def, eval₂_at_zero]
  · exact GlobalTheory.SW.SplitPrime.exists_degree_one θ hθ d hd hden m hm

theorem surjective_of_conj {N : Type} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ} (hp : p.Prime)
    (P Q : Ideal (𝓞 N)) [hP : P.IsMaximal] [hQ : Q.IsMaximal] (h1 : (p : 𝓞 N) ∈ P) (h2 : (p : 𝓞 N) ∈ Q)
    (hs : Function.Surjective (Int.castRingHom (𝓞 N ⧸ P))) :
    Function.Surjective (Int.castRingHom (𝓞 N ⧸ Q)) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hp').mpr (by simpa using h1)
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hQ.ne_top hp').mpr (by simpa using h2)
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (N ≃ₐ[ℚ] N)
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, ht⟩ := hs (Ideal.Quotient.mk P (σ⁻¹ • a))
  have h3 : (t : 𝓞 N) - σ⁻¹ • a ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ht]; simp
  have h4 : σ • ((t : 𝓞 N) - σ⁻¹ • a) ∈ Q := hσ ▸ Ideal.smul_mem_pointwise_smul σ _ _ h3
  have h5 : σ • (t : 𝓞 N) = t := map_intCast (MulSemiringAction.toRingHom _ _ σ) t
  rw [smul_sub, smul_inv_smul, h5] at h4
  exact ⟨t, by simpa using Ideal.Quotient.eq.2 h4⟩

theorem exists_splitsCompl (E : Type) [Field E] [NumberField E] (m : ℕ) :
    ∃ p : ℕ, p.Prime ∧ m < p ∧ Formalism.MainNotions.S.SplitsCompl E p := by
  let N : Type := IntermediateField.normalClosure ℚ E (AlgebraicClosure E)
  haveI : NumberField N := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI : IsAlgClosure ℚ (AlgebraicClosure E) := IsAlgClosure.ofAlgebraic ℚ E (AlgebraicClosure E)
  haveI : Normal ℚ N := normalClosure.normal ℚ E (AlgebraicClosure E)
  haveI : IsGalois ℚ N := IsGalois.mk
  obtain ⟨P, hP, hm, hs⟩ := exists_degree_one_avoiding N ((m.factorial : ℤ) * discr E)
    (mul_ne_zero (by exact_mod_cast m.factorial_ne_zero) (discr_ne_zero E))
  have hp := GlobalTheory.SW.SplitPrime.absNorm_prime P hP hs
  have hnd : ¬ ((Ideal.absNorm P : ℕ) : ℤ) ∣ (m.factorial : ℤ) * discr E := by
    rintro ⟨c, hc⟩
    apply hm
    rw [hc]
    push_cast
    exact P.mul_mem_right _ (Ideal.absNorm_mem P)
  refine ⟨_, hp, ?_, fun P' hP' hmem => ⟨?_, ?_⟩⟩
  · by_contra h
    exact hnd (Dvd.dvd.mul_right (by exact_mod_cast Nat.dvd_factorial hp.pos (not_lt.1 h)) _)
  · obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) P'
    have hQm : ((Ideal.absNorm P : ℕ) : 𝓞 N) ∈ Q := by
      have := (Ideal.mem_of_liesOver Q P' _).1 hmem
      simpa using this
    have hsQ := surjective_of_conj hp P Q (Ideal.absNorm_mem P) hQm hs
    have hs' : Function.Surjective (Int.castRingHom (𝓞 E ⧸ P')) := by
      intro x
      obtain ⟨t, ht⟩ := hsQ (algebraMap (𝓞 E ⧸ P') (𝓞 N ⧸ Q) x)
      refine ⟨t, FaithfulSMul.algebraMap_injective (𝓞 E ⧸ P') (𝓞 N ⧸ Q) ?_⟩
      rw [← ht]; simp
    have hq := GlobalTheory.SW.SplitPrime.absNorm_prime P' hP' hs'
    by_contra hne
    have hco : IsCoprime ((Ideal.absNorm P' : ℕ) : 𝓞 E) ((Ideal.absNorm P : ℕ) : 𝓞 E) :=
      ((Nat.coprime_primes hq hp).2 hne).cast
    obtain ⟨a, b, hab⟩ := hco
    exact hP'.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P'.add_mem (P'.mul_mem_left _ (Ideal.absNorm_mem P')) (P'.mul_mem_left _ hmem)))
  · exact GlobalTheory.Mem.RaySplit.not_mem_sq hp hmem
      ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hp).1 (fun h => hnd (h.mul_left _)) P'
        hP'.isPrime hmem)

end GlobalTheory.LargeSplitPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFlagStepLocallyStandardDualCoeffOneStatement
section
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagStep_locallyStandard_dualCoeff_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r), ∃ v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L), v ∈ Fr.Fj (a.val + 1) ∧ H.h v (Fr.es a) = 1 := by
  first | exact @GlobalTheory.locStd_exists_flag_coef_one | exact GlobalTheory.locStd_exists_flag_coef_one | (intros; apply GlobalTheory.locStd_exists_flag_coef_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagStepLocallyStandardDualCoeffIntegralStatement
section
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagStep_locallyStandard_dualCoeff_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) (v : V), v ∈ Fr.Fj (a.val + 1) → v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L) → H.h v (Fr.es a) ∈ M.L.O := by
  first | exact @GlobalTheory.locCoef_integral | exact GlobalTheory.locCoef_integral | (intros; apply GlobalTheory.locCoef_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandValuesShiftStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_values_shift : ∀ (n : ℕ) (χ : Fin n → ℂ), (∀ (t : ℂ) (k : ℕ), gelfVal (fun a => χ a + t) k = ∑ j ∈ range (k + 1), (k.choose j : ℂ) * t ^ (k - j) * gelfVal χ j) ∧ gelfVal χ 0 = n ∧ ∀ (s : Equiv.Perm (Fin n)) (k : ℕ), gelfVal (χ ∘ s) k = gelfVal χ k := by
  first | exact @GlobalTheory.GelfValSym.gelfVal_shift_symm | exact GlobalTheory.GelfValSym.gelfVal_shift_symm | (intros; apply GlobalTheory.GelfValSym.gelfVal_shift_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenLinTamagawaVolumeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genLin_tamagawa_volume : GenLinVolume := by
  first | exact @GlobalTheory.FlagMeas.genLinVolume | exact GlobalTheory.FlagMeas.genLinVolume | (intros; apply GlobalTheory.FlagMeas.genLinVolume <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraCentralActionStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_central_action : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (m : ℤ), IsParU lam → ∑ a, lam a = (m : ℝ) → IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v := by
  first | exact @GlobalTheory.SUCentre.centre_acts | exact GlobalTheory.SUCentre.centre_acts | (intros; apply GlobalTheory.SUCentre.centre_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometriesStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ d Λ, S.IsTerm d Λ → d = S.datOf Λ) ∧ (∀ h ∈ S.H0, ∀ Λ, S.datOf (h • Λ) = h • S.datOf Λ) ∧ (∀ n ∈ S.N, ∀ Λ, (S.datOf (n • Λ)).1 = (S.datOf Λ).1) ∧ (∀ n ∈ S.N', ∀ Λ, (S.datOf (n • Λ)).2.1 = (S.datOf Λ).2.1) ∧ ∀ φ ∈ isomG L S.Hm, (∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b) → (∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) → ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  first | exact @GlobalTheory.HL.DatumOf.main | exact GlobalTheory.HL.DatumOf.main | (intros; apply GlobalTheory.HL.DatumOf.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLevelLocalDualQuotientLengthOne
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem tidx_arith {ι : Type} (s : Finset ι) (r : ι → ℕ) (T f : ℕ) (hT : T.Prime) (hcard : s.card = f)
    (hdvd : ∏ i ∈ s, r i ∣ T ^ (2 * f)) (hlow : ∀ i ∈ s, r i ≠ 0 → T ^ 2 ≤ r i) : ∀ i ∈ s, r i = T ^ 2 := by
  have hT0 : 0 < T := hT.pos
  have hpow0 : T ^ (2 * f) ≠ 0 := pow_ne_zero _ hT.ne_zero

  have hprod0 : ∏ i ∈ s, r i ≠ 0 := by
    intro h
    rw [h] at hdvd
    exact hpow0 (zero_dvd_iff.mp hdvd)
  have hge : ∀ i ∈ s, T ^ 2 ≤ r i := fun i hi =>
    hlow i hi (fun h => hprod0 (Finset.prod_eq_zero hi h))

  have hle : ∏ i ∈ s, r i ≤ ∏ _i ∈ s, T ^ 2 := by
    rw [Finset.prod_const, hcard, ← pow_mul]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hpow0) hdvd
  intro i hi
  by_contra hne
  have hlt : ∏ _i ∈ s, T ^ 2 < ∏ i ∈ s, r i :=
    Finset.prod_lt_prod (fun j _ => pow_pos hT0 2) hge ⟨i, hi, lt_of_le_of_ne (hge i hi) (Ne.symm hne)⟩
  exact absurd hle (not_le.mpr hlt)

theorem tLat_local_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 ∧ ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT hs hdeg hL v hv
  obtain ⟨hncard, hloc⟩ := GlobalTheory.St.G.SplitPrime.split_place F E cm T hT hs

  have hF : Module.finrank ℚ F = f := by
    have h := Module.finrank_mul_finrank ℚ F E
    rw [cm.deg2, hdeg] at h
    omega
  have hfin : {w : HeightOneSpectrum (𝓞 F) | (T : 𝓞 F) ∈ w.asIdeal}.Finite :=
    Set.finite_of_ncard_pos (by rw [hncard]; exact Module.finrank_pos)
  have hcard : hfin.toFinset.card = f := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, hncard, hF]

  have hlow : ∀ w ∈ hfin.toFinset,
      (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup ≠ 0 →
      T ^ 2 ≤ (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup := by
    intro w hw h0
    have hw' : (T : 𝓞 F) ∈ w.asIdeal := (Set.Finite.mem_toFinset hfin).mp hw
    obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc w hw'
    exact GlobalTheory.T.prime_sq_le_local_hermitian_dual_index F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2
      (GlobalTheory.T.split_place_dual_quotient_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2) h0

  have hdvd := GlobalTheory.T.prod_local_relIndex_dvd_hermitian_dual F E cm n J hJ hdet T f L hT hs hdeg hL hfin.toFinset
    (fun w hw => (Set.Finite.mem_toFinset hfin).mp hw)
  rw [hL.2.2.2.1] at hdvd
  have heq := tidx_arith hfin.toFinset
    (fun w => (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup)
    T f hT hcard hdvd hlow v ((Set.Finite.mem_toFinset hfin).mpr hv)
  refine ⟨heq, ?_⟩
  obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc v hv
  exact GlobalTheory.T.local_hermitian_dual_quotient_cyclic_split_place F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2
    (GlobalTheory.T.split_place_dual_quotient_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2) heq

end GlobalTheory.St.G
end


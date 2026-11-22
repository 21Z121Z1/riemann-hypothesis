import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0433
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0012
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0436
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0373
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0437
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0206
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnfoldingBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqSmulNormalisedAmplitudeLargeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpNormalGap

open GlobalTheory.AmpNormal

theorem one_side_gap (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ}
    {μW μN μG νq : Measure (Mt k r)} {B l : R.H → Wp} {w : R.H} {dd m : ℝ}
    (hdg : R.IsDG ε mu) (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hS : SideG k r z π u μW μN μG νq) (hc : c ≠ 0)
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B)
    (hl : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l)
    (hbe : ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hw : R.KFin w) (hm : 0 < m)
    (hmass : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) = ENNReal.ofReal m)
    (hd0 : 0 < dd) (hdd : ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) :
    (∃ v, R.KFin v ∧ l v ≠ 0) ∧ ∃ β : ℂ, (∀ v ∈ R.sm, B v = β • l v) ∧ m * dd = ‖β‖ ^ 2 * ‖w‖ ^ 2 := by
  have hds : R.IsDS ε mu := GlobalTheory.isDS_of_isDG hdg
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨hmul, hone, hinn, hsm, hTKsm, hTK, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hKF k r ε mu R hds
  obtain ⟨hG1, hGm, hGi⟩ := uHGroup _ _ (det_hpk k r)
  obtain ⟨t, ht, hN, hz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, hcomm, hpsi⟩ := hz z hS.1
  have htd : IsUnit t.det := (hGi t ht).1
  have hti : t⁻¹ ∈ GG k r := (hGi t ht).2
  have hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ := by
    refine ⟨⟨ContinuousLinearMap.ext hone, fun a ha b hb => ContinuousLinearMap.ext (hmul a ha b hb)⟩, fun g hg v => ?_,
      hcont⟩
    rw [@norm_eq_sqrt_re_inner ℂ, hinn g hg, ← @norm_eq_sqrt_re_inner ℂ]
  have e1 : ∀ v, R.σ t⁻¹ (R.σ t v) = v := fun v => by
    rw [← hmul _ hti _ ht, Matrix.nonsing_inv_mul _ htd, hone]
  have e2 : ∀ v, R.σ t (R.σ t⁻¹ v) = v := fun v => by
    rw [← hmul _ ht _ hti, Matrix.mul_nonsing_inv _ htd, hone]
  obtain ⟨hS', hR⟩ := GlobalTheory.BesselMoveGap.bessel_move_gap hH k r Wp z π u c μW μN μG νq t ht hN hcomm hpsi hS
  obtain ⟨hbes, hmove⟩ := hR R hU
  obtain ⟨l₁, hl₁⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp z π u μW _ μG _ hdg hgap hok hS'
  have hl₂ : IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) (fun v => l (R.σ t v)) := by
    refine ⟨(hbes l).1 hl, fun x hx v hv => ⟨(hl₁.2 x hx v hv).1, ?_⟩⟩
    rw [(hl₁.2 x hx v hv).2, ← hbe _ (hsm t ht x hx) _ (hTK t ht v hv),
      hmove l₁ hl₁ _ (hsm t ht x hx) _ (hTK t ht v hv), e1, e1]
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r :=
    (GlobalTheory.quotMeas_ae_mem_and_measurable hKF k r ε mu R Wp z π u μW μN μG νq hds hS).1
  have htr : ∀ F : R.H → Wp,
      PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) (fun g => F (R.σ t (R.σ g w))) =
        PI.BesselPeriodGGP.l2SG νq (fun g => F (R.σ g w)) := by
    intro F
    unfold PI.BesselPeriodGGP.l2SG
    refine (lintegral_map_equiv _ (lmulEquiv t htd)).trans (lintegral_congr_ae ?_)
    filter_upwards [hae] with x hx
    have : R.σ t (R.σ (Matrix.of (lmulEquiv t htd x)) w) = R.σ (Matrix.of x) w := by
      show R.σ t (R.σ (t⁻¹ * Matrix.of x) w) = _
      rw [hmul _ hti _ hx, e2]
    simp only [this]
  have hB₁ : IsBes R z π (fun v => B (R.σ t v)) := (hbes B).1 hB
  obtain ⟨v, hv, hv0⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r ε mu h R Wp z π u μW _ μG _ (fun v => B (R.σ t v))
    (fun v => l (R.σ t v)) w hds hgap hok hS' hB₁ hw
    (by rw [htr B, hmass]; exact (ENNReal.ofReal_pos.2 hm).ne') (by rw [htr B, hmass]; exact ENNReal.ofReal_ne_top) hl₂
  have hvs : v ∈ R.sm := hTKsm v (hKT v hv)
  have hnz : NzOn R (fun v => l (R.σ t v)) := ⟨v, hvs, hv0⟩
  refine ⟨GlobalTheory.exists_kFin_ne_zero_of_cwCont hKF k r ε mu R hds Wp l hl.1 hl.2.1 hl.2.2.2 ⟨_, hsm t ht v hvs, hv0⟩, ?_⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.besselMaps_proportional_discreteSeries_largeGap hH k r ε mu R Wp z π u μW _ μG _ _ _ hdg hS' hl₂.1 hnz hB₁
  have hβ' : ∀ v ∈ R.sm, B v = β • l v := fun v hv => by
    have := hβ _ (hsm _ hti v hv)
    simpa only [e2] using this
  refine ⟨β, hβ', ?_⟩
  have hws : w ∈ R.sm := hTKsm w (hKT w hw)
  have hiso := (Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH.1 k r ε mu h R Wp z π u μW _ μG _ _ dd hdg hgap hok hS' hl₂ hdd hnz).2 w hws
  have h2 := (htr fun v => ((Real.sqrt dd : ℝ) : ℂ) • l v).symm.trans hiso
  have h3 : ENNReal.ofReal dd * PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) =
      ENNReal.ofReal (‖β‖ ^ 2) * PI.BesselPeriodGGP.l2SG νq (fun g => ((Real.sqrt dd : ℝ) : ℂ) • l (R.σ g w)) := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have en : ∀ y : Wp, ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := fun y => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl
    rw [en, en, hβ' _ (hsm _ hx w hws), ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
      norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow,
      Real.sq_sqrt hd0.le]
    congr 1
    ring
  rw [hmass, h2, ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h3
  linarith

theorem amp_eq_smul_normalised_gap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  intro hH D τ w w' θ W lam A h l l' hθ hka hT hT' hW hA hgap hok hl hl' hbe hbe'
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW
  obtain ⟨hlam, hds, b1, b2, hsm0, hv0, ⟨P, hP, hlowK⟩, hc, l1, l2, -⟩ := hA
  set R : Rep D.R.k D.R.rS := ⟨A.H, A.σ⟩ with hR
  have hDS : R.IsDS (epsSH D.R) lam := ⟨hlam, hds⟩
  have hDG : R.IsDG (epsSH D.R) lam := ⟨hlam, hds, h, hgap, hok⟩
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨-, -, -, hsm, hTKsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF _ _ _ _ R hDS
  obtain ⟨-, hGm, -⟩ := uHGroup _ _ (det_hpk D.R.k D.R.rS)
  rw [hN] at q1 q2 hbe hbe'
  obtain ⟨U, hS⟩ := sideG_of ENNReal.ofReal_lt_top z1 (t1 ▸ hT) c1 w1 hG q1
  obtain ⟨U', hS'⟩ := sideG_of ENNReal.ofReal_lt_top z2 (t2 ▸ hT') c2 w2 hG q2
  have hcs : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have : 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) = 2 * (D.host.ka / gg D) := by
      rw [mul_div_assoc]; rfl
    rw [this]
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * (D.host.ka / gg D)).ne'
  have hn : 0 < ‖A.v0‖ := norm_pos_iff.2 hv0
  set w0 : A.H := ((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0 with hw0
  have hw1 : ‖w0‖ = 1 := by rw [hw0, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hlow : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 :=
    ⟨P, hP, hw1, Submodule.smul_mem _ _ hlowK⟩
  have hv : A.v0 = ((‖A.v0‖ : ℝ) : ℂ) • w0 := by
    rw [hw0, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  have hvK : R.KFin A.v0 := by
    obtain ⟨S, h1, h2, h3⟩ := hwK
    exact ⟨S, h1, hv ▸ S.smul_mem _ h2, h3⟩
  have hws : w0 ∈ R.sm := hTKsm _ (hKT _ hwK)
  obtain ⟨c₀, hc₀, hdeg⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 _ _ (epsSH D.R) W.μG hG
  have hdd := (hdeg lam R hDG).1
  have hd0 : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC lam := mul_pos hc₀ (GlobalTheory.BesselNorm.fdegHC_pos lam hlam.1.injective)
  set dd := c₀ * Formalism.QuantumDeterminants.fdegHC lam
  have hp : (0 : ℝ) < Module.finrank ℂ W.Wp := by
    obtain ⟨g, -, hnt, -⟩ := c1
    exact_mod_cast Module.finrank_pos
  have hq : (0 : ℝ) < Module.finrank ℂ W.Wq := by
    obtain ⟨g, -, hnt, -⟩ := c2
    exact_mod_cast Module.finrank_pos
  obtain ⟨nz1, β, hβ, e1⟩ := one_side_gap hH R (B := A.B) (l := l) hDG hgap hok hS hcs (isBesselMapSm_of b1) hl hbe hvK
    (mul_pos hc hp) l1 hd0 hdd
  obtain ⟨nz2, β', hβ', e2⟩ := one_side_gap hH R (B := A.B') (l := l') hDG hgap hok hS' hcs (isBesselMapSm_of b2) hl' hbe'
    hvK (mul_pos hc hq) l2 hd0 hdd
  refine ⟨nz1, nz2, w0, (A.cN : ℂ)⁻¹ * ((β * (‖A.v0‖ : ℝ)) * star (β' * (‖A.v0‖ : ℝ))), hlow, ?_, ?_⟩
  · have hw00 : w0 ≠ 0 := by rw [← norm_pos_iff, hw1]; exact one_pos
    rw [show PI.BesselPeriodGGP.fdegH W.μG A.σ w0 = dd from hdd w0 hw00]
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    simp only [norm_mul, norm_star, norm_inv, Complex.norm_real, norm_norm, Real.norm_of_nonneg hc.le]
    have e1' : ‖β‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wp * dd := e1.symm
    have e2' : ‖β'‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wq * dd := e2.symm
    rw [mul_pow, mul_pow, mul_pow, mul_pow, e1', e2']
    field_simp
  · intro ν γ hγ hν
    have hae : ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := hν
    unfold LocS.J amp ampJ
    rw [Complex.ofReal_one, inv_one, one_smul, mul_smul]
    congr 1
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have a1 : A.Φ (γ * Matrix.of x) = (β * (‖A.v0‖ : ℝ)) • l (A.σ (γ * Matrix.of x) w0) := by
      have hs := hsm _ (hGm _ hγ _ hx) w0 hws
      have hs' := hsm _ (hGm _ hγ _ hx) A.v0 hsm0
      unfold LocS.Φ
      rw [hβ _ hs', mul_smul, ← hl.2.1 _ _ hs, ← map_smul, ← hv]
    have a2 : A.Φ' (Matrix.of x) = (β' * (‖A.v0‖ : ℝ)) • l' (A.σ (Matrix.of x) w0) := by
      have hs := hsm _ hx w0 hws
      have hs' := hsm _ hx A.v0 hsm0
      unfold LocS.Φ'
      rw [hβ' _ hs', mul_smul, ← hl'.2.1 _ _ hs, ← map_smul, ← hv]
    rw [a1, a2]
    ext y
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, ContinuousLinearMap.smul_apply,
      smul_smul]
    congr 1
    simp only [RCLike.star_def]
    ring

end GlobalTheory.AmpNormalGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypotheses
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalSetupGap

theorem exists_seq {k : ℕ} (u : Fin k → ℝ) : ∃ U : ℕ → ℝ, ∀ i : Fin k, U (i.val + 1) = u i :=
  ⟨fun n => if h : n - 1 < k then u ⟨n - 1, h⟩ else 0, fun i => by simp⟩

theorem exists_setup (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Mt k r)} {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r}
    (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) (hS : SideG k r z π u μW μN μG νq) {c : ℝ} (hc : 0 < c)
    (hd : ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG (PI.BesselPeriodGGP.eps48 k r) mu →
      ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * fdegHC mu) :
    ∃ l : ∀ ν, (R ν).H → Wp,
      Setup lam u b bv ga h q0 z π μW μN μG νq R l (fun ν => c * fdegHC (fun a => lam a + (ν a : ℝ))) := by
  have hnum := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (h / 2) := hnum.1.2.2.2.2
  have hDG : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 →
      (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := by
    intro ν hν
    obtain ⟨hp, hds⟩ := hF ν hν
    exact ⟨hp, hds, h / 2, (hnum.2 ν hν).2.2.1, hok⟩
  have hex : ∀ ν : Fin (2 * r + k + 1) → ℤ,
      ∃ l : (R ν).H → Wp, n1 ν ≤ q0 → IsBeL (R ν) z π μW μN l := by
    intro ν
    by_cases hν : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r (PI.BesselPeriodGGP.eps48 k r)
        (fun a => lam a + (ν a : ℝ)) (h / 2) (R ν) Wp z π u μW μN μG νq (hDG ν hν)
        (hnum.2 ν hν).2.2.1 hok hS
      exact ⟨l, fun _ => hl⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hν⟩
  choose l hl using hex
  refine ⟨l, ?_⟩
  unfold Setup SideFam
  refine ⟨hN, hF, hS, fun ν hν => ⟨hl ν hν, ?_, ?_⟩⟩
  · exact mul_pos hc (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hN ν hν).1
  · intro w hw
    exact hd _ (R ν) (hDG ν hν) w hw

theorem exists_setup_both : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t ht hNt hzt R hR
  have := FiniteDimensional.complete ℂ W.Wp
  have := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨U, hU⟩ := exists_seq (uS D w τ)
  obtain ⟨U', hU'⟩ := exists_seq (uS D w' τ)
  obtain ⟨hNum, -, -⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w U hU
  obtain ⟨hNum', -, -⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w' U' hU'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := hZ.1
  obtain ⟨hπ, hπ', hzb, hzb', hT, hT', hμG, hμW, -, hμW', -, hμN, hνS, hνS'⟩ := hW
  have hTw : 0 < Tz D.R.k D.R.rS W.z := by
    rw [hT]
    unfold Tr
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hTT.2.2.1 : 0 < (D.mem w).A.T)
  have hTw' : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [hT']
    unfold Tr
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hTT.2.2.2.1 : 0 < (D.mem w').A.T)
  have hNH : PI.BesselPeriodGGP.IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hμN]
    refine GlobalTheory.haarLie_isHaarOn_Nset _ _ _ ?_ ENNReal.ofReal_lt_top
    unfold kapN
    exact ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ)
  have hS1 : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨hzb, hTw, ⟨_, hπ⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U _ _ hzb hTw hπ hU, hμW, hNH, hμG, hνS⟩
  have hS2 : SideG D.R.k D.R.rS W.z' W.π' U' W.μW' W.μN W.μG W.νS' :=
    ⟨hzb', hTw', ⟨_, hπ'⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U' _ _ hzb' hTw' hπ' hU', hμW', hNH, hμG,
      hνS'⟩
  have hM1 := (GlobalTheory.BesselMoveGap.bessel_move_gap hH D.R.k D.R.rS W.Wp W.z W.π U
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.μW W.μN W.μG W.νS t ht hNt
    (hzt W.z hzb).1 (hzt W.z hzb).2 hS1).1
  have hM2 := (GlobalTheory.BesselMoveGap.bessel_move_gap hH D.R.k D.R.rS W.Wq W.z' W.π' U'
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.μW' W.μN W.μG W.νS' t ht hNt
    (hzt W.z' hzb').1 (hzt W.z' hzb').2 hS2).1
  obtain ⟨c, hc, hsch⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 D.R.k D.R.rS
    (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) W.μG hμG
  obtain ⟨l, hl⟩ := exists_setup hH hNum hR hM1 hc (fun mu Q h => (hsch mu Q h).1)
  obtain ⟨l', hl'⟩ := exists_setup hH hNum' hR hM2 hc (fun mu Q h => (hsch mu Q h).1)
  exact ⟨U, U', l, l', _, hl, hl'⟩

end GlobalTheory.Amp.LocalSetupGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudePieriRelevantCellLargeGap
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellPieriG

open GlobalTheory.CellPieri

variable {k r : ℕ}

theorem amp_eq_orb (hH : GlobalTheory.GapIn.Hyp) (hA : GlobalTheory.GapIn.AmpKF0) (hC : CellConv) (L : LocBessel k r) (R : Rep k r)
    (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H)
    [CompleteSpace L.Wp] [CompleteSpace L.Wq]
    (hR : R.IsDS L.ε mu) (hgap : GapAtLeast L.ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hcell : GapCell k r h)
    (hc : L.c ≠ 0) (hκ : L.κN ≠ ⊤) (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hl : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    (hw : PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hD : CellData L μG γ μR νR ν) (v v' : R.H) (hv : R.KFin v) (hv' : R.KFin v')
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefR R v v' ξ ξ') γ) ν ∧
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) * (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ)) • amp R l l' w νR γ =
        OrbInt L (coefR R v v' ξ ξ') γ ν := by
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨-, -, -, -, hsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw
  have hle : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, x ∈ R.TK := by
    intro x hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, w, hwK, rfl⟩
  have hD' : CellData (withRep L R mu hR) μG γ μR νR ν := hD
  obtain ⟨b, hb0, hb1, hb2⟩ := hC k r L h μG γ μR νR ν hκ hok hcell hD hD.2.2.1
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hOne : OnePlaceKF (withRep L R mu hR) h μG w l l' :=
    ⟨⟨hgap, hok, hc, hw, hG, fun x hx y hy => hl x (hsm x (hle x hx)) y (hle y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hle y hy)⟩,
      fun x hx y hy => hl x (hsm x (hle x hx)) y (hKT y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hKT y hy)⟩
  have h1 := hA k r (withRep L R mu hR) h μG w l l' hOne γ μR νR ν hD' b hb0 hb1 hb2 v v' hv hv' ξ ξ'
  have h2 := (GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD').2 b hb0 (by linarith)
    hb2 v v' hv hv' ξ ξ'
  refine ⟨h2, ?_⟩
  obtain ⟨c, hc0, hc1⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 k r L.ε μG hG
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn, -⟩ := hw
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hDG : R.IsDG L.ε mu := ⟨hR.1, hR.2, h, hgap, hok⟩
  have hf : (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) ≠ 0 := by
    rw [(hc1 mu R hDG).1 w hw0]
    exact Complex.ofReal_ne_zero.mpr (mul_pos hc0 (fdegHC_pos hR.1.1)).ne'
  have h3 : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • amp R l l' w νR γ =
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)⁻¹) • OrbInt L (coefR R v v' ξ ξ') γ ν := h1
  rw [mul_smul, h3, smul_smul, mul_inv_cancel₀ hf, one_smul]

theorem amp_pieri : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  intro hH hA hC k r ι κ _ _ _ _ ρ Γ d L R RI io pr ep mu muI h μG om om' l l' lI lI' w wI κ₀ κ₁
  haveI := FiniteDimensional.complete ℂ L.Wp
  haveI := FiniteDimensional.complete ℂ L.Wq
  intro hR hgap hRI hok hcell hc hκ hG hρ hT hom hom' hl hl' hlI ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hw hwI hκI γ μR νR ν hD
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  have hvs : v ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v hv
  have hvs' : v' ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v' hv'
  obtain ⟨hK, hsplit⟩ := GlobalTheory.KFinCoefSplit.kfin_coef_mul_split hKF k r ι κ ρ Γ d R RI io pr ep L.ε mu muI om om' v v' hR
    (fun I => (hRI I).1) hρ hT hv hv'
  obtain ⟨-, e0⟩ := amp_eq_orb hH hA hC L R mu h μG l l' w hR hgap hok hcell hc hκ hG hl hl' hw γ μR νR ν hD
    v v' hv hv' (l v) (l' v')
  have eI := fun I => amp_eq_orb hH hA hC L (RI I) (muI I) h μG (lI I) (lI' I) (wI I) (hRI I).1 (hRI I).2 hok hcell
    hc hκ hG (hlI I).1 (hlI I).2 (hwI I) γ μR νR ν hD _ _ (hK I).1 (hK I).2 (l v) (l' v')
  have hae := (GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD).1
  have hc0 : ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ ≠ 0 :=
    mul_ne_zero (inner_self_ne_zero.mpr hv0) (inner_self_ne_zero.mpr hv0')
  have horb : herm Γ (ρ γ *ᵥ om') om • OrbInt L (coefR R v v' (l v) (l' v')) γ ν =
      ∑ I, (ep I : ℂ) • OrbInt L (coefR (RI I) (∑ c, pr I c (tm R om v c)) (∑ c, pr I c (tm R om' v' c))
        (l v) (l' v')) γ ν := by
    unfold OrbInt
    simp only [← integral_smul]
    refine Eq.trans (integral_congr_ae ?_) (integral_finset_sum _ (fun I _ => (eI I).1.smul (ep I : ℂ)))
    filter_upwards [hae] with p hp
    obtain ⟨hm, he⟩ := herm_cell hρ hom hom' hD.1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hs := hsplit _ hm
    rw [he] at hs
    ext x
    simp only [besselIntg, coefR, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, map_smul, smul_smul, Pi.smul_apply,
      ← Finset.sum_smul]
    congr 1
    have key : ∀ (D A B C : ℂ) (e f : κ → ℂ), D * C = ∑ I, e I * f I →
        D * A * (B * C) = ∑ I, e I * A * (B * f I) := by
      intro D A B C e f hh
      rw [show D * A * (B * C) = D * C * (A * B) by ring, hh, Finset.sum_mul]
      exact Finset.sum_congr rfl fun I _ => by ring
    exact key _ _ _ _ _ _ hs
  apply smul_right_injective _ hc0
  simp only [Finset.smul_sum, smul_smul]
  rw [mul_comm, mul_assoc, mul_smul, e0, horb]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← (eI I).2, smul_smul, (hκI I v hvs).1, (hκI I v' hvs').2, inner_smul_left, inner_smul_right]
  congr 1
  simp only [RCLike.star_def]
  ring

end GlobalTheory.CellPieriG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardMiddleLatticesOverGenusLatticeStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_middleLattices_over_genus_lattice : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), {𝓛 : Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) | (∃ Λ', IsRowLat D F0 Λ' ∧ (Lsub Λ' (lf D F0)).comap (((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)).restrictScalars (𝓞 D.host.E)) = 𝓛) ∧ 𝓛.comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) = M}.ncard = (Tu D u - 1) ^ D.R.f := by
  first | exact @GlobalTheory.LoopC.GluingNum.gluingNum | exact GlobalTheory.LoopC.GluingNum.gluingNum | (intros; apply GlobalTheory.LoopC.GluingNum.gluingNum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CriticalLevelLePowAllPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.criticalLevel_le_pow_allPlaces : Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ, Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m : ℝ)) := by
  first | exact @GlobalTheory.CritLevelUpper.tcrit_le_pow | exact GlobalTheory.CritLevelUpper.tcrit_le_pow | (intros; apply GlobalTheory.CritLevelUpper.tcrit_le_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DegIAlongFamily
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.DegStepG

theorem vandLine (hH : GlobalTheory.GapIn.Hyp) (Cn m₀ : ℝ)
    (hnear : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
      1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
        l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r →
        Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2))
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ) (hCl : 1000 ≤ Cl) (hm : m₀ ≤ D.R.m) :
    Formalism.MainNotions.BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  intro hH0 τ w w' _ θ _ W _ lam' hl A hA I s hs A' hA'
  have hZ : GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 := hH0
  have hcard : (I.card : ℝ) ≤ D.R.r := by
    rw [← Formalism.MainNotions.BridgeLemma₂.deg_cast_r]
    have : I.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ I
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r := by linarith
  have h2 : l1dist (lam' + s • epsI I) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r :=
    le_trans (Formalism.MainNotions.BridgeLemma.l1_distance_sign_step _ _ s hs I) (by linarith)
  obtain ⟨g1, gok⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ lam' h1
  obtain ⟨g2, _⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ _ h2
  exact GlobalTheory.T.formalDegree_ratio_eq_harishChandra_ratio_largeGap hH D W lam' (lam' + s • epsI I) A A' _ hA hA' g1 g2 gok

theorem degI_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
      PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ,
        OwnEv Fm fun C' Cl x i => Formalism.MainNotions.BridgeLemma.DegreeRatioUnitShiftBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  refine ⟨1, 1000, zero_le_one, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hnear⟩ := GlobalTheory.T.gap_near_placeParameter_half_noncompactGap Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i => ?_⟩
  exact Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
    (vandLine hH Cn m₀ hnear (Fm.D x i) (Fm.L x i) _ _ _ _ _ _ _ _ _ hCl (hx0 x hx i).2.1)

end GlobalTheory.DegStepG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnfoldingBoundStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlag_unfolding_bound : UnfoldBound := by
  first | exact @GlobalTheory.FlagUnfold.unfoldBound | exact GlobalTheory.FlagUnfold.unfoldBound | (intros; apply GlobalTheory.FlagUnfold.unfoldBound <;> assumption)
end


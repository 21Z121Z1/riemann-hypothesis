import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslate
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0433
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0429
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0445
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0446
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0436
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0437
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0467
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0463
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0468
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0049
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0415
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0462
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRat
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthMomentsAmplitudesLargeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.AmpMomentsGap

theorem family_through_at_gap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (ν₀ : Fin (2 * r + k + 1) → ℤ) (R0 : Rep k r) (hN : Num k r lam u b bv ga h q0)
    (hR0 : R0.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν₀ a : ℝ))) :
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFam lam q0 R ∧ R ν₀ = R0 := by
  classical
  have hex : DSExistG := hH.1.2.2.2.1
  have hC : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P := by
    obtain ⟨P, hP, -⟩ := hR0.2
    exact ⟨P, hP⟩
  have H := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      (∑ a, (ν a).natAbs ≤ q0 → R.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))) ∧
      (ν = ν₀ → R = R0) := by
    intro ν
    by_cases h0 : ν = ν₀
    · refine ⟨R0, fun _ => ?_, fun _ => rfl⟩
      subst h0
      exact hR0
    · by_cases hq : ∑ a, (ν a).natAbs ≤ q0
      · obtain ⟨R, hR⟩ := hex k r _ _ (H.2 ν hq).1 hC ⟨h / 2, (H.2 ν hq).2.2.1, H.1.2.2.2.2⟩
        exact ⟨R, fun _ => GlobalTheory.isDS_of_isDG hR, fun h => absurd h h0⟩
      · exact ⟨R0, fun h => absurd h hq, fun _ => rfl⟩
  choose R hR using key
  exact ⟨R, fun ν hν => (hR ν).1 hν, (hR ν₀).2 rfl⟩

theorem moment_of_bessel (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Mt k r)}
    {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r} {l : ∀ ν, (R ν).H → Wp} {dg : (Fin (2 * r + k + 1) → ℤ) → ℝ}
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R l dg) (ν) (q : ℕ) (h1 : n1 ν + (r + 1) * q ≤ q0)
    (h2 : (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2) (R0 : Rep k r) (hR : R ν = R0) (B : R0.H → Wp)
    (hB : IsBes R0 z π B) (v : R0.H) (hv : v ≠ 0)
    (hlow : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P ∧
      v ∈ PI.UpqRep.lowKSub (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (fun g => R0.σ (P⁻¹ * g * P)))
    (h0 : l2SG νq (fun g => B (R0.σ g v)) ≠ 0) (ht : l2SG νq (fun g => B (R0.σ g v)) ≠ ⊤) (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q)) * (‖B (R0.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂νq ≤
      ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) * l2SG νq (fun g => B (R0.σ g v)) := by
  subst hR
  have hν : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) h1
  obtain ⟨hNum, hFam, hSide, hSF⟩ := id hS
  obtain ⟨⟨-, -, -, -, hOK⟩, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  obtain ⟨-, -, hgap, -⟩ := hfam ν hν
  have hDS := hFam ν hν
  obtain ⟨hBe, hpos, -⟩ := hSF ν hν
  obtain ⟨-, -, -, hsm, hTK, -, hKT, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r _ _ (R ν) hDS
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : (R ν).H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hvw : v = ((‖v‖ : ℝ) : ℂ) • w := by
    rw [hw, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwl : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w := by
    obtain ⟨P, hP, hvP⟩ := hlow
    exact ⟨P, hP, hw1, Submodule.smul_mem _ _ hvP⟩
  have hwK : (R ν).KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hwl
  have hvK : (R ν).KFin v := by
    obtain ⟨S, hS1, hS2, hS3⟩ := hwK
    exact ⟨S, hS1, by rw [hvw]; exact S.smul_mem _ hS2, hS3⟩
  have hws : w ∈ (R ν).sm := hTK _ (hKT _ hwK)
  obtain ⟨v₁, hv₁, hl⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq B (l ν) v hDS hgap hOK hSide hB
    hvK h0 ht hBe
  have hnz : NzOn (R ν) (l ν) := ⟨v₁, hTK _ (hKT _ hv₁), hl⟩
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := ⟨hDS.1, hDS.2, ⟨h / 2, hgap, hOK⟩⟩
  obtain ⟨c, hc⟩ := GlobalTheory.GapLine.bessel_line_gap hH k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) B hDG hSide hBe.1 hnz hB
  have hmass := ((Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg
    ((GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg).1 hS) ν hν).2 hnz).2 w hws
  have hmom := GlobalTheory.T.oneMajorantLength_moment_lowestKType hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν q h1 h2 w hwl a
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hSide
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 m0 m1 hq
  set K : ℝ := (‖v‖ * ‖c‖) ^ 2 / dg ν with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ᵐ x ∂νq, ‖B ((R ν).σ (Matrix.of x) v)‖ ^ 2 = K * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) := by
    filter_upwards [hae] with x hx
    have hxs := hsm _ hx w hws
    have : B ((R ν).σ (Matrix.of x) v) = ((‖v‖ : ℝ) : ℂ) • c • l ν ((R ν).σ (Matrix.of x) w) := by
      conv_lhs => rw [hvw, map_smul]
      rw [hB.2.1 _ _ hxs, hc _ hxs]
    rw [this, norm_smul, norm_smul, Complex.norm_real, norm_norm, hK]
    field_simp
  have e1 : l2SG νq (fun g => B ((R ν).σ g v)) = ENNReal.ofReal K := by
    rw [hw1, one_pow, ENNReal.ofReal_one] at hmass
    rw [← mul_one (ENNReal.ofReal K), ← hmass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [GlobalTheory.AmpMoments.sq_nnnorm, hx, one_mul, ENNReal.ofReal_mul hK0]
  rw [e1, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal K)]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right hmom _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with x hx
  have hl0 : 0 ≤ lenA k r z (Matrix.of x) a ^ (2 * q) := pow_nonneg Metric.infDist_nonneg _
  rw [GlobalTheory.AmpMoments.sq_nnnorm, hx, ← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul hK0]
  congr 1; ring

theorem amplitude_moments_gap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 Cq : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C := by
  intro hH Cg cb Cu cT CT C0 C1 Cq
  refine ⟨2 * Cg + 2 + |CT| + 10 * max 2 Cu, fun Cn => ⟨|Cn| + |Cq|, ?_⟩⟩
  intro D large₂ C' Cl hCl hBig hZ τ w w' hTT θ _ W hW lam' hlam A hA a q hq
  haveI := FiniteDimensional.complete ℂ W.Wp
  obtain ⟨-, -, hb, hm, -, -, -, hmk, hv, -, hka, hvb, hg, hgb, hCg, -, hT, -⟩ :=
    GlobalTheory.Amp.RangeModel.sizes_of D large₂ C' Cl Cg cb Cu cT CT C0 hBig.1 hZ
  have hθ := GlobalTheory.Amp.RangeModel.theta_pos D τ w w' θ W hW
  obtain ⟨hNum, -, heps⟩ := GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w (uOne D w τ) (fun i => by
    have := i.isLt
    simp only [uOne]
    rw [dif_pos ⟨by omega, by omega⟩]; rfl)

  have hex : ∀ i, ∃ n : ℤ, lam' i = lamD D τ i + n := fun i => by
    obtain ⟨n₁, h₁⟩ := hA.1.2 i
    obtain ⟨n₂, h₂⟩ := hNum.2.1.2 i
    exact ⟨n₁ - n₂, by push_cast at *; linarith⟩
  choose ν hν using hex
  obtain rfl : lam' = fun i => lamD D τ i + (ν i : ℝ) := funext hν
  have hn1 : ((n1 ν : ℕ) : ℝ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by
    refine le_trans (le_of_eq ?_) hlam
    simp [n1, l1dist]
  obtain ⟨hr1, hr2⟩ := GlobalTheory.AmpMoments.radius_bound hm hmk hBig.2.2 hn1 hq
  let R0 : Rep D.R.k D.R.rS := { H := A.H, σ := A.σ }
  obtain ⟨hA1, hA2, hA3, -, hA5, hA6, hA7, hA8, hA9, -⟩ := hA
  rw [← heps] at hA2 hA7
  have hDS : R0.IsDS (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) (fun i => lamD D τ i + (ν i : ℝ)) := ⟨hA1, hA2⟩
  obtain ⟨R, hFam, hR⟩ := family_through_at_gap hH _ _ _ _ _ _ _ _ _ ν R0 hNum hDS

  set c : ℝ := 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) with hc
  have hc2 : c = 2 * (Real.pi / D.host.v / gg D) := by rw [hc, hka, gg]; ring
  have hc0 : 0 < c := by rw [hc2]; have := Real.pi_pos; positivity
  obtain ⟨t, htG, htN, htz, hts⟩ := GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter D.R.k D.R.rS (c : ℂ) (by exact_mod_cast hc0.ne')
  choose s hs0 hs1 hs2 hs3 using hts
  have htd : IsUnit t.det := Matrix.isUnit_det_of_right_inverse (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv htG).2.1
  obtain ⟨U, U', l, l', dg, hS, -⟩ := GlobalTheory.T.amplitudeLocalData_momentPieriHypotheses hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t htG
    htN (fun z hz => (htz z hz).2) R hFam
  obtain ⟨-, -, hz, -, hTz, -, hG, -, -, -, -, -, hQ, -⟩ := hW
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hS.2.2.1
  have hSide : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨g1, g2, g3, g4, g5, GlobalTheory.AmpMoments.haar_of_conj htd htN g6, g7, hQ⟩
  have hB := (((GlobalTheory.BesselMoveGap.bessel_move_gap hH _ _ W.Wp W.z W.π U (c : ℂ) W.μW W.μN W.μG W.νS t htG htN (htz _ hz).2.1
    (htz _ hz).2.2 hSide).2 R0 (GlobalTheory.TensCompare.isURepOn_of_isDS hDS)).1 A.B).1 (GlobalTheory.AmpMoments.isBesselMapSm_of hA3)
  obtain ⟨hmul, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 _ _ _ _ R0 hDS
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts g5 g6
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot g7.2.2.1 m0 m1 g8
  set νq := W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j with hνq
  have hpt : ∀ᵐ x ∂νq, A.Φ (t * Matrix.of x) = A.B (R0.σ t (R0.σ (Matrix.of x) A.v0)) := by
    filter_upwards [hae] with x hx
    exact congrArg A.B (hmul t htG _ hx A.v0)
  have e1 : l2SG W.νS A.Φ = l2SG νq (fun g => A.B (R0.σ t (R0.σ g A.v0))) := by
    unfold l2SG
    rw [GlobalTheory.AmpMoments.lintegral_translate W.νS t htd]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [← hx]; rfl
  have hfr : 0 < Module.finrank ℂ W.Wp := by
    obtain ⟨_, _, -, hρ⟩ := g3
    haveI := hρ.1
    exact Module.finrank_pos
  have key := moment_of_bessel hH hS ν q hr1 hr2 R0 hR _ hB A.v0 hA6 hA7
    (by rw [← e1, hA9]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne')
    (by rw [← e1, hA9]; exact ENNReal.ofReal_ne_top) a
  have hsz := GlobalTheory.AmpMoments.size_bound (q := q) (Cu := Cu) hb hv hvb hg hgb hCg (T := Tz D.R.k D.R.rS W.z) (CT := CT)
    (r := D.R.rS) (by rw [hTz]; have := hT w; rw [hm] at this; exact_mod_cast this) (norm_nonneg (s a)) (by
      have := hs1 a
      rw [Complex.norm_real, Real.norm_of_nonneg hc0.le, ← inv_div c 2, hc2,
        mul_div_cancel_left₀ _ (two_ne_zero (α := ℝ))] at this
      exact this)
  have hm' : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by rw [hm]; push_cast; ring
  rw [e1, hm']
  refine le_trans ?_ (mul_le_mul_left (ENNReal.ofReal_le_ofReal hsz) _)
  rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right key _)
  rw [GlobalTheory.AmpMoments.lintegral_translate W.νS t htd, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with x hx
  rw [← hx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
    ← GlobalTheory.AmpMoments.lenA_mul W.z t (Matrix.of x) s hs0 (fun b => hs3 b _ hz), BranchingSupport.TensInh.lenA_eq_lA]
  rfl

end GlobalTheory.AmpMomentsGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericGenericTermsClosedUnderLocalUnitary
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOrbit

theorem mem_ngSet_iff {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u') :
    t ∈ (Y.tO u u').ngSet ↔ t.G ≠ 0 ∧ ¬ t.generic := by
  show (if t.G = 0 then (0:ℝ) else 1) ≠ 0 ∧ ¬ t.generic ↔ _
  by_cases h : t.G = 0 <;> simp [h]

theorem mem_genSet_iff {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u') :
    t ∈ (Y.tO u u').genSet ↔ t.G ≠ 0 ∧ t.generic := by
  show (if t.G = 0 then (0:ℝ) else 1) ≠ 0 ∧ t.generic ↔ _
  by_cases h : t.G = 0 <;> simp [h]

theorem finrank_Vp_eq (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Ranks.r, Ranks.rS]
  omega

theorem img_inv_img {D : D7} (Z : LocDat D) (p : PlF D) (h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
    (A : Submodule (Z.M p).L.O (Vp D p)) : LocNG.img h⁻¹ (LocNG.img h A) = A := by
  ext x
  simp only [LocNG.img, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨h x, ⟨x, hx, rfl⟩, by simp⟩

theorem noBB_of_moved {D : D7} (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D)
    (hRel : (FP p).RelG (LocNG.theta (Z.M p))) (h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hh : h ∈ (FP p).UW0)
    (A B : Submodule (Z.M p).L.O (Vp D p)) (hAB : LocNG.img h A = B)
    (hB : ∀ d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = B → ¬ LocNG.BBne (H := locH Z p) τ) :
    ∀ d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = A → ¬ LocNG.BBne (H := locH Z p) τ := by
  intro d τ hτ hL hbb
  obtain ⟨act, hmv, -⟩ := GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_eq D p) hRel
  have hm : LocNG.Datum.Moves h d (act.smul ⟨h, hh⟩ d) := (hmv ⟨h, hh⟩ d _).2 rfl
  obtain ⟨h1, h2⟩ := GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_eq D p) hRel h hh d _ τ hτ hm
  exact hB _ _ h1 (by show LocNG.img h τ.abelian₂ = B; rw [hL, hAB]) (h2.2 hbb)

theorem closed_ng_gen : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → LocClosed F F' Z FP (Y.tO u u').ngSet ∧ LocClosed F F' Z FP (Y.tO u u').genSet ∧ (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ ∀ t ∈ (Y.tO u u').genSet, t.G ≠ 0 := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel
  have gen := fun t Λ hT => GlobalTheory.T.isGenericTerm_iff_no_localDefect_baseFrames D X Y u u' F F' w hw hG Z FP hB hRel t Λ hT
  have pt := fun t Λ hT => (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hw hG t Λ hT).1
  have back : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D), TG F F' t Λ → TG F F' t' Λ' →
      (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t'.generic → t.generic := by
    intro t t' Λ Λ' hT hT' hloc hg
    rw [gen t Λ hT]
    rw [gen t' Λ' hT'] at hg
    intro p
    obtain ⟨h, hh, hAB⟩ := hloc p
    exact noBB_of_moved Z FP p (hRel p) h hh _ _ hAB (hg p)
  have fwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D), TG F F' t Λ → TG F F' t' Λ' →
      (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t.generic → t'.generic := by
    intro t t' Λ Λ' hT hT' hloc hg
    rw [gen t' Λ' hT']
    rw [gen t Λ hT] at hg
    intro p
    obtain ⟨h, hh, hAB⟩ := hloc p
    exact noBB_of_moved Z FP p (hRel p) h⁻¹ (inv_mem hh) _ _ (by rw [← hAB, img_inv_img]) (hg p)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t t' Λ Λ' hT hT' hloc ht
    rw [mem_ngSet_iff] at ht ⊢
    exact ⟨pt t' Λ' hT', fun hg => ht.2 (back t t' Λ Λ' hT hT' hloc hg)⟩
  · intro t t' Λ Λ' hT hT' hloc ht
    rw [mem_genSet_iff] at ht ⊢
    exact ⟨pt t' Λ' hT', fwd t t' Λ Λ' hT hT' hloc ht.2⟩
  · intro t ht
    exact ((mem_ngSet_iff Y u u' t).1 ht).1
  · intro t ht
    exact ((mem_genSet_iff Y u u' t).1 ht).1

end GlobalTheory.LocOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEqStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ↔ G.datOf (c.lat (ρ * n) t.lam) = G.datOf (c.lat ρ t₀.lam)) := by
  first | exact @GlobalTheory.HL.DatEq.row_eq_iff_datOf_eq | exact GlobalTheory.HL.DatEq.row_eq_iff_datOf_eq | (intros; apply GlobalTheory.HL.DatEq.row_eq_iff_datOf_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRowSameWeightSameLocalData
section
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.TermSame

theorem same : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → Formalism.L2.SG.TermOp.wt t = Formalism.L2.SG.TermOp.wt t' ∧ (nmlOf Y u u' t = nmlOf Y u u' t' → ∀ (p : PlF D) (P : LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), P.RelG (LocNG.theta (Y.M p)) → ∀ d, Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) → Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.toTerm.lam (lf D (X.Fu u)) (Quot.out t'.toTerm.cls).1 (Tu D u) (Tu D u'))) := by
  intro D X Y u u' t t' hG hr
  have hl : t.lam = t'.lam := congrArg (fun r => (r.1 : {Λ // Λ ∈ Y.what₂ u}).1) hr
  have hl' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : {Λ // Λ ∈ Y.what₂ u'}).1) hr
  have hi : iotaOf Y.TR (Y.cs u) (Y.cs u') t = iotaOf Y.TR (Y.cs u) (Y.cs u') t' := congrArg (fun r => r.2.2) hr
  refine ⟨by simp only [Formalism.L2.SG.TermOp.wt, hl, hl'], fun hnml p P hP d hO => ?_⟩
  have hΛ : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hΛ' : IsRowLat D (X.Fu u) t'.lam := (Y.rowsOK u).1 t'.lam t'.mem
  have one_nrat : ∀ {T : D.host.E} (F : LFlag (VS D) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F := by
    intro T F
    have h := one_mem_NLam (⊤ : Submodule (𝓞 D.host.E) (VS D).V) F
    exact ⟨h.1.1, h.2.1, h.2.2⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hnml]
    exact ⟨1, one_nrat _, 1, one_nrat _, by simp⟩
  obtain ⟨n, hn, n', hn', hlin⟩ := hmem
  have h0 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have h1 : t'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t'.rep.2.2.1
  have hmN : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := by
    have h := GlobalTheory.HL.CosetConst.conj_nlam_top (G := lf D (X.Fu u')) h0 hn'
    exact ⟨h.1.1, h.2.1, h.2.2⟩
  have hβ : n * (t.lin * n' * t.lin⁻¹) = t'.lin * t.lin⁻¹ := by
    rw [hlin]; simp only [mul_assoc]
  have hgm : Formalism.HermitianLatticesTheory.gmap (n * (t.lin * n' * t.lin⁻¹)) t.lam = t.lam := by
    have hg0 : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    have hg1 : Formalism.HermitianLatticesTheory.gmap t'.lin t'.lam' = t'.lam := t'.rep.2.2.2.1
    rw [hβ, Formalism.L2.SG.Pf.MainEqClass.gmap_mul', Formalism.L2.SG.Pf.MainEqClass.gmap_inv_of' hg0, hl', hg1, hl]
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    rw [hβ]
    show frame (mapLF t'.lin (lf D (X.Fu u'))) a = (t'.lin * t.lin⁻¹) (frame (mapLF t.lin (lf D (X.Fu u'))) a)
    rw [GlobalTheory.HL.CosetConst.frame_mapLF h1, GlobalTheory.HL.CosetConst.frame_mapLF h0]
    show _ = t'.lin (t.lin.symm (t.lin _))
    rw [LinearEquiv.symm_apply_apply]
  have hI := Formalism.L2.SG.Pf.iotaDict_fwd Y t t' hl hl' hi
  rw [← hβ] at hI
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hΛ
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).1
  have hrel : DCRel t.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 t.frame :=
    (hEq (Quot.out t.toTerm.cls) ⟨t.frame, t.rep.2.2.2.2⟩).1 (Quot.out_eq _)
  have hR0 : Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 ≠ 0 := hG
  have hGt : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    have e : Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 = Gval (lf D (X.Fu u)) t.frame :=
      hGF (Quot.out t.toTerm.cls) ⟨t.frame, t.rep.2.2.2.2⟩ hrel
    rw [← e]; exact hR0
  have hGt' : Gval (lf D (X.Fu u)) t'.frame ≠ 0 := by
    have hh : t'.lin = n⁻¹⁻¹ * t.lin * n' := by rw [inv_inv]; exact hlin
    rw [← GlobalTheory.HL.CosetConst.G_eq_frames t t' (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn) hn' hh]
    exact hGt
  have s1 := (GlobalTheory.T.localData_globalTerm_independent_of_representative D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t.lam hΛ
    (Quot.out t.toTerm.cls).1 t.frame (Quot.out t.toTerm.cls).2 t.rep.2.2.2.2 hR0 hrel p P hP d).1 hO
  have hpd' : PD D t.lam (lf D (X.Fu u)) u' t'.frame := by rw [hl]; exact t'.rep.2.2.2.2
  have s2 := GlobalTheory.T.global_terms_same_doubleCoset_same_local_data D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t.lam hΛ t.frame t'.frame
    t.rep.2.2.2.2 hpd' hGt n hn _ hmN hgm hfr hI p P hP d s1
  have s3 : Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.lam (lf D (X.Fu u)) t'.frame (Tu D u) (Tu D u')) := by
    rw [← hl]; exact s2
  have hEq' := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t'.lam hΛ'
  have hrel' : DCRel t'.lam (lf D (X.Fu u)) t'.frame (Quot.out t'.toTerm.cls).1 :=
    (hEq' ⟨t'.frame, t'.rep.2.2.2.2⟩ (Quot.out t'.toTerm.cls)).1 (Quot.out_eq _).symm
  exact (GlobalTheory.T.localData_globalTerm_independent_of_representative D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t'.lam hΛ' t'.frame
    (Quot.out t'.toTerm.cls).1 t'.rep.2.2.2.2 (Quot.out t'.toTerm.cls).2 hGt' hrel' p P hP d).1 s3

end GlobalTheory.LocOver.TermSame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRatStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAutomorphicCounting_of_compactDualVolumeRatio : GlobalTheory.FlagMeas.VolumeStep → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  first | exact @GlobalTheory.CountFinal.countingTheorem_of_volumeStep | exact GlobalTheory.CountFinal.countingTheorem_of_volumeStep | (intros; apply GlobalTheory.CountFinal.countingTheorem_of_volumeStep <;> assumption)
end


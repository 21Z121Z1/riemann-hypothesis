import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0715
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0724
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0727
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0725
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvHodgeMetricGramMumfordGoodGrowthBoundaryChart
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HodgeInvGood

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem conn_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E) (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : ∀ᶠ x in 𝓝 z, (H x).IsSymm) (ξ : E) : conn (fun x => (H x)⁻¹) z ξ = -(conn H z ξ)ᵀ := by
  rw [conn_congr (H' := fun x => dualGram (H x))
    (hs.mono fun x hx => by simp only [dualGram, transpose_nonsing_inv, hx.eq]) ξ, conn_dual h hu]

theorem norm_mul_apply_le {g : ℕ} (P Q : Matrix (Fin g) (Fin g) ℂ) (p q : ℝ) (hP : ∀ i j, ‖P i j‖ ≤ p)
    (hQ : ∀ i j, ‖Q i j‖ ≤ q) (i j : Fin g) : ‖(P * Q) i j‖ ≤ g * (p * q) := by
  rw [mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ (Finset.univ : Finset (Fin g)), ‖P i k * Q k j‖ ≤ p * q := fun k _ => by
    rw [norm_mul]
    exact mul_le_mul (hP i k) (hQ k j) (norm_nonneg _) ((norm_nonneg _).trans (hP i k))
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
  simp

theorem ofLp_coordVec {n : ℕ} (k : Fin n) : (coordVec k).ofLp = Pi.single k (1 : ℂ) := by simp

end GlobalTheory.HodgeInvGood

namespace GlobalTheory.HodgeInvGood

open GlobalTheory.HermFrame

theorem norm_apply_le_opNorm {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    ‖A i j‖ ≤ opNorm 1 1 A := by
  have h := gnorm_mulVec_le (PosDef.one (n := Fin g) (R := ℂ)) PosSemidef.one A (Pi.single j 1)
  have h1 : gnorm (1 : Matrix (Fin g) (Fin g) ℂ) (Pi.single j 1) = 1 := by
    rw [gnorm, form_single]; simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  set w := A *ᵥ Pi.single j 1 with hw
  have hwi : w i = A i j := by simp [hw, mulVec_single_one]
  rw [gnorm, form, one_mulVec, ← hwi]
  apply Real.le_sqrt_of_sq_le
  have e : w ⬝ᵥ star w = ∑ k, ((‖w k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)

end GlobalTheory.HodgeInvGood

namespace GlobalTheory.HodgeInvGood

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem inv_hodgeGram_goodBound : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ (c : ℝ) (N : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B v.ofLp).PosDef ∧ (∀ i k, ContDiffAt ℝ 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹ i k) v) ∧ GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c N (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹) v := by
  intro n a ha g rk τ₀ B hP
  obtain ⟨ρ, c₀, C, hρ0, hρ2, hc₀, h1, h2, h3, h4⟩ :=
    GlobalTheory.HodgeChartRow.hodgeChartBounds_of_schur_lemW GlobalTheory.T.schur_complement_block_quadratic_lower_bound GlobalTheory.T.exists_uniform_bound_smul_inv_add_sum_mul_mulVec n a g rk ha τ₀ B hP
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set D : ℝ := C' * (1 + 1 / Real.log 2 + 1 / (2 * Real.pi)) with hD
  have hD0 : 0 ≤ D := mul_nonneg hC'0 (by positivity)
  set c : ℝ := max (max ((1 / c₀) * (1 / Real.log 2) ^ g) ((g.factorial : ℝ) * D ^ g))
    (max (5 * C') (50 * g * C' ^ 2)) with hc
  refine ⟨ρ, hρ0, hρ2, c, if a = 0 then 0 else g, fun v hv => ?_⟩
  set z : Fin n → ℂ := v.ofLp with hzdef
  set S : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb ha) with hS
  set Y := hodgeGram ha τ₀ B with hY
  set Yv : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ := fun u => Y u.ofLp with hYv
  set s : ℝ := ∑ k ∈ S, |Real.log ‖v k‖| with hs
  have hz1 : z ∈ punctured ha 1 := ⟨fun k => (hv.1 k).trans_le (hρ2.trans (by norm_num)), hv.2⟩
  have hpd : (Y z).PosDef := (h4 z hv).1
  have hu : IsUnit (Y z).det := (isUnit_iff_isUnit_det _).1 hpd.isUnit
  obtain ⟨hYinf, -, hdd⟩ := GlobalTheory.HodgeGramLocal.hodgeGram_local n a g rk ha τ₀ B hP z hz1

  let φ : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ) := (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap
  have hφ : ∀ u, φ u = u.ofLp := fun u => rfl
  have hφd : ∀ ξ, fderiv ℂ φ v ξ = ξ.ofLp := fun ξ => by rw [φ.fderiv]; rfl
  have hY2 : MContDiffAt 2 Y z := hYinf.of_le (by norm_cast)
  have hYv2 : MContDiffAt 2 Yv v := fun i j =>
    (hY2 i j).comp v ((φ.restrictScalars ℝ).contDiff.contDiffAt)

  have hBsymm : ∀ i (j k : Fin g), (B i k j : ℝ) = B i j k := fun i j k => by
    simpa using (hP.psd i).isHermitian.apply j k
  have hsymR : ∀ x ∈ polydisc n 1, (imPeriod ha τ₀ B x).IsSymm := fun x hx =>
    IsSymm.ext fun j k => by simp [imPeriod, Matrix.sum_apply, hBsymm, (hP.symm x hx).apply]
  have hnb : ∀ᶠ u in 𝓝 v, u.ofLp ∈ polydisc n 1 :=
    φ.continuous.continuousAt.eventually_mem ((GlobalTheory.HodgeChartRow.isOpen_polydisc n 1).mem_nhds hz1.1)
  have hevS : ∀ᶠ u in 𝓝 v, (Yv u).IsSymm := hnb.mono fun u hu' =>
    IsSymm.ext fun j k => by simp [Yv, Y, hodgeGram, (hsymR _ hu').apply j k]
  have hevH : ∀ᶠ u in 𝓝 v, (Yv u).IsHermitian := hnb.mono fun u hu' => by
    ext j k; simp [Yv, Y, hodgeGram, conjTranspose_apply, (hsymR _ hu').apply j k]
  have hddv : ∀ ξ η, mddbar Yv v ξ η = 0 := fun ξ η => by
    ext i j
    have := GlobalTheory.ddbar_comp_holo (u := fun x => Y x i j) (φ := φ) (z := v) (hY2 i j) φ.contDiff.contDiffAt ξ η
    simp only [mddbar_apply]
    rw [show (fun x => Yv x i j) = fun x => Y (φ x) i j from rfl, this, hφd, hφd]
    have h0 := congrFun (congrFun (hdd ξ.ofLp η.ofLp) i) j
    simp only [mddbar_apply] at h0
    exact h0
  have hconn : ∀ ξ, conn Yv v ξ = conn Y z ξ.ofLp := fun ξ => by
    rw [show Yv = fun x => Y (φ x) from rfl, conn_comp_holo (hY2.of_le (by norm_num)) φ.differentiableAt ξ, hφd]
    rfl

  set Kf : Fin n → ℝ := fun k => C' * gnorm (poincareGram a z) (Pi.single k 1) with hKf
  have hKf0 : ∀ k, 0 ≤ Kf k := fun k => mul_nonneg hC'0 (gnorm_nonneg _ _)
  have hKe : ∀ k i j, ‖conn Y z (Pi.single k 1) i j‖ ≤ Kf k := fun k i j =>
    (norm_apply_le_opNorm _ i j).trans (((h3 z hv).2.2 _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (gnorm_nonneg _ _)))
  have hw0 : ∀ k, 0 ≤ poinWt S v k := fun k => by
    unfold poinWt; split_ifs <;> positivity
  have hKw : ∀ k, Kf k * poinWt S v k ≤ 5 * C' := fun k => by
    have h5 := GlobalTheory.T.poincareNorm_coordinateVector_mul_length_le_five n a ha ρ hρ2 v hv k
    calc Kf k * poinWt S v k = C' * (gnorm (poincareGram a z) (Pi.single k 1) * poinWt S v k) := by
          simp only [hKf]; ring
      _ ≤ C' * 5 := mul_le_mul_of_nonneg_left h5 hC'0
      _ = 5 * C' := by ring
  have hCe : ∀ k i j, ‖conn Yv v (coordVec k) i j‖ ≤ Kf k := fun k i j => by
    rw [hconn, ofLp_coordVec]; exact hKe k i j
  have hcG : ∀ ξ, conn (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) v ξ = -(conn Yv v ξ)ᵀ :=
    conn_inv Yv v (hYv2.of_le one_le_two) hu hevS
  have hcurvG : ∀ ξ η, curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) v ξ η =
      -((conn Yv v η)ᵀᴴ * conn Yv v ξ)ᵀ := GlobalTheory.T.chernCurvature_inverse_realSymmetric_gram Yv v hYv2 hu hevS hevH hddv
  have hdelG : ∀ ξ η, mdel (fun x => conn (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) x η) v ξ -
      mdel (fun x => conn (fun u : ReciprocityTheory.L2DbarEstimates.V n => (Y u.ofLp)⁻¹) x ξ) v η =
      -(conn Yv v η * conn Yv v ξ - conn Yv v ξ * conn Yv v η)ᵀ := GlobalTheory.T.holomorphicDeriv_chernConnection_inverseSymmetricGram Yv v hYv2 hu hevS

  obtain ⟨hts, hlog⟩ := GlobalTheory.T.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo n a ha ρ hρ2 v hv
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc0 : 0 ≤ c := (by positivity : (0:ℝ) ≤ 5 * C').trans ((le_max_left _ _).trans (le_max_right _ _))
  have hcA : (1 / c₀) * (1 / Real.log 2) ^ g ≤ c := (le_max_left _ _).trans (le_max_left _ _)
  have hcB : (g.factorial : ℝ) * D ^ g ≤ c := (le_max_right _ _).trans (le_max_left _ _)
  have hc5 : 5 * C' ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hc50 : 50 * g * C' ^ 2 ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hE : 1 / c₀ ≤ c * s ^ (if a = 0 then 0 else g) ∧
      (g.factorial : ℝ) * (C' * (1 + s / (2 * Real.pi))) ^ g ≤ c * s ^ (if a = 0 then 0 else g) := by
    by_cases ha0 : a = 0
    · rw [if_pos ha0, pow_zero, mul_one]
      have hs' : s / (2 * Real.pi) = 0 := by rw [← hts]; subst ha0; simp
      refine ⟨?_, ?_⟩
      · refine le_trans ?_ hcA
        have : (1 : ℝ) ≤ (1 / Real.log 2) ^ g := one_le_pow₀ (by rw [le_div_iff₀ hl2]; linarith)
        have hc1 : 0 ≤ 1 / c₀ := by positivity
        nlinarith
      · rw [hs', add_zero, mul_one]
        refine le_trans ?_ hcB
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC'0 ?_ g) (Nat.cast_nonneg _)
        rw [hD]
        have : (1 : ℝ) ≤ 1 + 1 / Real.log 2 + 1 / (2 * Real.pi) := by
          have : 0 ≤ 1 / Real.log 2 := by positivity
          have : 0 ≤ 1 / (2 * Real.pi) := by positivity
          linarith
        nlinarith
    · rw [if_neg ha0]
      have hs2 : Real.log 2 ≤ s := hlog (Nat.pos_of_ne_zero ha0)
      refine ⟨?_, ?_⟩
      · calc 1 / c₀ = ((1 / c₀) * (1 / Real.log 2) ^ g) * Real.log 2 ^ g := by
              rw [mul_assoc, ← mul_pow, one_div_mul_cancel hl2.ne', one_pow, mul_one]
          _ ≤ c * s ^ g := mul_le_mul hcA (pow_le_pow_left₀ hl2.le hs2 g) (by positivity) hc0
      · have h1s : 1 ≤ s / Real.log 2 := (one_le_div hl2).2 hs2
        have hM : C' * (1 + s / (2 * Real.pi)) ≤ D * s := by
          have e : D * s = C' * s + C' * (s / Real.log 2) + C' * (s / (2 * Real.pi)) := by
            rw [hD]; ring
          have : C' ≤ C' * (s / Real.log 2) := le_mul_of_one_le_right hC'0 h1s
          have : 0 ≤ C' * s := mul_nonneg hC'0 hs0
          rw [e]; nlinarith
        have hM0 : 0 ≤ C' * (1 + s / (2 * Real.pi)) := by positivity
        calc (g.factorial : ℝ) * (C' * (1 + s / (2 * Real.pi))) ^ g ≤ (g.factorial : ℝ) * (D * s) ^ g :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hM g) (Nat.cast_nonneg _)
          _ = ((g.factorial : ℝ) * D ^ g) * s ^ g := by rw [mul_pow]; ring
          _ ≤ c * s ^ g := mul_le_mul_of_nonneg_right hcB (by positivity)
  refine ⟨hpd, fun i k => (hYv2.inv hu) i k, ?_⟩
  refine ⟨fun i j => ?_, ?_, fun k i j => ?_, fun k l i j => ?_, fun k l i j => ?_⟩
  · show ‖((imPeriod ha τ₀ B z).map Complex.ofReal)⁻¹ i j‖ ≤ _
    exact (GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef g (imPeriod ha τ₀ B z) c₀ hc₀ (h1 z hv) i j).trans hE.1
  · show ‖((Y z)⁻¹).det‖⁻¹ ≤ _
    rw [det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, inv_inv]
    have hT0 : 0 ≤ 1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)) := by
      have : 0 ≤ ∑ i : Fin a, tlog (z (Fin.castLE ha i)) :=
        Finset.sum_nonneg fun i _ => (tlog_pos (hv.2 i) (hz1.1 _)).le
      linarith
    have hPSD : (imPeriod ha τ₀ B z).PosSemidef := by
      have := (h1 z hv).add (PosSemidef.one.smul hc₀.le)
      simpa using this
    have hMPSD : ((C' * (1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)))) • (1 : Matrix (Fin g) (Fin g) ℝ) -
        imPeriod ha τ₀ B z).PosSemidef := by
      have := (h2 z hv).add ((PosSemidef.one (n := Fin g) (R := ℝ)).smul
        (mul_nonneg (sub_nonneg.2 (le_max_left C 0)) hT0))
      convert this using 1
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hdet := GlobalTheory.T.norm_det_ofReal_le_factorial_mul_pow g (imPeriod ha τ₀ B z) _ (mul_nonneg hC'0 hT0) hPSD hMPSD
    refine hdet.trans ?_
    rw [hts]; exact hE.2
  · rw [hcG, Matrix.neg_apply, transpose_apply, norm_neg]
    exact (mul_le_mul_of_nonneg_right (hCe k j i) (hw0 k)).trans ((hKw k).trans hc5)
  · rw [hcurvG, Matrix.neg_apply, transpose_apply, norm_neg]
    have hP : ∀ p q, ‖(conn Yv v (coordVec l))ᵀᴴ p q‖ ≤ Kf l := fun p q => by
      rw [conjTranspose_apply, transpose_apply, norm_star]; exact hCe l p q
    have hprod := norm_mul_apply_le _ _ (Kf l) (Kf k) hP (hCe k) j i
    have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
    calc ‖((conn Yv v (coordVec l))ᵀᴴ * conn Yv v (coordVec k)) j i‖ * (poinWt S v k * poinWt S v l)
        ≤ g * (Kf l * Kf k) * (poinWt S v k * poinWt S v l) :=
          mul_le_mul_of_nonneg_right hprod (mul_nonneg (hw0 k) (hw0 l))
      _ = g * ((Kf k * poinWt S v k) * (Kf l * poinWt S v l)) := by ring
      _ ≤ g * ((5 * C') * (5 * C')) := mul_le_mul_of_nonneg_left
          (mul_le_mul (hKw k) (hKw l) (mul_nonneg (hKf0 l) (hw0 l)) (by positivity)) hg0
      _ ≤ 50 * g * C' ^ 2 := by nlinarith [sq_nonneg C']
      _ ≤ c := hc50
  · rw [hdelG, Matrix.neg_apply, transpose_apply, norm_neg, Matrix.sub_apply]
    have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
    have hA := norm_mul_apply_le _ _ (Kf l) (Kf k) (hCe l) (hCe k) j i
    have hB := norm_mul_apply_le _ _ (Kf k) (Kf l) (hCe k) (hCe l) j i
    calc ‖(conn Yv v (coordVec l) * conn Yv v (coordVec k)) j i - (conn Yv v (coordVec k) * conn Yv v (coordVec l)) j i‖
          * (poinWt S v k * poinWt S v l)
        ≤ (g * (Kf l * Kf k) + g * (Kf k * Kf l)) * (poinWt S v k * poinWt S v l) :=
          mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hA hB)) (mul_nonneg (hw0 k) (hw0 l))
      _ = 2 * g * ((Kf k * poinWt S v k) * (Kf l * poinWt S v l)) := by ring
      _ ≤ 2 * g * ((5 * C') * (5 * C')) := mul_le_mul_of_nonneg_left
          (mul_le_mul (hKw k) (hKw l) (mul_nonneg (hKf0 l) (hw0 l)) (by positivity)) (by positivity)
      _ = 50 * g * C' ^ 2 := by ring
      _ ≤ c := hc50

end GlobalTheory.HodgeInvGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenFrame

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

abbrev Os (s : ReciprocityTheory.Aut.SplitPlace L) : Type := ↥(s.v.adicCompletionIntegers (maximalRealSubfield L))

structure IsResidue (s : ReciprocityTheory.Aut.SplitPlace L) {k : Type} [CommRing k] (φ : Os s →+* k) : Prop where
  surj : Function.Surjective φ
  ker : ∀ x : Os s, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1

def IsCompOf (s : ReciprocityTheory.Aut.SplitPlace L) (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)) : Prop :=
  ∀ a c, ((y.val a c : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = (s.loc n κ).val a c

end Local

def colMat {k : Type} [CommRing k] {n : ℕ} (v : Fin n → k) (m : Fin n) : Matrix (Fin n) (Fin n) k :=
  1 + Matrix.vecMulVec v (Pi.single m 1)

variable {D : D7}

def FrameRed {V : HSp D} {n : ℕ} (hn : V.rank = n) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D))
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)) : Prop :=
  ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ y, IsCompOf s κ y → ∀ a c : Fin n,
    (redFn β s.w (finE V (P.ψ κ))).val (Fin.cast hn.symm a) (Fin.cast hn.symm c) =
      (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val a c

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

def CenRead (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) : Prop :=
  ∀ (i : Fin D.R.m) (t : T) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g)) → ∀ x,
      D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) =
        D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (((A3.A.fam.L i t).S.lvlOp (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P
          (A3.A.fam.lvlA F.P0 F.ψ0).ψ a).mulVec x))

end GlobalTheory.CenFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGoodSplitHeckePlaceOfSplitNotExcludedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodSplitHeckePlace_of_split_not_excluded : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (x : St P) (v : PlE (Dof x).host), IsSplitPl (Dof x).host v → v ∉ SbD (Dof x) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace x.m.z.R.toRealDat v := by
  first | exact @GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off | exact GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off | (intros; apply GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfMulIsHomogeneousOfNeZeroRight
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop

theorem isHomogeneous_of_mul_isHomogeneous_right {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ)
    (hQ : Q ≠ 0) (hQh : Q.IsHomogeneous b) (hPQ : (P * Q).IsHomogeneous (a + b)) :
    P.IsHomogeneous a := by
  have key : ∀ k, homogeneousComponent (k + b) (P * Q) = homogeneousComponent k P * Q := by
    intro k
    conv_lhs => rw [← sum_homogeneousComponent P]
    rw [Finset.sum_mul, map_sum]
    have hterm : ∀ i, homogeneousComponent (k + b) (homogeneousComponent i P * Q)
        = if i = k then homogeneousComponent i P * Q else 0 := by
      intro i
      have hm : homogeneousComponent i P * Q ∈ homogeneousSubmodule σ ℝ (i + b) :=
        (homogeneousComponent_isHomogeneous i P).mul hQh
      rw [homogeneousComponent_of_mem hm]
      by_cases h : i = k
      · simp [h]
      · have : k + b ≠ i + b := by omega
        rw [if_neg this, if_neg h]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · subst_vars; rfl
    · simp only [Finset.mem_range, not_lt] at h
      rw [homogeneousComponent_eq_zero k P (by omega), zero_mul]
  have hzero : ∀ k, k ≠ a → homogeneousComponent k P = 0 := by
    intro k hk
    have h1 : homogeneousComponent (k + b) (P * Q) = 0 := by
      have : k + b ≠ a + b := by omega
      have e := homogeneousComponent_of_mem (m := k + b) (hPQ : P * Q ∈ homogeneousSubmodule σ ℝ (a + b))
      rw [e, if_neg this]
    rw [key] at h1
    exact (mul_eq_zero.mp h1).resolve_right hQ
  rw [← sum_homogeneousComponent P]
  apply IsHomogeneous.sum
  intro k _
  by_cases hk : k = a
  · subst hk; exact homogeneousComponent_isHomogeneous k P
  · rw [hzero k hk]; exact isHomogeneous_zero _ _ _

example : ∀ {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ), Q ≠ 0 → Q.IsHomogeneous b → (P * Q).IsHomogeneous (a + b) → P.IsHomogeneous a :=
  fun P Q a b => isHomogeneous_of_mul_isHomogeneous_right P Q a b

end GlobalTheory.GrassTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMarkedBalancedIntFormPullbackIffSplitSurjectioStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) (X X₁ : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (s : X₁ →ₗ[O] X), (∀ a, r (s a) = a) → ∀ β : LinearMap.BilinForm ℤ X₁, IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β := by
  first | exact @GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff | exact GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff | (intros; apply GlobalTheory.PolFan.Mark.SplitPull.isMarked_pull_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMonHomOfSquaredDegenerationDataFunctionalEquatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_of_squaredDegenerationData_functionalEquation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → (¬ ∀ j, (f 0).f j = 0) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  first | exact @GlobalTheory.PsiFourth.key | exact GlobalTheory.PsiFourth.key | (intros; apply GlobalTheory.PsiFourth.key <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveBalancedFormPrimitiveAmongIntFormsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveBalancedForm_primitive_among_intForms : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (β : LinearMap.BilinForm ℤ X) (hβ : β ∈ balForms bar X), IsPrim bar (⟨β, hβ⟩ : balForms bar X) →
  ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  first | exact @GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq | exact GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq | (intros; apply GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayPrimeOfNormIntegerCongruentOneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRayPrime_of_norm_integer_congruent_one : ∀ (D : D7) (i : Fin 2) (jE : D.host.E →+* Qb), (D.host.g i).Prime → (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E) ∧ (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)}) → IsRayPrime (GlobalTheory.HeightCounting.KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g i) := by
  first | exact @GlobalTheory.RayPrimeOfNorm.isRayPrime_of_norm_eq | exact GlobalTheory.RayPrimeOfNorm.isRayPrime_of_norm_eq | (intros; apply GlobalTheory.RayPrimeOfNorm.isRayPrime_of_norm_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMFieldStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAdmissibleFan_of_cellMult_one_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → maxMult H.bar q φ ≤ 1 → IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ := by
  first | exact @GlobalTheory.PolFan.smoothEnd | exact GlobalTheory.PolFan.smoothEnd | (intros; apply GlobalTheory.PolFan.smoothEnd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelTaylorSeriesPreservedDivisionLatticeChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTaylorSeries_preserved_divisionLatticeChange : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z)) (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) (k : KerT t Y Gy ker) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), EntC k → ∃ k' : KerT (DivTr.colTTr w Z N h t) (divTr (D := w.D Z) N h Y) (latTr (D := w.D Z) N h Gy) (kerTr w Z N h ker), EntC k' := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.kerT_entC_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.kerT_entC_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.kerT_entC_setDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepAtlasRefinement
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

theorem locMaps_of_grel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → q ≫ PSpace.str _ _ = f ≫ Z.π ≫ (Y Z.i).s → Lifts (Z.π ≫ (Y Z.i).s) f q → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → LocMaps Z₁ A' := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hpW t Z g D hg hL A X' f q ty' A' hA hR hq hLift Z₁ g₀ hg₀ hH K _ w hw
  obtain ⟨τ, mu, u, hT, hπ, hZ₁, hZ⟩ := ((isMap_iff _ _ _).1 hg₀).2 K w hw
  have hAZ : A.FlagAt (w ≫ g₀) (fun σ j => u σ j ≫ mu.φ) := (hA K _ _).2 hZ
  obtain ⟨y, hyπ, hA'y⟩ := Atlas.FlagAt.exists_point hAZ A'
  have htan : ∀ σ i, IsTanAtG (Y Z.i).t ((y ≫ f) ≫ Z.π) (u σ i ≫ mu.φ) := by
    obtain ⟨a, φ, -, hf, -⟩ := id hA'y
    rw [Category.assoc]
    exact fun σ i => (hf.1 σ i).1
  obtain ⟨U, hU⟩ := exists_up htan
  have hR' := (hR K y U).1 (hU ▸ hA'y)
  have hyf : y ≫ f = w ≫ g₀ := Atlas.FlagAt.point_eq (hU ▸ hR'.1) hAZ (by rw [Category.assoc, hyπ])
  refine ⟨y, ⟨τ, mu, u, hT, hyπ.trans hπ, hZ₁, hA'y⟩, ?_⟩
  intro R _ _ _ _ _ _ z hz
  obtain ⟨α, hα₀⟩ := D.C.cover ((z ≫ g₀) (IsLocalRing.closedPoint R))
  have hα : ⊤ ≤ (z ≫ g₀) ⁻¹ᵁ D.C.B α :=
    ((IsLocalRing.closed_point_mem_iff (U := (z ≫ g₀) ⁻¹ᵁ D.C.B α)).1 hα₀).ge
  have hyz : y ≫ f = spMap (algebraMap R K) ≫ z ≫ g₀ := by rw [hyf, ← hz, Category.assoc]
  have hy : ⊤ ≤ (y ≫ f) ⁻¹ᵁ D.C.B α := by
    rw [hyz]
    exact GlobalTheory.FlagMod.le_preimage_map (z ≫ g₀) hα le_top
  obtain ⟨n', a, a', h₁, h₂, hann⟩ := GlobalTheory.T.lattice_step_holds_pullback E H Dw Xo p W Y i₀ hp hpW t Z g D hg hL Z₁ g₀ hg₀ hH R K z α hα
  obtain ⟨y₀, hy₀, hyq⟩ := GlobalTheory.T.carrier_matrix_transfer _ Z.X X' (Z.π ≫ (Y Z.i).s) D.C D.N t.k D.Em f q hq R K (z ≫ g₀) α hα n' a a' y hy _
    h₁ h₂ hyz (hR'.2 α hy) fun l j hj =>
      hann τ mu u hT (hz ▸ hZ₁) (y ≫ f) hyz hy (U t.σ (Fin.castLE t.le l)) (Fin.castLE t.le l) l.2
        (congrFun (congrFun hU t.σ) (Fin.castLE t.le l)) j hj
  exact hLift R K (z ≫ g₀) y₀ y hy₀ hyz hyq

end GlobalTheory.GrCl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimePosAllStatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) := by
  first | exact @GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt | exact GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt | (intros; apply GlobalTheory.HeightCounting.Up.PositiveBaseCharge.q0_pos_allSt <;> assumption)
end


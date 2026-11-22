import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareL2InequalityFundamentalSet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.PoincareL2

theorem nfac_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.mpr (div_ne_zero (PoinPf.dmin_ne X hy τ _) (PoinPf.dmin_ne X hy τ _))

theorem poincareNorm_sq_eq_weight_mul_norm_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    ENNReal.ofReal (X.pnorm la P y ^ 2) = ENNReal.ofReal (‖P y‖ ^ 2) * IW.Wpsi X la (fun _ => 0) y := by
  have h1 : X.pnorm la P y ^ 2 = ‖P y‖ ^ 2 * Real.exp (-phla X la y) := by
    rw [PoinPf.exp_neg_phla X la (nfac_pos' X la hy)]
    change (‖P y‖ * X.nfac la y) ^ 2 = _
    ring
  have h2 : IW.Wpsi X la (fun _ => 0) y = ENNReal.ofReal (Real.exp (-(phla X la y + 0))) := by
    simp [IW.Wpsi, hy]
  rw [h1, h2, add_zero, ENNReal.ofReal_mul (by positivity)]

theorem sum_le (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r),
      0 < X.p0 → X.p0 < r → IsOrth X x → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ y ∈ X.dom,
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) := by
  obtain ⟨C1, hC1, hS1⟩ := h1
  obtain ⟨C2, hC2, hS2⟩ := h2
  obtain ⟨C3, hC3, hS3⟩ := h3
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro E _ _ _ r X x hp0 hp0r hx hinj y hy
  have hb := FrameDegreeData.bOf_mem X hy
  have ho : IsOrth X (rmul y (FrameDegreeData.bOf X y)) := FrameDegreeData.ortho_bOf X hy
  set y' := rmul y (FrameDegreeData.bOf X y) with hy'
  have heq : ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) =
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y')) := by
    refine tsum_congr fun γ => ?_
    rw [hy', PoinPf.lact_rmul' γ.1 y (FrameDegreeData.bOf X y),
      PoinPf.kaY_rmul X hx ((PairUnfoldPf.lact_mem_dom_iff X γ.2 y).2 hy) hb]
  rw [heq]
  set S := ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y'))
  set N : ℝ := ((X.Ψ.card : ℝ) * r) ^ 8
  set M := muF X x (Metric.ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x)
  have e1 : M * S ≤ ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N)) :=
    (hS1 E r X x y' hp0 hp0r hx ho hinj).trans (mul_le_mul' le_rfl (hS2 E r X y' hp0 hp0r ho))
  have e3 : ENNReal.ofReal (Real.exp (-(C3 * N))) ≤ M := hS3 E r X x hp0 hp0r hx
  have hone : ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N))) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]; simp
  calc S = (ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N)))) * S := by
          rw [hone, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (C3 * N)) * M) * S := by gcongr
    _ = ENNReal.ofReal (Real.exp (C3 * N)) * (M * S) := by ring
    _ ≤ ENNReal.ofReal (Real.exp (C3 * N)) * (ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N))) := by
          gcongr
    _ = ENNReal.ofReal (Real.exp ((C1 + C2 + C3) * N)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add,
            ← Real.exp_add]
          congr 2; ring

end GlobalTheory.PoincareL2

theorem GlobalTheory.PoincareL2.poincare_l2_of_orthogonal (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ)
    * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF
    X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X
    y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp
    (-(C * ((X.Ψ.card : ℝ) * r) ^
    8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF
    : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X) → ℂ) (P0
    : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la
    (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0)
    (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^
    2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C *
    ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 /
    ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1)
    z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) := by
  obtain ⟨C, hC, hsum⟩ := GlobalTheory.PoincareL2.sum_le h1 h2 h3
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ r X la x x0 FF F P0 hp0 hp0r hx hx0 hFF hinj hFd hP0 hPF
  classical
  set bb : ℝ := (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) with hbbdef
  have hInv : IsInvFn X (fun _ : Frame X.Ψ r => (0 : ℝ)) := fun _ _ _ _ _ _ => rfl
  have hW := (IW.metricW_of GlobalTheory.NormFactor.nfacRmul_holds GlobalTheory.NormFactor.nfacLact_holds ortho_holds
    lu_holds X la (fun _ => 0) hInv (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩).1
  set W := IW.Wpsi X la (fun _ => 0) with hWdef
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x0 hx0
  set C1 := ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) with hC1def
  have hsumY := hsum E r X x hp0 hp0r hx hinj
  set Pd := X.dom.indicator P0 with hPd
  have hPdm : Measurable Pd := PairUnfoldPf.meas_indC X hP0.1.continuousOn
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => ‖Pd y‖ₑ ^ 2 * W y / ENNReal.ofReal (PoinPf.kaY X x bb y) with hψ
  have hψm : Measurable ψ :=
    ((hPdm.enorm.pow_const 2).mul hW.1).div (PoinPf.meas_kaY X x bb).ennreal_ofReal
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    have hyb : rmul y b ∈ X.dom := PoinPf.rmulDom X hb hy
    simp only [hψ, hPd, Set.indicator_of_mem hyb, Set.indicator_of_mem hy, hP0.2 y hy b hb,
      hW.2.1 y hy b hb, PoinPf.kaY_rmul X hx hy hb]
    have hpos : 0 < ‖bchar la b‖ ^ 2 := pow_pos (norm_pos_iff.2 (PoinPf.bchar_ne X la hb)) 2
    have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
    have ht : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hc : ‖bchar la b‖ₑ ^ 2 = ENNReal.ofReal (‖bchar la b‖ ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [enorm_mul, mul_pow, hc]
    congr 1
    rw [ENNReal.div_eq_inv_mul]
    calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ‖P0 y‖ₑ ^ 2 * ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W y)
        = (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) *
            (‖P0 y‖ₑ ^ 2 * W y) := by ring
      _ = ‖P0 y‖ₑ ^ 2 * W y := by rw [ENNReal.mul_inv_cancel h0 ht, one_mul]
  have hpt : ∀ z ∈ FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ≤
      C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
    intro z hz
    have hy : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hFF.2.1 hz
    rw [GlobalTheory.PoincareL2.poincareNorm_sq_eq_weight_mul_norm_sq X la _ hy]
    have hk0 : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ 0 :=
      fun γ => (ENNReal.ofReal_pos.2 (PoinPf.kaY_pos _ _ _ _)).ne'
    have hkt : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ ⊤ :=
      fun _ => ENNReal.ofReal_ne_top
    have hcs := PoinPf.cs_sq (fun γ : X.Γ => ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ)
      (fun γ => ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) hk0 hkt
    have e1 : ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) ≤
        (∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ) ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
      exact pow_le_pow_left₀ zero_le (PoinPf.enorm_poin_le X la P0 _) 2
    have e2 : ∀ γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
        ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) =
          ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
      intro γ
      have hγy : lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hy
      simp only [hψ, hPd, Set.indicator_of_mem hγy, hW.2.2 γ.1 γ.2 _ hy]
      rw [ENNReal.mul_div_right_comm]
    calc ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)
        ≤ ((∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
            ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) * C1) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) :=
          mul_le_mul_of_nonneg_right
            (e1.trans (hcs.trans (mul_le_mul_of_nonneg_left (hsumY _ hy) zero_le))) zero_le
      _ = C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
          rw [← tsum_congr e2, ENNReal.tsum_mul_right]; ring
  have hmeasγ : ∀ γ : X.Γ, AEMeasurable (fun z => ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))
      ((muF X x0).restrict FF) := fun γ =>
    (hψm.comp ((PairUnfoldPf.lact_cont X γ.1).comp (PairUnfoldPf.cpt_cont X x0)).measurable).aemeasurable
  have hunf := PairUnfoldPf.lunfold D FF measInv_holds hx0 hFF ψ hψm hψB
  have hmi := measInv_holds r X x0 x hx0 hx ψ hψm hψB
  have hrhs : ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF] with z hz
    have hyd : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := hz
    simp only [hψ, hPd, Set.indicator_of_mem hyd, hPF z hz, PoinPf.kaY_cpt X hx]
    rw [ENNReal.ofReal_div_of_pos (by unfold kaF; exact Real.exp_pos _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ENNReal.mul_div_right_comm]
  calc ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂muF X x0
      ≤ ∫⁻ z in FF, C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 :=
        setLIntegral_mono' hFF.1 hpt
    _ = C1 * ∑' γ : X.Γ, ∫⁻ z in FF, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeasγ]
    _ = C1 * ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂muF X x0 := by rw [hunf]
    _ = C1 * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
        rw [hmi, hrhs]

theorem GlobalTheory.PoincareL2.poincare_l2_inequality : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) :=
  GlobalTheory.PoincareL2.poincare_l2_of_orthogonal GlobalTheory.T.orbitSum_kernel_ballMeasure_le_integral GlobalTheory.T.lintegral_unitaryKernel_le_exp_pow_eight GlobalTheory.T.invariantMeasure_chartBall_orthonormal_lower_bound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVPointDefinedOverOfCoordsProportional
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem defOver_of_coord_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 →
    ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K)
      (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K),
      GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) →
      (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  intro K _ _ k₀ hk₀ P₀ m hm hm3 hmK z v l r H hr hv
  classical
  let Ix := {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1}
  have Lw := GlobalTheory.abelianSchemeLaws_all
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hm2K : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hmK
  have hcard := (Lw.1.mulN (Sp k₀) P₀ (m ^ 2) hm1).2.2.2.2 K (spMap k₀.subtype) hm2K
  have hfin : Finite Ix := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))

  have hσs : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
    intro σ hσ
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ w.2

  have hfix : ∀ (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) (y : Ix),
      (Over.homMk (spMap σ.toRingHom) (hσs σ hσ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1 = y.1 := by
    intro σ hσ y
    have hdef : DefOver k₀ y.1.left := by
      refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y' : Ix => y'.1.left).subset ?_)
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨⟨(Over.homMk (spMap τ.toRingHom) (hσs τ hτ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1, ?_⟩, ?_⟩
      · rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      · rfl
    obtain ⟨y₀, hy₀⟩ := hdef
    apply Over.OverMorphism.ext
    show spMap σ.toRingHom ≫ y.1.left = y.1.left
    rw [← hy₀, ← Category.assoc, hσs σ hσ]

  obtain ⟨-, U₂, -, U₄⟩ := CoordSep.coord_exists_unique_separate Lw.1 K (Sp k₀) P₀ (spMap k₀.subtype) m hm hmK Ix
    (fun i => i.1) (fun i => i.2)
  have hall : ∀ y : Over.mk (spMap k₀.subtype) ⟶ P₀.A, y ^ m ^ 2 = 1 → ∃ i : Ix, i.1 = y := fun y hy => ⟨⟨y, hy⟩, rfl⟩
  have hv0 : v ≠ 0 := (U₄ hm3 hall z z v H H).2
  have hl : l ≠ 0 := by
    intro h0
    apply hv0
    funext i
    rw [hv i, h0, zero_mul, Pi.zero_apply]
  have horb : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ z.left = z.left := by
    intro σ hσ
    let h : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype) := Over.homMk (spMap σ.toRingHom) (hσs σ hσ)
    have H2 := CoordReduce.isCoordPt_map Lw.2 P₀ σ.toRingHom (hσs σ hσ) (p := fun i : Ix => i.1)
      (fun i => i.2) (w := v) H
    have hp : (fun i : Ix => h ≫ i.1) = fun i => i.1 := funext fun i => hfix σ hσ i
    change GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => h ≫ i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (σ (v i))) at H2
    rw [hp] at H2
    have hσl : σ l ≠ 0 := (map_ne_zero σ).2 hl
    have H3 : GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (v i)) := by
      refine (U₂ (h ≫ z) (fun i => σ (v i)) v H2).2 ⟨Units.mk0 (l / σ l) (div_ne_zero hl hσl), ?_⟩
      funext i
      simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
      rw [hv i, map_mul, hσ _ (hr i)]
      field_simp
    have := (U₄ hm3 hall (h ≫ z) z v H3 H).1
    have e2 := congrArg CommaMorphism.left this
    exact e2
  refine defOver_of_finite_orbit K k₀ hk₀ _ z.left ((Set.finite_singleton z.left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  exact horb σ hσ

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianIsogenyExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PosAHIsog

open GlobalTheory.PullUnifHom GlobalTheory.PullHermitian GlobalTheory.CechPic

variable {A B : Over (Sp ℂ)} [GrpObj A] [GrpObj B]

def trivUnif {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : HolUnif A (LB.triv A.left) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun _ _ => 1
  fr_hol := fun _ => differentiableOn_const 1
  fr_ne := fun _ _ _ => one_ne_zero
  fr_compat := fun i j z h => by
    simp [valAt', valAt, h]

theorem trivUnif_factor {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    IsFactorAH (trivUnif u) 0 (fun _ => 1) :=
  ⟨Matrix.isHermitian_zero, fun _ => by simp, fun l i z hz => by simp [trivUnif]⟩

theorem pull_chart_iff (φ : A ⟶ B) {L : LB B.left} {g : ℕ} (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A))
    (ex' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ B)) (hφ : ∀ z, ex z ≫ φ = ex' z)
    (j : (L.pull φ.left).ι) (z : Fin g → ℂ) :
    ⊤ ≤ (ex z).left ⁻¹ᵁ (L.pull φ.left).U j ↔ ⊤ ≤ (ex' z).left ⁻¹ᵁ L.U (j PUnit.unit) := by
  have keyl : (ex z).left ≫ φ.left = (ex' z).left := by rw [← Over.comp_left, hφ]
  exact (chart_pull_iff' _ L _ j).trans (iff_of_eq (by rw [keyl]))

def pullUnif (φ : A ⟶ B) {L : LB B.left} {M : LB A.left} {g : ℕ} (u : HolUnif A M g) (u' : HolUnif B L g)
    (hφ : ∀ z, u.ex z ≫ φ = u'.ex z) : HolUnif A (L.pull φ.left) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun j z => u'.fr (j PUnit.unit) z
  fr_hol := fun j => (u'.fr_hol (j PUnit.unit)).mono
    (fun z hz => (pull_chart_iff φ u.ex u'.ex hφ j z).1 hz)
  fr_ne := fun j z hz => u'.fr_ne _ _ ((pull_chart_iff φ u.ex u'.ex hφ j z).1 hz)
  fr_compat := fun i j z h => by
    have keyl : (u.ex z).left ≫ φ.left = (u'.ex z).left := by rw [← Over.comp_left, hφ]
    have hi := (pull_chart_iff φ u.ex u'.ex hφ i z).1 (le_left' h)
    have hj := (pull_chart_iff φ u.ex u'.ex hφ j z).1 (le_right' h)
    show u'.fr (i PUnit.unit) z = _ * u'.fr (j PUnit.unit) z
    rw [valAt'_pull_g' _ L _ i j h, keyl]
    exact u'.fr_compat _ _ _ (inf_of _ hi hj)

theorem pullUnif_factor (φ : A ⟶ B) {L : LB B.left} {M : LB A.left} {g : ℕ} (u : HolUnif A M g)
    (u' : HolUnif B L g) (hφ : ∀ z, u.ex z ≫ φ = u'.ex z) (hΛ : u.Λ ≤ u'.Λ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ) (h : IsFactorAH u' Hm χ') :
    IsFactorAH (pullUnif φ u u' hφ) Hm (fun l => χ' ⟨l.1, hΛ l.2⟩) := by
  obtain ⟨h1, h3, h4⟩ := h
  exact ⟨h1, fun l => h3 _, fun l i z hz =>
    h4 ⟨l.1, hΛ l.2⟩ (i PUnit.unit) z ((pull_chart_iff φ u.ex u'.ex hφ i z).1 hz)⟩

theorem ex_nsmul {G : Over (Sp ℂ)} [GrpObj G] {g : ℕ} (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ G))
    (he : ∀ z w, e (z + w) = e z * e w) (he0 : e 0 = 1) (w : Fin g → ℂ) (n : ℕ) :
    e ((n : ℂ) • w) = e w ^ n := by
  induction n with
  | zero => simp [he0]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, he, ih, pow_succ]

theorem unif_ex_zero {G : Over (Sp ℂ)} [GrpObj G] {L : LB G.left} {g : ℕ} (u : HolUnif G L g) : u.ex 0 = 1 :=
  (u.ker 0).2 (zero_mem _)

end GlobalTheory.PosAHIsog

namespace GlobalTheory.PosAHIsog

open GlobalTheory.CechPic

theorem exists_isog_principal_lam :
    ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → u.IsAH Hm χ →
    ∃ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), 1 ≤ N ∧ IsMonHom ψ ∧ IsMonHom ρ ∧
      ψ ≫ ρ = (𝟙 A) ^ N ∧ ρ ≫ ψ = (𝟙 P.A) ^ N ∧
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) := by
  intro g A _ hA M u Hm χ hM hAH
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_complex _ A.hom hA.smooth
  have hint := GlobalTheory.TorusRM.ahFactor_im_int g A M u Hm χ hM (isFactorAH_of_isAH hAH)
  obtain ⟨Λ₁, N, Ef, hle, hN, hNΛ, hd1, hf1, hEf, hbij⟩ :=
    GlobalTheory.UnimodOver.exists_unimodular_overlattice g u.Λ Hm u.discrete u.full hAH.1 hAH.2.1 hint
  obtain ⟨P, uB, χB, -, hΛB, hAHB, -, -⟩ :=
    GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd1 hf1 hAH.1 hAH.2.1 hEf hbij
  haveI := P.isAb.comm
  haveI := P.isAb.smooth
  haveI := P.isAb.proper
  haveI : IsReduced P.A.left := GlobalTheory.isReduced_of_smooth_complex _ P.A.hom P.isAb.smooth
  have hsA := GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif A hA u
  have hsP := GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif P.A P.isAb uB
  have hle' : u.Λ ≤ uB.Λ := hΛB ▸ hle
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A P.A g hA P.isAb hsA hsP M P.L u uB
    LinearMap.id (fun x hx => hle' hx)
  obtain ⟨ρ, hρ, hρe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice P.A A g P.isAb hA hsP hsA P.L M uB u
    ((N : ℂ) • LinearMap.id) (fun x hx => by simpa using hNΛ x (hΛB ▸ hx))
  have hψe' : ∀ w, u.ex w ≫ ψ = uB.ex w := fun w => (hψe w).symm
  have hρe' : ∀ w, uB.ex w ≫ ρ = u.ex ((N : ℂ) • w) := fun w => by simpa using (hρe w).symm
  refine ⟨P, ψ, ρ, N, hN, hψ, hρ, ?_, ?_, ?_⟩
  · refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨w, rfl⟩ := u.ex_onto x
    rw [← Category.assoc, hψe', hρe', comp_pow, Category.comp_id,
      ex_nsmul u.ex u.ex_add (unif_ex_zero u)]
  · refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨w, rfl⟩ := uB.ex_onto x
    rw [← Category.assoc, hρe', hψe', comp_pow, Category.comp_id,
      ex_nsmul uB.ex uB.ex_add (unif_ex_zero uB)]
  · haveI := hψ
    have hM' : (P.L.pull ψ.left).IsLB := pull_isLB P.isLB _
    have hF₃ := pullUnif_factor ψ u uB hψe' hle' Hm χB (isFactorAH_of_isAH hAHB)
    obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
    have hamp : Out.RelAmple A H :=
      (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
    have hadd := GlobalTheory.T.hermitian_forms_add_of_factor_product g A hA (GlobalTheory.ProjSpace.isProjOver_of_relAmple hamp) (LB.triv A.left) M (P.L.pull ψ.left) (trivUnif u) u (pullUnif ψ u uB hψe')
      0 Hm Hm (fun _ => 1) χ _ (LB.isLB_triv _) hM hM' rfl rfl (trivUnif_factor u) (isFactorAH_of_isAH hAH) hF₃
      (by rw [zero_add])
    have hLM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
    have hLM' : (abelian₂ A (P.L.pull ψ.left)).IsLB := LB.isLB_linComb hM' _ _
    have hLT : (abelian₂ A (LB.triv A.left)).IsLB := LB.isLB_linComb (LB.isLB_triv _) _ _
    have hD : (LB.div (abelian₂ A (P.L.pull ψ.left)) (abelian₂ A (LB.triv A.left))).IsLB := LB.isLB_div hLM' hLT
    have hR : ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left).IsLB :=
      pull_isLB (LB.isLB_linComb P.isLB _ _) _
    refine (cls_eq_iff hLM hR).1 ?_
    have e₁ : cls _ hLM' = lam (cls _ hM') (fst A A) (snd A A) := cls_cube_two hM' _ _ hLM'
    have e₂ : cls _ hLT = lam (cls _ (LB.isLB_triv A.left)) (fst A A) (snd A A) :=
      cls_cube_two (LB.isLB_triv _) _ _ hLT
    rw [(cls_eq_iff hLM hD).2 hadd, cls_div hLM' hLT hD, GlobalTheory.RealMult.Elliptic.cls_pull_lam P.isLB _ _ hR,
      e₁, e₂, cls_pull P.isLB, lam_pull]
    have h0 : cls (LB.triv A.left) (LB.isLB_triv _) = 0 := rfl
    rw [h0]
    simp [lam]

end GlobalTheory.PosAHIsog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFreeModuleIsoStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_free_module_iso : ∀ (S T : Scheme.{0}) (f : S ⟶ T) (n : ℕ), Nonempty ((Scheme.Modules.pullback f).obj (GlobalTheory.QCoh.freeModule (X := T) (Fin n)) ≅ GlobalTheory.QCoh.freeModule (X := S) (Fin n)) := by
  first | exact @GlobalTheory.pullback_freeModule_iso_free | exact GlobalTheory.pullback_freeModule_iso_free | (intros; apply GlobalTheory.pullback_freeModule_iso_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqEulerCharacteristicStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_degree_eq_euler_characteristic : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsProjOver s → topologicalKrullDim G ≤ (0 : ℕ) → Nonempty G → f.residueDegree (genericPoint Y) ≠ 0 ∧ (letI := algebraΓOfHom s; chi B.functionField (structureModule G)) = f.residueDegree (genericPoint Y) := by
  first | exact @GlobalTheory.GenericFibreDegree.chi_eq_residueDegree | exact GlobalTheory.GenericFibreDegree.chi_eq_residueDegree | (intros; apply GlobalTheory.GenericFibreDegree.chi_eq_residueDegree <;> assumption)
end


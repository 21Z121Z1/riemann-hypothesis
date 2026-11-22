import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0066
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeNonsimpleFibresEqZero
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionCanonicalMultiplier
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.CanThLine

section Law

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_factor {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (a c : Fin g → ℝ) (m n : Fin g → ℤ) {l : Fin g → ℂ}
    (hl : l = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) (ζ : Fin g → ℂ) :
    cexp (-(π / 2 * ((ζ + l) ⬝ᵥ imInv τ *ᵥ (ζ + l)))) *
        (canMult a c m n *
          cexp (π * hermForm (imInv τ) ζ l + π / 2 * hermForm (imInv τ) l l)) =
      eC (((1 : ℕ) : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec c ⬝ᵥ ofIntVec n)) *
        eC (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ ζ)) *
        cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) := by
  have hl' : l = (fun i => (((m i : ℝ)) : ℂ)) + τ *ᵥ fun i => (((n i : ℝ)) : ℂ) := by
    simpa using hl
  have h1 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) ζ
  have h2 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) l
  rw [← hl'] at h1 h2
  have h3 := dot_mulVec_symm (isSymm_imInv hs) ζ l
  have e0 : (fun i => (((n i : ℝ)) : ℂ)) = ofIntVec n := by
    funext i; simp [ofIntVec]
  have h5 : (l ⬝ᵥ ofIntVec n) = ((m ⬝ᵥ n : ℤ) : ℂ) + ofIntVec n ⬝ᵥ τ *ᵥ ofIntVec n := by
    rw [hl, add_dotProduct, dotProduct_comm (τ *ᵥ _)]
    congr 1
    simp [dotProduct, ofIntVec]
  have e1 : ((a ⬝ᵥ (fun i => (m i : ℝ)) : ℝ) : ℂ) = ofRealVec a ⬝ᵥ ofIntVec m := by
    simp [dotProduct, ofRealVec, ofIntVec]
  have e2 : ((c ⬝ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) = ofRealVec c ⬝ᵥ ofIntVec n := by
    simp [dotProduct, ofRealVec, ofIntVec]
  rw [e0] at h1 h2
  rw [canMult, e1, e2]
  simp only [eC, ← Complex.exp_add]
  congr 1
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h3, h1, h2, h5,
    dotProduct_comm (ofIntVec n) ζ]
  push_cast
  ring

end Law

section Main

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_mem_thetaLevelChar {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    (fun ζ => cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) * θ (h⁻¹ *ᵥ ζ)) ∈
      GlobalTheory.thetaLevelChar a c 1 τ := by
  have hhi : h * h⁻¹ = 1 := mul_nonsing_inv _ hh
  have hback : ∀ v : Fin g → ℂ, h *ᵥ (h⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hhi, one_mulVec]
  have hd : Differentiable ℂ (fun ζ : Fin g → ℂ => h⁻¹ *ᵥ ζ) :=
    differentiable_pi.2 fun i => by
      simp only [mulVec, dotProduct]
      fun_prop
  refine GlobalTheory.mem_thetaLevelChar.2 ⟨?_, fun n n' z => ?_⟩
  · refine Differentiable.mul ?_ (hθ.comp hd)
    simp only [dotProduct, mulVec]
    fun_prop
  · set l : Fin g → ℂ := (fun i => (n' i : ℂ)) + τ *ᵥ fun i => (n i : ℂ) with hl
    have e : z + τ *ᵥ ofIntVec n + ofIntVec n' = z + l := by
      rw [hl, add_assoc, add_comm (τ *ᵥ _)]
      rfl
    have hL := hlaw n' n (h⁻¹ *ᵥ l) (hback l) (h⁻¹ *ᵥ z)
    rw [hH, hH, hback, hback] at hL
    have hG := gaussian_mul_factor hs hp a c n' n hl z
    simp only [e]
    rw [show h⁻¹ *ᵥ (z + l) = h⁻¹ *ᵥ z + h⁻¹ *ᵥ l from mulVec_add _ _ _, hL]
    linear_combination θ (h⁻¹ *ᵥ z) * hG

theorem eq_const_mul_canTh {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    ∃ κ : ℂ, ∀ z, θ z = κ * canTh τ a c (h *ᵥ z) := by
  have hmem := gaussian_mul_mem_thetaLevelChar hs hp hh hH hθ hlaw
  rw [GlobalTheory.thetaLevelChar_one (a := a) (b := c) (τ := τ) ⟨hs, hp⟩, Submodule.mem_span_singleton] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  refine ⟨κ, fun z => ?_⟩
  have hback : h⁻¹ *ᵥ (h *ᵥ z) = z := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]
  have hz := congrFun hκ (h *ᵥ z)
  simp only [Pi.smul_apply, smul_eq_mul] at hz
  rw [hback] at hz
  rw [canTh, thetaChar_eq_theta, mul_left_comm, hz, ← _root_.mul_assoc, ← Complex.exp_add]
  simp

end Main

theorem level_one_line : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (θ : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    Differentiable ℂ θ →
    (∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ), h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = GlobalTheory.CanTh.canMult a c m n *
        Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * θ z) →
    ∃ κ : ℂ, ∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z) := by
  intro g τ h Hm a c θ hs hp hh hH hθ hlaw
  exact eq_const_mul_canTh hs hp hh hH hθ hlaw

end GlobalTheory.CompanionTheory.CanThLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaNormInPeriodCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem re_dot_sub_re_hermForm {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (ζ : Fin g → ℂ) :
    (ζ ⬝ᵥ (B.map fun x : ℝ => (x : ℂ)).mulVec ζ).re - (hermForm (B.map fun x : ℝ => (x : ℂ)) ζ ζ).re =
      -2 * ((fun i => (ζ i).im) ⬝ᵥ B.mulVec fun i => (ζ i).im) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem periodMatrix_map_im {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    (GroundTheory.Heights₂.Heights.periodMatrix X Y).map Complex.im = Y := by
  ext i j
  simp [GroundTheory.Heights₂.Heights.periodMatrix]

theorem im_period_point {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (u₁ u₂ : Fin g → ℝ) :
    (fun i => (((GroundTheory.Heights₂.Heights.periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) +
      (fun i => (u₂ i : ℂ))) i).im) = Y.mulVec u₁ := by
  funext i
  simp [GroundTheory.Heights₂.Heights.periodMatrix, Matrix.mulVec, dotProduct, Complex.im_sum]

theorem thetaChar_eq {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (ζ : Fin g → ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (GroundTheory.Heights₂.Heights.periodMatrix X Y)
        (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) ζ =
      GroundTheory.Heights₂.Heights.thetaChar X Y a c ζ := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar GroundTheory.Heights₂.Heights.thetaChar
  refine tsum_congr fun k => ?_
  have e : ((fun i => (k i : ℂ)) + fun i => (a i : ℂ)) =
      fun i => ((intVec k i + a i : ℝ) : ℂ) := by
    funext i
    simp [intVec]
  rw [e]

theorem norm_mul_canTh : ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (h Hm : Matrix (Fin g) (Fin g) ℂ)
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ),
    X.IsSymm → Y.PosDef →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh (periodMatrix X Y) a c (h.mulVec z)) →
    ∀ (u₁ u₂ : Fin g → ℝ) (z : Fin g → ℂ),
      h.mulVec z = (periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) + (fun i => (u₂ i : ℂ)) →
      ‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) = ‖κ‖ * thetaNorm X Y a c u₁ u₂ := by
  intro g X Y a c h Hm θ κ _ hY hH hθ u₁ u₂ z hz
  have him := periodMatrix_map_im X Y
  have hinv : GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y) =
      Y⁻¹.map fun x : ℝ => (x : ℂ) := by
    rw [GlobalTheory.CanTh.imInv, him]
  have hq : (fun i => ((h.mulVec z) i).im) = Y.mulVec u₁ := by
    rw [hz]
    exact im_period_point X Y u₁ u₂
  have hdiff := re_dot_sub_re_hermForm Y⁻¹ (h.mulVec z)
  have hcancel : Y⁻¹.mulVec (Y.mulVec u₁) = u₁ := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hY.det_pos.ne'.isUnit, Matrix.one_mulVec]
  rw [hq, hcancel, dotProduct_comm (Y.mulVec u₁) u₁, ← hinv] at hdiff
  have hqf : u₁ ⬝ᵥ Y.mulVec u₁ = qf Y u₁ := rfl
  rw [hqf] at hdiff
  rw [hθ z, hH z z, norm_mul, GlobalTheory.CanTh.canTh, norm_mul, Complex.norm_exp, thetaChar_eq, thetaNorm,
    ← hz]
  have hre : ((Real.pi / 2 : ℂ) * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z))).re =
      Real.pi / 2 * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re := by
    have : ((Real.pi / 2 : ℂ)) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.re_ofReal_mul]
  rw [hre]
  have hexp : Real.exp (Real.pi / 2 * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re) *
      Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
        (hermForm (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y))
          (h.mulVec z) (h.mulVec z)).re) = Real.exp (-Real.pi * qf Y u₁) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    linear_combination (Real.pi / 2) * hdiff
  calc _ = ‖κ‖ * (‖GroundTheory.Heights₂.Heights.thetaChar X Y a c (h.mulVec z)‖ *
        (Real.exp (Real.pi / 2 * (h.mulVec z ⬝ᵥ
          (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re) *
        Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
          (hermForm (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y))
            (h.mulVec z) (h.mulVec z)).re))) := by ring
    _ = _ := by rw [hexp]

end GlobalTheory.CompanionTheory.Ar.Nform
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFourth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_alphaOf : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (alphaOf BM l H bp p) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hab hj hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hF p
  obtain ⟨hH, hbpc, hchart, hpt, -⟩ := hF
  intro w hw
  have hbw : bp w ∈ BM.O l \ ReciprocityTheory.AnForm.P.bdry BM.s := (hpt w hw).1
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u)) w := by
    refine GlobalTheory.CompanionTheory.Ar.PB.CWeight.contDiffAt_blockPot j p.2 ?_ ?_ ?_ ?_
    · intro r s
      exact (GlobalTheory.T.base_chart_flag_analytic_map K ι Φ y Ψ N j M n d BM l p.1 Un bp hUn hbpc hchart
        (fun w' hw' => (hpt w' hw').1) r s).contDiffAt (hUn.mem_nhds hw)
    · intro r s
      exact (hH p.1 r s w hw).contDiffAt.restrict_scalars ℝ
    · exact (BM.G_pos l p.1 (bp w) hbw).2
    · exact ((hpt w hw).2 p.1).2
  have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) w := by
    by_cases hb : M.blk p = none
    · have hreg := ((BM.good l (bp w) hbw.1).2.2 p hb).2.1
      have han := GlobalTheory.T.regular_function_analytic_on_chart _ _ _ M.x ((BM.F l).υ p) d n BM.Rb Un bp w hUn hw hbpc hchart hreg
      have hne : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsVal BM l p (bp w) ≠ 0 :=
        GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l p (bp w) hbw.1 hb
      obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic d _ w han hne
      have hre0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Complex.reCLM (Hh z)) w :=
        Complex.reCLM.contDiff.contDiffAt.comp w (hHh.contDiffAt.restrict_scalars ℝ)
      have hre : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (Hh z).re) w := by
        simpa using hre0
      refine hre.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      show GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp z) = (Hh z).re
      unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
      rw [if_pos hb]
      exact hz
    · have hz : (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) = fun _ => (0 : ℝ) := by
        funext u
        unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
        rw [if_neg hb]
      rw [hz]
      exact contDiffAt_const
  have he : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.alphaOf BM l H bp p = fun u =>
      GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u) -
        GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u) := rfl
  rw [he]
  exact (hA.sub hB).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartThird
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.GramPlane

theorem contDiffOn_conj_mul_mul {e N : ℕ} {Un : Set (Fin e → ℂ)} (hUn : IsOpen Un) (A G : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun w => A w r s) Un)
    (hG : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G w r s) Un) (r s : Fin N) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ((A w)ᴴ * G w * A w) r s) Un := by
  have hA' : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un := fun r s =>
    ((hA r s).contDiffOn hUn.uniqueDiffOn).restrict_scalars ℝ
  have hAc : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => star (A w r s)) Un := fun r s => by
    first
      | exact ContDiffOn.star (hA' r s)
      | exact (Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s))
      | (have h := Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s)
         simpa [Function.comp_def] using h)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine ContDiffOn.sum fun k _ => ?_
  refine ContDiffOn.mul ?_ (hA' k s)
  refine ContDiffOn.sum fun i _ => ?_
  exact (hAc i r).mul (hG i k)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.GramPlane

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_gram_plane : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => Gn w r s) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb _ _ _ _ X q Un Gn ΦYn ΦWn l H bp hUn hF r s
  obtain ⟨hH, hbp, hch, hO, hGn, -, -⟩ := hF
  have hGs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ (bp w) r s) Un :=
    GlobalTheory.T.base_chart_flag_analytic_map K ι Φ y Ψ N j M n d BM l τ Un bp hUn hbp hch (fun w hw => (hO w hw).1)
  have hMs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) r s) Un :=
    GramPlane.contDiffOn_conj_mul_mul hUn (H τ) (fun w => BM.G l τ (bp w)) (hH τ) hGs
  have hnum := MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
    (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) hMs
  have hden := MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
    ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) hMs
  have hne : ∀ w ∈ Un, minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
      ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) ≠ 0 := by
    intro w hw
    have hGp := (BM.G_pos l τ (bp w) (hO w hw).1).2
    have hdet := ((hO w hw).2 τ).2
    have hinj : Function.Injective (H τ w).mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hdet
    exact (SchurCalc.minor_pos (hGp.conjTranspose_mul_mul_same hinj) _).ne'
  have hq := hnum.mul (hden.inv hne)
  refine hq.congr fun w hw => ?_
  have e := hGn w hw r s
  clear * - e
  simp only [e, div_eq_mul_inv, Pi.inv_apply]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeNonsimpleFibresEqZeroStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_nonsimple_fibres_eq_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, cxSimple (conePts Q) Ψ w ∧
      ¬ cxSimple (conePts Q) Ψ' ((Ψ' w 0)⁻¹ • w)} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null | exact GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null <;> assumption)
end


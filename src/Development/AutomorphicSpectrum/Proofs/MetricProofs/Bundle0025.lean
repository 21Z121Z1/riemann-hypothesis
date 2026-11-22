import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0023
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RCombine
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GluedLocalRegularizationsOnAtlas
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0024

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityPropertiesStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_system_regularity_properties : ∀ (e : ℕ) (σ : Type) (S : AnSys e σ), IsOpen S.open' ∧ IsNull S.A S.open'ᶜ ∧ (∀ a, ∀ x ∈ S.open', IsTwiceDifferentiableAt S.A (S.potH a) x) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → IsPotential S.A (S.potT a t)) ∧ ∀ y ∈ S.open', Real.exp 1 ≤ rW S.L S.s y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics | exact GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.C2TendstoPullbackThroughChartStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.C2_tendsto_pullback_through_chart : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (c : OpenPartialHomeomorph X (Fin e → ℂ)) (g : ℝ → (Fin e → ℂ) → ℝ) (p : (Fin e → ℂ) → ℝ) (K' : Set (Fin e → ℂ)), K' ⊆ c.target → (TendstoUniformlyOn g p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (g t)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (g t))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (g t) z - fderiv ℝ p z‖ ≤ M * t) → (TendstoUniformlyOn (fun t => (g t ∘ c) ∘ c.symm) p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ ((g t ∘ c) ∘ c.symm)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ ((g t ∘ c) ∘ c.symm))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ ((g t ∘ c) ∘ c.symm) z - fderiv ℝ p z‖ ≤ M * t) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback | exact GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback | (intros; apply GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CommonResolutionPotentialComparison
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem r_combine : PullbackStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (Amp : HermLine ι) (β : MRing ι) (b : K → ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : AnSys D σ) (π₁ : R.X → S₁.X) (π₂ : R.X → S₂.X) (h₁ : HoloMap R.A S₁.A π₁) (h₂ : HoloMap R.A S₂.A π₂), IsPotential R.A (potOf R Amp) → IsPosPot R.A (potOf R Amp) → IsMultiHomog β b → β ∉ P → (∀ z ∈ mcPts P, evC z β = 0 → z ∈ mcPts J) → (∀ x, π₁ x ∈ bdry S₁.s → evC (R.lift x x) β = 0) → (∀ x, π₂ x ∈ bdry S₂.s → evC (R.lift x x) β = 0) → ∃ (L : LocPot R.X) (s : R.X → R.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set R.X) (C₅ C t₀ : ℝ), IsPotential R.A L ∧ IsSection R.A L s ∧ IsSNC R.A L s m W ∧ (∀ y, logNormSec L s y ≤ 0) ∧ (∀ x, x ∈ bdry s ↔ evC (R.lift x x) β = 0) ∧ t₀ ≤ S₁.t₀ ∧ t₀ ≤ S₂.t₀ ∧ (∀ a, IsSingWeight R.A L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁) C t₀ ∧ IsRegFamilyC2 R.A s (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁)) ∧ ∀ a, IsSingWeight R.A L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) C t₀ ∧ IsRegFamilyC2 R.A s (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) :=
  PositivityTheory.UnitarySelfGeneration.r_combine

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamily
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.HmCont

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {g : ℕ}

def cvec (z : Fin g → ℂ) : Fin g ⊕ Fin g → ℝ :=
  Sum.elim (fun k => (z k).re) (fun k => (z k).im)

def realBlock (H : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  Matrix.fromBlocks (H.map Complex.im) (-(H.map Complex.re)) (H.map Complex.re) (H.map Complex.im)

theorem cvec_dot_realBlock (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    cvec z ⬝ᵥ realBlock H *ᵥ cvec w = (z ⬝ᵥ H *ᵥ star w).im := by
  simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec, GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply, Matrix.neg_apply,
    Complex.im_sum, Complex.re_sum, Complex.mul_im, Complex.mul_re, Pi.star_apply, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_det_ne_zero {Λ ι : Type} [AddCommGroup Λ] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ Λ) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (inj : Function.Injective form) :
    (Matrix.of fun i j => form (b i) (b j)).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hform : form (∑ i, c i • b i) = 0 := by
    refine b.ext fun j => ?_
    have hj := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hj
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    exact hj
  have hsum : ∑ i, c i • b i = 0 := inj (by rw [hform, map_zero])
  exact hc0 (funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hsum))

theorem continuous_of_congruence {ι X : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]
    (T G : X → Matrix ι ι ℝ) (W : Matrix ι ι ℝ) (hT : Continuous T) (hW : W.det ≠ 0)
    (h : ∀ x, (T x)ᵀ * G x * T x = W) : Continuous G := by
  have hdet : ∀ x, (T x).det ≠ 0 := by
    intro x h0
    apply hW
    rw [← h x, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hG : ∀ x, G x = ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) := by
    intro x
    have h1 : (T x).adjugateᵀ * ((T x)ᵀ * G x * T x) * (T x).adjugate = (T x).det ^ 2 • G x := by
      calc (T x).adjugateᵀ * ((T x)ᵀ * G x * T x) * (T x).adjugate
          = (T x * (T x).adjugate)ᵀ * G x * (T x * (T x).adjugate) := by
            rw [Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = (T x).det ^ 2 • G x := by
            simp only [Matrix.mul_adjugate, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, sq]
    rw [h x] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (hdet x)), one_smul]
  have hcont : Continuous fun x => ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) := by
    have hd : Continuous fun x => (T x).det := hT.matrix_det
    have ha : Continuous fun x => (T x).adjugate := hT.matrix_adjugate
    exact ((hd.pow 2).inv₀ fun x => pow_ne_zero 2 (hdet x)).smul
      ((ha.matrix_transpose.matrix_mul continuous_const).matrix_mul ha)
  rw [show G = fun x => ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) from funext hG]
  exact hcont

theorem continuous_Hm (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ)
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (hform : ∀ x, (R x).form = form)
    (hP : ∀ v, Continuous fun x => (R x).P v) : Continuous fun x => (R x).Hm := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact continuous_of_const fun x => isEmptyElim x
  have hlat : ∀ S : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ,
      Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g ∧ Function.Bijective S.form := by
    intro S
    obtain ⟨h1, h2, h3, _, _, h4, _, _, _, _, _, _, _, _⟩ := S
    exact ⟨h1, h2, h3, h4⟩
  have hIm : ∀ (S : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ) (u v : Λ),
      ((S.P u) ⬝ᵥ S.Hm *ᵥ star (S.P v)).im = S.form u v := by
    intro S u v
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := S
    exact h u v
  obtain ⟨hfree, hfin, hrank, hbij⟩ := hlat (R x₀)
  have hinj : Function.Injective form := by
    rw [← hform x₀]
    exact hbij.1
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin g ⊕ Fin g) ℤ Λ) :=
    ⟨(Module.finBasisOfFinrankEq ℤ Λ (hrank.trans (two_mul g))).reindex finSumFinEquiv.symm⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      W = Matrix.of fun i j => ((form (b i) (b j) : ℤ) : ℝ) := ⟨_, rfl⟩
  have hW : W.det ≠ 0 := by
    have h0 := GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.gram_det_ne_zero b form hinj
    have hmap : W = (Int.castRingHom ℝ).mapMatrix (Matrix.of fun i j => form (b i) (b j)) := by
      ext i j
      rw [hWdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply]
      simp
    rw [hmap, ← RingHom.map_det]
    simpa using h0
  have hT : Continuous fun x =>
      (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) := by
    refine continuous_matrix fun a i => ?_
    rcases a with k | k
    · exact Complex.continuous_re.comp ((continuous_apply k).comp (hP (b i)))
    · exact Complex.continuous_im.comp ((continuous_apply k).comp (hP (b i)))
  have hTGT : ∀ x,
      (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)ᵀ *
        GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm *
        (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) = W := by
    intro x
    ext i j
    rw [Matrix.mul_assoc]
    calc _ = GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) ⬝ᵥ
            GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm *ᵥ GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b j)) := rfl
      _ = (((R x).P (b i)) ⬝ᵥ (R x).Hm *ᵥ star ((R x).P (b j))).im :=
          GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec_dot_realBlock _ _ _
      _ = (R x).form (b i) (b j) := hIm (R x) (b i) (b j)
      _ = W i j := by rw [hform x, hWdef, Matrix.of_apply]
  have hG : Continuous fun x => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm :=
    GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_of_congruence
      (fun x => (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a :
        Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ))
      (fun x => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm) W hT hW hTGT
  refine continuous_matrix fun k l => ?_
  have hre : Continuous fun x => ((R x).Hm k l).re := by
    have h := hG.matrix_elem (Sum.inr k) (Sum.inl l)
    simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, Matrix.fromBlocks_apply₂₁, Matrix.map_apply] at h
    exact h
  have him : Continuous fun x => ((R x).Hm k l).im := by
    have h := hG.matrix_elem (Sum.inl k) (Sum.inl l)
    simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, Matrix.fromBlocks_apply₁₁, Matrix.map_apply] at h
    exact h
  have heq : (fun x => (R x).Hm k l) =
      fun x => (((R x).Hm k l).re : ℂ) + (((R x).Hm k l).im : ℂ) * Complex.I :=
    funext fun x => (Complex.re_add_im _).symm
  show Continuous fun x => (R x).Hm k l
  rw [heq]
  exact (Complex.continuous_ofReal.comp hre).add ((Complex.continuous_ofReal.comp him).mul continuous_const)

end GlobalTheory.CompanionTheory.Ar.Cusp.HmCont
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddedResolutionAmpleMetricStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedded_resolution_ample_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsEmbedded R.A P R.U R.lift → ∃ Amp : HermLine ι, IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded | exact GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EpsilonSchedulePropertiesStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_schedule_properties : (∀ a b : ℝ, Real.exp 1 ≤ a → a ≤ b → Real.log b / b ≤ Real.log a / a) ∧ (∀ C t t' : ℝ, 0 ≤ C → 0 < t → t ≤ t' → t' ≤ Real.exp (-Real.exp 1) → epsT C t ≤ epsT C t') ∧ (∀ C t : ℝ, 1 ≤ C → 0 < t → t ≤ Real.exp (-Real.exp 1) → t ≤ epsT C t) ∧ (∀ C : ℝ, Tendsto (epsT C) (𝓝[>] 0) (𝓝 0)) ∧ (∀ C : ℝ, ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1) ∧ (∀ (n : ℕ) (a : Fin n → ℝ), (∀ j, 0 < a j) → ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.epsT_numerics | exact GlobalTheory.CompanionTheory.Ar.Num.epsT_numerics | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.epsT_numerics <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpan
section
namespace GlobalTheory.CompanionTheory.Ar.Exchange

theorem exists_completion_by_members (g m r : ℕ) (w : Fin r → Fin g → ℂ) (b : Fin m → Fin g → ℂ)
    (hw : LinearIndependent ℂ w) (hb : LinearIndependent ℂ b)
    (hwb : ∀ a, w a ∈ Submodule.span ℂ (Set.range b)) :
    ∃ (k : ℕ) (J : Fin k → Fin m), r + k = m ∧
      LinearIndependent ℂ (Fin.append w (fun j => b (J j))) := by
  classical
  let v : Fin r ⊕ Fin m → (Fin g → ℂ) := Sum.elim w b
  have hs : LinearIndepOn ℂ v (Set.range Sum.inl) := by
    rw [linearIndepOn_range_iff Sum.inl_injective]
    exact hw
  obtain ⟨B, -, hsB, hspan, hB⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  let S : Finset (Fin m) := Finset.univ.filter fun j => Sum.inr j ∈ B
  let J : Fin S.card → Fin m := S.orderEmbOfFin rfl
  let φ : Fin (r + S.card) → Fin r ⊕ Fin m := Fin.append Sum.inl (Sum.inr ∘ J)
  have hφ : Function.Injective φ :=
    Fin.append_injective_iff.mpr ⟨Sum.inl_injective,
      Sum.inr_injective.comp (S.orderEmbOfFin rfl).injective, fun _ _ => Sum.inl_ne_inr⟩
  have hJS : ∀ l, J l ∈ S := fun l => S.orderEmbOfFin_mem rfl l
  have hφB : Set.range φ ⊆ B := by
    rintro _ ⟨l, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp only [φ, Fin.append_left]
      exact hsB ⟨i, rfl⟩
    · simp only [φ, Fin.append_right, Function.comp_apply]
      have := hJS l
      simpa [S] using this
  have hBφ : B ⊆ Set.range φ := by
    rintro (i | j) hx
    · exact ⟨Fin.castAdd _ i, by simp [φ]⟩
    · have hj : j ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        simp [S, hx]
      obtain ⟨l, hl⟩ := hj
      exact ⟨Fin.natAdd _ l, by simp [φ, J, hl]⟩
  have hu : LinearIndependent ℂ (v ∘ φ) := by
    rw [← linearIndepOn_range_iff hφ]
    exact hB.mono hφB
  have hle1 : Submodule.span ℂ (Set.range (v ∘ φ)) ≤ Submodule.span ℂ (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    show v (φ l) ∈ _
    generalize φ l = x
    rcases x with i | j
    · exact hwb i
    · exact Submodule.subset_span ⟨j, rfl⟩
  have hle2 : Submodule.span ℂ (Set.range b) ≤ Submodule.span ℂ (Set.range (v ∘ φ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : b j ∈ Submodule.span ℂ (v '' B) := hspan ⟨Sum.inr j, Set.mem_univ _, rfl⟩
    have h2 : v '' B ⊆ Set.range (v ∘ φ) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, rfl⟩ := hBφ hx
      exact ⟨l, rfl⟩
    exact Submodule.span_mono h2 h1
  have hueq : (Fin.append w fun j => b (J j)) = v ∘ φ := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp [φ, v]
    · simp [φ, v]
  refine ⟨S.card, J, ?_, ?_⟩
  · have e1 := finrank_span_eq_card hu
    have e2 := finrank_span_eq_card hb
    rw [le_antisymm hle1 hle2, e2] at e1
    simpa using e1.symm
  · rw [hueq]
    exact hu

end GlobalTheory.CompanionTheory.Ar.Exchange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GluedLocalRegularizationsOnAtlasStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_local_regularizations_on_atlas : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ M : ℝ) (x : Fin B.n → X) (S : Fin B.n → Finset (Fin e)) (m : Fin B.n → Fin e → ℕ), A.Compatible B → (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) → (∀ j, (B.chart j).source ⊆ th.U (x j)) → (∀ y, logNormSec L s y ≤ 0) → IsClosed (bdry s) → (∀ j, ∀ y ∈ (B.chart j).target, ((B.chart j).symm y ∈ bdry s ↔ ∃ i ∈ S j, y i = 0)) → (∀ j, ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, (B.chart j).symm y ∉ bdry s → |rW L s ((B.chart j).symm y) - rLoc (S j) (m j) y| ≤ M) → IsSingWeight A L s th ph C₅ → ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |(polyMaxOff (S j) (fun z => th.φ (x j) ((B.chart j).symm z) + ph ((B.chart j).symm z)) (B.chart j y) t - th.φ (x j) y) - (polyMaxOff (S k) (fun z => th.φ (x k) ((B.chart k).symm z) + ph ((B.chart k).symm z)) (B.chart k y) t - th.φ (x k) y)| ≤ epsT C t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_charts_compare | exact GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_charts_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_charts_compare <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosIffLinearIndependent
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GramPos

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem posDef_Hm_transpose (R : RiemLat E g Λ) : (R.Hmᵀ).PosDef := by
  have hH : (R.Hmᵀ).IsHermitian := by
    ext i j
    exact R.herm.apply j i
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h1 := R.pos x hx
  have e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  have him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0 := hH.im_star_dotProduct_mulVec_self x
  rw [Complex.pos_iff]
  exact ⟨by rw [e]; exact h1, him.symm⟩

theorem gram_eq_mul (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) :
    R.gram u = ((Matrix.of u)ᵀ)ᴴ * R.Hmᵀ * (Matrix.of u)ᵀ := by
  ext a b
  simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_pos_of_linearIndependent (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ)
    (hu : LinearIndependent ℂ u) : 0 < (R.gram u).det := by
  have hC : Function.Injective ((Matrix.of u)ᵀ).mulVec := Matrix.mulVec_injective_iff.2 hu
  rw [gram_eq_mul]
  exact ((posDef_Hm_transpose R).conjTranspose_mul_mul_same hC).det_pos

theorem linearIndependent_of_det_ne_zero (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ)
    (hd : (R.gram u).det ≠ 0) : LinearIndependent ℂ u := by
  have hinj : Function.Injective (R.gram u).mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd))
  have hC : Function.Injective ((Matrix.of u)ᵀ).mulVec := by
    intro x y hxy
    apply hinj
    have hxy' : (Matrix.of u)ᵀ *ᵥ x = (Matrix.of u)ᵀ *ᵥ y := hxy
    simp only [gram_eq_mul, ← Matrix.mulVec_mulVec, hxy']
  exact Matrix.mulVec_injective_iff.1 hC

theorem gram_det_pos_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (LinearIndependent ℂ u → 0 < (R.gram u).det.re ∧ (R.gram u).det.im = 0) ∧ ((R.gram u).det ≠ 0 → LinearIndependent ℂ u) := by
  intro E _ _ _ g Λ _ _ R m u
  refine ⟨fun hu => ?_, linearIndependent_of_det_ne_zero R u⟩
  have h := Complex.pos_iff.1 (det_pos_of_linearIndependent R u hu)
  exact ⟨h.1, h.2.symm⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.GramPos
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviNonnegInChartOfPshStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_nonneg_in_chart_of_psh : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (th : LocPot X) (ph : X → ℝ) (U : Set X) (x₀ : X) (j : Fin B.n), A.Compatible B → IsPotential A th → IsOpen U → A.SmoothOn U ph → IsPshOn A U (th + LocPot.ofFun ph) → (B.chart j).source ⊆ th.U x₀ → ∀ y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' U, ∀ w : Fin e → ℂ, 0 ≤ levi (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) y w := by
  first | exact @GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase | exact GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase | (intros; apply GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalPshRegularizationLogBoundStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_psh_regularization_log_bound : ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ : ℝ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D), ContinuousOn u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsPsh (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) u → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) → ∃ (C t₀ : ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ t₀ ≤ 1 / 8 ∧ ∀ t, 0 < t → t ≤ t₀ → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, w t z = max (u z) (-C * Real.log (Real.log (1 / t)))) ∧ ContDiffOn ℝ ∞ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (ReciprocityTheory.AnForm.A.molli ρ t (w t)) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, u z ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z) ∧ ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), -C * Real.log (Real.log (1 / t)) ≤ polyMaxOff S u z t ∧ polyMaxOff S u z t - epsT C t ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ∧ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ≤ polyMaxOff S u z t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.molli_trunc_near_polyMax | exact GlobalTheory.CompanionTheory.Ar.Giv.molli_trunc_near_polyMax | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.molli_trunc_near_polyMax <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalRegularizationGradientBoundStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_regularization_gradient_bound : ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → DifferentiableOn ℝ u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ u z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, rLoc S m z ≤ Real.log (1 / t) + K → polyMaxOff S u z t ≤ u z + t ^ ((1 : ℝ) / 3) / 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_le_of_rLoc_le | exact GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_le_of_rLoc_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_le_of_rLoc_le <;> assumption)
end


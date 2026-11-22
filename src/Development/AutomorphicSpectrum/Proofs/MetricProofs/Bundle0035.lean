import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPuncturedExpOrder
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

def grMat (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (I₀ : Finset (Fin N)) (w : Finset (Fin N) → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  C + ∑ I, (w I / w I₀) • B I

def IsGrChart (N j : ℕ) (i : Fin N) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ)
    (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (w : Finset (Fin N) → ℂ), IsBlockDiag j h → h.det ≠ 0 → a ≠ 0 →
    (∀ I, IsStepRows N j i I → w I = a * minorIJ h I (stepCols N j i)) → w I₀ ≠ 0 →
      IsBlockDiag j (grMat C B I₀ w) ∧ (grMat C B I₀ w).det ≠ 0 ∧
        ∀ I, minorIJ (grMat C B I₀ w) I (stepCols N j i) * w I₀ = a * minorIJ h I (stepCols N j i)

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (k₀ : K) (z : (Σ k, ι k) → ℂ)
    (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) (basePart M.blk z) * z ⟨k₀, m⟩

def baseMono (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℂ :=
  ∏ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, F.c k⟩ ^ M.dy p k.1

def stepGap (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((BM.hom p).h z) - Real.log ((fsHerm ι (M.dy p)).h z)

def stepPh (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x : R.X) : ℝ :=
  if h : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x then stepGap M BM p h.2.choose else 0

def IsStepHyp (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  IsBlockMap κ v ∧ (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) ∧
    HoloMap R.A BM.Rb.A pr ∧
    ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))

def IsStepChart (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x y₀ : R.X) (W : Set R.X) (l : Fin BM.q)
    (H : R.X → Matrix (Fin N) (Fin N) ℂ) (D : R.X → ℂ) : Prop :=
  IsOpen W ∧ y₀ ∈ W ∧ W ⊆ R.U x ∧ (∀ y' ∈ W, pr y' ∈ BM.O l) ∧
    (∀ a b, R.A.HoloOn W fun y' => H y' a b) ∧ (∀ y' ∈ W, IsBlockDiag j (H y') ∧ (H y').det ≠ 0) ∧
    R.A.HoloOn W D ∧ (∀ y' ∈ W, D y' ≠ 0) ∧
    ∀ y' ∈ W, pr y' ∉ bdry BM.s →
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' =
        blockPot j p.2 (BM.G l p.1 (pr y')) (H y') + Real.log ‖D y'‖

def HasStepCharts (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  ∀ x y₀, y₀ ∈ R.U x → ∃ W l H D, IsStepChart M BM p κ v R pr x y₀ W l H D

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodsSubframeDetBounds
section
open Matrix Metric GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open scoped ComplexOrder

theorem frame_rank_of_gram_det_ne_zero {g k : ℕ} (M : Matrix (Fin g) (Fin k) ℂ)
    (h : (Mᵀ * M.map star).det ≠ 0) : M.rank = k := by
  have hu : IsUnit (Mᵀ * M.map star) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  simp only [Fintype.card_fin] at h1
  have h2 := Matrix.rank_mul_le_left Mᵀ (M.map star)
  rw [Matrix.rank_transpose] at h2
  have h3 := M.rank_le_width
  omega

theorem frame_compact_nhd {g k : ℕ} (M₀ : Matrix (Fin g) (Fin k) ℂ) (h : M₀.rank = k) :
    ∃ S : Set (Matrix (Fin g) (Fin k) ℂ), IsCompact S ∧ S ∈ nhds M₀ ∧ ∀ M ∈ S, M.rank = k := by
  have hP : (M₀.map star)ᴴ = M₀ᵀ := by
    ext i j
    simp
  have hpos : 0 < ((M₀ᵀ * M₀.map star).det).re := by
    have := GlobalTheory.re_det_pos_of_posDef (subframe_gram_posDef M₀ h)
    rw [hP] at this
    exact this
  have hU : IsOpen {M : Matrix (Fin g) (Fin k) ℂ | 0 < ((Mᵀ * M.map star).det).re} :=
    isOpen_lt continuous_const subframe_continuous_det
  haveI : LocallyCompactSpace (Matrix (Fin g) (Fin k) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin g → Fin k → ℂ))
  obtain ⟨S, hS, hSU, hSc⟩ := local_compact_nhds (hU.mem_nhds hpos)
  refine ⟨S, hSc, hS, fun M hM => frame_rank_of_gram_det_ne_zero M ?_⟩
  intro h0
  have := hSU hM
  rw [Set.mem_setOf_eq, h0] at this
  simp at this

theorem continuousAt_matrix_inv {X : Type*} [TopologicalSpace X] {g : ℕ}
    (A : X → Matrix (Fin g) (Fin g) ℂ) (x : X) (hA : ContinuousAt A x) (h : (A x).det ≠ 0) :
    ContinuousAt (fun y => (A y)⁻¹) x := by
  have hd : ContinuousAt (fun y => (A y).det) x :=
    (continuous_id.matrix_det).continuousAt.comp hA
  have ha : ContinuousAt (fun y => (A y).adjugate) x :=
    (continuous_id.matrix_adjugate).continuousAt.comp hA
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hd.inv₀ h).smul ha

theorem chartRadius_le_log_sum {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (h1 : ∀ k, ‖z k‖ < 1)
    (h0 : ∀ i : Fin n, i.val < a → z i ≠ 0) :
    1 ≤ chartRadius h z ∧ chartRadius h z ≤ (Real.exp 1 + 2) *
      (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) := by
  have hsum : ∑ j : Fin a, |Real.log ‖z (Fin.castLE h j)‖| =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    refine Finset.sum_bij (fun j _ => Fin.castLE h j) ?_ ?_ ?_ ?_
    · intro j _
      simp
    · intro j _ j' _ e
      exact Fin.castLE_injective h e
    · intro i hi
      have hi' : i.val < a := by simpa using hi
      exact ⟨⟨i.val, hi'⟩, Finset.mem_univ _, by ext; simp⟩
    · intro j _
      rfl
  have hterm : ∀ j : Fin a, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ =
      2 * |Real.log ‖z (Fin.castLE h j)‖| := by
    intro j
    have hc : cuspCoord h z j = z (Fin.castLE h j) := rfl
    have hn : 0 ≤ ‖z (Fin.castLE h j)‖ := norm_nonneg _
    rw [hc, Real.log_inv, Real.log_pow, abs_of_nonpos (Real.log_nonpos hn (h1 _).le)]
    push_cast
    ring
  have hr : chartRadius h z = Real.exp 1 + 2 *
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    rw [chartRadius, ← hsum, Finset.mul_sum]
    simp only [hterm]
  have hS : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [hr]
  constructor
  · linarith
  · nlinarith

theorem logPeriods_subframe_det_bounds : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ) (k : ℕ) (F : (Fin n → ℂ) → Matrix (Fin k) (Fin g) ℂ), ContinuousAt F 0 → (F 0).rank = k → ∃ (ρ K : ℝ) (N : ℕ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i : Fin n, i.val < a → z i ≠ 0) → ‖(F z * L.H z * (F z)ᴴ).det‖ ≤ K ∧ 1 ≤ K * (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) ^ N * ‖(F z * L.H z * (F z)ᴴ).det‖ := by
  intro n a g Λ _ L k F hF hrk
  obtain ⟨Q, A, hAd, hA0, hAH⟩ := GlobalTheory.T.period_matrix_local_trivialization n a g Λ L
  obtain ⟨ρ₁, c, C, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousAt A 0 := by
    have : ContinuousOn A (ball 0 1) :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
    exact this.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hAi := continuousAt_matrix_inv A 0 hAc hA0
  have hc2 : Continuous (fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hmul : ContinuousAt (fun z => F z * (A z)⁻¹) 0 :=
    ContinuousAt.comp (g := fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2)
      (f := fun z => (F z, (A z)⁻¹)) hc2.continuousAt (hF.prodMk hAi)
  have hG : ContinuousAt (fun z => (F z * (A z)⁻¹)ᵀ) 0 :=
    (continuous_id.matrix_transpose.continuousAt).comp hmul
  have hM0 : ((F 0 * (A 0)⁻¹)ᵀ).rank = k := by
    have hu : IsUnit ((A 0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hA0)
    rw [Matrix.rank_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu, hrk]
  obtain ⟨S, hS, hSn, hSr⟩ := frame_compact_nhd _ hM0
  obtain ⟨C', hC', hd⟩ := subframe_det_log_growth g k (Matrix (Fin g) (Fin k) ℂ) S hS id
    continuousOn_id hSr c C hc
  have hdet : ContinuousAt (fun z => (A z).det) 0 :=
    (continuous_id.matrix_det).continuousAt.comp hAc
  have hev : ∀ᶠ z in nhds (0 : Fin n → ℂ), (F z * (A z)⁻¹)ᵀ ∈ S ∧ (A z).det ≠ 0 :=
    (hG.eventually_mem hSn).and (hdet.eventually_ne hA0)
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have he : 0 < Real.exp 1 + 2 := by positivity
  refine ⟨min (min ρ₁ ρ₂) 1, C' * (Real.exp 1 + 2) ^ k, k, lt_min (lt_min hρ₁ hρ₂) one_pos,
    min_le_right _ _, fun z hz hz0 => ?_⟩
  have hzρ : ‖z‖ < min (min ρ₁ ρ₂) 1 := by simpa [dist_zero_right] using hz
  have hz1n : ‖z‖ < 1 := lt_of_lt_of_le hzρ (min_le_right _ _)
  have hz1 : ∀ k, ‖z k‖ < 1 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz1n
  have hzρ₁ : z ∈ closedBall (0 : Fin n → ℂ) ρ₁ := by
    have : ‖z‖ ≤ ρ₁ := hzρ.le.trans ((min_le_left _ _).trans (min_le_left _ _))
    simpa [dist_zero_right] using this
  have hzρ₂ : z ∈ ball (0 : Fin n → ℂ) ρ₂ := by
    have : ‖z‖ < ρ₂ := lt_of_lt_of_le hzρ ((min_le_left _ _).trans (min_le_right _ _))
    simpa [dist_zero_right] using this
  obtain ⟨hGS, hAz⟩ := hball z hzρ₂
  have hcusp : ∀ j : Fin a, cuspCoord L.a_le z j ≠ 0 := fun j => hz0 _ (by simp)
  have hzp : z ∈ puncturedChart L.a_le (ball (0 : Fin n → ℂ) 1) :=
    ⟨by simpa [dist_zero_right] using hz1n, hcusp⟩
  have hw := HodgeDerivative.logLift_mem L.a_le hzp
  have hexp := HodgeDerivative.expCover_logLift L.a_le hcusp
  have hAHz := hAH _ hw
  rw [hexp] at hAHz
  obtain ⟨hb1, hb2⟩ := hb _ hw (by rw [hexp]; exact hzρ₁)
  rw [hexp] at hb2
  obtain ⟨hr1, hr2⟩ := chartRadius_le_log_sum L.a_le z hz1 hz0
  have hx := hd _ hGS ((Q.τ (logLift a z)).map Complex.im) (chartRadius L.a_le z) hr1 hb1 hb2
  set Y := (Q.τ (logLift a z)).map Complex.im with hY
  set S' := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| with hS'
  have hAu : IsUnit (A z).det := isUnit_iff_ne_zero.2 hAz
  have hinv1 : (A z)⁻¹ * A z = 1 := Matrix.nonsing_inv_mul _ hAu
  have hinv2 : (A z)ᴴ * ((A z)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv1, Matrix.conjTranspose_one]
  have hkey : F z * L.H z * (F z)ᴴ = (F z * (A z)⁻¹) * (Y⁻¹).map Complex.ofReal * (F z * (A z)⁻¹)ᴴ := by
    rw [← hAHz, Matrix.conjTranspose_mul]
    have e : F z * (A z)⁻¹ * (A z * L.H z * (A z)ᴴ) * (((A z)⁻¹)ᴴ * (F z)ᴴ) =
        F z * ((A z)⁻¹ * A z) * L.H z * ((A z)ᴴ * ((A z)⁻¹)ᴴ) * (F z)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, hinv1, hinv2]
    simp
  have hd1 : ((F z * L.H z * (F z)ᴴ).det).re ≤ C' := by
    rw [hkey]
    exact hx.1
  have hd2 : 1 ≤ C' * chartRadius L.a_le z ^ k * ((F z * L.H z * (F z)ᴴ).det).re := by
    rw [hkey]
    exact hx.2
  have hpsd : (F z * L.H z * (F z)ᴴ).PosSemidef := by
    rw [hkey]
    have hYp : Y.PosDef := Q.im_posDef _ hw
    exact (subframe_map_posSemidef hYp.inv.posSemidef).mul_mul_conjTranspose_same _
  have hD := hpsd.det_nonneg
  obtain ⟨D, hDdef⟩ : ∃ D, D = (F z * L.H z * (F z)ᴴ).det := ⟨_, rfl⟩
  rw [← hDdef] at hd1 hd2 hD ⊢
  have hnorm : ‖D‖ = D.re := by
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hD
    have e : D = (D.re : ℂ) := by
      apply Complex.ext <;> simp [h2.symm]
    rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_nonneg h1]
  rw [hnorm]
  have hre : 0 ≤ D.re := (Complex.nonneg_iff.1 hD).1
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE1 : 1 ≤ (Real.exp 1 + 2) ^ k := one_le_pow₀ (by linarith [Real.exp_pos 1])
  constructor
  · calc D.re ≤ C' := hd1
      _ ≤ C' * (Real.exp 1 + 2) ^ k := le_mul_of_one_le_right hC'.le hE1
  · have hpow : chartRadius L.a_le z ^ k ≤ ((Real.exp 1 + 2) * (1 + S')) ^ k :=
      pow_le_pow_left₀ (by linarith) hr2 k
    calc (1 : ℝ) ≤ C' * chartRadius L.a_le z ^ k * D.re := hd2
      _ ≤ C' * ((Real.exp 1 + 2) * (1 + S')) ^ k * D.re := by gcongr
      _ = C' * (Real.exp 1 + 2) ^ k * (1 + S') ^ k * D.re := by rw [mul_pow]; ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorSumIdentityBaseChange
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorAny

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S)
    (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact (map_zero f).symm

def gap {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) (S : Type) [CommRing S] [Algebra Ω S]
    (h : Matrix (Fin N) (Fin N) S) : S :=
  algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J -
    algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J

theorem gap_map {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) {S S' : Type} [CommRing S] [Algebra Ω S]
    [CommRing S'] [Algebra Ω S'] (f : S →ₐ[Ω] S') (h : Matrix (Fin N) (Fin N) S) :
    f (gap T c₀ c₁ coef u J S h) = gap T c₀ c₁ coef u J S' (h.map f.toRingHom) := by
  have hm : ∀ (M : Matrix (Fin N) (Fin N) S) (I J : Finset (Fin N)),
      f (minorIJ M I J) = minorIJ (M.map f.toRingHom) I J :=
    fun M I J => (minorIJ_map f.toRingHom M I J).symm
  have hT : (T.map (algebraMap Ω S) * h).map f.toRingHom = T.map (algebraMap Ω S') * h.map f.toRingHom := by
    rw [Matrix.map_mul, Matrix.map_map]
    congr 1
    congr 1
    funext x
    exact f.commutes x
  simp only [gap, map_sub, map_mul, map_sum, AlgHom.commutes, hm, hT]

theorem minor_any : ∀ (Ω : Type) [Field Ω] [Infinite Ω] (N j : ℕ) (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω) (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)), (∀ h : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j h → c₀ * ∑ I, coef I * minorIJ (T * h) I J = c₁ * ∑ I, u I * minorIJ h I J) → ∀ (S : Type) [CommRing S] [Algebra Ω S] (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J = algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J := by
  intro Ω _ _ N j T c₀ c₁ coef u J hyp S _ _ h hh
  have hT : T.map (algebraMap Ω Ω) = T := Matrix.ext fun _ _ => rfl
  have key : ∀ M : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j M → gap T c₀ c₁ coef u J Ω M = 0 := by
    intro M hM
    simp only [gap, hT]
    exact sub_eq_zero.mpr (hyp M hM)
  let G : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) Ω) :=
    Matrix.of fun a b => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X (a, b) else 0
  have hP : gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G = 0 := by
    apply MvPolynomial.funext
    intro x
    show aeval x (gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G) = aeval x 0
    rw [map_zero, gap_map]
    apply key
    intro a b hab
    simp only [G, Matrix.map_apply, Matrix.of_apply, if_neg hab, map_zero]
  have hG : G.map (aeval (fun p : Fin N × Fin N => h p.1 p.2)).toRingHom = h := by
    ext a b
    simp only [G, Matrix.map_apply, Matrix.of_apply]
    split_ifs with hab
    · simp [aeval_X]
    · rw [map_zero]
      exact (hh a b hab).symm
  have hz := congrArg (aeval (fun p : Fin N × Fin N => h p.1 p.2)) hP
  rw [gap_map, hG, map_zero] at hz
  simp only [gap] at hz
  exact sub_eq_zero.mp hz

end GlobalTheory.CompanionTheory.Ar.PB.MinorAny
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolarIdentityFromSymmetricFormsStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polar_identity_from_symmetric_forms : ∀ (σ : Type) [Fintype σ] (D : ℕ) (a : (Fin (D + 1) → σ) → ℝ) (b : (Fin D → σ) → ℝ) (κ : ℕ → ℝ) (ε : σ → ℤ) (a₀ : σ), (∀ (π : Equiv.Perm (Fin (D + 1))) w, a (w ∘ π) = a w) → (∀ (π : Equiv.Perm (Fin D)) w, b (w ∘ π) = b w) → (∀ n : σ → ℤ, n a₀ = 0 → polar (D + 1) a (fun _ x => (n x : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 → polar (D + 1) a (mix (2 * k) (fun x => (ε x : ℝ)) fun x => (n x : ℝ)) = -(2 * κ k) * polar D b (mix (2 * k - 1) (fun x => (ε x : ℝ)) fun x => (n x : ℝ))) → ∀ (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (formPoly (D + 1) a) + eval (fun x => c x + u / 2 * ε x) (formPoly (D + 1) a) = (tsgPoly D κ (linePoly c ε (formPoly D b))).eval u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity | exact GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def v₀ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) := ⟨some p.1, p.2⟩

def v₁ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) :=
  if h : p.1 = k₀ then ⟨none, cast (congrArg ι h) p.2⟩ else ⟨some p.1, p.2⟩

theorem v₁_ne {k₀ : K} {p : Σ k, ι k} (h : p.1 ≠ k₀) : v₁ k₀ p = ⟨some p.1, p.2⟩ := dif_neg h

theorem v₁_self (k₀ : K) (m : ι k₀) : v₁ k₀ ⟨k₀, m⟩ = ⟨none, m⟩ := dif_pos rfl

def fstPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₀ k₀

def sndPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₁ k₀

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def normRhs (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : ℝ :=
  Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) *
      (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
        else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ +
    (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁))

def IsNormFn (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (f : RW.X → ℝ) : Prop :=
  ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F →
    M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ (fstPt k₀ (RW.lift x x)) →
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 →
    (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) →
    f x = normRhs M τ a F z₀ z₁ h t

def IsWChart (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e)
    (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsCompatChart RW.A ψ ∧ M.IsFrame F ∧ (∀ i, σ i ≠ i₀) ∧
    (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) ∧
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) ψ.target) ∧
    ∀ x' ∈ ψ.source, (∀ τ', IsBlockDiag j (H τ' (ψ x')) ∧ (H τ' (ψ x')).det ≠ 0) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ (RW.lift x' x')))) ∧
      ∃ z₀ z₁ : (Σ k, ι k) → ℂ, SameOrbit z₀ (fstPt k₀ (RW.lift x' x')) ∧ SameOrbit z₁ (sndPt k₀ (RW.lift x' x')) ∧
        ∀ τ' i, M.ExactAt F (τ', i) z₀ (H τ' (ψ x')) ∧
          M.ExactAt F (τ', i) z₁ (if τ' = τ then H τ (ψ x') * (1 + Matrix.single cb ca (ψ x' i₀)) else H τ' (ψ x'))

def IsWAtlas (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) : Prop :=
  HoloMap RW.A Rb.A pr ∧
    (∀ x, SameOrbit (Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) ∧
    ∀ x, ∃ ψ kb σ i₀ F H, x ∈ ψ.source ∧ IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H

def IsFibreChart {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N) (ca cb : Fin N)
    {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) : Prop :=
  ∃ (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X),
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) ∧
    ContinuousOn bp Un ∧ (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) ∧
    (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) ∧
    (∀ w ∈ Un, ∀ r s : Fin 2, Gn w r s =
      minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
          (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
        minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧
    (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∀ x₀, FA.Re.π x₀ = ΦYn z → ∃ z₀ : (Σ k, ι k) → ℂ,
      SameOrbit (FA.Re.R.lift x₀ x₀) z₀ ∧ SameOrbit (basePart M.blk z₀) (BM.Rb.lift (bp (Fin.tail z)) (bp (Fin.tail z))) ∧
      ∀ τ' i, M.ExactAt (BM.F l) (τ', i) z₀
        (if τ' = τ then H τ (Fin.tail z) * (1 + Matrix.single cb ca (z 0)) else H τ' (Fin.tail z))) ∧
    ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un →
      q 0 (ΦWn z) = ΦYn (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦWn z) = ΦYn (Fin.tail z)

theorem pullback_pullback {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (P : LocPot X)
    (f : Y → X) (g : Z → Y) (r : Z → X) (hf : Continuous f) (hg : Continuous g) (hr : Continuous r) (h : f ∘ g = r) :
    (P.pullback f hf).pullback g hg = P.pullback r hr := by
  subst h
  rfl

theorem orbit_symm {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  rw [inv_mul_cancel_left₀ (hc p.1)]

theorem orbit_trans {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' z'' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_lattice_by_isotropic_submodule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R.form I → ∃ (g' : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q ∧ LinearMap.ker q = Submodule.span ℂ (R.P '' I) ∧ (∀ a x, q (R.B a x) = R'.B a (q x)) ∧ Set.range R'.P = q '' (R.P '' {x | ∀ y ∈ I, R.form x y = 0}) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  first | exact @GlobalTheory.CompanionTheory.Relay.quotient_lattice_by_isotropic_submodule | exact GlobalTheory.CompanionTheory.Relay.quotient_lattice_by_isotropic_submodule | (intros; apply GlobalTheory.CompanionTheory.Relay.quotient_lattice_by_isotropic_submodule <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationFibreProductCompatibleStatement
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_fibre_product_compatible : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (P : Ideal (MRing ι)) (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (D : ℕ) (σ₁ σ₂ : Type) (S₁ : PB.AnSys D σ₁) (S₂ : PB.AnSys D σ₂) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) (A₁ : HermLine ι₁) (A₂ : HermLine ι₂) (A₁' A₂' : HermLine ι), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsPullHerm κ₁ v₁ A₁ A₁' → IsPullHerm κ₂ v₂ A₂ A₂' → (Re₁.ref a₁).a = A₁.a → (Re₂.ref a₂).a = A₂.a → (∀ x, Re₁.π x ∉ ReciprocityTheory.AnForm.P.bdry S₁.s → Real.log (A₁.h (Re₁.R.lift x x)) = Real.log ((Re₁.ref a₁).h (Re₁.R.lift x x)) + S₁.ph a₁ (Re₁.π x)) → (∀ x, Re₂.π x ∉ ReciprocityTheory.AnForm.P.bdry S₂.s → Real.log (A₂.h (Re₂.R.lift x x)) = Real.log ((Re₂.ref a₂).h (Re₂.R.lift x x)) + S₂.ph a₂ (Re₂.π x)) → IsMultiProjPrime P → IsoLineOn P {z | z ∈ mcPts P ∧ evC z β ≠ 0} A₁' A₂' → SameSing Re₁ Re₂ P κ₁ v₁ κ₂ v₂ β a₁ a₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine | exact GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_lattice_eigen_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection | exact GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection | (intros; apply GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

def selM {N : ℕ} (S : Finset (Fin N)) : Matrix (Fin N) (Fin S.card) ℂ :=
  Matrix.of fun a b => if a = S.orderEmbOfFin rfl b then 1 else 0

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end


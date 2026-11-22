import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityPointwiseEstimate
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem pointwise_energy_ineq : ∀ {W ι : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι] (w v : W) (Y : ι → W) (L : ι → ℝ) (A : W →L[ℝ] W) (C₁ C c φ : ℝ), 0 ≤ C₁ → C₁ * (1 + Fintype.card ι) ≤ C → c ≤ 0 → 0 ≤ φ → (∀ p, |L p| ≤ C₁) → c * C * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2) + φ * (2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ) - (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ ≤ (‖A‖ + 1) * (φ * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2)) := by
  intro W ι _ _ _ w v Y L A C₁ C c φ hC₁ hC hc hφ hL
  have hS0 : 0 ≤ ∑ p, ‖Y p‖ ^ 2 := Finset.sum_nonneg fun p _ => by positivity
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ p, ‖Y p‖ ^ 2 := ⟨_, rfl⟩
  rw [← hS] at hS0 ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = ‖w‖ ^ 2 + (1 / 4) * S + ‖v‖ ^ 2 := ⟨_, rfl⟩
  rw [← hD]
  have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hv2 : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hwD : ‖w‖ ^ 2 ≤ D := by rw [hD]; linarith
  have hSD : (1 / 4) * S ≤ D := by rw [hD]; linarith

  have hterm : ∀ p, -(c * L p * ⟪Y p, w⟫_ℝ) ≤ (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
    intro p
    have hin : |⟪Y p, w⟫_ℝ| ≤ ‖Y p‖ * ‖w‖ := abs_real_inner_le_norm _ _
    have hmul : |L p * ⟪Y p, w⟫_ℝ| ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
      rw [abs_mul]
      have h2 : ‖Y p‖ * ‖w‖ ≤ (1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2) := by
        nlinarith [sq_nonneg (‖Y p‖ - ‖w‖)]
      exact mul_le_mul (hL p) (hin.trans h2) (abs_nonneg _) hC₁
    have hle : L p * ⟪Y p, w⟫_ℝ ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      (le_abs_self _).trans hmul
    have := mul_le_mul_of_nonneg_left hle (neg_nonneg.2 hc)
    calc -(c * L p * ⟪Y p, w⟫_ℝ) = (-c) * (L p * ⟪Y p, w⟫_ℝ) := by ring
      _ ≤ (-c) * (C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))) := this
      _ = (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by ring
  have hsum : -(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      ≤ (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2) := by
    have h1 : ∑ p, -(c * L p * ⟪Y p, w⟫_ℝ)
        ≤ ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      Finset.sum_le_sum fun p _ => hterm p
    have h2 : ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))
        = (-c) * C₁ * ((1 / 2) * (S + (Fintype.card ι : ℝ) * ‖w‖ ^ 2)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← hS]
      simp [Finset.card_univ]
    rw [Finset.sum_neg_distrib, h2] at h1
    linarith
  have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hbr : (1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2
      ≤ (1 + (Fintype.card ι : ℝ)) * D := by
    nlinarith [mul_le_mul_of_nonneg_left hwD hN0, mul_nonneg hN0 hw2]
  have hcC : (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
      ≤ (-c) * C * D := by
    have hnc : 0 ≤ -c := neg_nonneg.2 hc
    calc (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
        ≤ (-c) * C₁ * ((1 + (Fintype.card ι : ℝ)) * D) :=
          mul_le_mul_of_nonneg_left hbr (mul_nonneg hnc hC₁)
      _ = (-c) * (C₁ * (1 + (Fintype.card ι : ℝ))) * D := by ring
      _ ≤ (-c) * C * D :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hnc) hD0

  have hAv : ⟪A v, w⟫_ℝ ≤ ‖A‖ * ‖v‖ * ‖w‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _))
  have hwv : ⟪w, v⟫_ℝ ≤ ‖w‖ * ‖v‖ := real_inner_le_norm _ _
  have hvw : 2 * (‖v‖ * ‖w‖) ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖v‖ - ‖w‖)]
  have hvwD : 2 * (‖v‖ * ‖w‖) ≤ D := by rw [hD] at *; linarith
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hbrack : 2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ ≤ (‖A‖ + 1) * D := by
    have h3 : ‖A‖ * (2 * (‖v‖ * ‖w‖)) ≤ ‖A‖ * D := mul_le_mul_of_nonneg_left hvwD hA0
    nlinarith
  have hφ' := mul_le_mul_of_nonneg_left hbrack hφ
  have hrew : (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      = -(-(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ) := by ring
  rw [hrew]
  nlinarith

end GlobalTheory.CompanionTheory.WaveSpd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityTimeDerivative
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.DensDeriv

section Generic

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def tD (u : ℝ → E → W) : ℝ → E → W := fun s y => deriv (fun r => u r y) s

def rD (L : E →L[ℝ] E) (u : ℝ → E → W) : ℝ → E → W := fun s y => fderiv ℝ (u s) y (L y)

variable {U : Set E} {u : ℝ → E → W}

theorem contDiffAt_F (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    ContDiffAt ℝ ∞ (Function.uncurry u) (s, y) :=
  hu.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ _, hy⟩)

theorem hasFDerivAt_F (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y)) (s, y) :=
  ((contDiffAt_F hU hu s hy).differentiableAt (by simp)).hasFDerivAt

theorem hasDerivAt_line (y : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ((r, y) : ℝ × E)) ((1 : ℝ), (0 : E)) s :=
  (hasDerivAt_id s).prodMk (hasDerivAt_const s y)

theorem hasDerivAt_time (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    HasDerivAt (fun r => u r y) (fderiv ℝ (Function.uncurry u) (s, y) (1, 0)) s :=
  by
  have h : HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y))
      ((fun r : ℝ => ((r, y) : ℝ × E)) s) := hasFDerivAt_F hU hu s hy
  exact h.comp_hasDerivAt s (hasDerivAt_line y s)

theorem tD_eq (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    tD u s y = fderiv ℝ (Function.uncurry u) (s, y) (1, 0) :=
  (hasDerivAt_time hU hu s hy).deriv

theorem rD_eq (L : E →L[ℝ] E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    rD L u s y = fderiv ℝ (Function.uncurry u) (s, y) (0, L y) := by
  have h2 := (hasFDerivAt_F hU hu s hy).comp y (hasFDerivAt_prodMk_right s y)
  have h3 : fderiv ℝ (u s) y = _ := HasFDerivAt.fderiv (f := u s) h2
  simp only [rD]
  rw [h3]
  simp

theorem contDiffOn_fderivF (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ U) :=
  hu.fderiv_of_isOpen (isOpen_univ.prod hU) (by simp)

theorem contDiffOn_tD (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (Function.uncurry (tD u)) (Set.univ ×ˢ U) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E => fderiv ℝ (Function.uncurry u) p (1, 0))
      (Set.univ ×ˢ U) :=
    (contDiffOn_fderivF hU hu).clm_apply contDiffOn_const
  refine h.congr ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact tD_eq hU hu s hy

theorem tD_rD (L : E →L[ℝ] E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    HasDerivAt (fun r => rD L u r y) (fderiv ℝ (tD u s) y (L y)) s := by
  set F := Function.uncurry u with hF
  have hD : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (s, y)) (s, y) :=
    (((contDiffOn_fderivF hU hu).contDiffAt
      ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
      (by simp)).hasFDerivAt
  have hL : HasDerivAt (fun r => rD L u r y)
      (fderiv ℝ (fderiv ℝ F) (s, y) (1, 0) (0, L y)) s := by
    have h2 : HasDerivAt (fun r => fderiv ℝ F (r, y))
        (fderiv ℝ (fderiv ℝ F) (s, y) (1, 0)) s :=
      hD.comp_hasDerivAt s (hasDerivAt_line y s)
    have h3 := h2.clm_apply (hasDerivAt_const s ((0 : ℝ), L y))
    simp only [ContinuousLinearMap.map_zero, add_zero] at h3
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    exact rD_eq L hU hu r hy
  have hR : HasFDerivAt (tD u s)
      (((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).comp
        (fderiv ℝ (fderiv ℝ F) (s, y))).comp (ContinuousLinearMap.inr ℝ ℝ E)) y := by
    have h2 := (ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).hasFDerivAt.comp y
      (hD.comp y (hasFDerivAt_prodMk_right s y))
    refine HasFDerivAt.congr_of_eventuallyEq h2 ?_
    filter_upwards [hU.mem_nhds hy] with z hz
    exact tD_eq hU hu s hz
  have hsym : IsSymmSndFDerivAt ℝ F (s, y) :=
    (contDiffAt_F hU hu s hy).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [hR.fderiv]
  have e : fderiv ℝ (fderiv ℝ F) (s, y) (1, 0) (0, L y)
      = fderiv ℝ (fderiv ℝ F) (s, y) (0, L y) (1, 0) := hsym _ _
  simpa [e] using hL

end Generic

section Mat

variable {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g * X
      map_add' := fun a b => Matrix.add_mul a b X
      map_smul' := fun c a => by simp }

theorem sm_dt {u : ℝ → Mat n → W} (hu : Sm u) : Sm (dt u) :=
  contDiffOn_tD isOpen_GLs hu

theorem hasDerivAt_dt {u : ℝ → Mat n → W} (hu : Sm u) (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun r => u r y) (dt u s y) s := by
  have h := hasDerivAt_time isOpen_GLs hu s hy
  rwa [← tD_eq isOpen_GLs hu s hy] at h

theorem hasDerivAt_Rt {u : ℝ → Mat n → W} (hu : Sm u) (X : Mat n) (s : ℝ) {y : Mat n}
    (hy : y ∈ GLs n) : HasDerivAt (fun r => Rt X u r y) (Rr X (dt u s) y) s :=
  tD_rD (mulR X) isOpen_GLs hu s hy

end Mat

end GlobalTheory.CompanionTheory.WaveSpd.DensDeriv

open GlobalTheory.CompanionTheory.WaveSpd.DensDeriv in

theorem GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens {n : ℕ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (u : ℝ → Mat n → W) (hu : Sm u) (s : ℝ) (y : Mat n)
    (hy : y ∈ GLs n) :
    HasDerivAt (fun r => dens u r y)
      (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ
        + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ
        + 2 * ⟪dt u s y, u s y⟫_ℝ) s := by
  have h1 := (hasDerivAt_dt (sm_dt hu) s hy).norm_sq
  have h3 := (hasDerivAt_dt hu s hy).norm_sq
  have h2 : HasDerivAt (fun r => ∑ p : Ix n, ‖Rt (hm p) u r y‖ ^ 2)
      (∑ p : Ix n, 2 * ⟪Rt (hm p) u s y, Rr (hm p) (dt u s) y⟫_ℝ) s := by
    have := HasDerivAt.fun_sum (u := Finset.univ)
      (fun (p : Ix n) _ => (hasDerivAt_Rt hu (hm p) s hy).norm_sq)
    exact this
  have h := (h1.add (h2.const_mul (1 / 4 : ℝ))).add h3
  refine (h.congr_deriv ?_)
  rw [real_inner_comm (dt (dt u) s y), real_inner_comm (dt u s y) (u s y), ← Finset.mul_sum]
  simp only [real_inner_comm (Rt _ u s y)]
  ring
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpowTSucc
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Ibp

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem val_mem (y : G n) : y.val ∈ GLs n := by
  show Matrix.det y.val ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

section Loc

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_congr (X : Mat n) {f g : Mat n → V} (h : Set.EqOn f g (GLs n)) :
    Set.EqOn (Rd X f) (Rd X g) (GLs n) := by
  intro y hy
  show fderiv ℝ f y (y * X) = fderiv ℝ g y (y * X)
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hy) h)]

theorem Eu_congr (s : Bool) (a b : Fin n) {f g : Mat n → V} (h : Set.EqOn f g (GLs n)) :
    Set.EqOn (Eu s a b f) (Eu s a b g) (GLs n) := by
  intro y hy
  unfold Eu
  simp only [Pi.smul_apply, Pi.add_apply]
  rw [Rd_congr _ h hy, Rd_congr _ h hy]

theorem diffAt {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {y : Mat n} (hy : y ∈ GLs n) :
    DifferentiableAt ℝ f y :=
  (hf.contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)

theorem Rd_add (X : Mat n) {f g : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hg : ContDiffOn ℝ ∞ g (GLs n)) : Set.EqOn (Rd X (f + g)) (Rd X f + Rd X g) (GLs n) := by
  intro y hy
  have e := (((diffAt hf hy).hasFDerivAt).add ((diffAt hg hy).hasFDerivAt)).fderiv
  show fderiv ℝ (f + g) y (y * X) = fderiv ℝ f y (y * X) + fderiv ℝ g y (y * X)
  exact congrArg (fun L => L (y * X)) e

theorem sm_sum {ι : Type} (t : Finset ι) (F : ι → Mat n → V)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) : ContDiffOn ℝ ∞ (∑ i ∈ t, F i) (GLs n) := by
  rw [Finset.sum_fn]
  exact ContDiffOn.sum fun i _ => hF i

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext y
  simp [Rd]

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Eu_add (s : Bool) (a b : Fin n) {f g : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hg : ContDiffOn ℝ ∞ g (GLs n)) :
    Set.EqOn (Eu s a b (f + g)) (Eu s a b f + Eu s a b g) (GLs n) := by
  intro y hy
  unfold Eu
  simp only [Pi.smul_apply, Pi.add_apply]
  rw [Rd_add _ hf hg hy, Rd_add _ hf hg hy]
  simp only [Pi.add_apply, smul_add]
  abel

theorem Eu_sum (s : Bool) (a b : Fin n) {ι : Type} (t : Finset ι) (F : ι → Mat n → V)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) :
    Set.EqOn (Eu s a b (∑ i ∈ t, F i)) (∑ i ∈ t, Eu s a b (F i)) (GLs n) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro y _; simp [Eu_zero]
  | insert i t hi ih =>
    intro y hy
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Eu_add s a b (hF i) (sm_sum t F hF) hy]
    simp only [Pi.add_apply, ih hy]

theorem Cpt_zero : Cpt (0 : Mat n → V) := ⟨0, fun _ _ _ => rfl⟩

theorem Cpt_add {f g : Mat n → V} (hf : Cpt f) (hg : Cpt g) : Cpt (f + g) := by
  obtain ⟨R1, h1⟩ := hf
  obtain ⟨R2, h2⟩ := hg
  refine ⟨max R1 R2, fun y hy hR => ?_⟩
  rw [Pi.add_apply, h1 y hy (lt_of_le_of_lt (le_max_left _ _) hR),
    h2 y hy (lt_of_le_of_lt (le_max_right _ _) hR), add_zero]

theorem Cpt_smul (c : ℂ) {f : Mat n → V} (hf : Cpt f) : Cpt (c • f) := by
  obtain ⟨R, h⟩ := hf
  exact ⟨R, fun y hy hR => by rw [Pi.smul_apply, h y hy hR, smul_zero]⟩

theorem Cpt_sum {ι : Type} (t : Finset ι) (F : ι → Mat n → V) (hF : ∀ i, Cpt (F i)) :
    Cpt (∑ i ∈ t, F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Cpt_zero
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact Cpt_add (hF i) ih

theorem Cpt_Rd (hL : LgFacts) (X : Mat n) {f : Mat n → V} (hf : Cpt f) : Cpt (Rd X f) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R, fun y hy hy' => ?_⟩
  have hc : ContinuousOn lg (GLs n) := ((hL n).2.2.2.1).continuousOn
  have hev : f =ᶠ[nhds y] (fun _ => (0 : V)) := by
    have h1 : ∀ᶠ z in nhds y, z ∈ GLs n := isOpen_GLs.mem_nhds hy
    have h2 : ∀ᶠ z in nhds y, R < lg z :=
      (hc.continuousAt (isOpen_GLs.mem_nhds hy)).preimage_mem_nhds (Ioi_mem_nhds hy')
    filter_upwards [h1, h2] with z hz1 hz2
    exact hR z hz1 hz2
  show fderiv ℝ f y (y * X) = 0
  rw [hev.fderiv_eq]
  simp

theorem Cpt_Eu (hL : LgFacts) (s : Bool) (a b : Fin n) {f : Mat n → V} (hf : Cpt f) :
    Cpt (Eu s a b f) :=
  Cpt_smul _ (Cpt_add (Cpt_Rd hL _ hf) (Cpt_smul _ (Cpt_Rd hL _ hf)))

theorem sm_Rd (hR : RCalc) (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  ((hR n).1 V f hf).1 X

theorem sm_Eu (hR : RCalc) (s : Bool) (a b : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) :=
  ((sm_Rd hR _ hf).add ((sm_Rd hR _ hf).const_smul _)).const_smul _

theorem sm_Epow (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    rw [Epow.eq_1]
    dsimp only
    split_ifs
    · exact hf
    · exact contDiffOn_const
  | succ m ih =>
    show ContDiffOn ℝ ∞ (Epow s (Nat.succ m) a b f) (GLs n)
    rw [Epow.eq_2]
    exact sm_sum _ _ fun c => sm_Eu hR _ _ _ (ih _ _)

theorem sm_EpowT (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (EpowT s m a b f) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    rw [EpowT.eq_1]
    dsimp only
    split_ifs
    · exact hf
    · exact contDiffOn_const
  | succ m ih =>
    show ContDiffOn ℝ ∞ (EpowT s (Nat.succ m) a b f) (GLs n)
    rw [EpowT.eq_2]
    exact sm_sum _ _ fun c => sm_Eu hR _ _ _ (ih _ _)

theorem Cpt_Epow (hL : LgFacts) (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} (hf : Cpt f) :
    Cpt (Epow s m a b f) := by
  induction m generalizing a b with
  | zero =>
    rw [Epow.eq_1]
    dsimp only
    split_ifs
    · exact hf
    · exact Cpt_zero
  | succ m ih =>
    show Cpt (Epow s (Nat.succ m) a b f)
    rw [Epow.eq_2]
    exact Cpt_sum _ _ fun c => Cpt_Eu hL _ _ _ (ih _ _)

theorem EpowT_succ' (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {h : Mat n → V}
    (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    Set.EqOn (EpowT s (m + 1) b a h) (∑ c, EpowT s m b c (Eu s a c h)) (GLs n) := by
  induction m generalizing b with
  | zero =>
    intro y _
    show EpowT s (Nat.succ 0) b a h y = _
    rw [EpowT.eq_2]
    simp only [EpowT.eq_1, Finset.sum_apply]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    all_goals first
      | (simp; done)
      | (intro c _ hc; simp [hc, Ne.symm hc, Eu_zero])
  | succ m ih =>
    intro y hy
    show EpowT s (Nat.succ (m + 1)) b a h y = _
    rw [EpowT.eq_2]
    simp only [Finset.sum_apply]
    have key : ∀ c, Eu s c b (EpowT s (m + 1) c a h) y =
        ∑ d, Eu s c b (EpowT s m c d (Eu s a d h)) y := by
      intro c
      rw [Eu_congr s c b (ih c) hy,
        Eu_sum s c b Finset.univ _ (fun d => sm_EpowT hR s m c d (sm_Eu hR s a d hh)) hy,
        Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    show _ = EpowT s (Nat.succ m) b d (Eu s a d h) y
    simp only [EpowT.eq_2, Finset.sum_apply]

end Loc

end GlobalTheory.CompanionTheory.WaveMult.Ibp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRrEqZero
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem Rd_ofReal_eq {n : ℕ} {Ψ : Mat n → ℝ} (hΨ : ContDiffOn ℝ ∞ Ψ (GLs n)) (X : Mat n)
    {y : Mat n} (hy : y ∈ GLs n) :
    Rd X (fun z => (Ψ z : ℂ)) y = ((Rr X Ψ y : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ Ψ y :=
    ((hΨ y hy).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
  have h : HasFDerivAt (fun z => (Ψ z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Ψ y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hd.hasFDerivAt
  simp only [Rd, Rr, h.fderiv]
  rfl

theorem integral_Rr_eq_zero : RCalc → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (Ψ : Mat n → ℝ), ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
  intro hR n _ _ μ _ Ψ hΨ hc X
  have hf : ContDiffOn ℝ ∞ (fun z => (Ψ z : ℂ)) (GLs n) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hΨ
  have hcf : Cpt (fun z => (Ψ z : ℂ)) := by
    obtain ⟨R, hR'⟩ := hc
    exact ⟨R, fun y hy h => by simp [hR' y hy h]⟩
  have h0 := (hR n).2.2 μ ℂ (fun z => (Ψ z : ℂ)) hf hcf X
  have h1 : (fun y : G n => Rd X (fun z => (Ψ z : ℂ)) y.val) =
      fun y : G n => ((Rr X Ψ y.val : ℝ) : ℂ) :=
    funext fun y => Rd_ofReal_eq hΨ X (val_mem_GLs y)
  rw [h1, integral_complex_ofReal] at h0
  exact Complex.ofReal_eq_zero.1 h0

end GlobalTheory.CompanionTheory.WaveSpd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpreadStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_models_spread : GlobalTheory.SpreadingModels.SchemeModels := by
  first | exact @GlobalTheory.CompanionTheory.NoethApprox.schemeModels | exact GlobalTheory.CompanionTheory.NoethApprox.schemeModels | (intros; apply GlobalTheory.CompanionTheory.NoethApprox.schemeModels <;> assumption)
end


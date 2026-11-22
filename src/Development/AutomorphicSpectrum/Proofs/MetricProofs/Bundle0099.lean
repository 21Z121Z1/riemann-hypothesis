import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0091
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0089
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0093
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0094

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV

theorem isStepRows_stepCols {N j : ℕ} (i : Fin N) : IsStepRows N j i (stepCols N j i) := by
  refine ⟨rfl, ?_⟩
  intro a ha
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  split_ifs at ha ⊢ with h
  · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha.1
  · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases h : (i : ℕ) + 1 ≤ j
  · have : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
      omega
    simp [e] at this
  · have : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
      omega
    simp [e] at this

theorem minorIJ_one_ne {N : ℕ} {I J : Finset (Fin N)} (h : I ≠ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I J = 0 := by
  unfold minorIJ
  split_ifs with e
  · obtain ⟨a, ha, hb⟩ : ∃ a ∈ I, a ∉ J := by
      by_contra hc
      push_neg at hc
      exact h (Finset.eq_of_subset_of_card_le hc e.ge)
    obtain ⟨r, hr⟩ : ∃ r, I.orderEmbOfFin e r = a := by
      have h2 : a ∈ Set.range (I.orderEmbOfFin e) := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      exact h2
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    rw [Matrix.submatrix_apply, hr]
    exact Matrix.one_apply_ne fun q => hb (q ▸ Finset.orderEmbOfFin_mem _ _ _)
  · rfl

theorem minorIJ_one_same {N : ℕ} (I : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem sum_minor_one {N : ℕ} (a : Finset (Fin N) → ℂ) (C : Finset (Fin N)) :
    ∑ I, a I * minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I C = a C := by
  rw [Finset.sum_eq_single C (fun I _ h => by rw [minorIJ_one_ne h, mul_zero])
    (fun h => absurd (Finset.mem_univ C) h), minorIJ_one_same, mul_one]

theorem sum_minor_mul {N j : ℕ} (hj : j ≤ N) (i : Fin N) {μ : Type} (a₁ a₂ : μ → Finset (Fin N) → ℂ)
    (S : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hS : ∀ m I', IsStepRows N j i I' → ∑ I, a₁ m I * minorIJ S I I' = c * a₂ m I')
    (h : Matrix (Fin N) (Fin N) ℂ) (hh : IsBlockDiag j h) (m : μ) :
    ∑ I, a₁ m I * minorIJ (S * h) I (stepCols N j i) = c * ∑ I, a₂ m I * minorIJ h I (stepCols N j i) := by
  obtain ⟨cb, off, -, -⟩ := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj
  have off' : ∀ I', ¬ IsStepRows N j i I' → minorIJ h I' (stepCols N j i) = 0 := fun I' hI =>
    (off h I' hh hI).resolve_right (stepCols_ne_empty i)
  simp only [cb, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j i I'
  · rw [← mul_assoc, ← hS m I' hI, Finset.sum_mul]
    exact Finset.sum_congr rfl fun I _ => by ring
  · simp [off' I' hI]

theorem coef_ne_zero {N j : ℕ} (hj : j ≤ N) (i : Fin N) {μ : Type} [Fintype μ] (a₁ a₂ : μ → Finset (Fin N) → ℂ)
    (b : μ → ℂ) (S S' : Matrix (Fin N) (Fin N) ℂ) (c : ℂ)
    (hS : ∀ m I', IsStepRows N j i I' → ∑ I, a₁ m I * minorIJ S I I' = c * a₂ m I')
    (hd : IsBlockDiag j S') (hSS : S * S' = 1) (hb : ∑ m, b m * a₁ m (stepCols N j i) = 1) : c ≠ 0 := by
  intro hc
  have h0 : ∀ m, a₁ m (stepCols N j i) = 0 := fun m => by
    have e1 := sum_minor_mul hj i a₁ a₂ S c hS S' hd m
    rw [hSS, hc, zero_mul, sum_minor_one (a₁ m)] at e1
    exact e1
  simp [h0] at hb

theorem map_inv_eq {Ω Ω₂ : Type} [Field Ω] [Field Ω₂] (φ : Ω →+* Ω₂) {N : ℕ} (T : Matrix (Fin N) (Fin N) Ω)
    (hd : T.det ≠ 0) : T⁻¹.map φ = (T.map φ)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]
  exact Matrix.map_one _ (map_zero φ) (map_one φ)

theorem map_rel {Ω Ω₂ : Type} [Field Ω] [Field Ω₂] (φ : Ω →+* Ω₂) {N : ℕ} {μ : Type}
    (u₁ u₂ : μ → Finset (Fin N) → Ω) (T₁ T₂ : Matrix (Fin N) (Fin N) Ω) (h₁ : T₁.det ≠ 0) (ρ : Ω)
    (P : Finset (Fin N) → Prop)
    (h : ∀ m I', P I' → ∑ I, u₁ m I * minorIJ (T₁⁻¹ * T₂) I I' = ρ * u₂ m I') :
    ∀ m I', P I' → ∑ I, φ (u₁ m I) * minorIJ ((T₁.map φ)⁻¹ * T₂.map φ) I I' = φ ρ * φ (u₂ m I') :=
  fun m I' hI' => by
    rw [← map_inv_eq φ T₁ h₁, ← Matrix.map_mul, ← map_mul, ← h m I' hI', map_sum]
    exact Finset.sum_congr rfl fun I _ => by rw [map_mul, minorIJ_map]

section Values

variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {Ω₂ : Type} [Field Ω₂]
  {x₂ : (Σ k, ι₂ k) → Ω₂} {zb : (Σ k, ι₂ k) → ℂ}

theorem reg_values (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N j : ℕ} (i : Fin N) {μ : Type} [Fintype μ]
    (U₁ U₂ : μ → Finset (Fin N) → Ω₂) (V : μ → Ω₂) (A : Matrix (Fin N) (Fin N) Ω₂) (r : Ω₂)
    (I₀ : Finset (Fin N)) (hI₀ : IsStepRows N j i I₀)
    (hU₁ : ∀ m I, RegAt x₂ (mCoordIdeal zb) (U₁ m I)) (hU₂ : ∀ m I, RegAt x₂ (mCoordIdeal zb) (U₂ m I))
    (hV : ∀ m, RegAt x₂ (mCoordIdeal zb) (V m)) (hA : ∀ a b, RegAt x₂ (mCoordIdeal zb) (A a b))
    (hrel : ∀ m I', IsStepRows N j i I' → ∑ I, U₁ m I * minorIJ A I I' = r * U₂ m I')
    (hinv : ∑ m, V m * U₂ m I₀ = 1) :
    RegAt x₂ (mCoordIdeal zb) r ∧ ∀ m I', IsStepRows N j i I' →
      ∑ I, valAt x₂ (U₁ m I) zb * minorIJ (valMat x₂ zb A) I I' = valAt x₂ r zb * valAt x₂ (U₂ m I') zb := by
  have hsum : ∀ m I', RegAt x₂ (mCoordIdeal zb) (∑ I, U₁ m I * minorIJ A I I') ∧
      valAt x₂ (∑ I, U₁ m I * minorIJ A I I') zb =
        ∑ I, valAt x₂ (U₁ m I) zb * minorIJ (valMat x₂ zb A) I I' := fun m I' => by
    obtain ⟨h1, h2⟩ := reg_sum hz Finset.univ (fun I => U₁ m I * minorIJ A I I') fun I _ =>
      ValRing.regAt_mul (hU₁ m I) (reg_minor hz hA I I').1
    refine ⟨h1, h2.trans (Finset.sum_congr rfl fun I _ => ?_)⟩
    rw [(reg_mul hz (hU₁ m I) (reg_minor hz hA I I').1).2, (reg_minor hz hA I I').2]
  have hr : RegAt x₂ (mCoordIdeal zb) r := by
    have e : r = ∑ m, V m * ∑ I, U₁ m I * minorIJ A I I₀ := by
      simp only [hrel _ I₀ hI₀]
      calc r = r * ∑ m, V m * U₂ m I₀ := by rw [hinv, mul_one]
        _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    rw [e]
    exact (reg_sum hz _ _ fun m _ => ValRing.regAt_mul (hV m) (hsum m I₀).1).1
  refine ⟨hr, fun m I' hI' => ?_⟩
  rw [← (hsum m I').2, hrel m I' hI']
  exact (reg_mul hz hr (hU₂ m I')).2

theorem valAt_one' (hz : zb ∈ mcPts (mCoordIdeal x₂)) : valAt x₂ (1 : Ω₂) zb = 1 :=
  (ValRing.regAt_valAt_ring K₂ ι₂ Ω₂ x₂ zb hz).2.2.2.1

theorem valAt_zero' (hz : zb ∈ mcPts (mCoordIdeal x₂)) : valAt x₂ (0 : Ω₂) zb = 0 :=
  (ValRing.regAt_valAt_ring K₂ ι₂ Ω₂ x₂ zb hz).2.2.1

theorem valMat_one (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N : ℕ} :
    valMat x₂ zb (1 : Matrix (Fin N) (Fin N) Ω₂) = 1 := by
  ext a b
  show valAt x₂ ((1 : Matrix (Fin N) (Fin N) Ω₂) a b) zb = _
  by_cases e : a = b
  · subst e
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, valAt_one' hz]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, valAt_zero' hz]

theorem valMat_blockDiag (hz : zb ∈ mcPts (mCoordIdeal x₂)) {N j : ℕ} {A : Matrix (Fin N) (Fin N) Ω₂}
    (hA : IsBlockDiag j A) : IsBlockDiag j (valMat x₂ zb A) := fun a b h => by
  show valAt x₂ (A a b) zb = 0
  rw [hA a b h, valAt_zero' hz]

end Values

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₂ : Type) [Field Ω₂] (x₂ : (Σ k, ι₂ k) → Ω₂) (φ : M.Ω →+* Ω₂) (zb : (Σ k, ι₂ k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal x₂) → M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → (∀ (m : ι k) (I : Finset (Fin N)), RegAt x₂ (mCoordIdeal zb) (φ (F₁.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₁.u' I ⟨k, m⟩)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u' I ⟨k, m⟩))) → (∀ a b, RegAt x₂ (mCoordIdeal zb) ((((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) a b) ∧ RegAt x₂ (mCoordIdeal zb) ((((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) a b)) → ∃ c : ℂ, c ≠ 0 ∧ ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, ∑ I, valAt x₂ (φ (F₁.u ⟨k, m⟩ I)) zb * minorIJ (CovMap.LocImg.valMat x₂ zb (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * h) I (stepCols N j p.2) = c * ∑ I, valAt x₂ (φ (F₂.u ⟨k, m⟩ I)) zb * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K₂ _ ι₂ _ Ω₂ _ x₂ φ zb F₁ F₂ hz hF₁ hF₂ hc₁ hc₂ p k hp hu hS
  obtain ⟨ρ, -, hρ⟩ := GlobalTheory.T.frame_change_scalar_factor K ι Φ y Ψ N j M F₁ F₂ hF₁ hF₂ hc₁ hc₂ p k hp
  have hd₁ := (hF₁.1 p.1).2
  have hd₂ := (hF₂.1 p.1).2
  have hstep : IsStepRows N j p.2 (stepCols N j p.2) := isStepRows_stepCols p.2
  have hinv : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F →
      ∑ m : ι k, φ (F.u' (stepCols N j p.2) ⟨k, m⟩) * φ (F.u ⟨k, m⟩ (stepCols N j p.2)) = 1 := fun F hF => by
    have e := hF.2.2.1 p k hp _ _ hstep hstep
    rw [if_pos rfl] at e
    rw [← map_one φ, ← e, map_sum]
    exact Finset.sum_congr rfl fun m _ => (map_mul φ _ _).symm
  have hrel := map_rel φ (fun (m : ι k) I => F₁.u ⟨k, m⟩ I) (fun (m : ι k) I => F₂.u ⟨k, m⟩ I) _ _ hd₁ ρ
    (IsStepRows N j p.2) hρ
  obtain ⟨hr, hval⟩ := reg_values hz p.2 (fun (m : ι k) I => φ (F₁.u ⟨k, m⟩ I))
    (fun (m : ι k) I => φ (F₂.u ⟨k, m⟩ I)) (fun m : ι k => φ (F₂.u' (stepCols N j p.2) ⟨k, m⟩)) _ (φ ρ) _ hstep
    (fun m I => (hu m I).1) (fun m I => (hu m I).2.1) (fun m => (hu m _).2.2.2) (fun a b => (hS a b).1) hrel
    (hinv F₂ hF₂)
  refine ⟨valAt x₂ (φ ρ) zb, ?_, fun h hh m => sum_minor_mul M.j_le p.2 _ _ _ _ hval h hh m⟩
  have hu₂ : IsUnit (F₂.T p.1).det := isUnit_iff_ne_zero.2 hd₂
  have hu₁ : IsUnit (F₁.T p.1).det := isUnit_iff_ne_zero.2 hd₁
  have e21 : ((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ = ((F₂.T p.1)⁻¹ * F₁.T p.1).map φ := by
    rw [Matrix.map_mul, map_inv_eq φ _ hd₂]
  have e12 : ((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ = ((F₁.T p.1)⁻¹ * F₂.T p.1).map φ := by
    rw [Matrix.map_mul, map_inv_eq φ _ hd₁]
  have hprod : (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * (((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) = 1 := by
    rw [e12, e21, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₂,
      Matrix.nonsing_inv_mul _ hu₁]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hbd : IsBlockDiag j (((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) := by
    rw [e21]
    exact ((((hF₂.1 p.1).1.inv hu₂).mul (hF₁.1 p.1).1).map φ)
  have hSS := (regMat_mul hz (fun a b => (hS a b).1) (fun a b => (hS a b).2)).2
  rw [hprod, valMat_one hz] at hSS
  refine coef_ne_zero M.j_le p.2 _ _ (fun m : ι k => valAt x₂ (φ (F₁.u' (stepCols N j p.2) ⟨k, m⟩)) zb) _ _ _ hval
    (valMat_blockDiag hz hbd) hSS.symm ?_
  have e := (reg_sum hz Finset.univ
    (fun m : ι k => φ (F₁.u' (stepCols N j p.2) ⟨k, m⟩) * φ (F₁.u ⟨k, m⟩ (stepCols N j p.2)))
    fun m _ => ValRing.regAt_mul (hu m _).2.2.1 (hu m _).1).2
  rw [hinv F₁ hF₁, valAt_one' hz] at e
  rw [e]
  exact Finset.sum_congr rfl fun m _ => (reg_mul hz (hu m _).2.2.1 (hu m _).1).2.symm

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistCompatStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_twist_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (rk (CMType H) D.p D.q (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (n (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ))) = if a = b then 1 else 0) ∧ ∀ l, ((𝔐'.V (.inl τ)).gr (Fl.b (.inl τ)) l).IsGenAt p' (U l l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistDegreeStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_twist_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (rk (CMType H) D.p D.q (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (n (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ))) = if a = b then 1 else 0) ∧ ∀ l : Fin D.q, ((𝔐'.V (.inr τ)).gr (Fl.b (.inr τ)) l.rev).IsGenAt p' (U l l)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFrameMetricNearPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_frame_metric_near_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (V : Set X) (y₀ : X) (zb : X → (Σ k, baseIdx ι M.blk k) → ℂ) (Hm : X → Matrix (Fin N) (Fin N) ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) (a : Fin N), IsOpen V → y₀ ∈ V → (∀ q, A.HoloOn V fun w => zb w q) → (∀ w ∈ V, zb w ∈ mcPts (mCoordIdeal M.x)) → (∀ w ∈ V, M.GoodAt F (mCoordIdeal (zb w))) → (∀ r s, A.HoloOn V fun w => Hm w r s) → (∀ w ∈ V, IsBlockDiag j (Hm w) ∧ (Hm w).det ≠ 0) → ∃ V' : Set X, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ∧ ∀ w ∈ V', (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamAlgebraicIndependentFinrankStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenFam_algebraicIndependent_finrank : ∀ (F₀ Ω G : Type) [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω] [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (d : ℕ), 0 < d → Module.finrank F₀ Ω = d → IsGenFam Ω G u → AlgebraicIndependent F₀ (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin F₀ (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) G = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.genFam_degree_over_subfield | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.genFam_degree_over_subfield | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.genFam_degree_over_subfield <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamRevInvSubfamilyStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenFam_revInv_subfamily : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeEqLogIndexStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelled_degree_eq_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index | exact GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index | (intros; apply GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalFrameOfTwistGenerationStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_frame_of_twist_generation : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] {κ : Type} (x : κ → Ω) (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) (m n r : ℕ) (V : Submodule Ω E)
    (φ : Fin n → Module.Dual Ω E) (cc : Fin r → E) (hV : L.IsVB r V) (hli : LinearIndependent Ω cc)
    (hsp : Submodule.span Ω (Set.range cc) = V) (hG : IsTwistGen ξ x L m φ) (P : Cpt ξ) (c₁ : κ)
    (hc : InChart ξ x c₁ P),
    ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin n) (Fin r) Ω) (B : Matrix (Fin r) (Fin n) Ω),
      T.det ≠ 0 ∧ Matrix.of (fun j a => φ j (cc a)) * T = (x c₁ ^ m) • C ∧ B * C = 1 ∧
        (∀ j a, C j a ∈ regAt ξ P) ∧ ∀ a j, B a j ∈ regAt ξ P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_at_point | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_at_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mixWord {n : ℕ} (a a₀ A' : HermLine ι) (k i : ℕ) : Fin n → HermLine ι :=
  fun j => if (j : ℕ) < i then a else if (j : ℕ) + 1 < k then a₀ else A'

open Classical in

def logRatio (a a₀ : HermLine ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then Real.log (a₀.h z) - Real.log (a.h z) else 0

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartWOfContinuousPeriodStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_chartW_of_continuous_period : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 → (∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) → x ∈ chartW bas B) ∧ ∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods.periods_at_centre | exact GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods.periods_at_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods.periods_at_centre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorExpansionOfScaledProductStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_expansion_of_scaled_product : ∀ {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (A C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (x : Ω) (m : Ψ ⊕ Ψ → ℕ)
    (hAT : ∀ s, A s * Ts s = (x ^ m s) • C s) (τ : Ψ) (t : StepIx Ψ p q) (hs : t.1 = .inl τ ∨ t.1 = .inr τ)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (h : Matrix (Fin (p + q)) (Fin (p + q)) Ω)
    (S : Finset (Fin (p + q))) (hS : S.card = (t.2 : ℕ) + 1),
    ∑ I, cMin A t J I * minorIJ (tMat Ts τ * h) I S =
      x ^ (m t.1 * ((t.2 : ℕ) + 1)) * ∑ I, cMin C t J I * minorIJ h I S := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.sum_cMin_tMat_mul | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.sum_cMin_tMat_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.sum_cMin_tMat_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorRatioRegularOfMatrixIdentityStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_ratio_regular_of_matrix_identity : ∀ {Ω : Type} [Field Ω] {n r : ℕ} (R : Subring Ω) (A C : Matrix (Fin n) (Fin r) Ω)
    (B : Matrix (Fin r) (Fin n) Ω) (T : Matrix (Fin r) (Fin r) Ω) (a : Ω) (hAT : A * T = a • C) (ha : a ≠ 0)
    (hT : T.det ≠ 0) (hBC : B * C = 1) (hC : ∀ j l, C j l ∈ R) (hB : ∀ l j, B l j ∈ R) (J₀ : Fin r → Fin n)
    (hz : (A.submatrix J₀ id).det ≠ 0)
    (hr : ∀ J : Fin r → Fin n, (A.submatrix J id).det / (A.submatrix J₀ id).det ∈ R),
    (C.submatrix J₀ id).det ≠ 0 ∧ (C.submatrix J₀ id).det ∈ R ∧ (C.submatrix J₀ id).det⁻¹ ∈ R ∧
      (A.submatrix J₀ id).det * T.det = a ^ r * (C.submatrix J₀ id).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.minor_isUnit_of_leftInverse | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.minor_isUnit_of_leftInverse | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.minor_isUnit_of_leftInverse <;> assumption)
end


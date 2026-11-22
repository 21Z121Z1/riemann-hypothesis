import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0003
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0014
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstantStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0002
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0010
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ExistsRegularRepBesselBigCellVectorEqBesselImpor
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0004
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0019
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BaseRepCapelliEigenDual
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoefZero

theorem continuousOn_of_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞}
    {f : B.Mat k r → E} (h : B.CkOn m (B.GV k r) f) : ContinuousOn f (B.GV k r) := by
  letI : NormedAddCommGroup (B.Mat k r) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (B.Mat k r) := Matrix.normedSpace
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  have h1 : ContinuousWithinAt f' (B.GV k r) g₀ :=
    (hf'.continuousOn.continuousAt (hU.mem_nhds hgU)).continuousWithinAt
  refine h1.congr_of_eventuallyEq ?_ (he g₀ hgU hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g a b
  exact he g a b

theorem coef_norm_finite_and_zero : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → R0.IsDG (PI.BesselPeriodGGP.eps48 P.k P.r) lam → PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f → TBB.jN2 p f < ⊤ ∧ (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) ∧ (TBB.jN2 p f = 0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R0 f hN hR0 hf
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨R, hfam, hR⟩ := GlobalTheory.family_through_discreteSeries hH P.k P.r lam P.u b bv ga h q0 R0 hN hR0
  subst hR
  obtain ⟨l, l', dg, hl, hl'⟩ := GlobalTheory.T.exists_family_functionals hH P Wp Wq p lam b bv ga h q0 R hN hfam
  have h0 : n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [n1]
  obtain ⟨hB, hdg, hfd⟩ := hl 0 h0
  obtain ⟨hB', -, -⟩ := hl' 0 h0
  obtain ⟨⟨-, -, -, -, hok⟩, hν⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  have hgap : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) lam (h / 2) := by
    simpa using (hν 0 h0).2.2.1
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hH.1.2.2.1 P.k P.r _ lam (R 0) Wp Wq (l 0) (l' 0) hR0).1 f hf
  obtain ⟨c, hc, hnorm⟩ := GlobalTheory.T.bessel_setting_uniform_constant hH P.k P.r Wp Wq p.T.base
  have hj : TBB.jN2 p f = ENNReal.ofReal (c * ‖s‖ ^ 2 / dg 0) := by
    rw [GlobalTheory.T.jN2_eq_normSq_base]
    exact hnorm _ lam (h / 2) (R 0) (l 0) (l' 0) (dg 0) hR0 hgap hok hB hB' hfd f s hs
  have hck := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH P.k P.r _ lam (h / 2) (R 0) Wp Wq (l 0) (l' 0) f s hR0 hgap hok hs).1
  refine ⟨by rw [hj]; exact ENNReal.ofReal_lt_top,
    GlobalTheory.T.aemeasurable_besselNormIntegrand_bigCell P Wp Wq p f (continuousOn_of_ckOn hck), fun hz x hx hG => ?_⟩
  have hs0 : s = 0 := by
    by_contra hne
    rw [hj, ENNReal.ofReal_eq_zero] at hz
    have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hne
    have : 0 < c * ‖s‖ ^ 2 / dg 0 := by positivity
    linarith
  obtain ⟨γ, hγ, -, hV⟩ := GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel P Wp Wq p x hx hG
  obtain ⟨OO, hOO⟩ := GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul hH P.k P.r _ lam (h / 2) (R 0) Wp Wq p.T.base (l 0) (l' 0) hR0 hgap hok hB hB'
  rw [hV f, (hOO f s hs γ hγ).2, hs0, zero_smul]

end GlobalTheory.CoefZero
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilyFunctionalSpanDual
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SuppliedNorm

theorem sup_norm : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → SupG p lam q0 R l l' dg s J tau → ∃ c : ℝ, 0 < c ∧ ∀ ν, n1 ν ≤ q0 → (J ν = 0 ∧ TBB.jN2 p (J ν) = 0 ∧ ¬ (NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν))) ∨ (J ν ≠ 0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) ∧ s ν ≠ 0 ∧ TBB.jN2 p (J ν) = ENNReal.ofReal (c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)))) := by
  intro hy P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hS
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨c₁, hc₁, h1⟩ := GlobalTheory.T.bessel_setting_uniform_constant hy P.k P.r Wp Wq p.T.base
  have hH : PI.BesselPeriodGGP.IsHaarOn (GG P.k P.r) p.T.base.μG := by
    haveI : IsFiniteMeasureOnCompacts p.T.base.μG := ⟨fun K hK => p.T.base.haarG.finite_compact K hK⟩
    haveI : IsLocallyFiniteMeasure p.T.base.μG := inferInstance
    exact ⟨inferInstance, p.T.base.haarG.ne_zero, p.T.base.haarG.conc, p.T.base.haarG.left⟩
  obtain ⟨c₂, hc₂, h2⟩ := GlobalTheory.BesselDegree.schur_fdeg hy P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) _ hH
  obtain ⟨⟨-, -, -, -, hgap⟩, hfam⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, fun ν hν => ?_⟩
  have hDS := hS.fam ν hν
  obtain ⟨hl, hdg, hfd⟩ := hS.left ν hν
  obtain ⟨hl', -, -⟩ := hS.right ν hν
  have hP := h1 _ _ (h / 2) (R ν) (l ν) (l' ν) (dg ν) hDS (hfam ν hν).2.2.1 hgap hl hl' hfd
  have h0 : TBB.jN2 p (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = 0 := by
    rw [GlobalTheory.T.jN2_eq_normSq_base, hP 0 0 ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun g _ => by simp, by simp⟩]
    simp
  by_cases hnz : NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
  · right
    obtain ⟨hc, hs⟩ := hS.coef ν hν hnz.1 hnz.2
    have hj : TBB.jN2 p (J ν) = ENNReal.ofReal (c₁ * dg ν) := by
      rw [GlobalTheory.T.jN2_eq_normSq_base, hP _ _ hc, hs]
      congr 1
      field_simp
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 P.k P.r _ _ (R ν) hDS).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    have hd : dg ν = c₂ * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := by
      rw [← hfd w hw0, (h2 _ (R ν) hDS).1 w hw0]
    refine ⟨?_, hnz.1, hnz.2, ?_, ?_⟩
    · intro hJ
      rw [hJ, h0] at hj
      exact absurd hj.symm (ENNReal.ofReal_pos.2 (mul_pos hc₁ hdg)).ne'
    · intro hs0
      rw [hs0, norm_zero] at hs
      exact hdg.ne hs
    · rw [hj, hd, mul_assoc]
  · left
    have hJ := hS.zero ν (fun hh => hnz hh.2)
    exact ⟨hJ, by rw [hJ, h0], hnz⟩

end GlobalTheory.SuppliedNorm
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsCoefContinuousOn
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupMeas

theorem isDS_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    (h : R.IsDG ε μ) (v : R.H) : ContinuousOn (fun g => R.σ g v) (GG k r) := by
  obtain ⟨P, hP, -, -, ⟨-, -, hc⟩, -⟩ := h.2
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have := (hc v).comp h3.continuousOn hmaps
  simpa only [Function.comp_def, e] using this

theorem isCoef_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {l : R.H → Wp} {l' : R.H → Wq} {F : Mx k r → (Wq →L[ℂ] Wp)} {s : ℂ}
    (h : R.IsDG ε μ) (hF : IsCoef R l l' F s) : ContinuousOn F (GG k r) := by
  obtain ⟨m, x, y, X, -, hF, -⟩ := hF
  refine ContinuousOn.congr ?_ hF
  exact continuousOn_finsetSum _ fun i _ =>
    (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (isDS_continuousOn h (y i))).smul continuousOn_const

theorem sup_meas : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → SupG p lam q0 R l l' dg s J tau → ∀ ν, AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) (J ν) (P.r + 1) [] (TBB.bigPt P.r c)) := by
  intro _ P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau _ hS ν
  apply GlobalTheory.T.aemeasurable_besselNormIntegrand_bigCell
  by_cases hν : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
  · exact isCoef_continuousOn (hS.fam ν hν.1) (hS.coef ν hν.1 hν.2.1 hν.2.2).1
  · rw [hS.zero ν hν]
    exact continuousOn_const

end GlobalTheory.SupMeas
end Gp91
end


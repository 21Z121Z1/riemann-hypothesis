import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0012
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0015
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonicStatement
section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polydisc_poisson_reproduces_harmonic : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (ρ R M : ℝ), 0 < ρ → ρ < R → ContinuousOn f (punct R) → SepHarm R f → (∀ z ∈ punct R, |f z| ≤ M) → ∀ z ∈ punct ρ, polyPoisson ρ f z = f z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimTwistSuccStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_twist_succ : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodense
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Bdry

theorem bdry_isClosed_dense_compl (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X)
    (hs : IsSection A L s) (hn : IsSNC A L s m W) : IsClosed (bdry s) ∧ Dense (bdry s)ᶜ := by
  have key := GlobalTheory.T.snc_boundary_coordinate_chart e X A L s nb m W hs hn
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨ψ, -, hyψ, S, hS⟩ := key y
    have hopen : IsOpen (ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0}) := by
      apply ψ.continuousOn.isOpen_inter_preimage ψ.open_source
      have : {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z : Fin e → ℂ | z i ≠ 0} := by
        ext z; simp
      rw [this]
      exact isOpen_biInter_finset fun i _ =>
        isOpen_ne_fun (continuous_apply i) continuous_const
    have hmem : y ∈ ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} := by
      refine ⟨hyψ, fun i hi h0 => hy ((hS y hyψ).2 ⟨i, hi, h0⟩)⟩
    refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
    rintro y' ⟨h1, h2⟩ hb
    obtain ⟨i, hi, h0⟩ := (hS y' h1).1 hb
    exact h2 i hi h0
  · rw [dense_iff_inter_open]
    intro V hV ⟨x, hx⟩
    obtain ⟨ψ, -, hxψ, S, hS⟩ := key x
    have hsub : V ∩ ψ.source ⊆ ψ.source := Set.inter_subset_right
    have himg : IsOpen (ψ '' (V ∩ ψ.source)) :=
      ψ.isOpen_image_of_subset_source (hV.inter ψ.open_source) hsub
    have hne : (ψ '' (V ∩ ψ.source)).Nonempty := ⟨ψ x, x, ⟨hx, hxψ⟩, rfl⟩
    obtain ⟨z, hz, hz0⟩ := (GlobalTheory.T.dense_coordinate_torus e).inter_open_nonempty _ himg hne
    obtain ⟨y, ⟨hyV, hyψ⟩, rfl⟩ := hz
    refine ⟨y, hyV, fun hb => ?_⟩
    obtain ⟨i, -, h0⟩ := (hS y hyψ).1 hb
    exact hz0 i h0

end GlobalTheory.CompanionTheory.Ar.Bdry
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChartStatement
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_in_compatible_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ → IsOpen U → A.SmoothOn U g → ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  first | exact @GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | exact GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | (intros; apply GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwLineSmoothConjInvariantGlueStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twLine_smooth_conjInvariant_glue : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (A : HermLine ι), p ≠ 0 → (IsSmoothHerm A → IsSmoothHerm (twLine p A)) ∧ (IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ IsConjInvariantH (twLine p A) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vPlus p)) = A.h z) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main | exact GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsMultiHomogIdealStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_isMultiHomogIdeal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), IsMultiHomogIdeal W → IsMultiHomogIdeal (twist p W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsPrimeStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → NoRoot p W → (twist p W).IsPrime := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | exact GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecomposition
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → ∃ T : Fin 3 → Matrix (Fin d) (Fin d) ℂ, ∀ a : ℂ, ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧ hessC (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) = Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (-(((1 + ‖a‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => ∑ i, (((fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)) a i : ℝ) : ℂ) * T i p' q') q) p := by
  intro d G y _ hC h1 h0
  let A : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ := fun p q => fderiv ℝ (fderiv ℝ fun y' => (G y' p q).re) y
  let B : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ := fun p q => fderiv ℝ (fderiv ℝ fun y' => (G y' p q).im) y
  refine ⟨![PositivityTheory.Xgp.fib_hess.hm ((-(1/2:ℝ)) • (A 0 1 + A 1 0)), PositivityTheory.Xgp.fib_hess.hm ((-(1/2:ℝ)) • (B 1 0 - B 0 1)), PositivityTheory.Xgp.fib_hess.hm ((1/2:ℝ) • (A 1 1 - A 0 0))], fun a => ?_⟩
  obtain ⟨hc, hH⟩ := PositivityTheory.Xgp.fib_hess.jet d G y hC h1 h0 a A B (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨hc, ?_⟩
  ext p q
  refine Fin.cases ?_ (fun p' => ?_) p <;> refine Fin.cases ?_ (fun q' => ?_) q
  all_goals simp only [hessC, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, hH, PositivityTheory.Xgp.fib_hess.tl_zero, PositivityTheory.Xgp.fib_hess.tl_zero', PositivityTheory.Xgp.fib_hess.tl_succ, PositivityTheory.Xgp.fib_hess.tl_succ', map_zero, ContinuousLinearMap.zero_apply]
  all_goals simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, ne_eq, Fin.succ_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, mul_one, Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  all_goals clear hH hc h0 h1 hC
  all_goals have hr : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  all_goals have hpos : (0:ℝ) < 1 + (a.re ^ 2 + a.im ^ 2) := by positivity
  all_goals have hne : (1 + ((a.re:ℂ) ^ 2 + (a.im:ℂ) ^ 2)) ≠ 0 := by exact_mod_cast hpos.ne'
  case refine_1.refine_1 =>
    rw [hr]
    push_cast
    field_simp
    ring
  all_goals have hz : ∀ j : Fin d, (Pi.single j.succ (1:ℂ) : Fin (d+1) → ℂ) 0 = 0 := fun j => by simp [Pi.single_apply, (Fin.succ_ne_zero j).symm]
  all_goals simp only [hz, mul_zero, Complex.zero_re, Complex.zero_im, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PositivityTheory.Xgp.fib_hess.hm, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply]
  all_goals try rw [hr]
  case refine_2.refine_2 =>
    apply Complex.ext
    · simp only [Complex.add_re, Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.normSq_ofNat]
      field_simp
      ring
    · simp only [Complex.add_re, Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.normSq_ofNat]
      field_simp
      ring
  all_goals push_cast
  all_goals field_simp
  all_goals ring
end


import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0210
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0084
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0323
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnFderivApply
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.RCalc.ByParts

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_deriv_eq_zero {Γ V : Type*} [TopologicalSpace Γ] [SecondCountableTopology Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] {μ : Measure Γ} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F F' : ℝ → Γ → V} {K : Set Γ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) (C : ℝ)
    (hc : ∀ t ∈ Metric.ball (0 : ℝ) ε, Continuous (F t)) (hc' : Continuous (F' 0))
    (hd : ∀ y, ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivAt (fun s => F s y) (F' t y) t)
    (hz : ∀ y, y ∉ K → F 0 y = 0)
    (hz' : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y, y ∉ K → F' t y = 0)
    (hb : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y ∈ K, ‖F' t y‖ ≤ C)
    (hconst : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∫ y, F t y ∂μ = ∫ y, F 0 y ∂μ) :
    ∫ y, F' 0 y ∂μ = 0 := by
  have hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ :=
    eventually_of_mem hs fun t ht => (hc t ht).aestronglyMeasurable
  have hint : Integrable (F 0) μ :=
    (hc 0 (Metric.mem_ball_self hε)).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hz)
  have hbi : Integrable (K.indicator fun _ => C) μ :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖F' t y‖ ≤ K.indicator (fun _ => C) y :=
    ae_of_all _ fun y t ht => by
      by_cases hy : y ∈ K
      · simpa [hy] using hb t ht y hy
      · simp [hy, hz' t ht y hy]
  have h1 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hint hc'.aestronglyMeasurable hbound hbi
    (ae_of_all _ hd)).2
  have h2 : HasDerivAt (fun t => ∫ y, F t y ∂μ) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (∫ y, F 0 y ∂μ)).congr_of_eventuallyEq ?_
    exact eventually_of_mem hs hconst
  exact h1.unique h2

theorem continuousOn_fderiv_apply {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace P] {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {S : Set P} {A B : P → E} (hA : ContinuousOn A S) (hB : ContinuousOn B S) (hm : MapsTo A S U) :
    ContinuousOn (fun p => fderiv ℝ f (A p) (B p)) S := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.continuousOn.comp hA hm).clm_apply hB

theorem hasDerivAt_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (g v : E) (t : ℝ) (hf : DifferentiableAt ℝ f (g + t • v)) :
    HasDerivAt (fun s : ℝ => f (g + s • v)) (fderiv ℝ f (g + t • v) v) t := by
  have h2 : HasDerivAt (fun s : ℝ => g + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add g
  exact hf.hasFDerivAt.comp_hasDerivAt t h2

variable {n : ℕ}

def c (X : Mat n) (t : ℝ) : Mat n := 1 + t • X

theorem continuous_c (X : Mat n) : Continuous (c X) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem c_zero (X : Mat n) : c X 0 = 1 := by simp [c]

theorem mul_c (y X : Mat n) (t : ℝ) : y * c X t = y + t • (y * X) := by
  simp [c, mul_add]

theorem exists_eps (X : Mat n) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, c X t ∈ GLs n := by
  have h : IsOpen (c X ⁻¹' GLs n) := isOpen_GLs.preimage (continuous_c X)
  have h0 : (0 : ℝ) ∈ c X ⁻¹' GLs n := by simp [c_zero, GLs]
  obtain ⟨ε, hε, h'⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.mem_nhds h0)
  exact ⟨ε, hε, h'⟩

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem mul_mem_GLs' {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  have h : x.det ≠ 0 := hx
  simp [GLs, Matrix.det_nonsing_inv, h]

def toG {x : Mat n} (hx : x ∈ GLs n) : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx

@[simp] theorem toG_val {x : Mat n} (hx : x ∈ GLs n) : (toG hx).val = x := rfl

theorem secondCountable_G : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem lg_le_lg_mul (hL : LgFacts) (y : G n) {x : Mat n} (hx : x ∈ GLs n) : lg y.val ≤ lg (y.val * x) + lg x := by
  obtain ⟨hsub, hinv, -⟩ := hL n
  have hdet : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have e : y.val = (y.val * x) * x⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  calc lg y.val = lg ((y.val * x) * x⁻¹) := by rw [← e]
    _ ≤ lg (y.val * x) + lg x⁻¹ := hsub _ (mul_mem_GLs' (val_mem_GLs y) hx) _ (inv_mem_GLs hx)
    _ = lg (y.val * x) + lg x := by rw [hinv x hx]

theorem fderiv_eq_zero_far (hL : LgFacts) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V} {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → f y = 0) {x : Mat n} (hx : x ∈ GLs n) (hlg : R < lg x) : fderiv ℝ f x = 0 := by
  obtain ⟨-, -, -, hsm, -⟩ := hL n
  have ho : IsOpen (GLs n ∩ lg ⁻¹' Ioi R) := hsm.continuousOn.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have he : f =ᶠ[𝓝 x] fun _ => (0 : V) :=
    eventually_of_mem (ho.mem_nhds ⟨hx, hlg⟩) fun y hy => hR y hy.1 hy.2
  rw [he.fderiv_eq]
  simp

theorem ibp_of (hL : LgFacts) (hU : Unimod) : IBP := by
  intro n _ _ μ _ V _ _ _ f hf hC X
  obtain ⟨R, hR⟩ := hC
  obtain ⟨-, -, -, hsm, hcpt, -⟩ := hL n
  haveI := (hU n μ).1
  haveI : SecondCountableTopology (G n) := secondCountable_G
  obtain ⟨ε, hε, hcε⟩ := exists_eps X
  have hball : ∀ t ∈ Metric.ball (0 : ℝ) ε, c X t ∈ GLs n := fun t ht => hcε t (Metric.ball_subset_closedBall ht)
  have hmem : ∀ (y : G n), ∀ t ∈ Metric.closedBall (0 : ℝ) ε, y.val * c X t ∈ GLs n :=
    fun y t ht => mul_mem_GLs' (val_mem_GLs y) (hcε t ht)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, lg (c X t) ≤ C₀ := by
    have hcont : ContinuousOn (fun t => lg (c X t)) (Metric.closedBall (0 : ℝ) ε) :=
      hsm.continuousOn.comp (continuous_c X).continuousOn hcε
    obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℝ) ε).bddAbove_image hcont
    exact ⟨C₀, fun t ht => hC₀ (mem_image_of_mem _ ht)⟩
  set K : Set (G n) := {y : G n | lg y.val ≤ R + C₀} with hKdef
  have hK : IsCompact K := hcpt (R + C₀)
  have hfar : ∀ (y : G n), y ∉ K → ∀ t ∈ Metric.closedBall (0 : ℝ) ε, R < lg (y.val * c X t) := by
    intro y hy t ht
    have h1 : R + C₀ < lg y.val := not_le.1 hy
    have h2 := lg_le_lg_mul hL y (hcε t ht)
    have h3 := hC₀ t ht
    linarith
  have hvalc : Continuous fun y : G n => y.val := Units.continuous_val
  obtain ⟨C, hCb⟩ : ∃ C, ∀ p ∈ K ×ˢ Metric.closedBall (0 : ℝ) ε,
      ‖fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X)‖ ≤ C := by
    have hcont : ContinuousOn (fun p : G n × ℝ => fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X))
        (K ×ˢ Metric.closedBall (0 : ℝ) ε) := by
      refine continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_
      · exact ((hvalc.comp continuous_fst).mul ((continuous_c X).comp continuous_snd)).continuousOn
      · exact ((hvalc.comp continuous_fst).mul continuous_const).continuousOn
      · exact fun p hp => hmem p.1 p.2 hp.2
    exact (hK.prod (isCompact_closedBall (0 : ℝ) ε)).exists_bound_of_continuousOn hcont
  have key := integral_deriv_eq_zero (μ := μ) (F := fun t (y : G n) => f (y.val * c X t))
    (F' := fun t (y : G n) => fderiv ℝ f (y.val * c X t) (y.val * X)) hK hε C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [c_zero, Rd] using key
  · intro t ht
    exact hf.continuousOn.comp_continuous (hvalc.mul continuous_const)
      fun y => hmem y t (Metric.ball_subset_closedBall ht)
  · refine continuousOn_univ.1 (continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_)
    · exact (hvalc.mul continuous_const).continuousOn
    · exact (hvalc.mul continuous_const).continuousOn
    · exact fun y _ => hmem y 0 (Metric.mem_closedBall_self hε.le)
  · intro y t ht
    have hd : DifferentiableAt ℝ f (y.val + t • (y.val * X)) := by
      rw [← mul_c]
      exact differentiableAt_of_smooth hf (hmem y t (Metric.ball_subset_closedBall ht))
    have := hasDerivAt_line (y.val) (y.val * X) t hd
    have e1 : (fun s : ℝ => f (y.val * c X s)) = fun s : ℝ => f (y.val + s • (y.val * X)) := by
      funext s; rw [mul_c]
    show HasDerivAt (fun s : ℝ => f (y.val * c X s)) (fderiv ℝ f (y.val * c X t) (y.val * X)) t
    rw [e1, mul_c]
    exact this
  · intro y hy
    exact hR _ (hmem y 0 (Metric.mem_closedBall_self hε.le)) (hfar y hy 0 (Metric.mem_closedBall_self hε.le))
  · intro t ht y hy
    have ht' := Metric.ball_subset_closedBall ht
    simp only [fderiv_eq_zero_far hL hR (hmem y t ht') (hfar y hy t ht'), ContinuousLinearMap.zero_apply]
  · intro t ht y hy
    exact hCb (y, t) ⟨hy, Metric.ball_subset_closedBall ht⟩
  · intro t ht
    have h0 := integral_mul_right_eq_self (μ := μ) (fun y : G n => f y.val) (toG (hball t ht))
    simpa [c_zero] using h0

end GlobalTheory.CompanionTheory.RCalc.ByParts

theorem GlobalTheory.CompanionTheory.RCalc.ibp : GlobalTheory.CompanionTheory.RCalc.IBP :=
  GlobalTheory.CompanionTheory.RCalc.ByParts.ibp_of GlobalTheory.T.length_function_facts_hold GlobalTheory.T.general_linear_group_unimodular
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirReal
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

private theorem sum_amat_first_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ a, Formalism.REAL.Amat l a j = l j - ((j : ℕ) : ℂ) := by
  have h : ∀ a, Formalism.REAL.Amat l a j = (if a = j then l j else 0) + (if a < j then -1 else 0) := by
    intro a
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : a = j
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio]
  simp [sub_eq_add_neg]

private theorem sum_amat_second_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ b, Formalism.REAL.Amat l j b = l j - ((n - 1 - j : ℕ) : ℂ) := by
  have h : ∀ b, Formalism.REAL.Amat l j b = (if j = b then l j else 0) + (if j < b then -1 else 0) := by
    intro b
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : j = b
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi]
  simp [sub_eq_add_neg]

private theorem gelfVal_two_eq_sum_sq_sub_sq {n : ℕ} (c : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal c 2 = ∑ j, (c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
  have key : ∀ j : Fin n,
      (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
        (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) =
        c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2 := by
    intro j
    have hj : (j : ℕ) + 1 ≤ n := j.isLt
    rw [sum_amat_first_index_eq, sum_amat_second_index_eq, Nat.sub_sub, Nat.cast_sub (by omega), Nat.cast_add,
      Nat.cast_one]
    ring
  calc GlobalTheory.Dec.gelfVal c 2
      = ∑ j, (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
          (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) := by
        simp only [GlobalTheory.Dec.gelfVal, sq, Matrix.mul_apply, Finset.sum_mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun j _ => key j

theorem conj_cas_of_isHerm {n : ℕ} {χ : Inf n} (h : IsHerm χ) : conj (cas χ) = cas χ := by
  obtain ⟨σ, hσ⟩ := h
  have hT : ∑ a, conj (χ true a) ^ 2 = ∑ a, χ false a ^ 2 := by
    rw [← Equiv.sum_comp σ (fun a => χ false a ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hσ a, neg_sq]
  have hF : ∑ a, conj (χ false a) ^ 2 = ∑ a, χ true a ^ 2 := by
    have h2 := congrArg conj hT
    simpa [map_sum, map_pow] using h2.symm
  have hK : ∀ j : Fin n, conj (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) = ((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ) := by
    intro j
    simp only [map_sub, map_div₀, map_natCast, map_one, map_ofNat]
  have hconj : ∀ x : Fin n → ℂ, conj (GlobalTheory.Dec.gelfVal x 2) =
      ∑ j, (conj (x j) ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
    intro x
    rw [gelfVal_two_eq_sum_sq_sub_sq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sub, map_pow, map_pow, hK]
  simp only [cas]
  rw [map_mul, map_add, hconj, hconj, map_ofNat, gelfVal_two_eq_sum_sq_sub_sq, gelfVal_two_eq_sum_sq_sub_sq]
  simp only [Finset.sum_sub_distrib]
  rw [hT, hF]
  ring

theorem conj_cosh_mul_sqrt {c : ℂ} (hc : conj c = c) (t : ℝ) :
    conj (Complex.cosh (t * c ^ (1 / 2 : ℂ))) = Complex.cosh (t * c ^ (1 / 2 : ℂ)) := by
  have hw2 : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
    have h := Complex.cpow_nat_inv_pow c (n := 2) two_ne_zero
    simpa [one_div] using h
  have hsq : conj (c ^ (1 / 2 : ℂ)) ^ 2 = (c ^ (1 / 2 : ℂ)) ^ 2 := by
    rw [← map_pow, hw2, hc]
  rw [← Complex.cosh_conj, map_mul, Complex.conj_ofReal]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · rw [h]
  · rw [h, mul_neg, Complex.cosh_neg]

theorem conj_coshT_cas : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T →
    conj (coshT g (cas χ)) = coshT g (cas χ) := by
  intro n χ g T hχ _
  have hc := conj_cas_of_isHerm hχ
  simp only [coshT]
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_mul, Complex.conj_ofReal, conj_cosh_mul_sqrt hc t]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneral
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegBasisGen

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem exists_left_inv {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ K) (hP : LinearIndependent K Pᵀ) : ∃ Y : Matrix κ ι K, Y * P = 1 := by
  have inj : LinearMap.ker P.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h0 := hv
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum] at h0
    simp only [op_smul_eq_smul] at h0
    funext i
    exact Fintype.linearIndependent_iff.1 hP v h0 i
  obtain ⟨f, hf⟩ := P.mulVecLin.exists_leftInverse_of_injective inj
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h := congrArg LinearMap.toMatrix' hf
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_id] at h

theorem degG_reindex (hF : WedgeF) (hI : WedgeI) {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (e : κ' ≃ κ) (x : GA E n) (M : Matrix (Fin n) κ E) :
    degG x (M.submatrix id e) = degG x M := by
  have hfr : (x⁻¹ : GA E n).val * (M.submatrix id e).map (algebraMap E (Ad E)) =
      ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))).submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hv : ∀ v, nI ((A.submatrix id e).map (cV v)) = nI (A.map (cV v)) := fun v => by
    rw [← Matrix.submatrix_map]
    exact (hI (Fin n)).reindex κ κ' e (A.map (cV v))
  have hw : ∀ w, nF ((A.submatrix id e).map (cW w)) = nF (A.map (cW w)) := fun w => by
    haveI := ultra w
    rw [← Matrix.submatrix_map]
    exact (hF (w.adicCompletion E) (Fin n)).reindex κ κ' e (A.map (cW w))
  simp only [degG, hfr, ← hA, hv, hw]

theorem degG_mul (mF : MulF) (mI : MulI) (lg : LogAbsBasic) (fs : FinSupp) {κ : Type} [Fintype κ] [DecidableEq κ]
    (x : GA E n) (P : Matrix (Fin n) κ E) (hP : LinearIndependent E Pᵀ) (s : Matrix κ κ E) (hs : s.det ≠ 0) :
    degG x (P * s) = degG x P := by
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * P.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hfr : (x⁻¹ : GA E n).val * (P * s).map (algebraMap E (Ad E)) = A * s.map (algebraMap E (Ad E)) := by
    rw [hA, Matrix.map_mul, Matrix.mul_assoc]
  obtain ⟨Y₀, hY₀⟩ := exists_left_inv P hP
  have hYA : (Y₀.map (algebraMap E (Ad E)) * x.val) * A = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, ← Matrix.map_mul, hY₀, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨h1, h2, h3⟩ := (lg E).1, (lg E).2.1, (lg E).2.2
  obtain ⟨f1, f2, f3⟩ := fs E (Fin n) κ A _ hYA
  have hu : IsUnit (algebraMap E (Ad E) s.det) := (IsUnit.mk0 _ hs).map _
  have hdet : ∀ {R : Type} [CommRing R] (f : Ad E →+* R),
      ((s.map (algebraMap E (Ad E))).map f).det = f (algebraMap E (Ad E) s.det) := fun f => by
    rw [RingHom.map_det, RingHom.map_det]
    rfl
  have hv : ∀ v, Real.log (nI ((A * s.map (algebraMap E (Ad E))).map (cV v))) =
      Real.log (nI (A.map (cV v))) + Real.log (‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2) := fun v => by
    have hne : ‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2 ≠ 0 :=
      pow_ne_zero _ (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero)
    rw [Matrix.map_mul, (mI (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f1 v) hne]
  have hw : ∀ w, Real.log (nF ((A * s.map (algebraMap E (Ad E))).map (cW w))) =
      Real.log (nF (A.map (cW w))) + Real.log ‖cW w (algebraMap E (Ad E) s.det)‖ := fun w => by
    haveI := ultra w
    have hne : ‖cW w (algebraMap E (Ad E) s.det)‖ ≠ 0 := norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero
    rw [Matrix.map_mul, (mF _ (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f2 w) hne]
  have hsupp : (Function.support fun w => Real.log (nF (A.map (cW w)))).Finite :=
    f3.subset fun w hw' h => hw' (by simp [h])
  have hprod := h3 s.det hs
  simp only [degG, hfr, ← hA, hv, hw]
  rw [Finset.sum_add_distrib, finsum_add_distrib hsupp (h1 _ hu)]
  unfold logAbs at hprod
  linarith

theorem degBasisG_of : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  intro hF hI mF mI lg fs E _ _ _ n κ _ _ x M hM
  obtain ⟨W, hW⟩ : ∃ W, W = Submodule.span E (Set.range Mᵀ) := ⟨_, rfl⟩
  rw [← hW]
  have hcard : Module.finrank E W = Fintype.card κ := by
    rw [hW]
    exact finrank_span_eq_card hM
  have hsub : ∀ k, (fun i => M i k) ∈ W := fun k => by
    rw [hW]
    exact Submodule.subset_span ⟨k, rfl⟩
  let e : Fin (Module.finrank E W) ≃ κ := (Fintype.equivFinOfCardEq hcard.symm).symm
  have hcol : ∀ j, (fun i => M i (e j)) ∈ W := fun j => hsub (e j)
  let b := Module.finBasis E W
  let s : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E :=
    Matrix.of fun i j => b.repr ⟨fun i' => M i' (e j), hcol j⟩ i
  have hfac : M.submatrix id e = basisMat W * s := by
    ext i j
    have h := congrArg (fun y : W => (y : Fin n → E) i) (b.sum_repr ⟨fun i' => M i' (e j), hcol j⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    simp only [Matrix.mul_apply, basisMat, Matrix.of_apply, Matrix.submatrix_apply, id, s]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hlin : LinearIndependent E (M.submatrix id e)ᵀ := hM.comp e e.injective
  have hs : s.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : M.submatrix id e *ᵥ v = 0 := by
      rw [hfac, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [Matrix.mulVec_eq_sum] at h1
    simp only [op_smul_eq_smul] at h1
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.1 hlin v h1 i)
  have hP : LinearIndependent E (basisMat W)ᵀ :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  calc degG x M = degG x (M.submatrix id e) := (degG_reindex hF hI e x M).symm
    _ = degG x (basisMat W * s) := by rw [hfac]
    _ = degG x (basisMat W) := degG_mul mF mI lg fs x _ hP s hs
    _ = deg x W := rfl

end GlobalTheory.CompanionTheory.DegBasisGen

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumSystemDescendsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.direct_sum_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (A : I → Sy.{1} K ι), (∀ i, (A i).Desc) → (sumSy A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | exact GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegers
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCOK

theorem exists_uniform_mem_sub : ∀ (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K),
      Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K _
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.LocalIntegers.exists_finset_generators l K
  choose c hc using GlobalTheory.T.integer_mem_lattice_sub_bound l K
  refine ⟨2 * s.sup c, fun k a => ?_⟩
  obtain ⟨d, hd⟩ := hs a
  have h1 : Lat.kP l K a = ∑ i ∈ s, algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (d i : ℚ_[l])) *
      Lat.kP l K i := by
    have h2 : Lat.kP l K a = algClToBdR l (((a : K) : PadicAlgCl l)) := rfl
    rw [h2, hd, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    rfl
  rw [h1, map_sum]
  refine Subring.sum_mem _ fun i hi => ?_
  rw [map_mul]
  exact Subring.mul_mem _ (GlobalTheory.CompanionTheory.LatCZp.padicInt_mem_sub l _ k (d i))
    (hc i _ k (Nat.mul_le_mul_left 2 (Finset.le_sup hi)))

end GlobalTheory.CompanionTheory.LatCOK
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictBlockOrder
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.Twist

theorem exists_nat_labelling_blk : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  intro α _ _ N m _ _ e
  let o := (Fintype.orderIsoFinOfCardEq α rfl).symm
  refine ⟨fun x => (o (blk e x)).val, fun x y => ?_⟩
  exact Fin.lt_def.symm.trans (OrderIso.lt_iff_lt o)

end GlobalTheory.CompanionTheory.Twist
end


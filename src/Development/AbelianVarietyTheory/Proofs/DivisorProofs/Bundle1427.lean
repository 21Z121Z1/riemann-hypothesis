import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.AutGrowth.ApproxId

theorem tendsto_integral_of_concentrate {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] {ν : Measure V}
    {f : V → ℂ} {x₀ : V} (hf : ContinuousAt f x₀) (β : ℕ → V → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (h0 : ∀ n x, 0 ≤ β n x) (h1 : ∀ n, ∫ x, β n x ∂ν = 1) (hs : ∀ n x, β n x ≠ 0 → dist x x₀ < r n)
    (hi : ∀ n, Integrable (β n) ν) (hfi : ∀ n, Integrable (fun x => (β n x : ℂ) * f x) ν) :
    Tendsto (fun n => ∫ x, (β n x : ℂ) * f x ∂ν) atTop (𝓝 (f x₀)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.1 hf (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hr) δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hrn : r n < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have e1 : ∫ x, (β n x : ℂ) * f x₀ ∂ν = f x₀ := by
    rw [integral_mul_const, integral_complex_ofReal, h1 n]; simp
  have e2 : ∫ x, (β n x : ℂ) * f x ∂ν - f x₀ = ∫ x, (β n x : ℂ) * (f x - f x₀) ∂ν := by
    conv_lhs => rw [← e1]
    refine (integral_sub (hfi n) ((hi n).ofReal.mul_const (f x₀))).symm.trans ?_
    congr 1; funext x; rw [mul_sub]; rfl
  rw [dist_eq_norm, e2]
  calc ‖∫ x, (β n x : ℂ) * (f x - f x₀) ∂ν‖ ≤ ∫ x, β n x * (ε / 2) ∂ν := by
        refine norm_integral_le_of_norm_le ((hi n).mul_const _) (.of_forall fun x => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 n x)]
        by_cases hx : β n x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact (hfδ ((hs n x hx).trans hrn)).le) (h0 n x)
    _ = ε / 2 := by rw [integral_mul_const, h1 n, one_mul]
    _ < ε := half_lt_self hε

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem sum_norm_sq_eq (N : Matrix (Fin a) (Fin a) (Cinf E)) (w : InfinitePlace E) :
    ∑ i, ∑ j, ‖N i j w‖ ^ 2 = (Matrix.trace (star N * N) w).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

omit [NumberField E] [IsTotallyComplex E] in

theorem trace_star_mul_conj (k : Kinf E a) (N : Matrix (Fin a) (Fin a) (Cinf E)) :
    Matrix.trace (star ((k : Matrix (Fin a) (Fin a) (Cinf E)) * N * star (k : Matrix (Fin a) (Fin a) (Cinf E))) *
      ((k : Matrix (Fin a) (Fin a) (Cinf E)) * N * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) =
      Matrix.trace (star N * N) := by
  have h1 : star (k : Matrix (Fin a) (Fin a) (Cinf E)) * k = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  set K : Matrix (Fin a) (Fin a) (Cinf E) := ↑k
  have e : star (K * N * star K) * (K * N * star K) = K * (star N * N * star K) := by
    rw [star_mul, star_mul, star_star]
    calc K * (star N * star K) * (K * N * star K) = K * star N * (star K * K) * N * star K := by
          simp only [mul_assoc]
      _ = K * (star N * N * star K) := by rw [h1, mul_one]; simp only [mul_assoc]
  rw [e, Matrix.trace_mul_comm, mul_assoc, h1, mul_one]

variable (E a) in

def frobSq (x : Lie E a) : ℝ := ∑ w, ∑ i, ∑ j, ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2

omit [IsTotallyComplex E] in
theorem frobSq_eq (x : Lie E a) :
    frobSq E a x = ∑ w, ((Matrix.trace (star (Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) *
      (Matrix.of x - 1)) : Cinf E) w).re := by
  rw [frobSq]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← sum_norm_sq_eq]
  rfl

omit [IsTotallyComplex E] in

theorem frobSq_conj (k : Kinf E a) (x : Lie E a) :
    frobSq E a (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = frobSq E a x := by
  have h2 : (k : Matrix (Fin a) (Fin a) (Cinf E)) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 k.2
  have e : Matrix.of (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) - 1 =
      (k : Matrix (Fin a) (Fin a) (Cinf E)) * (Matrix.of x - 1) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) := by
    rw [Unitary.coe_star, mul_sub, sub_mul, mul_one, h2]
    rfl
  rw [frobSq_eq, frobSq_eq, e, trace_star_mul_conj]

omit [IsTotallyComplex E] in
theorem contDiff_frobSq : ContDiff ℝ ∞ (frobSq E a) := by
  unfold frobSq
  refine ContDiff.sum fun w _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℝ).comp
    (((contDiff_apply ℝ ℂ w).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i))).sub contDiff_const)

omit [IsTotallyComplex E] in
theorem frobSq_one : frobSq E a (oneL E a) = 0 := by
  simp [frobSq]

omit [IsTotallyComplex E] in
theorem norm_sq_le_frobSq (x : Lie E a) (i j : Fin a) (w : InfinitePlace E) :
    ‖x i j w - oneL E a i j w‖ ^ 2 ≤ frobSq E a x := by
  unfold frobSq
  refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j,
    ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2) (fun w _ => by positivity) (Finset.mem_univ w))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j,
    ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ j)

variable (E a) in

def bumpR (m : ℝ) (x : Lie E a) : ℝ := Real.smoothTransition (1 - m ^ 2 * frobSq E a x)

omit [IsTotallyComplex E] in
theorem contDiff_bumpR (m : ℝ) : ContDiff ℝ ∞ (bumpR E a m) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_frobSq))

omit [IsTotallyComplex E] in
theorem bumpR_nonneg (m : ℝ) (x : Lie E a) : 0 ≤ bumpR E a m x := Real.smoothTransition.nonneg _

omit [IsTotallyComplex E] in
theorem bumpR_one (m : ℝ) : bumpR E a m (oneL E a) = 1 := by
  simp [bumpR, frobSq_one]

omit [IsTotallyComplex E] in
theorem dist_lt_of_bumpR_ne_zero {m : ℝ} (hm : 0 < m) {x : Lie E a} (h : bumpR E a m x ≠ 0) :
    dist x (oneL E a) < 1 / m := by
  have h1 : m ^ 2 * frobSq E a x < 1 := by
    by_contra hc
    exact h (Real.smoothTransition.zero_of_nonpos (by linarith))
  have hr : 0 < 1 / m := one_div_pos.2 hm
  rw [dist_pi_lt_iff hr]; intro i
  rw [dist_pi_lt_iff hr]; intro j
  rw [dist_pi_lt_iff hr]; intro w
  rw [Complex.dist_eq]
  have h2 := norm_sq_le_frobSq x i j w
  have h3 : (m * ‖x i j w - oneL E a i j w‖) ^ 2 < 1 := by
    rw [mul_pow]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
  have h4 : m * ‖x i j w - oneL E a i j w‖ < 1 := by
    have := abs_lt_of_sq_lt_sq' (h3.trans_eq (one_pow 2).symm) zero_le_one
    exact this.2
  rw [lt_div_iff₀ hm]
  linarith

omit [IsTotallyComplex E] in
theorem bumpR_conj (m : ℝ) (k : Kinf E a) (x : Lie E a) :
    bumpR E a m (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = bumpR E a m x := by
  simp only [bumpR, frobSq_conj]

end GlobalTheory.AutGrowth.ApproxId

namespace GlobalTheory.AutGrowth.ApproxId

theorem exists_approx_identity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure], ∃ α : ℕ → Lie E a → ℂ,
      (∀ n, IsTest (invSet E a) (α n) ∧ KInv (α n)) ∧
      ∀ ψ ∈ Sm E a, ∀ g, Tendsto (fun n => smoothing ν (α n) ψ g) atTop (𝓝 (ψ g)) := by
  intro E _ _ _ a ν _
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) (oneL E a) isUnit_one
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  let m : ℕ → ℝ := fun n => (n : ℝ) + N + 1
  have hm : ∀ n, 0 < m n := fun n => by positivity
  have hmN : ∀ n, 1 / m n < ε := fun n =>
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by simp [m])) hN
  have hsub : ∀ n, Metric.closedBall (oneL E a) (1 / m n) ⊆ invSet E a := fun n =>
    (Metric.closedBall_subset_ball (hmN n)).trans hball
  have hsupp : ∀ n, Function.support (bumpR E a (m n)) ⊆ Metric.closedBall (oneL E a) (1 / m n) :=
    fun n x hx => Metric.mem_closedBall.2 (dist_lt_of_bumpR_ne_zero (hm n) hx).le
  have hcs : ∀ n, HasCompactSupport (bumpR E a (m n)) := fun n =>
    HasCompactSupport.intro (isCompact_closedBall (oneL E a) (1 / m n)) fun x hx => by
      by_contra h; exact hx (hsupp n h)
  have hpos : ∀ n, 0 < ∫ x, bumpR E a (m n) x ∂ν := fun n =>
    (contDiff_bumpR (m n)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs n)
      (fun x => bumpR_nonneg _ x) (x := oneL E a) (by rw [bumpR_one]; norm_num)
  let β : ℕ → Lie E a → ℝ := fun n x => (∫ y, bumpR E a (m n) y ∂ν)⁻¹ * bumpR E a (m n) x
  have hβs : ∀ n x, β n x ≠ 0 → dist x (oneL E a) < 1 / m n := fun n x h =>
    dist_lt_of_bumpR_ne_zero (hm n) (right_ne_zero_of_mul h)
  have hβc : ∀ n, ContDiff ℝ ∞ (β n) := fun n => contDiff_const.mul (contDiff_bumpR _)
  have hβcs : ∀ n, HasCompactSupport (β n) := fun n => (hcs n).mul_left
  have hT : ∀ n, IsTest (invSet E a) (fun x => (β n x : ℂ)) := fun n => by
    refine ⟨Complex.ofRealCLM.contDiff.comp (hβc n), ?_, ?_⟩
    · exact HasCompactSupport.intro (isCompact_closedBall (oneL E a) (1 / m n)) fun x hx => by
        by_contra h
        exact hx (Metric.mem_closedBall.2 (hβs n x (fun h' => h (by simp [h']))).le)
    · refine (closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall).trans (hsub n)
      exact Metric.mem_closedBall.2 (hβs n x (fun h' => hx (by simp [h']))).le
  refine ⟨fun n x => (β n x : ℂ), fun n => ⟨hT n, fun k x => ?_⟩, fun ψ hψ g => ?_⟩
  · simp only [β, bumpR_conj]
  · have hv : chart ψ g (oneL E a) = ψ g := by
      have := chart_val ψ g 1
      simpa using this
    have hf : ContinuousAt (chart ψ g) (oneL E a) := (contDiffAt_chart hψ g isUnit_one).continuousAt
    have hr : Tendsto (fun n => 1 / m n) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (one_div_pos.2 (hm n)).le) (fun n => ?_)
      exact one_div_le_one_div_of_le (by positivity) (by simp [m])
    have h1 : ∀ n, ∫ x, β n x ∂ν = 1 := fun n => by
      simp only [β]
      rw [integral_const_mul, inv_mul_cancel₀ (hpos n).ne']
    have key := tendsto_integral_of_concentrate hf β (fun n => 1 / m n) hr
      (fun n x => mul_nonneg (inv_nonneg.2 (hpos n).le) (bumpR_nonneg _ x)) h1 hβs
      (fun n => (hβc n).continuous.integrable_of_hasCompactSupport (hβcs n))
      (fun n => (hT n).integrable_mul ν isOpen_invSet (hψ g).continuousOn)
    rw [hv] at key
    exact key

end GlobalTheory.AutGrowth.ApproxId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizer
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacDiag

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_mul_mat_inv {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k * mat k⁻¹ = 1 := by
  show ((k * k⁻¹ : UA σ J) : GL (Fin d) (AE F E)).1 = 1
  rw [mul_inv_cancel]; rfl

theorem mat_inv_mul_mat {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k⁻¹ * mat k = 1 := by
  show ((k⁻¹ * k : UA σ J) : GL (Fin d) (AE F E)).1 = 1
  rw [inv_mul_cancel]; rfl

def diagOne {R : Type} [CommRing R] {d : ℕ} (A B : Matrix (Fin d) (Fin d) R) (hAB : A * B = 1) (hBA : B * A = 1) :
    GL (Fin d ⊕ Fin d) R :=
  ⟨fromBlocks A 0 0 1, fromBlocks B 0 0 1, by simp [fromBlocks_multiply, hAB, ← fromBlocks_one],
    by simp [fromBlocks_multiply, hBA, ← fromBlocks_one]⟩

theorem diag_mem_KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) :
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ g : GlobalTheory.DblVac.UD σ W,
      ((g : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
        Matrix.fromBlocks (mat k) 0 0 1 ∧ g ∈ GlobalTheory.DblVac.KD σ W v := by
  intro k hk
  let M := diagOne (mat k) (mat k⁻¹) (mat_mul_mat_inv k) (mat_inv_mul_mat k)
  have hU : (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F W.J) *
      (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F W.J) := by
    have hk2 : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
    show (fromBlocks (mat k) 0 0 1)ᵀ * fromBlocks (incM F W.J) 0 0 (-incM F W.J) *
      (fromBlocks (mat k) 0 0 (1 : Matrix (Fin d) (Fin d) (AE F E))).map (cA σ) = fromBlocks (incM F W.J) 0 0 (-incM F W.J)
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [hk2, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
  refine ⟨⟨M, hU⟩, rfl, ?_, ?_⟩
  · intro u hu
    have h1 := hk.1 u hu
    show u • (fromBlocks (mat k) 0 0 1 - 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = 0
    have h1' : u • (mat k - 1) = 0 := h1
    rw [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_smul, ← sub_eq_add_neg]
    simp [h1']
  · intro z hz
    have hinv : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W)⁻¹ = fromBlocks (mat k⁻¹) 0 0 1 := rfl
    have hfw : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W) = fromBlocks (mat k) 0 0 1 := rfl
    rw [hinv, hfw]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).1)
    · rw [fromBlocks_mulVec]; simpa using hz.2
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).2)
    · rw [fromBlocks_mulVec]; simpa using hz.2

end GlobalTheory.DblVacDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqIsoSpecComp
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.HSChoice.EtaleSection

theorem exists_eq_isoSpec_comp {k : Type} [CommRing k] {X : Scheme.{0}} [IsAffine X] (g : X ⟶ Spec (.of k)) :
    letI := algebraΓOfHom g
    ∃ a : CommRingCat.of k ⟶ Γ(X, ⊤), a.hom = algebraMap k Γ(X, ⊤) ∧ g = X.isoSpec.hom ≫ Spec.map a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop, rfl, ?_⟩
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem natCard_subPts {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I)
    (Ω : Type) [Field Ω] [Algebra k Ω] :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Nat.card (S.subPts I Ω) = Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have e1 : Nat.card (S.subPts I Ω) =
      Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} := by
    refine (Nat.card_congr (Equiv.ofBijective (fun z => (⟨⟨z.1 ≫ I.subschemeι, by rw [Category.assoc]; exact z.2⟩,
      z.1, rfl⟩ : S.subPts I Ω)) ⟨?_, ?_⟩)).symm
    · intro z z' h
      apply Subtype.ext
      have h0 : z.1 ≫ I.subschemeι = z'.1 ≫ I.subschemeι := congrArg (fun x : S.subPts I Ω => x.1.1) h
      exact (cancel_mono I.subschemeι).1 h0
    · rintro ⟨x, z, hz⟩
      refine ⟨⟨z, ?_⟩, ?_⟩
      · rw [← Category.assoc, hz]
        exact x.2
      · apply Subtype.ext
        apply Subtype.ext
        exact hz
  have hmk : ∀ φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv) ≫ I.subschemeι ≫ S.str =
        spMap (algebraMap k Ω) := by
    intro φ
    rw [he, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [ha]
    exact φ.commutes r
  have e2 : Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} =
      Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
    refine (Nat.card_congr (Equiv.ofBijective (fun φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω =>
      (⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv, hmk φ⟩ :
        {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)})) ⟨?_, ?_⟩)).symm
    · intro φ ψ h
      simp only [Subtype.mk.injEq, cancel_mono] at h
      have h2 := Spec.map_injective h
      ext r
      exact congrArg (fun f => f.hom r) h2
    · rintro ⟨z, hz⟩
      have hψ : Spec.map (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)) = z ≫ I.subscheme.isoSpec.hom :=
        Spec.map_preimage _
      have hc : a ≫ Spec.preimage (z ≫ I.subscheme.isoSpec.hom) = CommRingCat.ofHom (algebraMap k Ω) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ, Category.assoc, ← he]
        exact hz
      refine ⟨AlgHom.mk (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)).hom (fun r => ?_), ?_⟩
      · have h3 := congrArg (fun f => f.hom r) hc
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, ha] at h3
        exact h3
      · apply Subtype.ext
        rw [Iso.comp_inv_eq]
        exact hψ
  rw [e1, e2]

theorem etale_of_algebraEtale {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I) :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Algebra.Etale k Γ(I.subscheme, ⊤) → Etale (I.subschemeι ≫ S.str) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  intro h
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have h2 : Etale (Spec.map a) := by
    refine HasRingHomProperty.Spec_iff.mpr ?_
    rw [ha]
    exact (RingHom.etale_algebraMap (R := k) (S := Γ(I.subscheme, ⊤))).mpr h
  rw [he]
  infer_instance

theorem finite_finrank {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (E : Type) [Field E]
    [Algebra F E] (s : Fin T.D → Fin T.N → E)
    (hfin : ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite) :
    (T.toLinSys.baseChange E).IsFiniteSub (T.linSection E s) ∧
    (letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
    Module.Finite E Γ((T.linSection E s).subscheme, ⊤) ∧
      (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = T.del) := by
  have hv : (T.toLinSys.baseChange E).IsVariety := hT.alg.variety.baseChange E
  have H := GlobalTheory.ProperCut.topSelf_eq_length_of_smooth (T.toLinSys.baseChange E).str hv.smooth hv.proj
    (T.toLinSys.baseChange E).isLB (fun i => (T.toLinSys.baseChange E).comb (s i)) hfin
  have hdel : (T.toLinSys.baseChange E).del = T.del :=
    GlobalTheory.FieldChangeInter.del_baseChange F E T.toLinSys hT.alg.variety.proj
  refine ⟨H.1, ?_⟩
  refine ⟨H.2.2.2.2.1, ?_⟩
  rw [← hdel]
  exact H.2.2.2.2.2.symm

private lemma isHomogeneous_join_C_X {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (v : Fin (D + 1) × Fin N) :
    (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v).IsHomogeneous
      (if v.1 = Fin.last D then 1 else 0) := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simpa [join, Fin.castSucc_ne_last] using isHomogeneous_C (Fin 1 × Fin N) (s i j)
  · simpa [join] using isHomogeneous_X K ((0 : Fin 1), j)

theorem isHomogeneous_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N δ : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f) :
    (spec s f).IsHomogeneous δ := by
  classical
  unfold spec
  rw [f.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro m hm
  have hprod : (m.prod fun v e =>
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) ^ e).IsHomogeneous
      (∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v) :=
    IsHomogeneous.prod _ _ _ fun v _ => (isHomogeneous_join_C_X s v).pow (m v)
  have hdeg : ∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v = δ := by
    rw [Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [Finsupp.notMem_support_iff.1 hv])]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa using hf m hm (Fin.last D)
    · intro i _ hi
      simp [hi]
    · simp
  have h2 := (isHomogeneous_C (Fin 1 × Fin N) (algebraMap F K (coeff m f))).mul hprod
  rw [zero_add, hdeg] at h2
  rw [aeval_monomial, MvPolynomial.algebraMap_apply]
  exact h2

private lemma eval_join_C_X_eq_join {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (ξ : Fin N → K)
    (v : Fin (D + 1) × Fin N) :
    eval (fun p : Fin 1 × Fin N => ξ p.2)
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) = join s ξ v := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simp [join]
  · simp [join]

theorem eval_spec {F K : Type} [CommRing F] [CommRing K] [Algebra F K] {D N : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (ξ : Fin N → K) :
    eval (fun p => ξ p.2) (spec s f) = aeval (join s ξ) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [spec, MvPolynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [spec, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [spec, map_mul, aeval_X] at hp ⊢
    rw [hp, eval_join_C_X_eq_join]

end GlobalTheory.HSChoice.EtaleSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOutsideImageIdealVanishingOnBoundaryStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_outside_imageIdeal_vanishing_on_boundary : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational → ∃ (d : ℕ) (g : MvPolynomial (Fin T.N) F), g.IsHomogeneous d ∧ g ∉ T.imageIdeal ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0 := by
  first | exact @GlobalTheory.BoundaryForm.exists_form_vanishing | exact GlobalTheory.BoundaryForm.exists_form_vanishing | (intros; apply GlobalTheory.BoundaryForm.exists_form_vanishing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEqStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_charpoly_eq_of_mem_Ell : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := by
  first | exact @GlobalTheory.CompanionEll.exists_GL_charpoly_eq | exact GlobalTheory.CompanionEll.exists_GL_charpoly_eq | (intros; apply GlobalTheory.CompanionEll.exists_GL_charpoly_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndefiniteUnitaryLieAlgAddISmulEqStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq : ∀ (p q : ℕ) (Z : Mat p q), ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  first | exact @GlobalTheory.HoweD.upq_span | exact GlobalTheory.HoweD.upq_span | (intros; apply GlobalTheory.HoweD.upq_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallyRealEvenNegPlacesLocalNormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_totallyReal_even_neg_places_local_norm : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ (S : Finset (M →+* ℂ)), (∀ φ ∈ S, ComplexEmbedding.conjugate φ ∈ S) → 4 ∣ S.card → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (∀ φ ∈ S, (φ a).re < 0) ∧ (∀ φ : M →+* ℂ, φ ∉ S → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  first | exact @GlobalTheory.NormSign.exists_neg_even_norm_away | exact GlobalTheory.NormSign.exists_neg_even_norm_away | (intros; apply GlobalTheory.NormSign.exists_neg_even_norm_away <;> assumption)
end


import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerCoordinatesBound
section
open NumberField

namespace GlobalTheory.CompanionTheory.NumberFieldCoord

theorem abs_repr_le_of_forall_norm_embedding_le :
    ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)),
      Function.Surjective (fun i => InfinitePlace.mk (τ i)) →
      ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) →
        ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  intro E _ _ I _ τ hτ
  classical
  set Lc := LinearMap.toContinuousLinearMap (mixedEmbedding.latticeBasis E).equivFun.toLinearMap
    with hLc
  refine ⟨‖Lc‖ + 1, by positivity, fun e R hR k => ?_⟩
  have hR0 : 0 ≤ R := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    obtain ⟨i, -⟩ := hτ w
    exact (norm_nonneg _).trans (hR i)
  have hw : ∀ w : InfinitePlace E, w (e : E) ≤ R := by
    intro w
    obtain ⟨i, rfl⟩ := hτ w
    simpa only [InfinitePlace.apply] using hR i
  have hn : ‖mixedEmbedding E (e : E)‖ ≤ R := by
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_of_isReal w.2] at h
      simpa [mixedEmbedding] using h
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun w => ?_
      have h := hw w.1
      rw [← InfinitePlace.norm_embedding_eq] at h
      simpa [mixedEmbedding] using h
  have hval : Lc (mixedEmbedding E (e : E)) k = (((RingOfIntegers.basis E).repr e k : ℤ) : ℝ) := by
    change (mixedEmbedding.latticeBasis E).equivFun (mixedEmbedding E (e : E)) k = _
    rw [Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply]
    have := integralBasis_repr_apply E e k
    rw [show (e : E) = algebraMap (𝓞 E) E e from rfl, this]
    simp
  rw [← hval, ← Real.norm_eq_abs]
  calc ‖Lc (mixedEmbedding E (e : E)) k‖ ≤ ‖Lc (mixedEmbedding E (e : E))‖ := norm_le_pi_norm _ k
    _ ≤ ‖Lc‖ * ‖mixedEmbedding E (e : E)‖ := Lc.le_opNorm _
    _ ≤ ‖Lc‖ * R := by gcongr
    _ ≤ (‖Lc‖ + 1) * R := by nlinarith

end GlobalTheory.CompanionTheory.NumberFieldCoord
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableExpNegSumAbs
section
open MeasureTheory Topology

universe u

namespace GlobalTheory.CompanionTheory.EisTube

noncomputable def ker {ι : Type} [Fintype ι] (z : ι → ℂ) (t : ι → ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)

theorem integrable_exp_neg_sum_abs {ι : Type} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ι → ℝ => Real.exp (-(c * ∑ i, |t i|))) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
    have h2 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Iic 0) :=
      (integrableOn_exp_mul_Iic hc 0).congr_fun (fun x hx => by rw [abs_of_nonpos hx, neg_mul_neg])
        measurableSet_Iic
    have h3 := h2.union h1
    rw [Set.Iic_union_Ioi, integrableOn_univ] at h3
    exact h3
  have hI : Integrable (fun t : ι → ℝ => ∏ i, Real.exp (-c * |t i|)) (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (f := fun _ x => Real.exp (-c * |x|)) fun _ => h1
  rw [volume_pi]
  refine hI.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [← Real.exp_sum, neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]

theorem uniform_bound {ι : Type} [Fintype ι] {P : Type u} {h : P → ℝ} (hh : ∀ p, 0 ≤ h p)
    {ψ : P → (ι → ℝ) → ℂ}
    (hψ : ∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i)))
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * (R * ∑ i, |t i|))) := by
  classical
  choose Cf hCf using hψ
  let vec : (ι → Bool) → ι → ℝ := fun σ i => R * (if σ i then 1 else -1)
  refine ⟨∑ σ : ι → Bool, |Cf (vec σ)|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun p t => ?_⟩
  let σ : ι → Bool := fun i => decide (0 ≤ t i)
  have hs : ∑ i, vec σ i * t i = R * ∑ i, |t i| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 0 ≤ t i
    · simp [vec, σ, hi, abs_of_nonneg hi]
    · have hi' : t i < 0 := not_le.mp hi
      simp [vec, σ, hi, abs_of_neg hi']
  have h1 := hCf (vec σ) p t
  rw [hs] at h1
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_right ?_ (hh p)
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ : ι → Bool => |Cf (vec σ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ))

theorem norm_ker_le {ι : Type} [Fintype ι] {z : ι → ℂ} {B : ℝ} (hz : ∀ i, |(z i).re| ≤ B)
    (t : ι → ℝ) : ‖ker z t‖ ≤ Real.exp (2 * Real.pi * (B * ∑ i, |t i|)) := by
  rw [ker, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have h1 : (2 * (Real.pi : ℂ) * ∑ i, z i * t i).re = 2 * Real.pi * ∑ i, (z i).re * t i := by
    have : (2 * (Real.pi : ℂ) * ∑ i, z i * t i) = ((2 * Real.pi : ℝ) : ℂ) * ∑ i, z i * t i := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul, Complex.re_sum]
    simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (z i).re * t i ≤ |(z i).re * t i| := le_abs_self _
    _ = |(z i).re| * |t i| := abs_mul _ _
    _ ≤ B * |t i| := mul_le_mul_of_nonneg_right (hz i) (abs_nonneg _)

theorem dom_bound {ι : Type} [Fintype ι] {P : Type u} {h : P → ℝ} (hh : ∀ p, 0 ≤ h p)
    {ψ : P → (ι → ℝ) → ℂ} {C B : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ((B + 1) * ∑ i, |t i|))))
    {z : ι → ℂ} (hz : ∀ i, |(z i).re| ≤ B) (p : P) (t : ι → ℝ) :
    ‖ψ p t * ker z t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := by
  rw [norm_mul]
  calc ‖ψ p t‖ * ‖ker z t‖
      ≤ (C * h p * Real.exp (-(2 * Real.pi * ((B + 1) * ∑ i, |t i|)))) *
          Real.exp (2 * Real.pi * (B * ∑ i, |t i|)) :=
        mul_le_mul (hC p t) (norm_ker_le hz t) (norm_nonneg _)
          (mul_nonneg (mul_nonneg hC0 (hh p)) (Real.exp_pos _).le)
    _ = C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem continuous_ker_right {ι : Type} [Fintype ι] (z : ι → ℂ) : Continuous (ker z) := by
  unfold ker
  fun_prop

theorem continuous_ker_left {ι : Type} [Fintype ι] (t : ι → ℝ) :
    Continuous (fun z : ι → ℂ => ker z t) := by
  unfold ker
  fun_prop

theorem re_le_of_dist {ι : Type} [Fintype ι] {z z₀ : ι → ℂ} (hz : dist z z₀ < 1) (i : ι) :
    |(z i).re| ≤ (∑ j, |(z₀ j).re|) + 1 := by
  have h1 : ‖z i - z₀ i‖ ≤ ‖z - z₀‖ := norm_le_pi_norm (z - z₀) i
  have h2 : ‖z - z₀‖ < 1 := by rwa [← dist_eq_norm]
  have h3 : |(z i - z₀ i).re| ≤ ‖z i - z₀ i‖ := Complex.abs_re_le_norm _
  have h4 : |(z₀ i).re| ≤ ∑ j, |(z₀ j).re| :=
    Finset.single_le_sum (f := fun j => |(z₀ j).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h5 : |(z i).re| ≤ |(z i - z₀ i).re| + |(z₀ i).re| := by
    have : (z i).re = (z i - z₀ i).re + (z₀ i).re := by simp
    rw [this]
    simpa using abs_add_le (z i - z₀ i).re (z₀ i).re
  linarith

noncomputable def lin {ι : Type} [Fintype ι] (t : ι → ℝ) : (ι → ℂ) →L[ℂ] ℂ :=
  (2 * (Real.pi : ℂ)) • ∑ i, (t i : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i

theorem lin_apply {ι : Type} [Fintype ι] (t : ι → ℝ) (z : ι → ℂ) :
    lin t z = 2 * (Real.pi : ℂ) * ∑ i, z i * t i := by
  simp [lin, mul_comm]

theorem continuous_lin {ι : Type} [Fintype ι] : Continuous (lin (ι := ι)) := by
  unfold lin
  fun_prop

theorem norm_lin_le {ι : Type} [Fintype ι] (t : ι → ℝ) :
    ‖lin t‖ ≤ 2 * Real.pi * ∑ i, |t i| := by
  have h00 : 0 ≤ 2 * Real.pi * ∑ i, |t i| := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h00 fun z => ?_
  rw [lin_apply, norm_mul]
  have h0 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [h0, mul_assoc (2 * Real.pi)]
  refine mul_le_mul_of_nonneg_left ?_ h2pi
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_comm, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)

theorem hasFDerivAt_ker {ι : Type} [Fintype ι] (w : ℂ) (t : ι → ℝ) (z : ι → ℂ) :
    HasFDerivAt (fun z : ι → ℂ => w * ker z t) ((w * ker z t) • lin t) z := by
  have h1 : HasFDerivAt (fun z : ι → ℂ => lin t z) (lin t) z := (lin t).hasFDerivAt
  have h2 := (h1.cexp).const_mul w
  have e : (fun z : ι → ℂ => w * ker z t) = fun z => w * Complex.exp (lin t z) := by
    funext z; simp only [ker, lin_apply]
  have e2 : (w * ker z t) • lin t = w • Complex.exp (lin t z) • lin t := by
    rw [smul_smul, ker, lin_apply]
  rw [e, e2]
  exact h2

theorem mul_exp_le {S : ℝ} (hS : 0 ≤ S) :
    S * Real.exp (-(2 * Real.pi * S)) ≤ Real.exp (-S) := by
  have h1 : S ≤ Real.exp S := by linarith [Real.add_one_le_exp S]
  calc S * Real.exp (-(2 * Real.pi * S))
      ≤ Real.exp S * Real.exp (-(2 * Real.pi * S)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (S + -(2 * Real.pi * S)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-S) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [Real.pi_gt_three]

theorem laplaceEntire (ι : Type) [Fintype ι] (P : Type u) [TopologicalSpace P]
    [FirstCountableTopology P] (h : P → ℝ) (hh : ∀ p, 0 ≤ h p)
    (hloc : ∀ p, ∃ U ∈ nhds p, BddAbove (h '' U))
    (ψ : P → (ι → ℝ) → ℂ) (hm : ∀ p, MeasureTheory.AEStronglyMeasurable (ψ p))
    (hc : ∀ t, Continuous (fun p => ψ p t))
    (hv : ∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t,
      ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i))) :
    (∀ p (z : ι → ℂ), MeasureTheory.Integrable
        (fun t : ι → ℝ => ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    (∀ p, Differentiable ℂ (fun z : ι → ℂ =>
        ∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    Continuous (fun q : (ι → ℂ) × P =>
        ∫ t : ι → ℝ, ψ q.2 t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, q.1 i * t i)) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p,
        ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖ ≤ C * h p) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hG : Integrable (fun t : ι → ℝ => Real.exp (-(2 * Real.pi * ∑ i, |t i|))) :=
    integrable_exp_neg_sum_abs h2pi
  have hmeas : ∀ p (z : ι → ℂ), AEStronglyMeasurable (fun t => ψ p t * ker z t) := fun p z =>
    (hm p).mul (continuous_ker_right z).aestronglyMeasurable
  have hI : ∀ p (z : ι → ℂ), Integrable (fun t => ψ p t * ker z t) := by
    intro p z
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv ((∑ j, |(z j).re|) + 1 + 1)
    have hz : ∀ i, |(z i).re| ≤ (∑ j, |(z j).re|) + 1 := fun i =>
      re_le_of_dist (by simp) i
    exact Integrable.mono' (hG.const_mul (C * h p)) (hmeas p z)
      (Filter.Eventually.of_forall fun t => dom_bound hh hC0 hC hz p t)
  refine ⟨hI, ?_, ?_, ?_⟩
  · intro p z₀
    change DifferentiableAt ℂ (fun z : ι → ℂ => ∫ t : ι → ℝ, ψ p t * ker z t) z₀
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv ((∑ j, |(z₀ j).re|) + 1 + 1)
    have hb : ∀ t : ι → ℝ, ∀ z ∈ Metric.ball z₀ 1,
        ‖(ψ p t * ker z t) • lin t‖ ≤ C * h p * (2 * Real.pi) * Real.exp (-(1 * ∑ i, |t i|)) := by
      intro t z hz
      have hS : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hCh : 0 ≤ C * h p := mul_nonneg hC0 (hh p)
      rw [norm_smul, one_mul]
      calc ‖ψ p t * ker z t‖ * ‖lin t‖
          ≤ (C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|))) * (2 * Real.pi * ∑ i, |t i|) :=
            mul_le_mul (dom_bound hh hC0 hC (re_le_of_dist hz) p t) (norm_lin_le t) (norm_nonneg _)
              (mul_nonneg hCh (Real.exp_pos _).le)
        _ = C * h p * (2 * Real.pi) *
              ((∑ i, |t i|) * Real.exp (-(2 * Real.pi * ∑ i, |t i|))) := by ring
        _ ≤ C * h p * (2 * Real.pi) * Real.exp (-∑ i, |t i|) :=
            mul_le_mul_of_nonneg_left (mul_exp_le hS) (mul_nonneg hCh h2pi.le)
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := volume)
      (F := fun (z : ι → ℂ) (t : ι → ℝ) => ψ p t * ker z t)
      (F' := fun (z : ι → ℂ) (t : ι → ℝ) => (ψ p t * ker z t) • lin t) (x₀ := z₀)
      (s := Metric.ball z₀ 1)
      (bound := fun t => C * h p * (2 * Real.pi) * Real.exp (-(1 * ∑ i, |t i|)))
      (Metric.ball_mem_nhds _ one_pos) (Filter.Eventually.of_forall fun z => hmeas p z) (hI p z₀)
      ((hmeas p z₀).smul continuous_lin.aestronglyMeasurable)
      (Filter.Eventually.of_forall hb)
      ((integrable_exp_neg_sum_abs one_pos).const_mul _)
      (Filter.Eventually.of_forall fun t z _ => hasFDerivAt_ker (ψ p t) t z)
    exact key.differentiableAt
  · change Continuous (fun q : (ι → ℂ) × P => ∫ t : ι → ℝ, ψ q.2 t * ker q.1 t)
    rw [continuous_iff_continuousAt]
    rintro ⟨z₀, p₀⟩
    obtain ⟨U, hU, M, hM⟩ := hloc p₀
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv ((∑ j, |(z₀ j).re|) + 1 + 1)
    have hev : ∀ᶠ q : (ι → ℂ) × P in 𝓝 (z₀, p₀), dist q.1 z₀ < 1 ∧ q.2 ∈ U :=
      ((continuous_fst.tendsto (z₀, p₀)).eventually (Metric.ball_mem_nhds z₀ one_pos)).and
        ((continuous_snd.tendsto (z₀, p₀)).eventually hU)
    refine continuousAt_of_dominated
      (bound := fun t => C * M * Real.exp (-(2 * Real.pi * ∑ i, |t i|)))
      (Filter.Eventually.of_forall fun q => hmeas q.2 q.1)
      (hev.mono fun q hq => Filter.Eventually.of_forall fun t => ?_)
      (hG.const_mul (C * M)) (Filter.Eventually.of_forall fun t => ?_)
    · exact (dom_bound hh hC0 hC (re_le_of_dist hq.1) q.2 t).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM ⟨_, hq.2, rfl⟩) hC0) (Real.exp_pos _).le)
    · exact (((hc t).comp continuous_snd).mul
        ((continuous_ker_left t).comp continuous_fst)).continuousAt
  · intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have hz : ∀ z ∈ K, ∀ i, |(z i).re| ≤ R := fun z hzK i =>
      (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm z i).trans (hR z hzK))
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv (R + 1)
    refine ⟨C * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|)), fun z hzK p => ?_⟩
    have key := norm_integral_le_of_norm_le (hG.const_mul (C * h p))
      (Filter.Eventually.of_forall fun t => dom_bound hh hC0 hC (hz z hzK) p t)
    rw [integral_const_mul] at key
    calc ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖
        ≤ C * h p * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := key
      _ = (C * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|))) * h p := by ring

end GlobalTheory.CompanionTheory.EisTube
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
section
open scoped Matrix
open MeasureTheory

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

def PosOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, w ≠ 0 → 0 < ε * (star w ⬝ᵥ Z.mulVec w).re

def NonnegOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, 0 ≤ ε * (star w ⬝ᵥ Z.mulVec w).re

theorem integrable_of_mul_unimodular {α : Type} [MeasurableSpace α] (μ : Measure α) (a b : α → ℂ)
    (hi : Integrable (fun x => a x * b x) μ) (hb : AEStronglyMeasurable b μ) (hb1 : ∀ x, ‖b x‖ = 1) :
    Integrable a μ := by
  have hfun : a = fun x => (a x * b x) * star (b x) := by
    funext x
    rw [mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hb1]
    simp
  have hmeas : AEStronglyMeasurable a μ := by
    rw [hfun]
    exact hi.1.mul hb.star
  refine hi.mono hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hb1, mul_one]

theorem vanish_abs {X : Type} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] (e : X → X → ℂ)
    (he : ∀ z, Continuous fun v => e v z) (he' : ∀ v, Continuous fun z => e v z)
    (hen : ∀ a b, ‖e a b‖ = 1) (J : X → ℂ) (hJ : Integrable J μ) (N : Set X) (hN : IsOpen N)
    (hb : ∀ N' : Set X, IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : X → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, J v * e v z ∂μ) * Φ z ∂μ = 0) (z₀ : X) (hz : z₀ ∈ closure N) :
    ∫ v, J v * e v z₀ ∂μ = 0 := by
  have hbd : ∀ z, ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v‖ ∂μ := by
    intro z
    calc ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v * e v z‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ v, ‖J v‖ ∂μ := by
        congr 1
        ext v
        rw [norm_mul, hen, mul_one]
  have hFc : Continuous fun z => ∫ v, J v * e v z ∂μ := by
    refine continuous_of_dominated (F := fun z v => J v * e v z) (bound := fun v => ‖J v‖)
      (fun z => hJ.1.mul (he z).aestronglyMeasurable) (fun z => Filter.Eventually.of_forall
        fun v => by rw [norm_mul, hen, mul_one]) hJ.norm
      (Filter.Eventually.of_forall fun v => continuous_const.mul (he' v))
  set F : X → ℂ := fun z => ∫ v, J v * e v z ∂μ with hFdef
  have hzero : ∀ z₁ ∈ N, F z₁ = 0 := by
    intro z₁ hz₁
    by_contra hc
    set c := F z₁ with hcdef
    let G : X → ℝ := fun z => (starRingEnd ℂ c * F z).re
    have hGc : Continuous G := Complex.continuous_re.comp (continuous_const.mul hFc)
    have hG1 : 0 < G z₁ := by
      show 0 < (starRingEnd ℂ c * c).re
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact Complex.normSq_pos.mpr hc
    have hN'o : IsOpen (N ∩ {z | 0 < G z}) := hN.inter (isOpen_lt continuous_const hGc)
    obtain ⟨Φ, hΦc, hΦi, hΦpos, hΦsupp, hΦ1, hint⟩ :=
      hb _ hN'o Set.inter_subset_left z₁ ⟨hz₁, hG1⟩
    have hint' : ∫ z, F z * Φ z ∂μ = 0 := hint
    have hFΦi : Integrable (fun z => F z * Φ z) μ := by
      refine Integrable.mono (hΦi.norm.const_mul (∫ v, ‖J v‖ ∂μ))
        (hFc.aestronglyMeasurable.mul hΦi.1) (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_mul, abs_norm,
        abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hbd z) (norm_nonneg _)
    let H : X → ℝ := fun z => (starRingEnd ℂ c * (F z * Φ z)).re
    have hHeq : ∀ z, H z = G z * (Φ z).re := by
      intro z
      simp only [H, G]
      rw [← mul_assoc, Complex.mul_re, (hΦpos z).2, mul_zero, sub_zero]
    have hHnn : ∀ z, 0 ≤ H z := by
      intro z
      rw [hHeq]
      by_cases hz : z ∈ N ∩ {z | 0 < G z}
      · exact mul_nonneg hz.2.le (hΦpos z).1
      · rw [hΦsupp z hz]
        simp
    have hHc : Continuous H := Complex.continuous_re.comp (continuous_const.mul (hFc.mul hΦc))
    have hHi : Integrable H μ := (hFΦi.const_mul (starRingEnd ℂ c)).re
    have hHpos : 0 < ∫ z, H z ∂μ := by
      rw [integral_pos_iff_support_of_nonneg (fun z => hHnn z) hHi]
      apply hHc.isOpen_support.measure_pos μ
      refine ⟨z₁, ?_⟩
      rw [Function.mem_support, hHeq]
      exact (mul_pos hG1 hΦ1).ne'
    have hHzero : ∫ z, H z ∂μ = 0 := by
      have h : ∫ z, H z ∂μ = (∫ z, starRingEnd ℂ c * (F z * Φ z) ∂μ).re :=
        integral_re (hFΦi.const_mul _)
      rw [h, integral_const_mul, hint', mul_zero, Complex.zero_re]
    linarith
  exact closure_minimal hzero (isClosed_eq hFc continuous_const) hz

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralAddRightMulChar
section
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.PsiShift

theorem integral_add_right_mul_char {K : Type*} [AddCommGroup K] [MeasurableSpace K]
    [MeasurableAdd K] (μ : Measure K) [μ.IsAddRightInvariant] (ψ : AddChar K Circle)
    (f : K → ℂ) (x : K) :
    ∫ y, f (y + x) * (ψ (-y) : ℂ) ∂μ = (ψ x : ℂ) * ∫ y, f y * (ψ (-y) : ℂ) ∂μ := by
  have h := integral_add_right_eq_self (μ := μ) (fun y => f y * (ψ (-(y - x)) : ℂ)) x
  have h1 : ∀ y, f (y + x) * (ψ (-(y + x - x)) : ℂ) = f (y + x) * (ψ (-y) : ℂ) := fun y => by
    simp
  have h2 : ∀ y, f y * (ψ (-(y - x)) : ℂ) = (ψ x : ℂ) * (f y * (ψ (-y) : ℂ)) := fun y => by
    have : -(y - x) = x + -y := by abel
    rw [this, AddChar.map_add_eq_mul]
    push_cast
    ring
  simp only [h1, h2] at h
  rw [h, integral_const_mul]

theorem vecMul_unipotent {R : Type*} [CommRing R] (h y x : R) :
    ![h, h * y] ᵥ* !![1, x; 0, 1] = ![h, h * (y + x)] := by
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

end GlobalTheory.CompanionTheory.PsiShift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalOpenStabilizer
section
namespace GlobalTheory.CompanionTheory.Smooth

def linearFormStabiliser {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {g : G | l ∘ₗ ρ g = l}
  mul_mem' := by
    intro a b ha hb
    have ha' : l ∘ₗ ρ a = l := ha
    have hb' : l ∘ₗ ρ b = l := hb
    show l ∘ₗ ρ (a * b) = l
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha', hb']
  one_mem' := by
    show l ∘ₗ ρ 1 = l
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    have ha' : l ∘ₗ ρ a = l := ha
    show l ∘ₗ ρ a⁻¹ = l
    conv_lhs => rw [← ha']
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem isOpen_linearForm_stabiliser {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (l : Module.Dual ℂ V)
    (hl : ∀ x ∈ K, l ∘ₗ ρ x = l) : IsOpen {g : G | l ∘ₗ ρ g = l} :=
  Subgroup.isOpen_mono (H₁ := K) (H₂ := linearFormStabiliser ρ l) (fun x hx => hl x hx) hK

end GlobalTheory.CompanionTheory.Smooth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorOfScaledIsometricIntertwiner
section
open Topology

namespace GlobalTheory.CompanionTheory.CompactOperators

theorem isCompactOperator_of_scaled_isometric_intertwiner
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) (Φ : H →L[ℂ] K) (c : ℝ) (hc : 0 < c)
    (hΦ : ∀ x, ‖Φ x‖ = c * ‖x‖) (hAB : Φ ∘L A = B ∘L Φ) (hB : IsCompactOperator B) :
    IsCompactOperator A := by
  have hcn : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) Φ := by
    refine Φ.antilipschitz_of_bound fun x => ?_
    rw [Real.coe_toNNReal _ hcn, hΦ, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hemb : IsClosedEmbedding Φ := hanti.isClosedEmbedding Φ.uniformContinuous
  obtain ⟨S, hS, hSn⟩ := hB
  refine ⟨Φ ⁻¹' S, hemb.isCompact_preimage hS, ?_⟩
  have hpre : A ⁻¹' (Φ ⁻¹' S) = Φ ⁻¹' (B ⁻¹' S) := by
    ext x
    show Φ (A x) ∈ S ↔ B (Φ x) ∈ S
    rw [show Φ (A x) = B (Φ x) from ContinuousLinearMap.ext_iff.mp hAB x]
  rw [hpre]
  exact Φ.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hSn)

end GlobalTheory.CompanionTheory.CompactOperators
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroup
section
open Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Topology

theorem isCompact_addSubgroup_sup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  intro X _ _ _ A B hA hB
  have h : ((A ⊔ B : AddSubgroup X) : Set X) = (A : Set X) + (B : Set X) := by
    ext x
    simp only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]
  rw [h]
  exact hA.add hB

end GlobalTheory.CompanionTheory.Topology
end


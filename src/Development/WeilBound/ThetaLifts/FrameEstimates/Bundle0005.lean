import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.OneVar
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped NNReal ENNReal
open MeasureTheory Metric

section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_sep (Λ : Submodule ℤ V) [DiscreteTopology Λ] :
    ∃ ε : ℝ, 0 < ε ∧ Pairwise (Function.onFun Disjoint fun x : Λ => ball (x : V) ε) := by
  obtain ⟨δ, hδ, h⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set Λ)) 0 rfl
  refine ⟨δ / 2, by positivity, fun x y hxy => ?_⟩
  apply Metric.ball_disjoint_ball
  by_contra hlt
  push Not at hlt
  apply hxy
  have hm : x - y ∈ ball (0 : Λ) δ := by
    rw [mem_ball_zero_iff]
    have : ‖x - y‖ = dist (x : V) (y : V) := by
      rw [dist_eq_norm]; rfl
    linarith
  exact sub_eq_zero.1 (h hm)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_pt {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε) (N : ℕ) {x y : V} (hy : y ∈ ball x ε) :
    ((1 + c * ‖x‖) ^ N)⁻¹ ≤ (1 + ε) ^ N * ((1 + ‖c • (1 : ℝ)‖ * ‖y‖) ^ N)⁻¹ := by
  have hcn : ‖c • (1 : ℝ)‖ = c := by simp [abs_of_pos hc]
  rw [hcn]
  have h1 : ‖y‖ ≤ ‖x‖ + ε := by
    have := mem_ball_iff_norm.1 hy
    have h2 := norm_le_norm_add_norm_sub' y x
    linarith
  have hx := norm_nonneg x
  have hy0 := norm_nonneg y
  have h2 : 1 + c * ‖y‖ ≤ (1 + ε) * (1 + c * ‖x‖) := by
    have : c * ‖y‖ ≤ c * (‖x‖ + ε) := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 : c * ε ≤ ε := by nlinarith
    have h4 : 0 ≤ ε * (c * ‖x‖) := by positivity
    nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h2 N

theorem oneVar_core (Λ : Submodule ℤ V) [DiscreteTopology Λ] (N : ℕ) (hN : Module.finrank ℝ V < N) :
    ∃ K : ℝ≥0, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ K * ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) := by
  borelize V
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  set μ : Measure V := Measure.addHaar with hμ
  obtain ⟨ε, hε, hd⟩ := oneVar_sep Λ
  set f : V → ℝ≥0∞ := fun y => ENNReal.ofReal (((1 + ‖y‖) ^ N)⁻¹) with hf
  have hfm : Measurable f := by
    rw [hf]; fun_prop
  have hI : ∫⁻ y, f y ∂μ < ⊤ := by
    have := finite_integral_one_add_norm (E := V) (μ := μ) (r := (N : ℝ)) (by exact_mod_cast hN)
    refine lt_of_eq_of_lt (lintegral_congr fun y => ?_) this
    rw [hf, Real.rpow_neg (by positivity), Real.rpow_natCast]
  set b : ℝ≥0∞ := μ (ball (0 : V) ε) with hb
  have hb0 : b ≠ 0 := (measure_ball_pos μ _ hε).ne'
  have hbt : b ≠ ⊤ := measure_ball_lt_top.ne
  set A : ℝ≥0∞ := ENNReal.ofReal ((1 + ε) ^ N) with hA
  have hK : b⁻¹ * A * ∫⁻ y, f y ∂μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hb0) ENNReal.ofReal_ne_top) hI.ne
  refine ⟨(b⁻¹ * A * ∫⁻ y, f y ∂μ).toNNReal, fun c hc hc1 => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  have hsc : ∫⁻ y, f (c • y) ∂μ = ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) * ∫⁻ y, f y ∂μ := by
    rw [← lintegral_map hfm (measurable_const_smul c), Measure.map_addHaar_smul μ hc.ne', lintegral_smul_measure,
      abs_of_pos (by positivity), smul_eq_mul]
  have hpt : ∀ x : Λ, b * ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y in ball (x : V) ε, f (c • y) ∂μ := by
    intro x
    have e1 : b = μ (ball (x : V) ε) := (Measure.addHaar_ball_center μ _ _).symm
    rw [e1, mul_comm, ← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
    simp only [hf]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := oneVar_pt hc hc1 hε N hy
    simpa [norm_smul] using this
  have hsum : b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y, f (c • y) ∂μ := by
    rw [← ENNReal.tsum_mul_left]
    refine (ENNReal.tsum_le_tsum hpt).trans ?_
    rw [ENNReal.tsum_mul_left, ← lintegral_iUnion (fun _ => measurableSet_ball) hd]
    gcongr
    exact Measure.restrict_le_self
  calc ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)
      = b⁻¹ * (b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hb0 hbt, one_mul]
    _ ≤ b⁻¹ * (A * ∫⁻ y, f (c • y) ∂μ) := by gcongr
    _ = _ := by rw [hsc]; ring

end

theorem oneVar_of : OneVar := by
  intro V _ _ _ Λ _ N hN
  obtain ⟨K, hK⟩ := oneVar_core Λ N hN
  refine ⟨K, fun l => ?_⟩
  have h := hK (Real.exp (-max 0 l)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by simp))
  rw [← Real.exp_nat_mul, ← Real.exp_neg, mul_neg, neg_neg] at h
  refine le_trans (ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_) h
  have : Real.exp (-max 0 l) ≤ Real.exp (-l) := Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
  gcongr

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.Parity
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ParityOfCoefficients

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem neg_mem_schA {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) : (fun x => Φ (-x)) ∈ schA F κ := by
  classical
  induction h using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f,
      fun y => g (-y), ⟨hg.1.comp_continuous continuous_neg, hg.2.comp_homeomorph (Homeomorph.neg _)⟩, ?_⟩
    funext x
    simp only [pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.neg_apply]
    congr 2
    funext i
    exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem exists_haar : ∃ μ : Measure (κ → AF F), μ.IsAddHaarMeasure ∧
    ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (κ → AF F)) := inferInstance
  exact ⟨Measure.addHaarMeasure K, inferInstance, fun f => integral_neg_eq_self f _⟩

theorem coef_neg (ψ : AddChar (AF F) ℂ) (μ : Measure (κ → AF F))
    (hμ : ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ) (Φ₁ Φ₂ : (κ → AF F) → ℂ)
    (w : (κ → AF F) × (κ → AF F)) :
    coef F ψ μ Φ₁ Φ₂ (-w) = coef F ψ μ (fun x => Φ₁ (-x)) (fun x => Φ₂ (-x)) w := by
  unfold coef
  rw [← hμ]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [schr, Prod.fst_neg, Prod.snd_neg, neg_dotProduct_neg, neg_add]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

def negOne (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J :=
  ⟨-1, by
    change ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J *
      ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J
    rw [Units.val_neg, Units.val_one, Matrix.map_neg _ (map_neg (cA σ)),
      Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
    simp⟩

theorem mat_negOne_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (negOne σ J)⁻¹ = -1 := rfl

theorem mat_one_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (1 : UA σ J)⁻¹ = 1 := rfl

end ParityOfCoefficients

open ParityOfCoefficients in

theorem parity_of (hC : CoefEq) (hF : FourierInj) : Parity := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨μ, hμ, hneg⟩ := exists_haar (F := F) (κ := Fin n × Fin d)
  have pres : ∀ Φ ∈ schA F (Fin n × Fin d), om (negOne σ X.J, 1) Φ ∈ schA F (Fin n × Fin d) :=
    fun Φ hΦ => (IsUWeilPair.isUSplitting hp.weil).pres _ Φ hΦ
  have key : ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ x u,
      om (negOne σ X.J, 1) Φ₁ x * (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₂ u) =
        Φ₁ (-x) * (starRingEnd ℂ) (Φ₂ (-u)) := by
    intro Φ₁ h₁ Φ₂ h₂
    refine hF F _ B.ψ hp.base.std μ hμ _ (pres _ h₁) _ (pres _ h₂) _ (neg_mem_schA h₁) _ (neg_mem_schA h₂) ?_
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂, ← coef_neg B.ψ μ hneg, mat_negOne_inv,
      mat_one_inv, Matrix.transpose_one, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul, map_neg]
  by_cases h0 : ∃ Φ₀ ∈ schA F (Fin n × Fin d), ∃ u, Φ₀ (-u) ≠ 0
  · obtain ⟨Φ₀, hΦ₀, u, hu⟩ := h0
    have h1 := congrArg norm (key Φ₀ hΦ₀ Φ₀ hΦ₀ u u)
    simp only [norm_mul, Complex.norm_conj] at h1
    have h2 : ‖om (negOne σ X.J, 1) Φ₀ u‖ = ‖Φ₀ (-u)‖ :=
      (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp h1
    have h3 : ‖Φ₀ (-u)‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have h4 : (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u) ≠ 0 := by
      rw [← norm_ne_zero_iff, Complex.norm_conj, h2]; exact h3
    refine ⟨negOne σ X.J, (starRingEnd ℂ) (Φ₀ (-u)) / (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u), rfl, ?_,
      fun Φ hΦ => funext fun x => ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_conj, h2, div_self h3]
    · rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key Φ hΦ Φ₀ hΦ₀, mul_comm]
  · refine ⟨negOne σ X.J, 1, rfl, norm_one, fun Φ hΦ => ?_⟩
    have z : ∀ Ψ ∈ schA F (Fin n × Fin d), Ψ = 0 := fun Ψ hΨ => funext fun x => by
      by_contra hx
      exact h0 ⟨Ψ, hΨ, -x, by rwa [neg_neg]⟩
    rw [z _ (pres Φ hΦ), one_smul, z _ (neg_mem_schA hΦ)]

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.UFinMulRId
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem denom_fin {K : Set (Af F)} (hK : IsCompact K) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : F, algebraMap F (Af F) x ∈ K → IsIntegral ℤ ((m : F) * x) := by
  have hopen : IsOpen {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hNe : Nonempty {M : ℕ // 0 < M} := ⟨⟨1, Nat.one_pos⟩⟩
  obtain ⟨M, hM⟩ := hK.elim_directed_cover
    (fun M : {M : ℕ // 0 < M} => ⋃ d ∈ {d : ℕ | 0 < d ∧ d ∣ M.1},
      (fun a : Af F => (d : Af F) * a) ⁻¹' {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v})
    (fun M => isOpen_biUnion fun d _ => hopen.preimage (continuous_const.mul continuous_id))
    (fun a _ => by
      obtain ⟨d, hd, h⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a
      exact Set.mem_iUnion.2 ⟨⟨d, hd⟩, Set.mem_iUnion₂.2 ⟨d, ⟨hd, dvd_refl d⟩, h⟩⟩)
    (fun M N => ⟨⟨M.1 * N.1, Nat.mul_pos M.2 N.2⟩, fun a ha => by
      obtain ⟨d, hd, h⟩ := Set.mem_iUnion₂.1 ha
      exact Set.mem_iUnion₂.2 ⟨d, ⟨hd.1, hd.2.mul_right _⟩, h⟩, fun a ha => by
      obtain ⟨d, hd, h⟩ := Set.mem_iUnion₂.1 ha
      exact Set.mem_iUnion₂.2 ⟨d, ⟨hd.1, hd.2.mul_left _⟩, h⟩⟩)
  refine ⟨M.1, M.2, fun x hx => ?_⟩
  obtain ⟨d, hd, h⟩ := Set.mem_iUnion₂.1 (hM hx)
  have h2 : ∀ v, (algebraMap F (Af F) ((d : F) * x)) v ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [map_mul, map_natCast]
    exact h
  obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 _ h2
  have hdx : IsIntegral ℤ ((d : F) * x) := by
    rw [hy]
    exact y.isIntegral_coe
  obtain ⟨e, he⟩ := hd.2
  have hei : IsIntegral ℤ (e : F) := by
    have h3 := isIntegral_algebraMap (R := ℤ) (A := F) (x := (e : ℤ))
    simpa using h3
  rw [he, Nat.cast_mul, mul_comm (d : F) (e : F), mul_assoc]
  exact hei.mul hdx

variable (F) in

def uFin : AF F := pairA F 0 1

theorem evI_uFin : evI F (uFin F) = 0 := by
  unfold evI uFin pairA
  exact map_zero _

theorem snd_uFin_mul (a : AF F) : sndA F (uFin F * a) = sndA F a := by
  show (1 : Af F) * a.2 = a.2
  exact one_mul _

theorem uFin_mul_rId (t : ℝ) : uFin F * rId F t = uFin F := by
  show pairA F 0 1 * rId F t = pairA F 0 1
  refine Prod.ext ?_ ?_
  · show (0 : Ainf F) * (rId F t).1 = 0
    exact zero_mul _
  · show (1 : Af F) * ((1 : Af F) + 0) = 1
    simp

theorem exists_int_mul (x : E) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * x) := by
  have hq : IsAlgebraic ℚ x := (Algebra.IsIntegral.isIntegral x).isAlgebraic
  have hz : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hq
  obtain ⟨d, hd, hy⟩ := hz.exists_integral_multiple
  rw [Algebra.smul_def, eq_intCast] at hy
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · refine ⟨k, by omega, ?_⟩
    simpa using hy
  · refine ⟨k, by omega, ?_⟩
    have h2 := hy.neg
    simpa using h2
private theorem isIntegral_natCast_mul_of_dvd {A : Type} [CommRing A] {a b : ℕ} (hab : a ∣ b) {y : A}
    (h : IsIntegral ℤ ((a : A) * y)) : IsIntegral ℤ ((b : A) * y) := by
  obtain ⟨e, rfl⟩ := hab
  have he : IsIntegral ℤ (e : A) := by
    have h3 := isIntegral_algebraMap (R := ℤ) (A := A) (x := (e : ℤ))
    simpa using h3
  rw [Nat.cast_mul, mul_comm (a : A) (e : A), mul_assoc]
  exact he.mul h

theorem denom_AE {K : Set (AE F E)} (hK : IsCompact K) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : E, (∃ c ∈ K, uFin F • inclR (F := F) (AF F) x = uFin F • c) → IsIntegral ℤ ((m : E) * x) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop (F := F) (E := E)
  let b := Module.finBasis F E
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  have hcont : ∀ i, Continuous fun c : AE F E => sndA F (B.coord i c) := fun i =>
    continuous_snd.comp (IsModuleTopology.continuous_of_linearMap (B.coord i))
  choose m hm hint using fun i => denom_fin (hK.image (hcont i))
  choose n hn hbi using fun i => exists_int_mul (b i)
  refine ⟨(∏ i, m i) * ∏ i, n i, Nat.mul_pos (Finset.prod_pos fun i _ => hm i) (Finset.prod_pos fun i _ => hn i), ?_⟩
  rintro x ⟨c, hcK, hxc⟩
  have hcoord : ∀ i, algebraMap F (Af F) (b.repr x i) = sndA F (B.coord i c) := by
    intro i
    have h1 := congrArg (fun y => sndA F (B.coord i y)) hxc
    simp only [LinearMap.map_smul, smul_eq_mul, snd_uFin_mul] at h1
    rw [← h1]
    simp [B, inclR, Algebra.TensorProduct.basis_repr_tmul]
  have hr : ∀ i, IsIntegral ℤ (((∏ j, m j : ℕ) : F) * b.repr x i) := fun i =>
    isIntegral_natCast_mul_of_dvd (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (hint i _ ⟨c, hcK, (hcoord i).symm⟩)
  have hbb : ∀ i, IsIntegral ℤ (((∏ j, n j : ℕ) : E) * b i) := fun i =>
    isIntegral_natCast_mul_of_dvd (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) (hbi i)
  have hx : (((∏ i, m i) * ∏ i, n i : ℕ) : E) * x =
      ∑ i, algebraMap F E (((∏ j, m j : ℕ) : F) * b.repr x i) * (((∏ j, n j : ℕ) : E) * b i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast]
    push_cast
    ring
  rw [hx]
  exact (integralClosure ℤ E).sum_mem fun i _ => (hr i).algebraMap.mul (hbb i)

omit [NumberField E] in
theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb]

omit [NumberField E] in
theorem piInf_rId {w : InfinitePlace F} (τ : EmbOver E w) (t : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (rId F t)) = (Real.exp t : ℝ) := by
  simp only [piInf, compInf, infEmb, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  show InfinitePlace.Completion.extensionEmbedding w ((rId F t).1 w) = ((Real.exp t : ℝ) : ℂ)
  have hy : InfiniteAdeleRing.ringEquiv_mixedSpace F (rId F t).1 =
      ((fun _ => Real.exp t), (fun _ => ((Real.exp t : ℝ) : ℂ))) := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (algebraMap ℝ (mixedEmbedding.mixedSpace F) (Real.exp t - 1))) = _
    rw [map_add, map_one, RingEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_ <;> funext v <;> simp
  by_cases hw : w.IsReal
  · have h1 := congrArg (fun z => z.1 ⟨w, hw⟩) hy
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, h1]
  · have h1 := congrArg (fun z => z.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 hw⟩) hy
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h1
    exact h1

end PositivityTheory.ThKEst

end
end


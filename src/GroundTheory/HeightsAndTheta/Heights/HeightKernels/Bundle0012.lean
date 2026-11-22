import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaConstants
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace KThetaConstants

lemma log_lhs (C₃ ρ d : ℝ) (g : ℕ) (hC₃ : 0 < C₃) (hg : (0 : ℝ) < g) (hρ : 0 < ρ) (hd : 0 < d) :
    Real.log ((C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g) =
      (g / 2) * Real.log (C₃ * g) + (-(1 / 2)) * Real.log d + g * Real.log (1 + 1 / ρ) := by
  have h1 : 0 < C₃ * g := mul_pos hC₃ hg
  have h2 : 0 < 1 + 1 / ρ := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow h1, Real.log_rpow hd, Real.log_pow]

lemma log_rhs (C ρ d : ℝ) (g : ℕ) (hd : 0 < d) :
    Real.log (((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) *
        exp (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g))) =
      (-(1 / 4)) * (g * Real.log 2 + Real.log d) +
        (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g)) := by
  have h1 : 0 < (2 : ℝ) ^ g * d := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow h1, Real.log_exp,
    Real.log_mul (by positivity) hd.ne', Real.log_pow]

end KThetaConstants

open KThetaConstants in

theorem ThetaConstants.proof : ThetaConstants.Statement := by
  intro C₃ hC₃
  have hK1 : (1 : ℝ) ≤ max C₃ 1 := le_max_right _ _
  have hK0 : (0 : ℝ) < max C₃ 1 := by linarith
  have hlK : 0 ≤ Real.log (max C₃ 1) := Real.log_nonneg hK1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + Real.log (max C₃ 1) / (2 * Real.log 2), by positivity, ?_⟩
  intro g ρ d hg hρ hd hρ2 hdinv
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  have h2g : (0 : ℝ) < 2 * g := by linarith
  have hl2g : Real.log 2 ≤ Real.log (2 * g) := Real.log_le_log (by norm_num) (by linarith)
  have h1 : -Real.log d ≤ g * Real.log (2 * g) := by
    have hpow : ρ ^ 2 * (2 * (g : ℝ)) ^ (g - 1) ≤ (2 * (g : ℝ)) ^ g := by
      obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ' (2 * ((n + 1 : ℕ) : ℝ)) n]
      exact mul_le_mul_of_nonneg_right hρ2 (pow_nonneg h2g.le n)
    have := Real.log_le_log (inv_pos.mpr hd) (hdinv.trans hpow)
    rwa [Real.log_inv, Real.log_pow] at this
  have h2 : Real.log (C₃ * g) ≤ Real.log (max C₃ 1) + Real.log (2 * g) := by
    rw [← Real.log_mul hK0.ne' h2g.ne']
    apply Real.log_le_log (mul_pos hC₃ hg0)
    have : C₃ ≤ max C₃ 1 := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_right this hg0.le,
      mul_le_mul_of_nonneg_left (show (g : ℝ) ≤ 2 * g by linarith) hK0.le]
  have h5 : (g : ℝ) / 2 * Real.log (max C₃ 1) ≤
      Real.log (max C₃ 1) / (2 * Real.log 2) * g * Real.log (2 * g) := by
    rw [show Real.log (max C₃ 1) / (2 * Real.log 2) * g * Real.log (2 * g) =
        (g * Real.log (max C₃ 1) * Real.log (2 * g)) / (2 * Real.log 2) by ring,
      le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hl2g (mul_nonneg hg0.le hlK)]
  have ha := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ g / 2 by positivity)
  have hc := mul_le_mul_of_nonneg_left hl2g hg0.le
  rw [← Real.log_le_log_iff (by positivity) (by positivity), log_lhs C₃ ρ d g hC₃ hg0 hρ hd,
    log_rhs _ ρ d g hd]
  nlinarith [h1, ha, hc, h5]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCubeParseval
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace KThetaCubeParseval

lemma torusChar_eq {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = Complex.exp (((2 * π * ∑ i, (m i : ℝ) * u i : ℝ) : ℂ) * Complex.I) := by
  unfold torusChar
  congr 1
  push_cast
  ring

lemma norm_torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ‖torusChar m u‖ = 1 := by
  rw [torusChar_eq, Complex.norm_exp_ofReal_mul_I]

lemma torusChar_mul_conj {g : ℕ} (k l : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar k u * conj (torusChar l u) = torusChar (k - l) u := by
  rw [torusChar_eq, torusChar_eq, torusChar_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

lemma continuous_torusChar {g : ℕ} (m : Fin g → ℤ) : Continuous (torusChar m) := by
  unfold torusChar
  fun_prop

lemma measureReal_cube (g : ℕ) :
    (volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)).real Set.univ = 1 := by
  simp [Measure.real, Real.volume_Icc_pi]

end KThetaCubeParseval

open KThetaCubeParseval in

theorem ThetaCubeParseval.proof (h : ThetaCharIntegral.Statement) : ThetaCubeParseval.Statement := by
  intro g c hc
  set μ := volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)

  set F : (Fin g → ℤ) × (Fin g → ℤ) → (Fin g → ℝ) → ℂ :=
    fun p u => c p.1 * conj (c p.2) * torusChar (p.1 - p.2) u with hF
  have hnorm1 : ∀ u, Summable fun k => ‖c k * torusChar k u‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hnorm2 : ∀ u, Summable fun l => ‖conj (c l) * conj (torusChar l u)‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hpt : ∀ u, ((‖∑' k, c k * torusChar k u‖ ^ 2 : ℝ) : ℂ) = ∑' p, F p u := by
    intro u
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Complex.conj_tsum]
    simp only [map_mul]
    rw [tsum_mul_tsum_of_summable_norm (hnorm1 u) (hnorm2 u)]
    congr 1
    ext p
    rw [hF]
    dsimp only
    rw [← torusChar_mul_conj]
    ring
  have hnormF : ∀ p u, ‖F p u‖ = ‖c p.1‖ * ‖c p.2‖ := by
    intro p u
    simp [hF, norm_torusChar]
  have hint : ∀ p, Integrable (F p) μ := fun p =>
    ((continuous_torusChar (p.1 - p.2)).const_smul (c p.1 * conj (c p.2))).integrableOn_Icc
  have hμ : μ.real Set.univ = 1 := measureReal_cube g
  have hsum : Summable fun p => ∫ u, ‖F p u‖ ∂μ := by
    simp only [hnormF, integral_const, hμ, one_smul]
    exact Summable.mul_of_nonneg hc hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hterm : ∀ p, ∫ u, F p u ∂μ = if p.1 - p.2 = 0 then c p.1 * conj (c p.2) else 0 := by
    intro p
    rw [hF]
    dsimp only
    rw [integral_const_mul, h g (p.1 - p.2)]
    split_ifs <;> simp
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_tsum]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hterm]
  have hinj : Function.Injective fun k : Fin g → ℤ => (k, k) := fun a b hab => (Prod.mk.inj hab).1
  rw [← hinj.tsum_eq]
  · congr 1
    ext k
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro p hp
    have : p.1 - p.2 = 0 := by
      by_contra hne
      exact hp (by simp [hne])
    exact ⟨p.1, Prod.ext rfl (sub_eq_zero.mp this)⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaSummandNorm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

noncomputable section

namespace KThetaSummandNorm

lemma im_dot_period {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (w v : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (v i : ℂ))).im = w ⬝ᵥ (Y *ᵥ v) := by
  simp only [dotProduct, mulVec, periodMatrix, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_sum, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp

lemma im_dot_real {g : ℕ} (w c : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ fun i => (c i : ℂ)).im = 0 := by
  simp [dotProduct, Complex.im_sum]

lemma qf_add {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.IsSymm) (w u : Fin g → ℝ) :
    qf Y (w + u) = qf Y w + 2 * (w ⬝ᵥ (Y *ᵥ u)) + qf Y u := by
  have h : u ⬝ᵥ (Y *ᵥ w) = w ⬝ᵥ (Y *ᵥ u) := by
    rw [dotProduct_mulVec, ← vecMul_transpose, hY.eq, dotProduct_comm]
  simp only [qf, mulVec_add, dotProduct_add, add_dotProduct, h]
  ring

end KThetaSummandNorm

open KThetaSummandNorm in
theorem ThetaSummandNorm.proof : ThetaSummandNorm.Statement := by
  intro g X Y a b u₁ u₂ k hY
  set w : Fin g → ℝ := intVec k + a with hw
  have hW : (fun i => ((intVec k i + a i : ℝ) : ℂ)) = fun i => (w i : ℂ) := rfl
  have hzb : (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) +
      (fun i => (b i : ℂ)) =
      periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ) := by
    ext i; simp [add_assoc]
  have hre : (π * Complex.I *
      ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (w i : ℂ))) +
      2 * π * Complex.I * ((fun i => (w i : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ)))).re =
      -π * qf Y w - 2 * π * (w ⬝ᵥ (Y *ᵥ u₁)) := by
    rw [dotProduct_add]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im,
      im_dot_period, im_dot_real]
    simp only [qf]
    ring
  unfold thetaSummand
  rw [hW, hzb, Complex.norm_exp, hre, ← Real.exp_add]
  congr 1
  have : intVec k + a + u₁ = w + u₁ := rfl
  rw [this, qf_add Y hY w u₁]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

theorem ThetaBound.proof (hG : GaussianSum.Statement) (hMean : ThetaMean.Statement)
    (hMaj : ThetaNormMajorant.Statement) (hSplit : ThetaFirstCoordSplit.Statement)
    (hConst : ThetaConstants.Statement) : ThetaBound.Statement := by
  obtain ⟨C₃, hC₃, hG⟩ := hG
  obtain ⟨C, hC, hK⟩ := hConst C₃ hC₃
  refine ⟨C, hC, ?_⟩
  intro g _ X Y ρ a b _ hY hR _ _
  refine ⟨hMean g X Y a b hY, fun u₁ u₂ => ?_⟩
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ))
  have hdet : Y.det⁻¹ ≤ ρ ^ 2 * (2 * (g : ℝ)) ^ (g - 1) := by
    have h := hR.det_le
    rwa [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h
  have hg : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have h1 := hMaj g X Y a b u₁ u₂ hY
  have h2 := hSplit g Y ρ a u₁ hY hR.pos hR.first
  have h3 := (hG g Y ρ hY hR.pos hR.min (a + u₁)).2
  have h4 := hK g ρ Y.det hg hR.pos hY.det_pos hR.sq_le hdet
  have he : 0 ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := (exp_pos _).le
  calc thetaNorm X Y a b u₁ u₂ ≤ ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) := h1
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) *
          ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := h2
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) *
          ((C₃ * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g) :=
        mul_le_mul_of_nonneg_left h3 he
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) * (((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
          exp (g * log (1 + 1 / ρ) + C * g * log (2 * g))) :=
        mul_le_mul_of_nonneg_left h4 he
    _ = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
          exp (-(π / (2 * ρ ^ 2)) * δ ^ 2 + (g * log (1 + 1 / ρ) + C * g * log (2 * g))) := by
        rw [exp_add (-(π / (2 * ρ ^ 2)) * δ ^ 2)]; ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StandardInnerSingleNe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField TensorProduct GroundTheory.Heights₂.Heights

noncomputable section

def IsOrthogonalFamily {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K) {X : Type*}
    (L : X → Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (σ : K →+* ℂ) (x y : X), x ≠ y → ∀ l ∈ L x, ∀ l' ∈ L y,
    (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l') = 0

def S6.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (X : Type) [Fintype X]
    [DecidableEq X] (L : X → Submodule (𝓞 K) E.carrier) (μ : ℝ),
    DirectSum.IsInternal L → (∀ x, E.rank (L x) = 1) → IsOrthogonalFamily E L →
    (∀ x, μ ≤ E.normDegree (L x)) →
    ∀ (E' E'' : HermitianBundle.{0} K), HermitianExtension E' E E'' →
      (E''.rank ⊤ : ℝ) * μ ≤ E''.normDegree ⊤

def coordLines (K : Type*) [Field K] : Fin 2 → Submodule (𝓞 K) (Fin 2 → 𝓞 K) :=
  fun x => LinearMap.range (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x)

theorem coordLines_isInternal (K : Type*) [Field K] : DirectSum.IsInternal (coordLines K) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)]
    rw [disjoint_iff_inf_le]
    rintro v ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    simp at h0 h1
    ext i; fin_cases i <;> simp [h0.symm]
  · exact LinearMap.iSup_range_single _ _

theorem coordLines_rank (K : Type*) [Field K] [NumberField K] (x : Fin 2) :
    (HermitianBundle.standard K 2).rank (coordLines K x) = 1 := by
  change Module.finrank (𝓞 K) (LinearMap.range (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x)) = 1
  have hinj : Function.Injective (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x) := by
    intro a b h; simpa using congrFun h x
  rw [← (LinearEquiv.ofInjective _ hinj).finrank_eq, Module.finrank_self]

theorem standard_inner_single_ne (K : Type*) [Field K] [NumberField K] (σ : K →+* ℂ)
    (x y : Fin 2) (hxy : x ≠ y) (a b : 𝓞 K) :
    ((HermitianMetric.standard K (Fin 2)).form σ).inner
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (Pi.single x a : Fin 2 → 𝓞 K))
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (Pi.single y b : Fin 2 → 𝓞 K)) = 0 := by
  rw [HermitianMetric.standard_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [standardCoord_tmul, standardCoord_tmul]
  by_cases hi : i = x
  · subst hi
    simp [hxy]
  · simp [Pi.single_apply, hi]

theorem coordLines_orthogonal (K : Type*) [Field K] [NumberField K] :
    IsOrthogonalFamily (HermitianBundle.standard K 2) (coordLines K) := by
  intro σ x y hxy l hl l' hl'
  obtain ⟨a, rfl⟩ := hl
  obtain ⟨b, rfl⟩ := hl'
  exact standard_inner_single_ne K σ x y hxy a b

theorem S6.hypotheses_inhabited :
    DirectSum.IsInternal (coordLines ℚ) ∧
      (∀ x, (HermitianBundle.standard ℚ 2).rank (coordLines ℚ x) = 1) ∧
      IsOrthogonalFamily (HermitianBundle.standard ℚ 2) (coordLines ℚ) ∧
      (∀ x, min ((HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ 0))
          ((HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ 1)) ≤
        (HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ x)) ∧
      Nonempty (HermitianExtension (HermitianBundle.integers ℚ) (HermitianBundle.standard ℚ 2)
        (HermitianBundle.integers ℚ)) := by
  refine ⟨coordLines_isInternal ℚ, coordLines_rank ℚ, coordLines_orthogonal ℚ, fun x => ?_,
    ⟨HermitianExtension.standardSplit ℚ⟩⟩
  fin_cases x
  · exact min_le_left _ _
  · exact min_le_right _ _

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartCutoffEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def chartCutoff {D : ℕ} (k : ℕ) (y : Fin D → ℂ) : ℝ :=
  Real.smoothTransition (2 - (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2)

def ChartCutoffEnergy.Statement : Prop :=
  ∀ (n : ℕ) (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ), (∀ i, (T i).PosDef) →
    ∃ K : ℝ, ∀ k : ℕ,
      ∫ y : Fin (n + 1) → ℂ,
        ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ K

example (D k : ℕ) : chartCutoff k (0 : Fin D → ℂ) = 1 := by
  simp only [chartCutoff, Pi.zero_apply, norm_zero]
  exact Real.smoothTransition.one_of_one_le (by norm_num)

example : chartCutoff 0 (fun _ : Fin 1 => (2 : ℂ)) = 0 := by
  simp only [chartCutoff, Finset.univ_unique, Finset.sum_singleton, Complex.norm_ofNat]
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)

example : ∀ i : Fin 1, ((fun _ => Matrix.diagonal ![(1 : ℂ), 4, 1]) i :
    Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef :=
  fun _ => Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartDensityIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartDensityIntegrable.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    Integrable (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y)

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num

example : (!![(2 : ℂ), 1; 1, 2] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef := by
  have h : (!![(2 : ℂ), 1; 1, 2] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) =
      (!![(1 : ℂ), 1; 0, 0])ᴴ * !![(1 : ℂ), 1; 0, 0] + 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  rw [h]
  exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self _) Matrix.PosDef.one

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def chartMixedEnergy {e : ℕ} (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : ℕ) : ℝ :=
  ∫ y : Fin e → ℂ, (hermChartPot M y - hermChartPot N y) *
    maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y

def ChartEnergy.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef →
    ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M N k =
      1 / 2 * (Real.log M.det.re - Real.log N.det.re) *
        chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) ≠ 1 :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one, fun h => by
    have h1 := congrFun (congrFun h 0) 0
    simp at h1⟩

example (M N : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) :
    chartMixedEnergy M N 0 = ∫ y : Fin 0 → ℂ, (hermChartPot M y - hermChartPot N y) *
      maDensity (fun _ : Fin 0 => hermChartPot N) y := by
  simp [chartMixedEnergy]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartHessCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder

noncomputable section

def ChartHessCompare.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef →
    ∃ C : ℝ, ∀ y : Fin e → ℂ, (cxHessian (hermChartPot M) y).PosDef ∧
      ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one⟩

end

end GroundTheory.Heights₂.Heights
end


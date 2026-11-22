import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendAeLinearOfLocalSqBoundDense
section
open MeasureTheory

namespace GlobalTheory

theorem lintegral_enorm_sq_Lp {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (f : Lp E 2 ν) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖f‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm

theorem eLpNorm_two_le_of_lintegral {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (g : Q → E) (B : ℝ) (hB : 0 ≤ B)
    (h : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B ^ 2)) :
    eLpNorm g 2 ν ≤ ENNReal.ofReal B := by
  have e := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := ν) (p := 2) (by norm_num)
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at e
  rw [← e, ENNReal.ofReal_pow hB] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem extend_ae_linear_of_local_sq : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : Submodule ℂ H), Dense (D : Set H) → ∀ F : H → X → E,
    (∀ u ∈ D, ∀ u' ∈ D, F (u + u') =ᵐ[μ] fun x => F u x + F u' x) →
    (∀ (b : ℂ), ∀ u ∈ D, F (b • u) =ᵐ[μ] fun x => b • F u x) →
    (∀ n, ∃ C : ℝ, ∀ u ∈ D, AEStronglyMeasurable (F u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖F u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    ∃ T : H → X → E, (∀ u ∈ D, T u = F u) ∧
      (∀ u u' : H, T (u + u') =ᵐ[μ] fun x => T u x + T u' x) ∧
      (∀ (b : ℂ) (u : H), T (b • u) =ᵐ[μ] fun x => b • T u x) ∧
      (∀ n, ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (T u) (μ.restrict (K n)) ∧
        ∫⁻ x in K n, (‖T u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) := by
  intro X _ μ K hK hcov H _ _ E _ _ _ D hD F hadd hsmul hbd
  classical
  choose C hC using hbd
  set w : ℕ → ℝ := fun n => (2:ℝ)⁻¹ ^ n / (1 + max (C n) 0) with hw
  have hwpos : ∀ n, 0 < w n := fun n =>
    div_pos (pow_pos (by norm_num) n) (by have := le_max_right (C n) 0; linarith)
  have hw0 : ∀ n, ENNReal.ofReal (w n) ≠ 0 := fun n => by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hwpos n
  set ν : Measure X := Measure.sum (fun n => ENNReal.ofReal (w n) • μ.restrict (K n)) with hν
  have hint : ∀ f : X → ENNReal,
      ∫⁻ x, f x ∂ν = ∑' n, ENNReal.ofReal (w n) * ∫⁻ x in K n, f x ∂μ := by
    intro f
    rw [hν, lintegral_sum_measure]
    congr 1; funext n
    rw [lintegral_smul_measure, smul_eq_mul]
  have hνμ : ν ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [hν, Measure.sum_apply _ hs]
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      measure_mono_null Set.inter_subset_left h0, mul_zero]
  have hμν : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [hν, Measure.sum_apply _ hs, ENNReal.tsum_eq_zero] at h0
    have h1 : ∀ n, μ (s ∩ K n) = 0 := fun n => by
      have := h0 n
      rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (hw0 n)
    have : s = ⋃ n, s ∩ K n := by rw [← Set.inter_iUnion, hcov, Set.inter_univ]
    rw [this]; exact measure_iUnion_null h1
  have hsq : ∀ u ∈ D, ∫⁻ x, ‖F u x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal ((Real.sqrt 2 * ‖u‖) ^ 2) := by
    intro u hu
    rw [hint]
    have hB : (Real.sqrt 2 * ‖u‖) ^ 2 = ∑' n : ℕ, (2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2 := by
      rw [tsum_mul_right, tsum_geometric_inv_two, mul_pow, Real.sq_sqrt (by norm_num)]
    rw [hB, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)]
    refine ENNReal.tsum_le_tsum fun n => ?_
    have h2 : ∫⁻ x in K n, ‖F u x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C n * ‖u‖ ^ 2) := (hC n u hu).2
    have hM : 0 ≤ max (C n) 0 := le_max_right _ _
    calc ENNReal.ofReal (w n) * ∫⁻ x in K n, ‖F u x‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal (w n) * ENNReal.ofReal (max (C n) 0 * ‖u‖ ^ 2) := by
          gcongr
          exact h2.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
      _ = ENNReal.ofReal (w n * (max (C n) 0 * ‖u‖ ^ 2)) := (ENNReal.ofReal_mul (hwpos n).le).symm
      _ ≤ ENNReal.ofReal ((2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hw]
          simp only
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹) n) (sq_nonneg ‖u‖)]
  have hae : ∀ u ∈ D, AEStronglyMeasurable (F u) ν := fun u hu =>
    aestronglyMeasurable_sum_measure_iff.2 fun n => (hC n u hu).1.smul_measure _
  have hmem : ∀ u ∈ D, MemLp (F u) 2 ν := fun u hu =>
    ⟨hae u hu, (eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u hu)).trans_lt
      ENNReal.ofReal_lt_top⟩
  let L : D →ₗ[ℂ] Lp E 2 ν :=
    { toFun := fun u => (hmem u u.2).toLp (F u)
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hνμ.ae_le (hadd u u.2 v v.2))
      map_smul' := fun b u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hνμ.ae_le (hsmul b u u.2)) }
  have hL : ∀ u (hu : u ∈ D), L ⟨u, hu⟩ = (hmem u hu).toLp (F u) := fun _ _ => rfl
  have hLb : ∃ c, ∀ u : D, ‖L u‖ ≤ c * ‖D.subtype u‖ := by
    refine ⟨Real.sqrt 2, fun u => ?_⟩
    rw [show L u = (hmem u u.2).toLp (F u) from rfl, Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u u.2))
  have hdense : DenseRange D.subtype := hD.denseRange_val
  set Ext : H →L[ℂ] Lp E 2 ν := L.extendOfNorm D.subtype with hExtdef
  have hExt : ∀ u (hu : u ∈ D), Ext u = (hmem u hu).toLp (F u) := fun u hu => by
    rw [← hL u hu]
    exact LinearMap.extendOfNorm_eq hdense hLb ⟨u, hu⟩
  let T : H → X → E := fun u => if u ∈ D then F u else ⇑(Ext u)
  have hTae : ∀ u, T u =ᵐ[ν] Ext u := by
    intro u
    by_cases hu : u ∈ D
    · simp only [T, if_pos hu]
      rw [hExt u hu]
      exact (MemLp.coeFn_toLp _).symm
    · simp only [T, if_neg hu]
      rfl
  have hres : ∀ n, μ.restrict (K n) ≪ ν := fun n =>
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hμν
  refine ⟨T, fun u hu => if_pos hu, fun u u' => ?_, fun b u => ?_, fun n => ?_⟩
  · refine hμν.ae_le ?_
    filter_upwards [hTae (u + u'), hTae u, hTae u', Lp.coeFn_add (Ext u) (Ext u')]
      with x h1 h2 h3 h4
    rw [h1, map_add, h4, Pi.add_apply, ← h2, ← h3]
  · refine hμν.ae_le ?_
    filter_upwards [hTae (b • u), hTae u, Lp.coeFn_smul b (Ext u)] with x h1 h2 h4
    rw [h1, map_smul, h4, Pi.smul_apply, ← h2]
  · refine ⟨‖Ext‖ ^ 2 / w n, fun u => ⟨?_, ?_⟩⟩
    · exact ((Lp.aestronglyMeasurable (Ext u)).congr (hTae u).symm).mono_ac (hres n)
    · have e1 : ∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ = ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ :=
        lintegral_congr_ae ((hres n).ae_le ((hTae u).mono fun x hx => by simp only [hx]))
      have e2 : ENNReal.ofReal (w n) * ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ
          ≤ ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2) := by
        calc _ ≤ ∑' m, ENNReal.ofReal (w m) * ∫⁻ x in K m, ‖Ext u x‖ₑ ^ 2 ∂μ :=
              ENNReal.le_tsum (f := fun m => ENNReal.ofReal (w m) * ∫⁻ x in K m, ‖Ext u x‖ₑ ^ 2 ∂μ) n
          _ = ∫⁻ x, ‖Ext u x‖ₑ ^ 2 ∂ν := (hint _).symm
          _ = ENNReal.ofReal (‖Ext u‖ ^ 2) := lintegral_enorm_sq_Lp ν _
          _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            rw [← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (Ext.le_opNorm u) 2
      have hd : ENNReal.ofReal (‖Ext‖ ^ 2 / w n * ‖u‖ ^ 2)
          = ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2) / ENNReal.ofReal (w n) := by
        rw [← ENNReal.ofReal_div_of_pos (hwpos n)]
        congr 1; ring
      change ∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ ≤ _
      rw [e1, hd, ENNReal.le_div_iff_mul_le (Or.inl (hw0 n)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact e2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodEqProdMulFinprodIte
section
namespace GlobalTheory.FinprodProdMulIte

open Classical in

theorem finprod_eq_prod_mul_finprod_ite {ι : Type} (S₁ : Finset ι) (f g : ι → ℂ)
    (hf : (Function.mulSupport f).Finite) (hfg : ∀ p, p ∉ S₁ → f p = g p) :
    ∏ᶠ p, f p = (∏ p ∈ S₁, f p) * ∏ᶠ p, (if p ∈ S₁ then (1 : ℂ) else g p) := by
  have hsub₁ : Function.mulSupport (fun p => if p ∈ S₁ then f p else (1 : ℂ)) ⊆ (S₁ : Set ι) := by
    intro p hp
    by_contra h
    have h' : p ∉ S₁ := h
    exact hp (by simp [h'])
  have hsub₂ : Function.mulSupport (fun p => if p ∈ S₁ then (1 : ℂ) else g p)
      ⊆ Function.mulSupport f := by
    intro p hp
    by_cases h : p ∈ S₁
    · exact absurd (by simp [h]) hp
    · intro h1
      exact hp (by simp [h, ← hfg p h, h1])
  have h₁ : ∏ᶠ p, (if p ∈ S₁ then f p else (1 : ℂ)) = ∏ p ∈ S₁, f p := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub₁]
    exact Finset.prod_congr rfl fun p hp => by simp [hp]
  rw [← h₁, ← finprod_mul_distrib (S₁.finite_toSet.subset hsub₁) (hf.subset hsub₂)]
  refine finprod_congr fun p => ?_
  by_cases h : p ∈ S₁
  · simp [h]
  · simp [h, hfg p h]

end GlobalTheory.FinprodProdMulIte
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
section
open NumberField

namespace GlobalTheory

open NumberField in

theorem _root_.GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ↔ differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  rw [← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact (dvd_differentIdeal_iff (P := M)).1 (Ideal.dvd_iff_le.2 hle) (h ⟨M, hM.isPrime⟩)
  · intro h P
    show Algebra.IsUnramifiedAt _ P.asIdeal
    rw [← not_dvd_differentIdeal_iff, h, Ideal.dvd_iff_le, top_le_iff]
    exact P.isPrime.ne_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapThresholdPaysFarTerms
section
open Matrix Finset Real

namespace GlobalTheory

private theorem log_le_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h1 : Real.log (Real.sqrt x / 2) ≤ Real.sqrt x / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (Real.sqrt x / 2) = Real.log (Real.sqrt x) - Real.log 2 :=
    Real.log_div hs.ne' (by norm_num)
  have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← hx2]
    rw [Real.log_pow]
    push_cast
    ring
  have h4 := Real.log_two_lt_d9
  linarith

set_option maxHeartbeats 800000 in

theorem gap_threshold_pays_far_terms : ∀ (Cg : ℝ) (n f q : ℕ) (rd g b : ℝ) (h t : ℝ), 0 ≤ Cg → 3 ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ g → g ≤ b ^ Cg → 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h → ((n : ℝ) * f * rd * g * b)⁻¹ ^ (11 * q) ≤ t → t ≤ 1 / 2 → let ep : ℝ := 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2); 64 * (n : ℝ) ^ 2 ≤ h * ep ∧ 1 ≤ h * ep ^ 2 / 16 ∧ (3 * Real.sqrt n / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-(h * ep ^ 2 / 16))) ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := by
  intro Cg n f q rd g b h t hCg hn hf hq hqn hrd hlogf hb hg1 hgb hh ht1 _ht2 ep
  have hep : ep = 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) := rfl
  clear_value ep
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hqnR : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hf0 : (f : ℝ) ≠ 0 := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hfpos : (0 : ℝ) < f := by linarith
  set s := Real.sqrt (n : ℝ) with hs_def
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith)
  have hsn : s ≤ n := by nlinarith
  have hqs : (q : ℝ) ≤ s := (Real.le_sqrt (by positivity) (by linarith)).2 hqnR
  set ℓ := Real.log (b * rd) with hℓ_def
  have hbrd : 2 ≤ b * rd := le_trans hb (le_mul_of_one_le_right (by linarith) hrd)
  have hℓ : 0.69 ≤ ℓ := by
    have e1 := Real.log_le_log (by norm_num) hbrd
    have e2 := Real.log_two_gt_d9
    linarith
  have hlogb : Real.log b ≤ ℓ := Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith) hrd)
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hKl : 2.76 ≤ (Cg + 4) * ℓ := by nlinarith [mul_nonneg hCg (by linarith : (0 : ℝ) ≤ ℓ)]

  have hX : 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ ≤ h * ep ^ 2 / 16 := by
    have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep ^ 2 / 16
        = 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ := by
      rw [hep]
      field_simp
      norm_num
    rw [← e]
    have := mul_le_mul_of_nonneg_right hh (sq_nonneg ep)
    linarith
  have hn3f : 1 ≤ (n : ℝ) ^ 3 * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hfR
  refine ⟨?_, ?_, ?_⟩
  · have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep
        = 800000000 * ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) := by
      rw [hep]
      field_simp
      norm_num
    have hep0 : 0 ≤ ep := by rw [hep]; positivity
    have h1 := mul_le_mul_of_nonneg_right hh hep0
    have hn11 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hf3 : (1 : ℝ) ≤ (f : ℝ) ^ 3 := one_le_pow₀ hfR
    have hP : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 * f ^ 3 :=
      le_trans hn11 (le_mul_of_one_le_right (by positivity) hf3)
    have h2 : 2.76 * (n : ℝ) ^ 2 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) :=
      mul_le_mul hKl hP (by positivity) (by linarith)
    have hz : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    linarith
  · have h2 : 2.76 * 1 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 3 * f) :=
      mul_le_mul hKl hn3f (by norm_num) (by linarith)
    linarith
  · set X := h * ep ^ 2 / 16 with hX_def
    set M := (n : ℝ) * f * rd * g * b with hM_def
    have hgpos : 0 < g := by linarith
    have hMpos : 0 < M := by
      have : (0 : ℝ) < rd := by linarith
      have : (0 : ℝ) < b := by linarith
      positivity
    set Lb := s + s + Cg * ℓ + ℓ with hLb_def
    have hLb0 : 0 ≤ Lb := by
      have : 0 ≤ Cg * ℓ := mul_nonneg hCg (by linarith)
      linarith

    have hnexp : (n : ℝ) ≤ Real.exp s := by
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 (log_le_sqrt_of_one_le _ (by linarith))
    have hfexp : (f : ℝ) ≤ Real.exp s := by
      calc (f : ℝ) = Real.exp (Real.log f) := (Real.exp_log hfpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 hlogf
    have hgexp : g ≤ Real.exp (Cg * ℓ) := by
      calc g ≤ b ^ Cg := hgb
        _ = Real.exp (Real.log b * Cg) := Real.rpow_def_of_pos (by linarith) Cg
        _ ≤ Real.exp (Cg * ℓ) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_right hlogb hCg
          linarith
    have hbrdexp : b * rd = Real.exp ℓ := (Real.exp_log (by linarith)).symm
    have hMle : M ≤ Real.exp Lb := by
      have e1 : M = (n : ℝ) * f * g * (b * rd) := by rw [hM_def]; ring
      have e2 : Real.exp Lb = Real.exp s * Real.exp s * Real.exp (Cg * ℓ) * Real.exp ℓ := by
        rw [hLb_def, Real.exp_add, Real.exp_add, Real.exp_add]
      rw [e1, e2, hbrdexp]
      have a1 : (n : ℝ) * f ≤ Real.exp s * Real.exp s :=
        mul_le_mul hnexp hfexp (by positivity) (by positivity)
      have a2 : (n : ℝ) * f * g ≤ Real.exp s * Real.exp s * Real.exp (Cg * ℓ) :=
        mul_le_mul a1 hgexp (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right a2 (by positivity)

    have htpos : 0 < t := lt_of_lt_of_le (pow_pos (inv_pos.2 hMpos) _) ht1
    have hinvt : t⁻¹ ≤ Real.exp (11 * s * Lb) := by
      rw [inv_pow] at ht1
      have a1 : t⁻¹ ≤ M ^ (11 * q) := inv_le_of_inv_le₀ (pow_pos hMpos _) ht1
      have a2 : M ^ (11 * q) ≤ Real.exp Lb ^ (11 * q) := pow_le_pow_left₀ hMpos.le hMle _
      have a3 : Real.exp Lb ^ (11 * q) = Real.exp (((11 * q : ℕ) : ℝ) * Lb) :=
        (Real.exp_nat_mul Lb (11 * q)).symm
      have a4 : ((11 * q : ℕ) : ℝ) * Lb ≤ 11 * s * Lb := by
        push_cast
        have : 11 * (q : ℝ) ≤ 11 * s := by linarith
        exact mul_le_mul_of_nonneg_right this hLb0
      calc t⁻¹ ≤ M ^ (11 * q) := a1
        _ ≤ Real.exp Lb ^ (11 * q) := a2
        _ = Real.exp (((11 * q : ℕ) : ℝ) * Lb) := a3
        _ ≤ Real.exp (11 * s * Lb) := Real.exp_le_exp.2 a4

    have hA : 3 * s / t ^ 2 ≤ Real.exp (2 + s + 22 * s * Lb) := by
      have e1 : 3 * s / t ^ 2 = 3 * s * (t⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
      have e2 : Real.exp (2 + s + 22 * s * Lb)
          = Real.exp 2 * Real.exp s * (Real.exp (11 * s * Lb)) ^ 2 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [e1, e2]
      have b1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp 2
        linarith
      have b2 : s ≤ Real.exp s := by
        have := Real.add_one_le_exp s
        linarith
      have b3 : (t⁻¹) ^ 2 ≤ (Real.exp (11 * s * Lb)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinvt 2
      have b4 : 3 * s ≤ Real.exp 2 * Real.exp s :=
        mul_le_mul b1 b2 (by linarith) (by positivity)
      exact mul_le_mul b4 b3 (by positivity) (by positivity)
    have hpow : (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) hA _

    have hsmall : 2 * (f : ℝ) * 3 ^ f ≤ Real.exp (4 * f) := by
      have c1 : 2 * (f : ℝ) ≤ Real.exp (2 * f) := by
        have := Real.add_one_le_exp (2 * (f : ℝ))
        linarith
      have c2 : (3 : ℝ) ^ f ≤ Real.exp (f * 2) := by
        rw [Real.exp_nat_mul]
        have : (3 : ℝ) ≤ Real.exp 2 := by
          have := Real.add_one_le_exp 2
          linarith
        exact pow_le_pow_left₀ (by norm_num) this f
      have e : Real.exp (4 * f) = Real.exp (2 * f) * Real.exp (f * 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      exact mul_le_mul c1 c2 (by positivity) (by positivity)

    have hexp : ((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)
        ≤ -((n : ℝ) ^ 2 * f) := by
      push_cast
      have hP0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f := by positivity
      have hKl0 : 0 ≤ (Cg + 1) * ℓ := mul_nonneg (by linarith) (by linarith)
      have k1 : (n : ℝ) ^ 2 * f * s * ((Cg + 1) * ℓ) ≤ (n : ℝ) ^ 2 * f * n * ((Cg + 1) * ℓ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsn hP0) hKl0
      have k2 : (n : ℝ) ^ 2 * f * s ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hsn hP0
      have k3 : (f : ℝ) ≤ (n : ℝ) ^ 2 * f :=
        le_mul_of_one_le_left hfpos.le (one_le_pow₀ (by linarith))
      have k4 : (n : ℝ) ^ 2 * f * 3 ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hnR hP0
      have k5 : (n : ℝ) ^ 2 * f * n * 107 ≤ (n : ℝ) ^ 2 * f * n * (156 * ℓ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have k6 : 0 ≤ (n : ℝ) ^ 2 * f * n * (Cg * ℓ) :=
        mul_nonneg (by positivity) (mul_nonneg hCg (by linarith))
      have k7 : (n : ℝ) ^ 2 * f * s ^ 2 = (n : ℝ) ^ 2 * f * n := by rw [hs2]
      have k8 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f * n := by positivity
      rw [hLb_def]
      linarith
    calc (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-X))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb))
            * (Real.exp (4 * f) * Real.exp (-X)) := by
          apply mul_le_mul hpow (mul_le_mul_of_nonneg_right hsmall (by positivity))
            (by positivity) (by positivity)
      _ = Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := Real.exp_le_exp.2 hexp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Imports
section
namespace GlobalTheory.TargetStatementBis

open NumberField

theorem main {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V)
    (h : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h₁⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) c
    refine ⟨d * b, mul_ne_zero hd (nonZeroDivisors.ne_zero b.2), ?_⟩
    have key : ((b : 𝓞 K)) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : 𝓞 K) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_smul, key, smul_comm d a x]
    exact Λ.smul_mem a h₁

theorem target : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V] (Λ : Submodule (NumberField.RingOfIntegers K) V), Submodule.span K (↑Λ : Set V) = ⊤ → ∀ (v : V), ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ Λ :=
  fun Λ h v => main Λ h v

end GlobalTheory.TargetStatementBis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBis
section
namespace GlobalTheory.QuotientCardinality

open ValuativeRel

theorem main : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {ϖ : ↥(Valuation.integer (ValuativeRel.valuation F))}, Irreducible ϖ → ∀ {a : ℤ} {m : ℕ} {u v : (↥(Valuation.integer (ValuativeRel.valuation F)))ˣ}, (↑ϖ : F) ^ a * (↑(↑u : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) * (↑(↑v : ↥(Valuation.integer (ValuativeRel.valuation F))) : F) = (↑ϖ : F) ^ m → a = (↑m : ℤ) := by
  intro F _ _ _ _ ϖ hϖ a m u v h
  have hint := Valuation.integer.integers (ValuativeRel.valuation F)
  have hu : ValuativeRel.valuation F ((u : (ValuativeRel.valuation F).integer) : F) = 1 :=
    hint.one_of_isUnit u.isUnit
  have hv : ValuativeRel.valuation F ((v : (ValuativeRel.valuation F).integer) : F) = 1 :=
    hint.one_of_isUnit v.isUnit
  have hne : (ϖ : F) ≠ 0 := by
    intro h0
    exact hϖ.ne_zero (Subtype.ext (by simpa using h0))
  have hpos : 0 < ValuativeRel.valuation F (ϖ : F) := by
    rw [pos_iff_ne_zero]
    exact (map_ne_zero (ValuativeRel.valuation F)).mpr hne
  have hne1 : ValuativeRel.valuation F (ϖ : F) ≠ 1 := by
    intro h1
    exact hϖ.not_isUnit ((hint.isUnit_iff_valuation_eq_one (x := ϖ)).mpr h1)
  have h2 := congrArg (ValuativeRel.valuation F) h
  rw [map_mul, map_mul, hu, hv, mul_one, mul_one, map_zpow₀, map_pow, ← zpow_natCast] at h2
  exact zpow_right_injective₀ hpos hne1 h2

end GlobalTheory.QuotientCardinality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixExtLast
section
namespace GlobalTheory.MatrixExtLast

theorem matrix_ext_last {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h₁ : ∀ i j : Fin k, M (Fin.castSucc i) (Fin.castSucc j) = N (Fin.castSucc i) (Fin.castSucc j))
    (h₂ : ∀ i : Fin k, M (Fin.castSucc i) (Fin.last k) = N (Fin.castSucc i) (Fin.last k))
    (h₃ : ∀ j : Fin k, M (Fin.last k) (Fin.castSucc j) = N (Fin.last k) (Fin.castSucc j))
    (h₄ : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h₄
    | cast j => exact h₃ j
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact h₂ i
    | cast j => exact h₁ i j

end GlobalTheory.MatrixExtLast
end


import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0002

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkaMeasKabRight
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

section Alg

variable {G : Type*} [Group G] {Γ : Subgroup G} {φ : G → ℂ}

theorem rrka_Kab_symm (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x y : G) : rrk_Kab Γ φ y x = rrk_Kab Γ φ x y := by
  unfold rrk_Kab
  rw [← (Equiv.inv Γ).tsum_eq (fun γ : Γ => ‖φ (y⁻¹ * (γ : G) * x)‖ₑ)]
  refine tsum_congr fun γ => ?_
  show ‖φ (y⁻¹ * ((γ⁻¹ : Γ) : G) * x)‖ₑ = _
  have e : y⁻¹ * ((γ⁻¹ : Γ) : G) * x = (x⁻¹ * (γ : G) * y)⁻¹ := by simp [mul_assoc]
  rw [e, hsa, enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]

theorem rrka_K_symm (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x y : G) : rrk_K Γ φ y x = star (rrk_K Γ φ x y) := by
  unfold rrk_K
  rw [tsum_star, ← (Equiv.inv Γ).tsum_eq (fun γ : Γ => φ (y⁻¹ * (γ : G) * x))]
  refine tsum_congr fun γ => ?_
  show φ (y⁻¹ * ((γ⁻¹ : Γ) : G) * x) = _
  have e : y⁻¹ * ((γ⁻¹ : Γ) : G) * x = (x⁻¹ * (γ : G) * y)⁻¹ := by simp [mul_assoc]
  rw [e, hsa]

theorem rrka_Kab_smul (δ : Γ) (x y : G) : rrk_Kab Γ φ ((δ : G) * y) x = rrk_Kab Γ φ y x := by
  unfold rrk_Kab
  rw [← (Equiv.mulLeft δ).tsum_eq (fun γ : Γ => ‖φ (((δ : G) * y)⁻¹ * (γ : G) * x)‖ₑ)]
  refine tsum_congr fun γ => ?_
  show ‖φ (((δ : G) * y)⁻¹ * ((δ * γ : Γ) : G) * x)‖ₑ = _
  have e : ((δ : G) * y)⁻¹ * ((δ * γ : Γ) : G) * x = y⁻¹ * (γ : G) * x := by simp [mul_assoc]
  rw [e]

theorem rrka_K_smul (δ : Γ) (x y : G) : rrk_K Γ φ ((δ : G) * y) x = rrk_K Γ φ y x := by
  unfold rrk_K
  rw [← (Equiv.mulLeft δ).tsum_eq (fun γ : Γ => φ (((δ : G) * y)⁻¹ * (γ : G) * x))]
  refine tsum_congr fun γ => ?_
  show φ (((δ : G) * y)⁻¹ * ((δ * γ : Γ) : G) * x) = _
  have e : ((δ : G) * y)⁻¹ * ((δ * γ : Γ) : G) * x = y⁻¹ * (γ : G) * x := by simp [mul_assoc]
  rw [e]

end Alg

section Meas

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}

theorem rrka_meas_Kab_right (hφm : Measurable φ) (x : G) : Measurable fun y => rrk_Kab Γ φ x y :=
  Measurable.tsum fun γ => (hφm.comp (measurable_const_mul (x⁻¹ * (γ : G)))).enorm

theorem rrka_lint [μ.IsMulLeftInvariant] (h : rr_FD μ Γ D) (hφm : Measurable φ) (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x : G) :
    ∫⁻ y, ‖φ (x⁻¹ * y)‖ₑ * rrk_Kab Γ φ y x ∂μ = ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ := by
  rw [(rr_isFD h).lintegral_eq_tsum'']
  have e : ∀ δ : Γ, ∫⁻ y in D, ‖φ (x⁻¹ * (δ • y))‖ₑ * rrk_Kab Γ φ (δ • y) x ∂μ =
      ∫⁻ y in D, ‖φ (x⁻¹ * (δ : G) * y)‖ₑ * rrk_Kab Γ φ x y ∂μ := by
    intro δ
    refine lintegral_congr fun y => ?_
    rw [Subgroup.smul_def, smul_eq_mul, rrka_Kab_smul, rrka_Kab_symm hsa, ← mul_assoc]
  rw [tsum_congr e, ← lintegral_tsum (μ := μ.restrict D)
    (f := fun (δ : Γ) y => ‖φ (x⁻¹ * (δ : G) * y)‖ₑ * rrk_Kab Γ φ x y) (fun δ =>
    ((hφm.comp (measurable_const_mul (x⁻¹ * (δ : G)))).enorm.mul (rrka_meas_Kab_right hφm x)).aemeasurable)]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.tsum_mul_right, sq]
  rfl

theorem rrka_summable_of {ι : Type*} {f : ι → ℂ} (hf : ∑' i, ‖f i‖ₑ ≠ ∞) : Summable f :=
  Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 hf)

theorem rrk_idem [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (h : rr_FD μ Γ D) (hφm : Measurable φ)
    (hsa : ∀ z, φ z⁻¹ = star (φ z)) (hid : ∀ z, ∫ g, φ g * φ (g⁻¹ * z) ∂μ = φ z) (x : G)
    (hx : ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) :
    Summable (fun γ : Γ => φ (x⁻¹ * (γ : G) * x)) ∧
      rrk_K Γ φ x x = ((∫ y in D, ‖rrk_K Γ φ x y‖ ^ 2 ∂μ : ℝ) : ℂ) ∧
      MemLp (fun y => rrk_K Γ φ x y) 2 (μ.restrict D) := by
  set ψ : Γ → G → ℂ := fun γ y => φ (x⁻¹ * y) * φ (y⁻¹ * (γ : G) * x) with hψ
  have hψm : ∀ γ, Measurable (ψ γ) := fun γ =>
    (hφm.comp (measurable_const_mul _)).mul (hφm.comp ((measurable_inv.mul_const _).mul_const _))
  have hψint : ∀ γ : Γ, ∫ y, ψ γ y ∂μ = φ (x⁻¹ * (γ : G) * x) := by
    intro γ
    rw [← hid (x⁻¹ * (γ : G) * x),
      ← integral_mul_left_eq_self (fun g => φ g * φ (g⁻¹ * (x⁻¹ * (γ : G) * x))) x⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e : (x⁻¹ * y)⁻¹ * (x⁻¹ * (γ : G) * x) = y⁻¹ * (γ : G) * x := by simp [mul_assoc]
    simp only [hψ, e]
  have hpt : ∀ y, ∑' γ : Γ, ‖ψ γ y‖ₑ = ‖φ (x⁻¹ * y)‖ₑ * rrk_Kab Γ φ y x := by
    intro y
    simp only [hψ, enorm_mul]
    rw [ENNReal.tsum_mul_left]
    rfl
  have hsum : ∑' γ : Γ, ∫⁻ y, ‖ψ γ y‖ₑ ∂μ = ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ := by
    rw [← rrka_lint h hφm hsa x, ← lintegral_tsum (fun γ => (hψm γ).enorm.aemeasurable)]
    exact lintegral_congr hpt
  have hfin : ∑' γ : Γ, ∫⁻ y, ‖ψ γ y‖ₑ ∂μ ≠ ∞ := by rw [hsum]; exact hx
  have hS : Summable (fun γ : Γ => φ (x⁻¹ * (γ : G) * x)) := by
    refine rrka_summable_of (ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun γ => ?_))
    rw [← hψint γ]
    exact enorm_integral_le_lintegral_enorm _
  set Ψ : G → ℂ := fun y => φ (x⁻¹ * y) * rrk_K Γ φ y x with hΨ
  have hΨeq : Ψ = fun y => ∑' γ : Γ, ψ γ y := by
    funext y
    simp only [hΨ, hψ]
    rw [tsum_mul_left]
    rfl
  have hfin2 : ∫⁻ y, ∑' γ : Γ, ‖ψ γ y‖ₑ ∂μ ≠ ∞ := by
    rw [lintegral_tsum (fun γ => (hψm γ).enorm.aemeasurable)]; exact hfin
  have hae : ∀ᵐ y ∂μ, Summable fun γ : Γ => ψ γ y := by
    filter_upwards [ae_lt_top (Measurable.tsum fun γ => (hψm γ).enorm) hfin2] with y hy
    exact rrka_summable_of hy.ne
  have hΨm : AEStronglyMeasurable Ψ μ := by
    rw [hΨeq]; exact rrk_aesm_tsum (fun γ => (hψm γ).aestronglyMeasurable) hae
  have hΨfin : ∫⁻ y, ‖Ψ y‖ₑ ∂μ < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) (lt_top_iff_ne_top.2 hfin2)
    rw [hΨeq]
    exact enorm_tsum_le_tsum_enorm
  have hΨint : Integrable Ψ μ := ⟨hΨm, hasFiniteIntegral_iff_enorm.2 hΨfin⟩
  have e1 : rrk_K Γ φ x x = ∫ y, Ψ y ∂μ := by
    calc rrk_K Γ φ x x = ∑' γ : Γ, ∫ y, ψ γ y ∂μ := tsum_congr fun γ => (hψint γ).symm
      _ = ∫ y, ∑' γ : Γ, ψ γ y ∂μ := (integral_tsum (fun γ => (hψm γ).aestronglyMeasurable) hfin).symm
      _ = ∫ y, Ψ y ∂μ := by rw [hΨeq]
  have e2 := (rr_isFD h).integral_eq_tsum'' Ψ hΨint
  have e3 : ∑' δ : Γ, ∫ y in D, Ψ (δ • y) ∂μ = ∫ y in D, ∑' δ : Γ, Ψ (δ • y) ∂μ := by
    refine (integral_tsum (μ := μ.restrict D) (f := fun (δ : Γ) y => Ψ (δ • y)) (fun δ => ?_) ?_).symm
    · exact (hΨm.comp_measurePreserving (measurePreserving_smul δ μ)).restrict
    · rw [← (rr_isFD h).lintegral_eq_tsum'' (fun y => ‖Ψ y‖ₑ)]
      exact hΨfin.ne
  have e4 : ∀ y, ∑' δ : Γ, Ψ (δ • y) = ((‖rrk_K Γ φ x y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    have a : ∀ δ : Γ, Ψ (δ • y) = φ (x⁻¹ * (δ : G) * y) * rrk_K Γ φ y x := by
      intro δ
      simp only [hΨ]
      rw [Subgroup.smul_def, smul_eq_mul, rrka_K_smul, ← mul_assoc]
    rw [tsum_congr a, tsum_mul_right, rrka_K_symm hsa x y]
    show rrk_K Γ φ x y * star (rrk_K Γ φ x y) = _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have haeD : ∀ᵐ y ∂μ.restrict D, rrk_Kab Γ φ x y < ∞ := by
    filter_upwards [ae_lt_top ((rrka_meas_Kab_right (Γ := Γ) hφm x).pow_const 2) hx] with y hy
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at hy
    simp at hy
  have hKm : AEStronglyMeasurable (fun y => rrk_K Γ φ x y) (μ.restrict D) := by
    refine rrk_aesm_tsum (fun γ => (hφm.comp (measurable_const_mul _)).aestronglyMeasurable) ?_
    filter_upwards [haeD] with y hy
    exact rrka_summable_of hy.ne
  refine ⟨hS, ?_, hKm, ?_⟩
  · rw [e1, e2, e3, ← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall e4)
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) (lt_top_iff_ne_top.2 hx)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    gcongr
    exact enorm_tsum_le_tsum_enorm

end Meas

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

theorem rrkb_mul_le (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem rrkb_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  rcases le_total a 1 with h | h
  · exact le_trans h le_self_add
  · calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ 1 + a ^ 2 := le_add_self

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μ] in
theorem rrkb_sq_fin (f : Lp ℂ 2 (μ.restrict D)) : ∫⁻ y in D, ‖(f : G → ℂ) y‖ₑ ^ 2 ∂μ ≠ ∞ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero ENNReal.ofNat_ne_top
    (Lp.eLpNorm_lt_top f)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact h.ne

theorem rrkb_lint (h : rr_FD μ Γ D) {r : G → G} (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G)
    {F : G → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x in D, F (r (x * g)) ∂μ = ∫⁻ x in D, F x ∂μ := by
  obtain ⟨h1, h2⟩ := rr_map h g
  calc ∫⁻ x in D, F (r (x * g)) ∂μ = ∫⁻ x in D, F (rr_rep (Γ : Set G) D (x * g)) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr g)] with x hx
        rw [hx]
    _ = ∫⁻ y, F y ∂(Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)) :=
        (lintegral_map' hF.aemeasurable h1).symm
    _ = ∫⁻ x in D, F x ∂μ := by rw [h2]

theorem rrkb_r_fix (h : rr_FD μ Γ D) {r : G → G} (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) :
    ∀ᵐ y ∂μ.restrict D, ∀ γ : Γ, r ((γ : G) * y) = y := by
  classical
  have hnull : ∀ δ : Γ, (δ : G) ≠ 1 →
      μ ((fun y => (δ : G) * y) ⁻¹' ((fun y => (δ : G) * y) '' D ∩ D)) = 0 := by
    intro δ hδ
    rw [measure_preimage_mul]
    exact h.3 δ δ.2 hδ
  have hB : μ (⋃ δ : Γ, ⋃ (_ : (δ : G) ≠ 1),
      (fun y => (δ : G) * y) ⁻¹' ((fun y => (δ : G) * y) '' D ∩ D)) = 0 :=
    measure_iUnion_null (fun δ => measure_iUnion_null (fun hδ => hnull δ hδ))
  rw [ae_restrict_iff' h.1, ae_iff]
  refine measure_mono_null ?_ hB
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push_neg at hy
  obtain ⟨hyD, γ, hγ⟩ := hy
  obtain ⟨γ', hγ'Γ, hr1, hmem⟩ := hr ((γ : G) * y)
  have hδ : ((⟨γ' * γ, Γ.mul_mem hγ'Γ γ.2⟩ : Γ) : G) ≠ 1 := by
    intro h1
    apply hγ
    rw [hr1, ← mul_assoc]
    exact (congrArg (· * y) h1).trans (one_mul y)
  simp only [Set.mem_iUnion]
  refine ⟨⟨γ' * γ, Γ.mul_mem hγ'Γ γ.2⟩, hδ, ?_⟩
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_image]
  refine ⟨⟨y, hyD, rfl⟩, ?_⟩
  show γ' * γ * y ∈ D
  rw [mul_assoc]
  exact hmem

theorem rrkb_step2 (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ) {r : G → G} (hrm : Measurable r)
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (f : Lp ℂ 2 (μ.restrict D)) (x : G)
    (hx : ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) :
    ∫ g, φ g * (f : G → ℂ) (r (x * g)) ∂μ = ∫ y in D, rrk_K Γ φ x y * (f : G → ℂ) y ∂μ := by
  set f0 : G → ℂ := (f : G → ℂ) with hf0
  have hf0m : StronglyMeasurable f0 := Lp.stronglyMeasurable f
  set ψ : G → ℂ := fun y => φ (x⁻¹ * y) * f0 (r y) with hψ
  have hψm : StronglyMeasurable ψ :=
    ((hφm.comp (measurable_const_mul _)).stronglyMeasurable).mul (hf0m.comp_measurable hrm)
  have e1 : ∫ g, φ g * f0 (r (x * g)) ∂μ = ∫ y, ψ y ∂μ := by
    rw [← integral_mul_left_eq_self ψ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [hψ]
  have hfd := rr_isFD h
  have hfix := rrkb_r_fix h hr
  have hγm : ∀ γ : Γ, StronglyMeasurable fun y => ψ (γ • y) := fun γ =>
    hψm.comp_measurable (measurable_const_smul γ)
  have hsum : ∑' γ : Γ, ∫⁻ y in D, ‖ψ (γ • y)‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_tsum (fun γ => (hγm γ).enorm.aemeasurable)]
    have e2 : ∫⁻ y in D, ∑' γ : Γ, ‖ψ (γ • y)‖ₑ ∂μ = ∫⁻ y in D, rrk_Kab Γ φ x y * ‖f0 y‖ₑ ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hfix] with y hy
      rw [rrk_Kab, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      simp only [hψ, Subgroup.smul_def, smul_eq_mul, enorm_mul, hy γ, mul_assoc]
    rw [e2]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun y => rrkb_mul_le _ _)
    rw [lintegral_add_right _ (hf0m.enorm.pow_const 2)]
    exact ENNReal.add_ne_top.2 ⟨hx, rrkb_sq_fin f⟩
  have hψi : Integrable ψ μ := ⟨hψm.aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_enorm, hfd.lintegral_eq_tsum'']
    exact lt_top_iff_ne_top.2 hsum⟩
  rw [e1, hfd.integral_eq_tsum'' ψ hψi, ← integral_tsum (fun γ => (hγm γ).aestronglyMeasurable) hsum]
  refine integral_congr_ae ?_
  filter_upwards [hfix] with y hy
  rw [rrk_K, ← tsum_mul_right]
  refine tsum_congr fun γ => ?_
  simp only [hψ, Subgroup.smul_def, smul_eq_mul, hy γ, mul_assoc]

theorem rrkb_step1 (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ) {r : G → G} (hrm : Measurable r)
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D)) (hφ : Integrable φ μ)
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, R g v⟫_ℂ ∂μ) (f : Lp ℂ 2 (μ.restrict D)) :
    ((T f : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D] fun x => ∫ g, φ g * (f : G → ℂ) (r (x * g)) ∂μ := by
  set f0 : G → ℂ := (f : G → ℂ) with hf0
  have hf0m : StronglyMeasurable f0 := Lp.stronglyMeasurable f
  set Φ : G × G → ℂ := fun p => φ p.1 * f0 (r (p.2 * p.1)) with hΦ
  have hΦm : StronglyMeasurable Φ :=
    ((hφm.comp measurable_fst).stronglyMeasurable).mul
      (hf0m.comp_measurable (hrm.comp (measurable_snd.mul measurable_fst)))
  have hInt : ∀ s, MeasurableSet s → (μ.restrict D) s < ∞ →
      Integrable Φ (μ.prod ((μ.restrict D).restrict s)) := by
    intro s hs hfin
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hΦm.enorm.aemeasurable]
    set C : ℝ≥0∞ := (μ.restrict D) s + ∫⁻ y in D, ‖f0 y‖ₑ ^ 2 ∂μ with hC
    have hCfin : C ≠ ∞ := ENNReal.add_ne_top.2 ⟨hfin.ne, rrkb_sq_fin f⟩
    have hb : ∀ g, ∫⁻ x, ‖Φ (g, x)‖ₑ ∂((μ.restrict D).restrict s) ≤ ‖φ g‖ₑ * C := by
      intro g
      have hm1 : Measurable fun x => ‖f0 (r (x * g))‖ₑ :=
        (hf0m.comp_measurable (hrm.comp (measurable_mul_const g))).enorm
      simp only [hΦ, enorm_mul]
      rw [lintegral_const_mul _ hm1]
      refine mul_le_mul' le_rfl ?_
      calc ∫⁻ x, ‖f0 (r (x * g))‖ₑ ∂((μ.restrict D).restrict s)
          ≤ ∫⁻ x, (1 + ‖f0 (r (x * g))‖ₑ ^ 2) ∂((μ.restrict D).restrict s) :=
            lintegral_mono fun x => rrkb_le_one_add_sq _
        _ = (μ.restrict D) s + ∫⁻ x, ‖f0 (r (x * g))‖ₑ ^ 2 ∂((μ.restrict D).restrict s) := by
            rw [lintegral_add_left measurable_const, lintegral_one, Measure.restrict_apply_univ]
        _ ≤ (μ.restrict D) s + ∫⁻ x in D, ‖f0 (r (x * g))‖ₑ ^ 2 ∂μ :=
            add_le_add le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)
        _ = C := by rw [rrkb_lint h hr g (F := fun y => ‖f0 y‖ₑ ^ 2) (hf0m.enorm.pow_const 2)]
    calc ∫⁻ g, ∫⁻ x, ‖Φ (g, x)‖ₑ ∂((μ.restrict D).restrict s) ∂μ ≤ ∫⁻ g, ‖φ g‖ₑ * C ∂μ := lintegral_mono hb
      _ = (∫⁻ g, ‖φ g‖ₑ ∂μ) * C := lintegral_mul_const _ hφm.enorm
      _ < ∞ := ENNReal.mul_lt_top hφ.2 (lt_top_iff_ne_top.2 hCfin)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s hs hfin
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hfin.ne
  · intro s hs hfin
    exact (hInt s hs hfin).integral_prod_right
  · intro s hs hfin
    rw [← L2.inner_indicatorConstLp_one (𝕜 := ℂ) hs hfin.ne (T f), hT]
    have e : ∀ g, ⟪indicatorConstLp 2 hs hfin.ne (1 : ℂ), R g f⟫_ℂ =
        ∫ x in s, f0 (r (x * g)) ∂(μ.restrict D) := by
      intro g
      rw [L2.inner_indicatorConstLp_one]
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hR g f, ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr g)] with x a1 a2
      rw [a1, a2]
    simp only [e]
    have hsw := integral_integral_swap (f := fun g x => φ g * f0 (r (x * g))) (μ := μ)
      (ν := (μ.restrict D).restrict s) (hInt s hs hfin)
    rw [← hsw]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact (integral_const_mul _ _).symm

theorem rrk_unfold (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D)) (hφ : Integrable φ μ)
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, R g v⟫_ℂ ∂μ)
    (hK : ∀ᵐ x ∂μ.restrict D, ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) (f : Lp ℂ 2 (μ.restrict D)) :
    ∀ᵐ x ∂μ.restrict D, ((T f : Lp ℂ 2 (μ.restrict D)) : G → ℂ) x =
      ∫ y in D, rrk_K Γ φ x y * (f : G → ℂ) y ∂μ := by
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep h
  filter_upwards [rrkb_step1 h hφm hrm hr hR T hφ hT f, hK] with x a1 a2
  rw [a1]
  exact rrkb_step2 h hφm hrm hr f x a2

end Formalism.MainNotions.LeviCoordinates

end
end


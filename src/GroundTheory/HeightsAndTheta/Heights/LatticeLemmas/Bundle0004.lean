import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PPointwiseLelong

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSpherePhase
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory Real

noncomputable section

theorem phaseLaw_map_arg_exp_mul {c : ℂ} (hc : c ≠ 0) :
    phaseLaw.map (fun θ : ℝ ↦ Complex.arg (Complex.exp (θ * Complex.I) * c)) = phaseLaw := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  have hI : Set.Ioc (-π) (-π + 2 * π) = Set.Ioc (-π) π := by ring_nf
  have h1 := AddCircle.measurePreserving_mk (2 * π) (-π)
  rw [hI] at h1
  have h2 := measurePreserving_add_right (volume : Measure (AddCircle (2 * π)))
    ((Complex.arg c : ℝ) : AddCircle (2 * π))
  have h3 := AddCircle.measurePreserving_equivIoc (T := 2 * π) (a := -π)
  have h4 : MeasurePreserving (Subtype.val : Set.Ioc (-π) (-π + 2 * π) → ℝ)
      (Measure.comap Subtype.val volume) (volume.restrict (Set.Ioc (-π) π)) :=
    ⟨measurable_subtype_coe, by rw [map_comap_subtype_coe measurableSet_Ioc, hI]⟩
  have hcomp := h4.comp (h3.comp (h2.comp h1))
  have hfun : (fun θ : ℝ ↦ Complex.arg (Complex.exp (θ * Complex.I) * c)) =
      Subtype.val ∘ (AddCircle.equivIoc (2 * π) (-π)) ∘
        (fun x ↦ x + ((Complex.arg c : ℝ) : AddCircle (2 * π))) ∘
        ((↑) : ℝ → AddCircle (2 * π)) := by
    funext θ
    have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have he : Complex.exp (θ * Complex.I) * c =
        (‖c‖ : ℂ) * Complex.exp (((θ + Complex.arg c : ℝ) : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c]
      rw [mul_left_comm, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, he,
      Complex.arg_real_mul _ hc', Complex.arg_exp]
    simp only [Complex.mul_I_im, Complex.ofReal_re]
    rw [← AddCircle.coe_add]
    rfl
  rw [hfun]
  have hmeas : Measurable (Subtype.val ∘ (AddCircle.equivIoc (2 * π) (-π)) ∘
        (fun x ↦ x + ((Complex.arg c : ℝ) : AddCircle (2 * π))) ∘
        ((↑) : ℝ → AddCircle (2 * π))) := hcomp.measurable
  rw [phaseLaw, ProbabilityTheory.cond, Measure.map_smul, hcomp.map_eq]

theorem SpherePhase.proof (h1 : SphereLawBasic.Statement) (h2 : SphereLawUnitary.Statement) :
    SpherePhase.Statement := by
  intro N p hp hN
  have hμ : IsProbabilityMeasure (sphereLaw N) := (h1 N (by omega)).1
  have hph : IsProbabilityMeasure phaseLaw := PointwiseLelong.isProbabilityMeasure_phaseLaw
  have hA : Continuous (coordAlong p) := PointwiseLelong.continuous_coordAlong p
  have hG : Measurable fun z ↦ (‖coordAlong p z‖, orthoDir p z) :=
    (continuous_norm.comp hA).measurable.prodMk (PointwiseLelong.measurable_orthoDir p)

  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := coordAlong p
      map_add' := fun x y ↦ by simp [coordAlong, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x ↦ by simp [coordAlong, Finset.mul_sum, mul_assoc] }
  have hL : ∀ z, L z = coordAlong p z := fun _ ↦ rfl
  have hpp : coordAlong p p = 1 := by
    have : ∀ j, p j * star (p j) = ((‖p j‖ ^ 2 : ℝ) : ℂ) := fun j ↦ by
      rw [Complex.star_def, Complex.mul_conj']; push_cast; ring
    simp only [coordAlong, this]
    rw [← Complex.ofReal_sum, hp]; simp

  have key : ∀ (x : ℂ) (w : Fin N → ℂ), coordAlong p w = 0 →
      ∑ j, ‖x * p j + w j‖ ^ 2 = ‖x‖ ^ 2 + ∑ j, ‖w j‖ ^ 2 := by
    intro x w hw
    have hp' : ∑ j, Complex.normSq (p j) = 1 := by simpa [Complex.sq_norm] using hp
    have hcross : ∑ j, (x * p j * (starRingEnd ℂ) (w j)).re = 0 := by
      rw [← Complex.re_sum]
      have : ∑ j, x * p j * (starRingEnd ℂ) (w j) = x * (starRingEnd ℂ) (coordAlong p w) := by
        simp [coordAlong, map_sum, Finset.mul_sum, mul_comm, mul_assoc]
      rw [this, hw]; simp
    simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, hp', ← Finset.mul_sum, hcross]
    ring

  let R : ℝ → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun θ ↦
    LinearMap.id + ((Complex.exp (θ * Complex.I) - 1) • L).smulRight p
  have hR : ∀ θ z, R θ z = z + ((Complex.exp (θ * Complex.I) - 1) * coordAlong p z) • p :=
    fun θ z ↦ rfl
  have hRa : ∀ θ z, coordAlong p (R θ z) = Complex.exp (θ * Complex.I) * coordAlong p z := by
    intro θ z
    rw [← hL, hR, map_add, map_smul, smul_eq_mul, hL, hL, hpp]
    ring
  have hRw : ∀ θ z, R θ z - coordAlong p (R θ z) • p = z - coordAlong p z • p := by
    intro θ z
    rw [hRa, hR]
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hRo : ∀ θ z, orthoDir p (R θ z) = orthoDir p z := by
    intro θ z
    rw [orthoDir, orthoDir, hRw]
  have hRn : ∀ θ v, ∑ j, ‖R θ v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
    intro θ v
    have hw0 : coordAlong p (v - coordAlong p v • p) = 0 := by
      rw [← hL, map_sub, map_smul, smul_eq_mul, hL, hL, hpp]
      ring
    have s1 : ∑ j, ‖R θ v j‖ ^ 2 = ∑ j,
        ‖(Complex.exp (θ * Complex.I) * coordAlong p v) * p j + (v - coordAlong p v • p) j‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ ↦ by
        rw [hR]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring_nf
    have s2 : ∑ j, ‖v j‖ ^ 2 = ∑ j, ‖coordAlong p v * p j + (v - coordAlong p v • p) j‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ ↦ by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring_nf
    rw [s1, s2, key _ _ hw0, key _ _ hw0, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinv : ∀ θ : ℝ, (sphereLaw N).map (R θ) = sphereLaw N := fun θ ↦ h2 N (R θ) (hRn θ)

  have hne : ∀ᵐ z ∂sphereLaw N, coordAlong p z ≠ 0 := by
    have hker : LinearMap.ker L ≠ ⊤ := by
      intro h
      have hp0 : p ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, hL, hpp] at hp0
      exact one_ne_zero hp0
    have h0 := (h1 N (by omega)).2.2 _ hker
    rw [ae_iff]
    have hset : {z | ¬coordAlong p z ≠ 0} = (LinearMap.ker L : Set (Fin N → ℂ)) := by
      ext z
      simp only [ne_eq, not_not, Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, hL]
    rw [hset, h0]

  have hF : Measurable fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z)) :=
    (Complex.measurable_arg.comp hA.measurable).prodMk hG
  let Φ : ℝ × (Fin N → ℂ) → ℝ × (ℝ × (Fin N → ℂ)) := fun q ↦
    (Complex.arg (Complex.exp (q.1 * Complex.I) * coordAlong p q.2),
      (‖coordAlong p q.2‖, orthoDir p q.2))
  have hΦ : Measurable Φ := by
    refine (Complex.measurable_arg.comp ?_).prodMk (hG.comp measurable_snd)
    exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_fst).mul
      continuous_const)).mul (hA.comp continuous_snd)).measurable
  ext S hS
  have hstep : ∀ θ : ℝ, (sphereLaw N)
      ((fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) =
      ∫⁻ z, S.indicator 1 (Φ (θ, z)) ∂sphereLaw N := by
    intro θ
    conv_lhs => rw [← hinv θ]
    rw [Measure.map_apply (LinearMap.continuous_of_finiteDimensional (R θ)).measurable (hF hS)]
    have hpre : (R θ) ⁻¹' ((fun z ↦ (Complex.arg (coordAlong p z),
        (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) = (fun z ↦ Φ (θ, z)) ⁻¹' S := by
      ext z
      simp only [Set.mem_preimage, Φ, hRa, hRo, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [hpre, ← lintegral_indicator_one (hS.preimage (hΦ.comp measurable_prodMk_left) :
      MeasurableSet ((fun z ↦ Φ (θ, z)) ⁻¹' S))]
    rfl
  rw [Measure.map_apply hF hS, Measure.prod_apply_symm hS]
  calc _ = ∫⁻ θ, (sphereLaw N)
          ((fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S)
          ∂phaseLaw := by rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ θ, ∫⁻ z, S.indicator 1 (Φ (θ, z)) ∂sphereLaw N ∂phaseLaw :=
        lintegral_congr fun θ ↦ hstep θ
    _ = ∫⁻ z, ∫⁻ θ, S.indicator 1 (Φ (θ, z)) ∂phaseLaw ∂sphereLaw N :=
        lintegral_lintegral_swap ((measurable_one.indicator hS).comp hΦ).aemeasurable
    _ = ∫⁻ z, phaseLaw ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) ∂sphereLaw N := by
        refine lintegral_congr_ae (hne.mono fun z hz ↦ ?_)
        have hg : Measurable fun θ : ℝ ↦
            Complex.arg (Complex.exp (θ * Complex.I) * coordAlong p z) :=
          Complex.measurable_arg.comp ((Complex.continuous_exp.comp
            (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const).measurable
        show ∫⁻ θ, S.indicator 1 (Φ (θ, z)) ∂phaseLaw =
          phaseLaw ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S)
        rw [← lintegral_indicator_one (hS.preimage measurable_prodMk_right :
          MeasurableSet ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S))]
        conv_rhs => rw [← phaseLaw_map_arg_exp_mul hz]
        rw [lintegral_map ((measurable_one.indicator (hS.preimage measurable_prodMk_right))) hg]
        rfl
    _ = ∫⁻ y, phaseLaw ((fun x ↦ (x, y)) ⁻¹' S)
          ∂(sphereLaw N).map fun z ↦ (‖coordAlong p z‖, orthoDir p z) :=
        (lintegral_map (measurable_measure_prodMk_right hS) hG).symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereProjectionLaw
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereProjectionLaw

variable {n : ℕ}

theorem ofReal_norm_sq (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * star x := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem ofReal_sum_norm_sq (v : Fin n → ℂ) :
    ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) = ∑ j, v j * star (v j) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ ↦ ofReal_norm_sq (v j)

theorem coordAlong_smul (p w : Fin n → ℂ) (c : ℂ) :
    coordAlong p (c • w) = c * coordAlong p w := by
  simp [coordAlong, Finset.mul_sum, mul_assoc]

theorem coordAlong_sub (p z w : Fin n → ℂ) :
    coordAlong p (z - w) = coordAlong p z - coordAlong p w := by
  simp [coordAlong, sub_mul, Finset.sum_sub_distrib]

theorem coordAlong_self {p : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1) : coordAlong p p = 1 := by
  rw [coordAlong, ← ofReal_sum_norm_sq, hp, Complex.ofReal_one]

theorem std_norm (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]

theorem sum_norm_sq_smul (c : ℂ) (w : Fin n → ℂ) :
    ∑ j, ‖(c • w) j‖ ^ 2 = ‖c‖ ^ 2 * ∑ j, ‖w j‖ ^ 2 := by
  simp [mul_pow, Finset.mul_sum]

theorem sum_norm_sq_sub {p z : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hz : ∑ j, ‖z j‖ ^ 2 = 1) :
    ∑ j, ‖(z - coordAlong p z • p) j‖ ^ 2 = 1 - ‖coordAlong p z‖ ^ 2 := by
  apply Complex.ofReal_injective
  set a := coordAlong p z with ha
  have hzp : ∑ j, p j * star (z j) = star a := by
    simp [ha, coordAlong, star_sum, mul_comm]
  have hpp : ∑ j, p j * star (p j) = 1 := by rw [← ofReal_sum_norm_sq, hp, Complex.ofReal_one]
  have hzz : ∑ j, z j * star (z j) = 1 := by rw [← ofReal_sum_norm_sq, hz, Complex.ofReal_one]
  have key : ∀ j, (z - a • p) j * star ((z - a • p) j) =
      z j * star (z j) - star a * (z j * star (p j)) - a * (p j * star (z j)) +
        a * star a * (p j * star (p j)) := by
    intro j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub, star_mul']
    ring
  rw [ofReal_sum_norm_sq, Finset.sum_congr rfl fun j _ ↦ key j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hzp, hpp, hzz, ← coordAlong, ← ha, Complex.ofReal_sub, Complex.ofReal_one,
    ofReal_norm_sq]
  ring

theorem exists_unitary_first {m : ℕ} (p : Fin (m + 1) → ℂ) (hp : ∑ j, ‖p j‖ ^ 2 = 1) :
    ∃ U : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ),
      (∀ v, ∑ j, ‖U v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2) ∧ ∀ v, U v 0 = coordAlong p v := by
  let p' : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 p
  have hp' : ‖p'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [p', hp]
  have hon : Orthonormal ℂ (({0} : Set (Fin (m + 1))).domRestrict fun _ ↦ p') := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl,
      show (({0} : Set (Fin (m + 1))).domRestrict fun _ ↦ p') j = p' from rfl,
      inner_self_eq_norm_sq_to_K, hp']
    simp
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = p' := hb 0 (Set.mem_singleton 0)
  let Ulin : (Fin (m + 1) → ℂ) ≃ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)).symm ≪≫ₗ b.repr.toLinearEquiv ≪≫ₗ
      WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)
  have hUapp : ∀ v, Ulin v = (b.repr (WithLp.toLp 2 v)).ofLp := fun v ↦ rfl
  refine ⟨Ulin.toLinearMap, fun v ↦ ?_, fun v ↦ ?_⟩
  · have h := b.repr.norm_map (WithLp.toLp 2 v)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at h2
    simpa [hUapp] using h2
  · rw [LinearEquiv.coe_coe, hUapp, OrthonormalBasis.repr_apply_apply, hb0, PiLp.inner_apply]
    simp [p', RCLike.inner_apply, coordAlong]

theorem span_singleton_ne_top {N : ℕ} (hN : 2 ≤ N) (p : Fin N → ℂ) :
    Submodule.span ℂ {p} ≠ ⊤ := by
  intro h
  have h1 := finrank_span_le_card (R := ℂ) ({p} : Set (Fin N → ℂ))
  rw [h, finrank_top, Module.finrank_fin_fun] at h1
  simp at h1
  omega

end SphereProjectionLaw

open SphereProjectionLaw in

theorem SphereProjectionLaw.proof (h1 : SphereLawBasic.Statement) (h2 : SphereLawUnitary.Statement)
    (h3 : SphereLawFirstCoord.Statement) (h4 : SpherePhase.Statement) :
    SphereProjectionLaw.Statement := by
  intro N p hp
  refine ⟨fun hN ↦ ?_, fun hN ↦ ⟨?_, h4 N p hp hN, ?_⟩⟩
  ·
    subst hN
    filter_upwards [(h1 1 le_rfl).2.1] with z hz
    simp only [Fin.sum_univ_one] at hz hp
    have hz1 : ‖z 0‖ = 1 := by nlinarith [norm_nonneg (z 0)]
    have hp1 : ‖p 0‖ = 1 := by nlinarith [norm_nonneg (p 0)]
    simp [coordAlong, hz1, hp1]
  ·
    have hnull := measure_eq_zero_iff_ae_notMem.mp
      ((h1 N (by omega)).2.2 _ (span_singleton_ne_top hN p))
    filter_upwards [(h1 N (by omega)).2.1, hnull] with z hz hzS
    set a := coordAlong p z with ha
    set w := z - a • p with hw
    have hw0 : w ≠ 0 := by
      intro h
      apply hzS
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨a, (sub_eq_zero.mp h).symm⟩
    have hsq : ∑ j, ‖w j‖ ^ 2 = 1 - ‖a‖ ^ 2 := sum_norm_sq_sub hp hz
    have hpos : 0 < ∑ j, ‖w j‖ ^ 2 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
      calc (0 : ℝ) < ‖w j‖ ^ 2 := by positivity
        _ ≤ ∑ j, ‖w j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j ↦ ‖w j‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
    set s := √(1 - ‖a‖ ^ 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr (hsq ▸ hpos)
    have hss : s ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt (hsq ▸ hpos.le)
    have hdir : orthoDir p z = ((s : ℂ))⁻¹ • w := by
      rw [orthoDir, std_norm, ← ha, ← hw, hsq]
    have hwp : coordAlong p w = 0 := by
      rw [hw, coordAlong_sub, coordAlong_smul, coordAlong_self hp, mul_one, sub_self]
    refine ⟨?_, ?_, ?_⟩
    · rw [hdir, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs0.ne'), one_smul, hw,
        add_sub_cancel]
    · rw [hdir, coordAlong_smul, hwp, mul_zero]
    · rw [hdir, std_norm, sum_norm_sq_smul, hsq, ← hss, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hs0.le, inv_pow, inv_mul_cancel₀ (pow_pos hs0 2).ne', Real.sqrt_one]
  ·
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    obtain ⟨U, hU, hU0⟩ := exists_unitary_first p hp
    have hf : (fun z ↦ ‖coordAlong p z‖ ^ 2) =
        (fun z : Fin (m + 1) → ℂ ↦ ‖z ⟨0, by omega⟩‖ ^ 2) ∘ U := by
      funext z
      simp [hU0]
    have hUm : Measurable U := U.continuous_of_finiteDimensional.measurable
    have hgm : Measurable fun z : Fin (m + 1) → ℂ ↦ ‖z ⟨0, by omega⟩‖ ^ 2 :=
      ((continuous_apply _).norm.pow 2).measurable
    rw [hf, ← Measure.map_map hgm hUm, h2 _ U hU, h3 _ hN]

end

end GroundTheory.Heights₂.Heights
end


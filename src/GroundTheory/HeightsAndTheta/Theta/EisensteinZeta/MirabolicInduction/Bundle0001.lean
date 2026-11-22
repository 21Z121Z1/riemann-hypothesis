import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements

-- bundled from GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmClassReducedParamsNonemptyPf
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors

theorem image_mul_span_pair (u a b : ℂ) :
    (fun z => u * z) '' (Submodule.span ℤ ({a, b} : Set ℂ) : Set ℂ) =
      (Submodule.span ℤ ({u * a, u * b} : Set ℂ) : Set ℂ) := by
  have h := Submodule.map_span (LinearMap.mulLeft ℤ u) ({a, b} : Set ℂ)
  rw [Set.image_pair] at h
  simp only [LinearMap.mulLeft_apply] at h
  rw [← h, Submodule.map_coe]
  rfl

theorem image_mul_latticeOf (u τ : ℂ) :
    (fun z => u * z) '' latticeOf τ = (Submodule.span ℤ ({u, u * τ} : Set ℂ) : Set ℂ) := by
  rw [latticeOf, image_mul_span_pair, mul_one]

theorem latticeOf_neg (t : ℂ) : latticeOf (-t) = latticeOf t := by
  unfold latticeOf
  congr 1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · have : -(-x) ∈ Submodule.span ℤ ({1, -x} : Set ℂ) :=
        Submodule.neg_mem _ (Submodule.subset_span (by simp))
      simpa using this

theorem span_denom_num_eq (g : SL(2, ℤ)) (τ : ℂ) :
    Submodule.span ℤ ({(g 1 0 : ℂ) * τ + g 1 1, (g 0 0 : ℂ) * τ + g 0 1} : Set ℂ) =
      Submodule.span ℤ ({1, τ} : Set ℂ) := by
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  apply le_antisymm
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · exact Submodule.mem_span_pair.mpr ⟨g 1 1, g 1 0, by simp [zsmul_eq_mul]; ring⟩
    · exact Submodule.mem_span_pair.mpr ⟨g 0 1, g 0 0, by simp [zsmul_eq_mul]; ring⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · refine Submodule.mem_span_pair.mpr ⟨g 0 0, -g 1 0, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg]
      linear_combination hdet
    · refine Submodule.mem_span_pair.mpr ⟨-g 0 1, g 1 1, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg]
      linear_combination τ * hdet

theorem IsLatticeParam.smul {Λ : Set ℂ} {τ : ℍ} (h : IsLatticeParam Λ τ) (g : SL(2, ℤ)) :
    IsLatticeParam Λ (g • τ) := by
  obtain ⟨c, hc, hΛ⟩ := h
  set D : ℂ := (g 1 0 : ℂ) * τ + g 1 1 with hD
  have hD0 : D ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) τ
    simpa [UpperHalfPlane.denom, D] using this
  have hgτ : ((g • τ : ℍ) : ℂ) = ((g 0 0 : ℂ) * τ + g 0 1) / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [D]
  have key : (fun z => D * z) '' latticeOf ((g • τ : ℍ) : ℂ) = latticeOf (τ : ℂ) := by
    rw [image_mul_latticeOf, hgτ, mul_div_cancel₀ _ hD0, latticeOf, span_denom_num_eq]
  refine ⟨D⁻¹ * c, mul_ne_zero (inv_ne_zero hD0) hc, ?_⟩
  have : (fun z => D⁻¹ * c * z) '' Λ = (fun z => D⁻¹ * z) '' ((fun z => c * z) '' Λ) := by
    rw [Set.image_image]; simp [mul_assoc]
  rw [this, hΛ, ← key, Set.image_image]
  simp [inv_mul_cancel_left₀ hD0]

variable {K : Type*} [Field K] [NumberField K]

theorem im_div_ne_zero_of_basis (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    {ι : Type*} (b : Module.Basis ι ℚ K) (e : ι ≃ Fin 2) :
    (σ (b (e.symm 1)) / σ (b (e.symm 0))).im ≠ 0 := by
  set w : ℂ := (σ (b (e.symm 0)))⁻¹ with hw
  intro h0
  have hall : ∀ x : K, (σ x * w).im = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨j, rfl⟩ := e.symm.surjective i
      fin_cases j
      · simp only [Fin.zero_eta, w]
        rw [mul_inv_cancel₀]
        · simp
        · exact (map_ne_zero σ).mpr (b.ne_zero _)
      · simpa [div_eq_mul_inv, w] using h0
    | zero => simp
    | add y z _ _ hy hz => simp [add_mul, hy, hz]
    | smul q y _ hy =>
      rw [Rat.smul_def, map_mul, map_ratCast, mul_assoc]
      simp [hy]
  have hw0 : w ≠ 0 := inv_ne_zero ((map_ne_zero σ).mpr (b.ne_zero _))
  have hwim : w.im = 0 := by simpa using hall 1
  obtain ⟨x, hx⟩ := hσ
  apply hx
  have hxr : σ x = (σ x * w) * w⁻¹ := by field_simp
  have hwinv : (w⁻¹).im = 0 := by simp [Complex.inv_im, hwim]
  rw [hxr, Complex.mul_im, hall x, hwinv]
  ring

theorem exists_isLatticeParam_fractionalIdeal (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ τ : ℍ, IsLatticeParam (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) τ := by
  set b := basisOfFractionalIdeal K I
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ I) = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b]
  let e : Module.Free.ChooseBasisIndex ℤ I ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  set ω₀ := b (e.symm 0)
  set ω₁ := b (e.symm 1)
  have hrange : Set.range b = {ω₀, ω₁} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := e.symm.surjective i
      fin_cases j
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  have hI : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (Submodule.span ℤ ({ω₀, ω₁} : Set K) : Set K) := by
    rw [← hrange]
    ext x
    exact (mem_span_basisOfFractionalIdeal (K := K) (I := I)).symm
  have hσI : σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (Submodule.span ℤ ({σ ω₀, σ ω₁} : Set ℂ) : Set ℂ) := by
    rw [hI]
    have h := Submodule.map_span σ.toAddMonoidHom.toIntLinearMap ({ω₀, ω₁} : Set K)
    rw [Set.image_pair] at h
    have h' := congrArg (fun p : Submodule ℤ ℂ => (p : Set ℂ)) h
    simpa [Submodule.map_coe] using h'
  have h0 : σ ω₀ ≠ 0 := (map_ne_zero σ).mpr (b.ne_zero _)
  set t : ℂ := σ ω₁ / σ ω₀
  have ht : t.im ≠ 0 := im_div_ne_zero_of_basis σ hσ b e
  have himage : (fun z => (σ ω₀)⁻¹ * z) '' (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) =
      latticeOf t := by
    rw [hσI, image_mul_span_pair, inv_mul_cancel₀ h0, latticeOf, inv_mul_eq_div]
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · refine ⟨⟨-t, by simpa using hneg⟩, (σ ω₀)⁻¹, inv_ne_zero h0, ?_⟩
    show _ = latticeOf (-t)
    rw [latticeOf_neg, himage]
  · exact ⟨⟨t, hpos⟩, (σ ω₀)⁻¹, inv_ne_zero h0, himage⟩

theorem ClassReducedParamsNonempty.proof : ClassReducedParamsNonempty.Statement := by
  intro K _ _ h2 σ hσ A
  refine ClassGroup.induction (K := K) (fun I => ?_) A
  obtain ⟨τ, hτ⟩ := exists_isLatticeParam_fractionalIdeal h2 σ hσ I
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  exact ⟨g • τ, I, rfl, hg, hτ.smul g⟩

end GroundTheory.Heights₂.Theta
end
end

-- bundled from GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmEtaLogPeriodNegConjPf
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularForm Complex
open scoped Real

theorem qParam_neg_conj (h : ℝ) (z : ℂ) :
    Function.Periodic.qParam h (-(starRingEnd ℂ) z) =
      starRingEnd ℂ (Function.Periodic.qParam h z) := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem eta_negConj (τ : ℍ) : η (negConj τ : ℂ) = starRingEnd ℂ (η (τ : ℂ)) := by
  have hc : ((negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ) (τ : ℂ) := rfl
  have hq1 : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hm := (multipliable_one_sub_pow hq1).hasProd.map (starRingEnd ℂ) Complex.continuous_conj
  have hprod : ∏' n : ℕ, (1 - eta_q n ((negConj τ : ℍ) : ℂ)) =
      starRingEnd ℂ (∏' n : ℕ, (1 - eta_q n (τ : ℂ))) := by
    rw [← hm.tprod_eq]
    congr 1
    funext n
    simp [hc, eta_q, qParam_neg_conj]
  unfold ModularForm.eta
  rw [hprod, hc, qParam_neg_conj, map_mul]

theorem EtaLogPeriodNegConj.proof : EtaLogPeriodNegConj.Statement := by
  intro τ
  have him : (negConj τ).im = τ.im := by
    show (-(starRingEnd ℂ) (τ : ℂ)).im = (τ : ℂ).im
    simp
  unfold etaLogPeriod etaPeriod
  rw [him, eta_negConj, Complex.norm_conj]

example : 0 < etaPeriod (negConj UpperHalfPlane.I) := etaPeriod_pos _

end GroundTheory.Heights₂.Theta
end
end

-- bundled from GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmEtaPeriodLatticeClassPf
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups

namespace EtaPeriodLatticeClass

theorem discriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (γ • τ) = denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
  have h := congr_fun
    (SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ) τ
  rw [SL_slash_apply] at h
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  rw [← h, mul_comm (ModularForm.discriminant (γ • τ)), ← mul_assoc, ← zpow_add₀ hd]
  simp

theorem norm_eta_smul_pow_four (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4 = ‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4 := by
  have h := congr_arg norm (discriminant_smul γ τ)
  simp only [ModularForm.discriminant, norm_mul, norm_pow, norm_zpow] at h
  have h6 : (‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4) ^ 6 = (‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul]
    rw [show (4 : ℕ) * 6 = 24 from rfl, show (2 : ℕ) * 6 = 12 from rfl, h]
    norm_cast
  exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h6

theorem etaPeriod_smul (γ : SL(2, ℤ)) (τ : ℍ) : etaPeriod (γ • τ) = etaPeriod τ := by
  unfold etaPeriod
  rw [norm_eta_smul_pow_four, ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  have : ‖denom γ τ‖ ≠ 0 := norm_ne_zero_iff.mpr (denom_ne_zero γ τ)
  field_simp

theorem mem_latticeOf {τ z : ℂ} : z ∈ latticeOf τ ↔ ∃ m n : ℤ, z = m + n * τ := by
  unfold latticeOf
  rw [SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩

theorem coord_unique {τ : ℍ} {m n m' n' : ℤ}
    (h : (m : ℂ) + n * (τ : ℂ) = m' + n' * (τ : ℂ)) : m = m' ∧ n = n' := by
  have him := congr_arg Complex.im h
  have hre := congr_arg Complex.re h
  simp at him hre
  have hn : n = n' := by
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h τ.im_pos.ne'
  subst hn
  refine ⟨?_, rfl⟩
  exact_mod_cast (by linarith : (m : ℝ) = m')

theorem exists_SL_smul_eq {τ τ' : ℍ} {μ : ℂ} (hμ : μ ≠ 0)
    (h1 : ∀ z ∈ latticeOf (τ : ℂ), μ * z ∈ latticeOf (τ' : ℂ))
    (h2 : ∀ w ∈ latticeOf (τ' : ℂ), μ⁻¹ * w ∈ latticeOf (τ : ℂ)) :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by

  obtain ⟨d, c, hdc⟩ := mem_latticeOf.mp (h2 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨b, a, hba⟩ := mem_latticeOf.mp (h2 τ' (mem_latticeOf.mpr ⟨0, 1, by simp⟩))

  obtain ⟨h, g, hhg⟩ := mem_latticeOf.mp (h1 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨f, e, hfe⟩ := mem_latticeOf.mp (h1 τ (mem_latticeOf.mpr ⟨0, 1, by simp⟩))
  rw [mul_one] at hdc hhg

  have k1 : ((d * h + c * f : ℤ) : ℂ) + ((d * g + c * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination hinv - μ * hdc - (d : ℂ) * hhg - (c : ℂ) * hfe
  have k2 : ((b * h + a * f : ℤ) : ℂ) + ((b * g + a * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination (τ' : ℂ) * hinv - μ * hba - (b : ℂ) * hhg - (a : ℂ) * hfe
  obtain ⟨E4, E3⟩ := coord_unique k1
  obtain ⟨E2, E1⟩ := coord_unique k2
  have hdet1 : (a * d - b * c) * (e * h - f * g) = 1 := by
    linear_combination (c * f + d * h) * E1 + E4 - (c * e + d * g) * E2

  have hw : (c : ℂ) * τ + d ≠ 0 := by
    rw [add_comm, ← hdc]; exact inv_ne_zero hμ
  have hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / ((c : ℂ) * τ + d) := by
    rw [eq_div_iff hw, add_comm ((c : ℂ) * τ), ← hdc, add_comm ((a : ℂ) * τ), ← hba]
    field_simp

  have hdetpos : 0 < a * d - b * c := by
    have him := congr_arg Complex.im hτ'
    rw [Complex.div_im] at him
    have hN : 0 < Complex.normSq ((c : ℂ) * τ + d) := Complex.normSq_pos.mpr hw
    have key : (τ' : ℂ).im * Complex.normSq ((c : ℂ) * τ + d) = ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [him, sub_mul, div_mul_cancel₀ _ hN.ne', div_mul_cancel₀ _ hN.ne']
      simp
      ring
    have : (0 : ℝ) < ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [← key]; exact mul_pos τ'.im_pos hN
    have := (pos_of_mul_pos_left this τ.im_pos.le)
    exact_mod_cast this
  have hdet : a * d - b * c = 1 :=
    Int.eq_one_of_mul_eq_one_right hdetpos.le hdet1
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨γ, UpperHalfPlane.ext ?_⟩
  rw [coe_specialLinearGroup_apply, hτ']
  simp [γ]

theorem of_EtaPeriodModularInvariant (hinv : EtaPeriodModularInvariant.Statement) :
    EtaPeriodLatticeClass.Statement := by
  rintro Λ τ τ' ⟨c, hc, hΛ⟩ ⟨c', hc', hΛ'⟩
  have h1 : ∀ z ∈ latticeOf (τ : ℂ), c' / c * z ∈ latticeOf (τ' : ℂ) := by
    intro z hz
    rw [← hΛ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [← hΛ']
    exact ⟨x, hx, by field_simp⟩
  have h2 : ∀ w ∈ latticeOf (τ' : ℂ), (c' / c)⁻¹ * w ∈ latticeOf (τ : ℂ) := by
    intro w hw
    rw [← hΛ'] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [← hΛ]
    exact ⟨x, hx, by field_simp⟩
  obtain ⟨γ, hγ⟩ := exists_SL_smul_eq (div_ne_zero hc' hc) h1 h2
  rw [← hγ, hinv]

theorem proof : EtaPeriodLatticeClass.Statement :=
  of_EtaPeriodModularInvariant etaPeriod_smul

end EtaPeriodLatticeClass

example : etaPeriod (ModularGroup.T • UpperHalfPlane.I) = etaPeriod UpperHalfPlane.I :=
  EtaPeriodLatticeClass.etaPeriod_smul _ _

end GroundTheory.Heights₂.Theta
end
end


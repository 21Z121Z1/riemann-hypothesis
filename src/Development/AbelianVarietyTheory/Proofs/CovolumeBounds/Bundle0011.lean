import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0149

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LintegralHyperboloidFibration
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.ConePolar

theorem angle_shift (h : ℝ → ℝ≥0∞) (hp : Function.Periodic h (2 * Real.pi)) :
    ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, h θ = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), h θ := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have h1 := AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) hp.lift
  have h2 := AddCircle.lintegral_preimage (2 * Real.pi) 0 hp.lift
  simp only [Function.Periodic.lift_coe] at h1 h2
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [zero_add] at h2
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, h1, h2]

theorem radial (a : ℝ) (ha : 0 ≤ a) (F H : ℝ → ℝ≥0∞) :
    ∫⁻ ρ in Set.Ioi (Real.sqrt a), ENNReal.ofReal ρ * (F (ρ ^ 2 - a) * H ρ)
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * H (Real.sqrt (a + τ)) := by
  have himg : (fun ρ : ℝ => ρ ^ 2 - a) '' Set.Ioi (Real.sqrt a) = Set.Ioi 0 := by
    ext τ
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      have h0 := Real.sqrt_nonneg a
      have h1 := Real.sq_sqrt ha
      nlinarith
    · intro hτ
      refine ⟨Real.sqrt (a + τ), Real.sqrt_lt_sqrt ha (by linarith), ?_⟩
      rw [Real.sq_sqrt (by linarith)]; ring
  have hinj : Set.InjOn (fun ρ : ℝ => ρ ^ 2 - a) (Set.Ioi (Real.sqrt a)) := by
    intro x hx y hy hxy
    have h0 := Real.sqrt_nonneg a
    simp only [Set.mem_Ioi] at hx hy
    have : x ^ 2 = y ^ 2 := by simpa using hxy
    exact (pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).1 this
  have hder : ∀ x ∈ Set.Ioi (Real.sqrt a), HasDerivWithinAt (fun ρ : ℝ => ρ ^ 2 - a) (2 * x)
      (Set.Ioi (Real.sqrt a)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).sub_const a).hasDerivWithinAt (s := Set.Ioi (Real.sqrt a))
    simpa using this
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj,
    ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 ≤ x := (Real.sqrt_nonneg a).trans (le_of_lt hx)
  rw [show a + (x ^ 2 - a) = x ^ 2 by ring, Real.sqrt_sq hx0, abs_of_nonneg (by positivity),
    ENNReal.ofReal_mul (by norm_num), ← mul_assoc (1 / 2 : ℝ≥0∞), ← mul_assoc (1 / 2 : ℝ≥0∞)]
  have : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal 2 = 1 := by
    rw [ENNReal.ofReal_ofNat, one_div, ENNReal.inv_mul_cancel (by simp) (by simp)]
  rw [this, one_mul]

theorem plane (a : ℝ) (ha : 0 ≤ a) (F : ℝ → ℝ≥0∞) (g : ℂ → ℝ≥0∞) (hF : Measurable F) (hg : Measurable g) :
    ∫⁻ z : ℂ, Set.indicator {z : ℂ | a < Complex.normSq z} (fun z => F (Complex.normSq z - a) * g z) z
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((Real.sqrt (a + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ))) := by
  rw [← radial a ha F (fun ρ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))),
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (Complex.I * p.2) := by
    intro p
    rw [Complex.polarCoord_symm_apply, mul_comm Complex.I, Complex.exp_mul_I]
    simp
  have hn : ∀ ρ θ : ℝ, Complex.normSq ((ρ : ℂ) * Complex.exp (Complex.I * θ)) = ρ ^ 2 := by
    intro ρ θ
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hm : Measurable (Set.indicator {z : ℂ | a < Complex.normSq z}
      (fun z => F (Complex.normSq z - a) * g z)) := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.continuous_normSq.measurable)
    exact (hF.comp (Complex.continuous_normSq.measurable.sub_const a)).mul hg
  simp only [hsymm, smul_eq_mul]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  swap
  · refine Measurable.aemeasurable ?_
    refine (measurable_fst.ennreal_ofReal).mul (hm.comp ?_)
    fun_prop
  have hsub : Set.Ioi (Real.sqrt a) = Set.Ioi (Real.sqrt a) ∩ Set.Ioi (0 : ℝ) := by
    rw [Set.Ioi_inter_Ioi, max_eq_left (Real.sqrt_nonneg a)]
  rw [hsub, ← Measure.restrict_restrict measurableSet_Ioi,
    ← lintegral_indicator (s := Set.Ioi (Real.sqrt a)) measurableSet_Ioi]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ
  simp only [Set.indicator, Set.mem_setOf_eq, hn, Set.mem_Ioi, Real.sqrt_lt' hρ0]
  split_ifs with h
  · have hmg : Measurable fun θ : ℝ => g ((ρ : ℂ) * Complex.exp (Complex.I * θ)) :=
      hg.comp (by fun_prop)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hmg, angle_shift]
    intro θ
    simp only
    congr 2
    push_cast
    rw [mul_add, Complex.exp_add, mul_comm Complex.I (2 * _), Complex.exp_two_pi_mul_I, mul_one]
  · simp

theorem measurable_snoc (k : ℕ) :
    Measurable fun q : (Fin k → ℂ) × ℂ => (Fin.snoc (α := fun _ => ℂ) q.1 q.2 : Fin (k + 1) → ℂ) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simp only [Fin.snoc_castSucc]; fun_prop

theorem measurable_sqLen (k : ℕ) : Measurable (sqLen : (Fin k → ℂ) → ℝ) := by
  unfold sqLen
  exact Finset.measurable_sum _ fun i _ => Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)

theorem lintegral_snoc (k : ℕ) (f : (Fin (k + 1) → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v = ∫⁻ w : Fin k → ℂ, ∫⁻ z : ℂ, f (Fin.snoc (α := fun _ => ℂ) w z) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) (Fin.last k)).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod,
    lintegral_prod_symm' _ (by exact hf.comp (MeasurableEquiv.measurable _))]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

end GlobalTheory.HCXi.ConePolar

namespace GlobalTheory.HCXi
open ConePolar

theorem lintegral_cone_polar : ∀ (k : ℕ) (ψ : (Fin (k + 1) → ℂ) → ℝ≥0∞) (F : ℝ → ℝ≥0∞), Measurable ψ → Measurable F → (∫⁻ v : Fin (k + 1) → ℂ in {v | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}, F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ : ℝ in Set.Ioi 0, F τ * ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))) := by
  intro k ψ F hψ hF
  have hinit : Measurable fun v : Fin (k + 1) → ℂ => sqLen (Fin.init v : Fin k → ℂ) :=
    (measurable_sqLen k).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  have hlast : Measurable fun v : Fin (k + 1) → ℂ => Complex.normSq (v (Fin.last k)) :=
    Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)
  have hS := measurableSet_lt hinit hlast
  rw [← lintegral_indicator hS, lintegral_snoc k _
    (by exact Measurable.indicator ((hF.comp (hlast.sub hinit)).mul hψ) hS)]
  have h1 : ∀ w : Fin k → ℂ, (∫⁻ z : ℂ, Set.indicator
      {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}
      (fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v)
      (Fin.snoc (α := fun _ => ℂ) w z)) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ),
        F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) w
          (((Real.sqrt (sqLen w + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))) := by
    intro w
    rw [← plane (sqLen w) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) F
      (fun z => ψ (Fin.snoc (α := fun _ => ℂ) w z)) hF
      (hψ.comp ((measurable_snoc k).comp measurable_prodMk_left))]
    refine lintegral_congr fun z => ?_
    simp [Set.indicator]
  simp only [h1]
  have hG : Measurable fun q : ((Fin k → ℂ) × ℝ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1.1
      (((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : ((Fin k → ℂ) × ℝ) × ℝ =>
      (q.1.1, ((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH := hG.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  rw [lintegral_const_mul' _ _ (by simp), lintegral_lintegral_swap
    (by exact ((hF.comp measurable_snd).mul hH).aemeasurable)]
  congr 1
  refine lintegral_congr fun τ => ?_
  have hG' : Measurable fun q : (Fin k → ℂ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1
      (((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : (Fin k → ℂ) × ℝ =>
      (q.1, ((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH' := hG'.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  simp only at hH'
  rw [lintegral_const_mul _ hH', Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hG'.aemeasurable]

end GlobalTheory.HCXi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ParabolicLineStabilizerLevi
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.LineStabiliser

open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser

variable (k r' : ℕ)

def fst : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩

def lst : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

theorem e0_eq : e0 k r' = Pi.single (fst k r') 1 := rfl

theorem gram_mulVec_e0 : Hpk k (1 + r') *ᵥ e0 k r' = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  rw [e0_eq, mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem star_e0_vecMul_hpk_eq_single_lst : star (e0 k r') ᵥ* Hpk k (1 + r') = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  have h : star (e0 k r') = Pi.single (fst k r') 1 := by
    rw [e0_eq, ← Pi.single_star, star_one]
  rw [h, single_one_vecMul, Matrix.row_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem pair_e0_left (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    star (e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ v) = v (lst k r') := by
  rw [dotProduct_mulVec, star_e0_vecMul_hpk_eq_single_lst, single_one_dotProduct]

theorem lift_lst (w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' w (lst k r') = 0 := by
  unfold liftVec
  rw [dif_neg]
  simp only [lst]
  omega

theorem e0_lst_eq_zero : e0 k r' (lst k r') = 0 := by
  rw [e0_eq, Pi.single_apply, if_neg]
  simp only [lst, fst, Fin.ext_iff]
  omega

theorem decomp (u : Fin (2 * (1 + r') + k + 1) → ℂ) (hu : u (lst k r') = 0) :
    u = liftVec k 1 r' ((incl k 1 r')ᴴ *ᵥ u) + u (fst k r') • e0 k r' := by
  have hc : ∀ j, ((incl k 1 r')ᴴ *ᵥ u) j = u (levPos k 1 r' j) := fun j =>
    inclH_mul k 1 r' (Matrix.of fun a _ => u a) j j
  ext i
  have hi := i.isLt
  rw [Pi.add_apply, Pi.smul_apply, e0_eq, Pi.single_apply, smul_eq_mul]
  unfold liftVec
  by_cases h : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos h, hc, if_neg (by simp only [fst, Fin.ext_iff]; omega), mul_zero, add_zero]
    congr 1
    simp only [levPos, Fin.ext_iff]
    omega
  · rw [dif_neg h, zero_add]
    by_cases h0 : i = fst k r'
    · rw [if_pos h0, mul_one, h0]
    · rw [if_neg h0, mul_zero, ← hu]
      congr 1
      simp only [fst, lst, Fin.ext_iff] at h0 ⊢
      omega

theorem pair_unitary {n : ℕ} (H p : Matrix (Fin n) (Fin n) ℂ) (hp : pᴴ * H * p = H) (v w : Fin n → ℂ) :
    star (p *ᵥ w) ⬝ᵥ (H *ᵥ (p *ᵥ v)) = star w ⬝ᵥ (H *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hp]

theorem pair_lift (v w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' w) ⬝ᵥ (Hpk k (1 + r') *ᵥ liftVec k 1 r' v) = star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [liftVec_eq, liftVec_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, gram_inner]

theorem pair_shift (v w : Fin (2 * r' + k + 1) → ℂ) (c d : ℂ) :
    star (liftVec k 1 r' w + d • e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ (liftVec k 1 r' v + c • e0 k r')) =
      star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [star_add, add_dotProduct, star_smul, smul_dotProduct, pair_e0_left, mulVec_add, dotProduct_add,
    pair_lift, mulVec_smul, gram_mulVec_e0, dotProduct_smul, dotProduct_single_one]
  simp [lift_lst, e0_lst_eq_zero]

theorem acts_through_level_one : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by
  intro k r' a p hp he
  have hp' : pᴴ * Hpk k (1 + r') * p = Hpk k (1 + r') := hp
  have ha : a ≠ 0 := by
    rintro rfl
    have h := pair_unitary _ p hp' (Pi.single (lst k r') 1) (e0 k r')
    rw [he, zero_smul, star_zero, zero_dotProduct, pair_e0_left] at h
    simp at h
  have hl : ∀ w, (p *ᵥ liftVec k 1 r' w) (lst k r') = 0 := by
    intro w
    have h := pair_unitary _ p hp' (liftVec k 1 r' w) (e0 k r')
    rw [he, star_smul, smul_dotProduct, pair_e0_left, pair_e0_left, lift_lst, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (star_ne_zero.2 ha)
  have hd : ∀ w, p *ᵥ liftVec k 1 r' w =
      liftVec k 1 r' (((incl k 1 r')ᴴ * p * incl k 1 r') *ᵥ w) +
        (p *ᵥ liftVec k 1 r' w) (fst k r') • e0 k r' := by
    intro w
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← liftVec_eq k 1 r' w]
    exact decomp k r' _ (hl w)
  refine ⟨ha, (incl k 1 r')ᴴ * p * incl k 1 r', ?_, fun w => ⟨_, hd w⟩⟩
  generalize (incl k 1 r')ᴴ * p * incl k 1 r' = g at hd
  show gᴴ * Hpk k r' * g = Hpk k r'
  ext i j
  have h := pair_unitary _ p hp' (liftVec k 1 r' (Pi.single j 1)) (liftVec k 1 r' (Pi.single i 1))
  rw [hd (Pi.single j 1), hd (Pi.single i 1), pair_shift, pair_lift, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, mulVec_mulVec, ← Pi.single_star, star_one, single_one_dotProduct,
    single_one_dotProduct, mulVec_single_one, mulVec_single_one] at h
  exact h

end GlobalTheory.HCXi.LineStabiliser
end
end


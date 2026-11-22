import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivCexpPhaseLe
section
open scoped ContDiff
open scoped Nat

noncomputable section

namespace GlobalTheory

theorem norm_iteratedFDeriv_real_cexp (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

theorem norm_iteratedFDeriv_succ_clm_add_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (h : E → ℂ) (hh : ContDiff ℝ ∞ h) (i : ℕ) (t : E) :
    ‖iteratedFDeriv ℝ (i + 1) (fun t => L t + h t) t‖ ≤ ‖L‖ + ‖iteratedFDeriv ℝ (i + 1) h t‖ := by
  have hd : ∀ s, DifferentiableAt ℝ h s := fun s =>
    (hh.differentiable (by simp)).differentiableAt
  have hf : fderiv ℝ (fun t => L t + h t) = fun s => L + fderiv ℝ h s := by
    funext s
    exact (L.hasFDerivAt.add (hd s).hasFDerivAt).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hf, ← norm_iteratedFDeriv_fderiv]
  have hfh : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (by simp)
  change ‖iteratedFDeriv ℝ i ((fun _ => L) + fderiv ℝ h) t‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_const (c := L)).contDiffAt (hfh.of_le (by exact_mod_cast le_top)).contDiffAt]
  refine (norm_add_le _ _).trans ?_
  gcongr ?_ + _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [iteratedFDeriv_const_of_ne hi.ne']
    simp

theorem norm_iteratedFDeriv_cexp_phase_le :
    ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by
  intro V E _ _ _ _ _ _ B h hh hre n R
  set F : E → ℝ := fun t => ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j h t‖ with hF
  have hFc : Continuous F := by
    refine continuous_finset_sum _ (fun j _ => ?_)
    exact (hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hFc.continuousOn
  refine ⟨(n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n, fun y t ht => ?_⟩
  have htb : t ∈ Metric.closedBall (0 : E) R := by simpa using ht
  have hKj : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j h t‖ ≤ |K| := by
    intro j hj
    have h1 : ‖iteratedFDeriv ℝ j h t‖ ≤ F t :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j h t‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h2 : F t ≤ K := (le_abs_self _).trans ((Real.norm_eq_abs (F t)) ▸ hK t htb)
    exact (h1.trans h2).trans (le_abs_self K)
  set D : ℝ := (1 + ‖B‖ + |K|) * (1 + ‖y‖) with hD
  have hy0 := norm_nonneg y
  have hB0 := norm_nonneg B
  have hK0 := abs_nonneg K
  have hD1 : 1 ≤ D := by
    rw [hD]; nlinarith
  have hDge : ‖B‖ * ‖y‖ + |K| ≤ D := by
    rw [hD]; nlinarith
  have hphi : ContDiff ℝ ∞ (fun t => B y t + h t) := (B y).contDiff.add hh
  have hcomp : (fun t => Complex.exp (B y t + h t)) = Complex.exp ∘ (fun t => B y t + h t) := rfl
  rw [hcomp]
  have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Complex.exp) (f := fun t => B y t + h t)
    (n := n) (N := ∞) Complex.contDiff_exp hphi (by exact_mod_cast le_top) t (C := 1) (D := D)
    (fun i _ => by rw [norm_iteratedFDeriv_real_cexp, hre y t, Real.exp_zero])
    (fun i hi1 hin => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      calc ‖iteratedFDeriv ℝ (j + 1) (fun t => B y t + h t) t‖
          ≤ ‖B y‖ + ‖iteratedFDeriv ℝ (j + 1) h t‖ :=
            norm_iteratedFDeriv_succ_clm_add_le (B y) h hh j t
        _ ≤ ‖B‖ * ‖y‖ + |K| := add_le_add (B.le_opNorm y) (hKj _ hin)
        _ ≤ D := hDge
        _ ≤ D ^ (j + 1) := le_self_pow₀ hD1 (by omega))
  calc _ ≤ (n ! : ℝ) * 1 * D ^ n := key
    _ = (n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n * (1 + ‖y‖) ^ n := by rw [hD, mul_pow]; ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeLintegralTaylorTailIteratedDeriv
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem taylorTail_step_one {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (a : ℝ) (hg : Differentiable ℝ g) (hd : Continuous (deriv g))
    (hlim : Tendsto g atTop (𝓝 0)) :
    ENNReal.ofReal ‖g a‖ ≤ ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := by
  by_cases hI : IntegrableOn (deriv g) (Ioi a)
  · have hint : ∫ x in Ioi a, deriv g x = 0 - g a :=
      integral_Ioi_of_hasDerivAt_of_tendsto hg.continuous.continuousWithinAt
        (fun x _ => (hg x).hasDerivAt) hI hlim
    rw [zero_sub] at hint
    have h1 : ‖g a‖ ≤ ∫ x in Ioi a, ‖deriv g x‖ := by
      calc ‖g a‖ = ‖∫ x in Ioi a, deriv g x‖ := by rw [hint, norm_neg]
        _ ≤ ∫ x in Ioi a, ‖deriv g x‖ := norm_integral_le_integral_norm _
    calc ENNReal.ofReal ‖g a‖ ≤ ENNReal.ofReal (∫ x in Ioi a, ‖deriv g x‖) := ENNReal.ofReal_le_ofReal h1
      _ = ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := ofReal_integral_norm_eq_lintegral_enorm hI
  · have : ∫⁻ t in Ioi a, ‖deriv g t‖ₑ = ∞ := by
      by_contra hne
      exact hI ⟨hd.aestronglyMeasurable, lt_top_iff_ne_top.mpr hne⟩
    rw [this]; exact le_top

theorem taylorTail_inner (j : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫⁻ t in Ioo (0:ℝ) s, ENNReal.ofReal (t ^ j / (j.factorial : ℝ))
      = ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) := by
  have hcont : Continuous (fun t : ℝ => t ^ j / (j.factorial : ℝ)) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le,
      intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
    push_cast
    rw [zero_pow (Nat.succ_ne_zero j), sub_zero, div_div, mul_comm]
  · exact (hcont.integrableOn_Icc (a := 0) (b := s)).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact div_nonneg (pow_nonneg ht.1.le _) (by positivity)

theorem taylorTail_tonelli (f : ℝ → ℝ≥0∞) (hf : Measurable f) (j : ℕ) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ∫⁻ s in Ioi t, f s
      = ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) * f s := by
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) with hw
  have hwm : Measurable w := by fun_prop
  let G : ℝ → ℝ → ℝ≥0∞ := fun t s => w t * (Ioi t).indicator f s
  have hG : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have : Function.uncurry G = fun p : ℝ × ℝ => w p.1 * ({p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.2) p) := by
      ext ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, G, Set.indicator, mem_Ioi, mem_setOf_eq]
    rw [this]
    exact (hwm.comp measurable_fst).mul ((hf.comp measurable_snd).indicator hS)
  have step1 : ∫⁻ t in Ioi (0:ℝ), w t * ∫⁻ s in Ioi t, f s
      = ∫⁻ t in Ioi (0:ℝ), ∫⁻ s in Ioi (0:ℝ), G t s := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [G]
    rw [lintegral_const_mul _ (hf.indicator measurableSet_Ioi), lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr (le_of_lt (mem_Ioi.mp ht))]
  rw [step1, lintegral_lintegral_swap hG.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have : ∀ t, G t s = (Iio s).indicator w t * f s := by
    intro t
    by_cases h : t < s <;> simp [G, Set.indicator, h]
  simp_rw [this]
  rw [lintegral_mul_const _ (hwm.indicator measurableSet_Iio), lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, taylorTail_inner j s hs]

theorem taylorTail_bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (h : ℝ → F) (m : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hlim : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0)) :
    ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ m / (m.factorial : ℝ)) * ‖iteratedDeriv (m + 1) h t‖ₑ := by
  have hdiff : ∀ n : ℕ, Differentiable ℝ (iteratedDeriv n h) := fun n =>
    hh.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)
  have hcont : ∀ n : ℕ, Continuous (iteratedDeriv n h) := fun n => (hdiff n).continuous
  have key : ∀ j ≤ m, ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ := by
    intro j
    induction j with
    | zero =>
      intro _
      have := taylorTail_step_one h 0 (hdiff 0) (by rw [← iteratedDeriv_one]; exact hcont 1)
        (by simpa using hlim 0 (Nat.zero_le _))
      simpa [iteratedDeriv_one] using this
    | succ j ih =>
      intro hj
      refine (ih (Nat.le_of_succ_le hj)).trans ?_
      calc ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ
          ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) *
              ∫⁻ s in Ioi t, ‖iteratedDeriv (j + 1 + 1) h s‖ₑ := by
            refine lintegral_mono (fun t => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (zero_le')
            have := taylorTail_step_one (iteratedDeriv (j+1) h) t (hdiff _)
              (by rw [← iteratedDeriv_succ]; exact hcont _) (hlim (j+1) hj)
            simpa [iteratedDeriv_succ] using this
        _ = _ := taylorTail_tonelli _ ((hcont _).enorm.measurable) j
  exact key m le_rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfExtension
section
namespace GlobalTheory.NormExtensionBound

open scoped Pointwise

theorem exists_extension {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    (ev : A →+* K) : ∃ ev' : B →+* K, ∀ a, ev' (algebraMap A B a) = ev a := by
  haveI hP : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker ev) ⊥ (by
      intro a ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker ev) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker ev) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ev)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker ev) (B ⧸ Q) := inferInstance
  haveI : FaithfulSMul (A ⧸ RingHom.ker ev) (B ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker ev) (B ⧸ Q) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun h => FaithfulSMul.algebraMap_injective _ (B ⧸ Q) (by rw [h, map_zero])
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker ev) K :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun h => FaithfulSMul.algebraMap_injective _ K (by rw [h, map_zero])
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker ev) (B ⧸ Q) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  let f : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker ev] K := IsAlgClosed.lift
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk Q), fun a => ?_⟩
  have h := f.commutes (Ideal.Quotient.mk _ a)
  exact h

theorem norm_le_one_of_extension {p : ℕ} [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (ev : A →+* PadicAlgCl p) (h : ∀ a, ‖ev a‖ ≤ 1)
    (ev' : B →+* PadicAlgCl p) (hev : ∀ a, ev' (algebraMap A B a) = ev a) (b : B) :
    ‖ev' b‖ ≤ 1 := by
  haveI : IsUltrametricDist (PadicAlgCl p) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p)
  obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := A) b
  have hcomp : ev'.comp (algebraMap A B) = ev := RingHom.ext hev
  have hq' := congrArg ev' hq
  rw [map_zero, Polynomial.hom_eval₂, hcomp, hqm.as_sum, Polynomial.eval₂_add,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hq'
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hq'
  set y := ev' b
  by_contra hy
  push_neg at hy
  have hxn : y ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, ev (q.coeff i) * y ^ i :=
    eq_neg_of_add_eq_zero_left hq'
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hn
  · rw [h0] at hxn
    simp at hxn
  have hy1 : 1 ≤ ‖y‖ := hy.le
  have hle : ‖∑ i ∈ Finset.range q.natDegree, ev (q.coeff i) * y ^ i‖ ≤ ‖y‖ ^ (q.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.mp hi
    calc ‖ev (q.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (q.natDegree - 1) :=
          mul_le_mul (h _) (pow_le_pow_right₀ hy1 (by omega)) (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = ‖y‖ ^ (q.natDegree - 1) := one_mul _
  have h1 : ‖y‖ ^ q.natDegree ≤ ‖y‖ ^ (q.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hle
  have h2 : ‖y‖ ^ (q.natDegree - 1) < ‖y‖ ^ q.natDegree := pow_lt_pow_right₀ hy (by omega)
  linarith

theorem main : ∀ (p : ℕ) [Fact (Nat.Prime p)] (A B : Type) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)]
    (𝔷 : Ideal B), Function.Injective (algebraMap A B) →
    (∀ (b : B), (∀ (σ : B ≃ₐ[A] B), σ b = b) → b ∈ Set.range (algebraMap A B)) →
    Ideal.IsMaximal 𝔷 → ∀ (ev : A →+* PadicAlgCl p), (∀ (a : A), ‖ev a‖ ≤ (1 : ℝ)) →
    (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < (1 : ℝ)) →
    ∃ (ev' : B →+* PadicAlgCl p), (∀ (a : A), ev' (algebraMap A B a) = ev a) ∧
      (∀ (b : B), ‖ev' b‖ ≤ (1 : ℝ)) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < (1 : ℝ) := by
  intro p _ A B _ _ _ _ _ _ _ 𝔷 hinj hfix hmax ev h1 h2
  obtain ⟨e, he⟩ := exists_extension hinj ev
  have hle := norm_le_one_of_extension ev h1 e he
  let m : Ideal B :=
    { carrier := {b | ‖e b‖ < 1}
      add_mem' := fun {a b} ha hb => by
        show ‖e (a + b)‖ < 1
        rw [map_add]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c b hb => by
        show ‖e (c * b)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hb }
  have hm : ∀ b, b ∈ m ↔ ‖e b‖ < 1 := fun _ => Iff.rfl
  have hmne : m ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, hm]
    simp
  have hmu : m.under A = IsLocalRing.maximalIdeal A := by
    symm
    apply (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hmne)
    intro a ha
    rw [Ideal.mem_comap, hm, he]
    exact h2 a ha
  haveI hmm : m.IsPrime := ⟨hmne, fun {a b} hab => by
    rw [hm, map_mul, norm_mul] at hab
    by_contra hc
    rw [not_or, hm, hm, not_lt, not_lt] at hc
    exact absurd hab (not_lt.2 (one_le_mul_of_one_le_of_one_le hc.1 hc.2))⟩
  have hzu : 𝔷.under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) 𝔷)
  haveI : Algebra.IsInvariant A B (B ≃ₐ[A] B) := ⟨fun b hb => hfix b hb⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B (B ≃ₐ[A] B) 𝔷 m
    (hzu.trans hmu.symm)
  refine ⟨e.comp (g : B →+* B), fun a => ?_, fun b => hle _, fun b hb => ?_⟩
  · simp [he]
  · have : g • b ∈ m := by
      rw [hg]
      exact Ideal.smul_mem_pointwise_smul g b 𝔷 hb
    exact this

end GlobalTheory.NormExtensionBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMapRingOfIntegersLeOne
section
namespace GlobalTheory.RingOfIntegersNormBound

theorem norm_le_one_of_isIntegral {F : Type*} [NormedField F] [IsUltrametricDist F]
    {x : F} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨q, hq, hqx⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hqx
  have hlead : q.coeff q.natDegree = 1 := hq
  rw [hlead, map_one, one_mul] at hqx
  have hpow : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ F (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hqx
  have hpos : 0 < ‖x‖ := lt_trans one_pos hlt
  have key : ∀ n : ℕ,
      ‖∑ i ∈ Finset.range n, algebraMap ℤ F (q.coeff i) * x ^ i‖ < ‖x‖ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ‖x‖ ^ n < ‖x‖ ^ (n + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self n)
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ih.trans h1) ?_)
      rw [norm_mul, norm_pow]
      have h2 : ‖algebraMap ℤ F (q.coeff n)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one F (q.coeff n)
      calc ‖algebraMap ℤ F (q.coeff n)‖ * ‖x‖ ^ n ≤ 1 * ‖x‖ ^ n :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ‖x‖ ^ n := one_mul _
        _ < _ := h1
  have := key q.natDegree
  rw [← norm_neg, ← hpow, norm_pow] at this
  exact lt_irrefl _ this

theorem norm_map_ringOfIntegers_le_one {K : Type} [Field K] [NumberField K] {p : ℕ}
    [Fact (Nat.Prime p)] (f : K →+* ℂ_[p]) (c : NumberField.RingOfIntegers K) :
    ‖(f : K → ℂ_[p]) (↑c : K)‖ ≤ (1 : ℝ) :=
  norm_le_one_of_isIntegral (map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe c))

end GlobalTheory.RingOfIntegersNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMultisetSumLeOfForallLeUltrametric
section
namespace GlobalTheory

open Polynomial

theorem norm_multiset_sum_le_of_forall_le_ultrametric {K : Type} [NormedField K]
    [IsUltrametricDist K] (m : Multiset K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x ∈ m, ‖x‖ ≤ C) :
    ‖m.sum‖ ≤ C := by
  induction m using Multiset.induction_on with
  | empty => simpa using hC
  | cons a s ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Multiset.mem_cons_self _ _)
    · exact ih fun x hx => h x (Multiset.mem_cons_of_mem hx)

theorem norm_multiset_prod_le_pow_card_of_forall_le {K : Type} [NormedField K]
    (m : Multiset K) {B : ℝ} (h : ∀ x ∈ m, ‖x‖ ≤ B) :
    ‖m.prod‖ ≤ B ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    have ha := h a (Multiset.mem_cons_self _ _)
    exact mul_le_mul ha (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _)
      ((norm_nonneg _).trans ha)

theorem norm_coeff_natDegree_sub_le_pow_of_roots_le (K : Type) [NormedField K]
    [IsUltrametricDist K] [IsAlgClosed K] (Q : Polynomial K) (hQ : Q.Monic) (B : ℝ)
    (hB : ∀ r : K, Q.IsRoot r → ‖r‖ ≤ B) (i : ℕ) (hi : i ≤ Q.natDegree) :
    ‖Q.coeff (Q.natDegree - i)‖ ≤ B ^ i := by
  have hcard : Multiset.card Q.roots = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroot : ∀ r ∈ Q.roots, ‖r‖ ≤ B := fun r hr => hB r (isRoot_of_mem_roots hr)
  have hBi : 0 ≤ B ^ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp
    · have : 0 < Multiset.card Q.roots := by omega
      obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.1 this
      exact pow_nonneg ((norm_nonneg _).trans (hroot r hr)) _
  rw [Polynomial.coeff_eq_esymm_roots_of_card hcard (Nat.sub_le _ _), hQ.leadingCoeff,
    Nat.sub_sub_self hi, one_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Multiset.esymm]
  refine norm_multiset_sum_le_of_forall_le_ultrametric _ hBi ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨hle, hc⟩ := Multiset.mem_powersetCard.1 ht
  rw [← hc]
  exact norm_multiset_prod_le_pow_card_of_forall_le t fun y hy =>
    hroot y (Multiset.mem_of_le hle hy)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormUnitLeOfEsymm
section
namespace GlobalTheory.ElementarySymmetricNormBound

open Polynomial

theorem sum_esymm_eq_zero (s : Multiset ℂ) (x : ℂ) (hx : x ∈ s) :
    ∑ j ∈ Finset.range (Multiset.card s + 1),
      (-1) ^ j * (s.esymm j * x ^ (Multiset.card s - j)) = 0 := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_finset_sum] at h
  simp only [Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_one] at h
  rw [← h]
  exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨x, hx, sub_self x⟩)

theorem norm_le_of_esymm (s : Multiset ℂ) (M : ℝ) (hM : 1 ≤ M)
    (h : ∀ j, 1 ≤ j → j ≤ Multiset.card s → ‖s.esymm j‖ ≤ M) (x : ℂ) (hx : x ∈ s) :
    ‖x‖ ≤ (Multiset.card s : ℝ) * M := by
  have hn1 : 1 ≤ Multiset.card s := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx⟩
  by_cases hx1 : ‖x‖ ≤ 1
  · calc ‖x‖ ≤ 1 := hx1
      _ ≤ M := hM
      _ ≤ (Multiset.card s : ℝ) * M :=
          le_mul_of_one_le_left (by linarith) (by exact_mod_cast hn1)
  push_neg at hx1
  have h0 := sum_esymm_eq_zero s x hx
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm]
  rw [Finset.sum_range_succ'] at h0
  simp only [pow_zero, he0, one_mul, Nat.sub_zero] at h0
  have hxn : x ^ Multiset.card s = -∑ i ∈ Finset.range (Multiset.card s),
      (-1) ^ (i + 1) * (s.esymm (i + 1) * x ^ (Multiset.card s - (i + 1))) :=
    eq_neg_of_add_eq_zero_right h0
  have hbound : ‖x‖ ^ Multiset.card s ≤
      (Multiset.card s : ℝ) * M * ‖x‖ ^ (Multiset.card s - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    calc _ ≤ ∑ i ∈ Finset.range (Multiset.card s),
          ‖(-1 : ℂ) ^ (i + 1) * (s.esymm (i + 1) * x ^ (Multiset.card s - (i + 1)))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (Multiset.card s), M * ‖x‖ ^ (Multiset.card s - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact mul_le_mul (h (i + 1) (by omega) (by omega)) (pow_le_pow_right₀ hx1.le (by omega))
            (pow_nonneg (norm_nonneg _) _) (by linarith)
      _ = (Multiset.card s : ℝ) * M * ‖x‖ ^ (Multiset.card s - 1) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hpos : 0 < ‖x‖ ^ (Multiset.card s - 1) := pow_pos (by linarith) _
  have hsplit : ‖x‖ ^ Multiset.card s = ‖x‖ * ‖x‖ ^ (Multiset.card s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit] at hbound
  exact le_of_mul_le_mul_right hbound hpos

theorem norm_unit_le_of_esymm :
    ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), Multiset.card B = n → (1 : ℝ) ≤ M →
      (∀ (j : ℕ), (1 : ℕ) ≤ j → j ≤ n →
        ‖Multiset.esymm (Multiset.map (fun (b : ℂˣ) ↦ (↑b : ℂ)) B) j‖ ≤ M) →
      ∀ b ∈ B, ‖(↑b : ℂ)‖ ≤ (↑n : ℝ) * M := by
  intro n B M hcard hM h b hb
  have hb' := norm_le_of_esymm (B.map (fun b : ℂˣ => (b : ℂ))) M hM
    (fun j hj1 hj2 => by
      rw [Multiset.card_map, hcard] at hj2
      exact h j hj1 hj2) (b : ℂ) (Multiset.mem_map_of_mem _ hb)
  rwa [Multiset.card_map, hcard] at hb'

end GlobalTheory.ElementarySymmetricNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntRingHomExtOfIsHausdorff
section
open Matrix Polynomial

namespace GlobalTheory

theorem padicInt_ringHom_ext_of_isHausdorff : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  (f g : ℤ_[p] →+* O), f = g := by
  intro p _ O _ hH f g
  ext z
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hH _ fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (p : ℤ_[p]) ^ n * w + (z.appr n : ℕ) := by rw [mul_comm, hw]; ring
  have key : f z - g z = (p : O) ^ n * (f w - g w) := by
    rw [hz]
    simp only [map_add, map_mul, map_pow, map_natCast, mul_sub]
    abel
  rw [SModEq.zero, key, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory
end


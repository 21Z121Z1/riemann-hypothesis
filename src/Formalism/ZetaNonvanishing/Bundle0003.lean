import Formalism.Bundle0002
import Formalism.ZetaNonvanishing.LandauLemma
import Formalism.ZetaNonvanishing.Bundle0001

-- bundled from Formalism.ZetaNonvanishing.GzLipschitz
section
open ArithmeticFunction

noncomputable section

namespace Formalism

namespace LogFactorialMertensBounds

def A (k : ℕ) : ℝ := ∑ n ∈ Finset.Ioc 0 k, Λ n / n

def P (k : ℕ) (x : ℝ) : ℝ :=
  x * A k - ∑ n ∈ Finset.Ioc 0 k, Λ n - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

def K0 : ℝ := Real.log 4 + 7

lemma lipschitzConst_nonneg : 0 ≤ K0 := by
  unfold K0
  have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  linarith

lemma Icc_one_eq_Ioc (k : ℕ) : Finset.Icc 1 k = Finset.Ioc 0 k := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

lemma sum_log_eq_log_factorial (k : ℕ) :
    ∑ n ∈ Finset.Ioc 0 k, Real.log n = Real.log (k.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))]
    ring

lemma sum_log_eq (k : ℕ) :
    ∑ n ∈ Finset.Ioc 0 k, Real.log n = ∑ n ∈ Finset.Ioc 0 k, Λ n * ((k / n : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Finset.Ioc 0 k, Real.log n = ∑ d ∈ n.divisors, Λ d :=
    fun n _ => ArithmeticFunction.vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Finset.Ioc 0 k) (s' := fun d => (Finset.Ioc 0 k).filter (d ∣ ·))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  · intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h0, hk⟩, hd, -⟩
      have hle := Nat.le_of_dvd h0 hd
      have hpos := Nat.pos_of_dvd_of_pos hd h0
      exact ⟨⟨⟨h0, hk⟩, hd⟩, hpos, by omega⟩
    · rintro ⟨⟨⟨h0, hk⟩, hd⟩, -, -⟩
      exact ⟨⟨h0, hk⟩, hd, by omega⟩

lemma mertens_upper (k : ℕ) (hk : 1 ≤ k) : A k ≤ Real.log k + (Real.log 4 + 4) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hpsi : ∑ n ∈ Finset.Ioc 0 k, Λ n ≤ (Real.log 4 + 4) * k := by
    have h := Chebyshev.psi_le_const_mul_self (x := (k:ℝ)) hk0.le
    simpa [Chebyshev.psi] using h
  have hfact : Real.log (k.factorial : ℝ) ≤ k * Real.log k := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le_pow k)
  have hmain : (k:ℝ) * A k ≤ ∑ n ∈ Finset.Ioc 0 k, Λ n * ((k / n : ℕ) : ℝ) +
      ∑ n ∈ Finset.Ioc 0 k, Λ n := by
    rw [A, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnpos : 0 < n := hn.1
    have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
    have h1N : k < (k / n + 1) * n := by
      rw [Nat.add_mul, one_mul]
      exact Nat.lt_div_mul_add hnpos
    have h1R : (k:ℝ) ≤ (((k / n : ℕ) : ℝ) + 1) * n := by exact_mod_cast h1N.le
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (k:ℝ) / n ≤ ((k / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hnR]
      exact h1R
    have h3 : (k:ℝ) * (Λ n / n) = Λ n * ((k:ℝ) / n) := by ring
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left h2 hΛ]
  rw [← sum_log_eq, sum_log_eq_log_factorial] at hmain
  have h4 : (k:ℝ) * A k ≤ k * (Real.log k + (Real.log 4 + 4)) := by nlinarith
  exact le_of_mul_le_mul_left h4 hk0

lemma mertens_lower (k : ℕ) (hk : 1 ≤ k) : Real.log k - 1 ≤ A k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hfl : Real.log (k.factorial : ℝ) ≤ k * A k := by
    rw [← sum_log_eq_log_factorial, sum_log_eq, A, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hd : ((k / n : ℕ) : ℝ) ≤ (k:ℝ) / n := Nat.cast_div_le
    have h3 : (k:ℝ) * (Λ n / n) = Λ n * ((k:ℝ) / n) := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left hd hΛ
  have hst : k * Real.log k - k ≤ Real.log (k.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (k:ℝ) hk0.le k
    have hpos : (0:ℝ) < (k:ℝ) ^ k / k.factorial := by positivity
    have h2 := Real.log_le_log hpos h
    rw [Real.log_exp, Real.log_div (by positivity) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)),
      Real.log_pow] at h2
    linarith
  have h5 : (k:ℝ) * (Real.log k - 1) ≤ k * A k := by nlinarith
  exact le_of_mul_le_mul_left h5 hk0

lemma Sz_eq (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx2 : x ≤ k + 1) :
    Sz x = x * A k - ∑ n ∈ Finset.Ioc 0 k, Λ n := by
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg k) hx1
  have key : ∀ k' : ℕ, ∑ n ∈ Finset.Icc 1 k', Λ n * (x / n - 1) =
      x * A k' - ∑ n ∈ Finset.Ioc 0 k', Λ n := by
    intro k'
    rw [Icc_one_eq_Ioc, A, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  unfold Sz
  rcases lt_or_eq_of_le hx2 with h | h
  · rw [show ⌊x⌋₊ = k from (Nat.floor_eq_iff hx0).2 ⟨hx1, h⟩, key]
  · subst h
    have hf : ⌊(k:ℝ) + 1⌋₊ = k + 1 := by
      rw [← Nat.cast_add_one, Nat.floor_natCast]
    have hone : ((k:ℝ) + 1) / (((k + 1 : ℕ)) : ℝ) = 1 := by
      push_cast
      exact div_self (by positivity)
    rw [hf, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), key, hone]
    ring

lemma Gz_eq_P (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx2 : x ≤ k + 1) : Gz x = P k x := by
  unfold Gz P
  rw [Sz_eq k x hx1 hx2]

lemma hasDerivAt_P (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (P k) (A k - Real.log x + Real.eulerMascheroniConstant) x := by
  have h1 := ((((hasDerivAt_id' (x := x)).mul_const (A k)).sub_const
    (∑ n ∈ Finset.Ioc 0 k, Λ n)).sub (Real.hasDerivAt_mul_log hx.ne')).add
    ((hasDerivAt_id' (x := x)).const_mul (1 + Real.eulerMascheroniConstant))
  refine (h1.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [P, Pi.add_apply, Pi.sub_apply]

lemma deriv_bound (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx1' : 1 / 2 ≤ x) (hx2 : x ≤ k + 1) :
    |A k - Real.log x + Real.eulerMascheroniConstant| ≤ K0 := by
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hl4 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  unfold K0
  rw [abs_le]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hA : A 0 = 0 := by simp [A]
    have hx1'' : x ≤ 1 := by simpa using hx2
    have hlx : Real.log x ≤ 0 := Real.log_nonpos (by linarith) hx1''
    have hlx2 : Real.log (1 / 2) ≤ Real.log x := Real.log_le_log (by norm_num) hx1'
    rw [one_div, Real.log_inv] at hlx2
    rw [hA]
    constructor <;> linarith
  · have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hup := mertens_upper k hk
    have hlo := mertens_lower k hk
    have h1 : Real.log k ≤ Real.log x := Real.log_le_log (by linarith) hx1
    have h2 : Real.log x ≤ Real.log (2 * k) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul two_ne_zero (by positivity)] at h2
    constructor <;> linarith

lemma lip_piece (k : ℕ) (x y : ℝ) (hx1 : (k:ℝ) ≤ x) (hx1' : 1 / 2 ≤ x) (hx2 : x ≤ k + 1)
    (hy1 : (k:ℝ) ≤ y) (hy1' : 1 / 2 ≤ y) (hy2 : y ≤ k + 1) :
    |Gz y - Gz x| ≤ K0 * |y - x| := by
  have hs : Convex ℝ (Set.Icc (max (k:ℝ) (1 / 2)) (k + 1)) := convex_Icc _ _
  have hder : ∀ t ∈ Set.Icc (max (k:ℝ) (1 / 2)) (k + 1),
      HasDerivWithinAt (P k) (A k - Real.log t + Real.eulerMascheroniConstant)
        (Set.Icc (max (k:ℝ) (1 / 2)) (k + 1)) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right (k:ℝ) (1 / 2)) ht.1)
    exact (hasDerivAt_P k htpos).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc (max (k:ℝ) (1 / 2)) (k + 1),
      ‖A k - Real.log t + Real.eulerMascheroniConstant‖ ≤ K0 := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact deriv_bound k t (le_trans (le_max_left _ _) ht.1) (le_trans (le_max_right _ _) ht.1) ht.2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb hs
    ⟨max_le hx1 hx1', hx2⟩ ⟨max_le hy1 hy1', hy2⟩
  rw [Gz_eq_P k x hx1 hx2, Gz_eq_P k y hy1 hy2]
  simpa [Real.norm_eq_abs] using h

lemma lip_upto (k : ℕ) : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ k + 1 → 1 / 2 ≤ y → y ≤ k + 1 →
    |Gz y - Gz x| ≤ K0 * |y - x| := by
  have hK := lipschitzConst_nonneg
  induction k with
  | zero =>
    intro x y hx1 hx2 hy1 hy2
    exact lip_piece 0 x y (by rw [Nat.cast_zero]; linarith) hx1 hx2
      (by rw [Nat.cast_zero]; linarith) hy1 hy2
  | succ k ih =>
    intro x y hx1 hx2 hy1 hy2
    push_cast at hx2 hy2
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have split : ∀ u v : ℝ, 1 / 2 ≤ u → u ≤ k + 1 → k + 1 ≤ v → v ≤ k + 1 + 1 →
        |Gz v - Gz u| ≤ K0 * |v - u| := by
      intro u v hu1 hu2 hv1 hv2
      have e1 := ih u (k + 1) hu1 hu2 (by linarith) le_rfl
      have e2 := lip_piece (k + 1) (k + 1 : ℝ) v (by push_cast; linarith) (by linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by linarith) (by push_cast; linarith)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ k + 1 - u)] at e1
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - (k + 1))] at e2
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - u)]
      calc |Gz v - Gz u| ≤ |Gz v - Gz (k + 1)| + |Gz (k + 1) - Gz u| := abs_sub_le _ _ _
        _ ≤ K0 * (v - (k + 1)) + K0 * (k + 1 - u) := add_le_add e2 e1
        _ = K0 * (v - u) := by ring
    rcases le_total x (k + 1) with hxk | hxk <;> rcases le_total y (k + 1) with hyk | hyk
    · exact ih x y hx1 hxk hy1 hyk
    · exact split x y hx1 hxk hyk hy2
    · have h := split y x hy1 hyk hxk hx2
      rwa [abs_sub_comm (Gz x), abs_sub_comm x] at h
    · exact lip_piece (k + 1) x y (by push_cast; linarith) hx1 (by push_cast; linarith)
        (by push_cast; linarith) hy1 (by push_cast; linarith)

end LogFactorialMertensBounds

open LogFactorialMertensBounds in
theorem zetaPrimeSumErrorLipschitz : GzLipschitz := by
  have hK := lipschitzConst_nonneg
  have hlip : ∀ a b : ℝ, 1 / 2 ≤ a → 1 / 2 ≤ b → |Gz a - Gz b| ≤ K0 * |a - b| := by
    intro a b ha hb
    exact lip_upto (⌊a⌋₊ + ⌊b⌋₊) b a hb
      (by push_cast; linarith [Nat.lt_floor_add_one b, Nat.cast_nonneg (α := ℝ) ⌊a⌋₊]) ha
      (by push_cast; linarith [Nat.lt_floor_add_one a, Nat.cast_nonneg (α := ℝ) ⌊b⌋₊])
  refine ⟨K0 + 2 * |Gz (1 / 2)|, fun t t' ht ht' => ⟨?_, ?_⟩⟩
  · have h := hlip t (1 / 2) ht le_rfl
    have h2 : |Gz t| ≤ |Gz t - Gz (1 / 2)| + |Gz (1 / 2)| := by
      have := abs_sub_abs_le_abs_sub (Gz t) (Gz (1 / 2))
      linarith
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - 1 / 2)] at h
    nlinarith [abs_nonneg (Gz (1 / 2)), mul_nonneg (abs_nonneg (Gz (1 / 2))) (by linarith : (0:ℝ) ≤ t - 1 / 2)]
  · exact le_trans (hlip t t' ht ht')
      (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (Gz (1 / 2))]) (abs_nonneg _))

end Formalism
end
end

-- bundled from Formalism.ZetaNonvanishing.LandauEq
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

namespace LandauMellinIdentity

def Imel (H : ℝ → ℝ) (s : ℂ) : ℂ := ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1)

lemma imel_differentiableOn {H : ℝ → ℝ} {a : ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    (hint : ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) :
    DifferentiableOn ℂ (Imel H) {s : ℂ | a < s.re} := by
  intro s hs
  have hHc : AEStronglyMeasurable (fun x : ℝ => (H x : ℂ)) (volume.restrict (Ioi 1)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hH)
  have hnorm : ∀ σ : ℝ, a < σ →
      IntegrableOn (fun x : ℝ => ‖(H x : ℂ)‖ * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    refine (hint σ hσ).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos x hx)]
  exact (mellinDeriv (fun x => (H x : ℂ)) a hHc hnorm s hs).differentiableAt
    |>.differentiableWithinAt

end LandauMellinIdentity

open LandauMellinIdentity in
theorem landauEq : LandauEq := by
  intro H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq
  have hint : ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) :=
    landauLemma_of mellinDeriv H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq
  intro σ hσ
  refine ⟨hint σ hσ, ?_⟩

  have hOpen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hIan : AnalyticOnNhd ℂ (Imel H) {s : ℂ | a < s.re} :=
    (imel_differentiableOn hH hpos hint).analyticOnNhd hOpen

  set A : Set ℂ := {s : ℂ | b < s.re} with hA
  set B : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioi a with hB
  have hb1A : ((b + 1 : ℝ) : ℂ) ∈ A := by simp [hA]
  have hb1B : ((b + 1 : ℝ) : ℂ) ∈ B := ⟨b + 1, by simp; linarith, rfl⟩
  have hAconv : Convex ℝ A := convex_halfSpace_re_gt b
  have hApc : IsPreconnected A := hAconv.isPreconnected
  have hBpc : IsPreconnected B :=
    (isPreconnected_Ioi).image _ Complex.continuous_ofReal.continuousOn
  have hTpc : IsPreconnected (A ∪ B) := IsPreconnected.union _ hb1A hb1B hApc hBpc
  have hTsub : A ∪ B ⊆ {s : ℂ | a < s.re} := by
    rintro s (hs | ⟨t, ht, rfl⟩)
    · show a < s.re
      have : b < s.re := hs
      linarith
    · show a < ((t : ℂ)).re
      simpa using ht
  have hΦan : AnalyticOnNhd ℂ Φ (A ∪ B) := by
    rintro s (hs | ⟨t, ht, rfl⟩)
    · exact hΦ1 s hs
    · by_cases htb : t ≤ b
      · exact hΦ2 t ht htb
      · exact hΦ1 _ (by simpa using lt_of_not_ge htb)
  have hev : Φ =ᶠ[𝓝 ((b + 1 : ℝ) : ℂ)] Imel H := by
    have hAo : IsOpen A := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hAo.mem_nhds hb1A] with s hs
    exact hΦeq s hs
  have heq := hΦan.eqOn_of_preconnected_of_eventuallyEq (hIan.mono hTsub) hTpc
    (Or.inl hb1A) hev
  exact heq (Or.inr ⟨σ, hσ, rfl⟩)

end Formalism
end
end

-- bundled from Formalism.ZetaNonvanishing.MeasurableGchi
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction

lemma Sz_eq_Sa : Sz = Sa (fun n => Λ n) := rfl

lemma Schi_eq_Sa {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Schi χ = Sa (fun n => Λ n * (χ n).re) := rfl

lemma vM_bound : ∀ n : ℕ, |(Λ n : ℝ)| ≤ 1 * Λ n := fun n => by
  rw [one_mul, abs_of_nonneg vonMangoldt_nonneg]

lemma twist_bound {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ∀ n : ℕ, |Λ n * (χ n).re| ≤ 1 * Λ n := fun n => by
  rw [one_mul, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
  have h1 : |(χ n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
  exact mul_le_of_le_one_right vonMangoldt_nonneg h1

lemma measurable_Gz (h3 : MellinSgen) : Measurable Gz := by
  have := (h3 _ 1 vM_bound).1
  unfold Gz
  rw [Sz_eq_Sa]
  fun_prop

lemma measurable_Gchi (h3 : MellinSgen) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Measurable (Gchi χ) := by
  have := (h3 _ 1 (twist_bound χ)).1
  unfold Gchi
  rw [Schi_eq_Sa]
  fun_prop

lemma rint_Gz (h3 : MellinSgen) (h5 : MellinElem) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gz x * x ^ (-σ - 1)) (Ioi 1) := by
  have hS := h3 _ 1 vM_bound
  have a1 := rint_of_abs _ hS.1 σ (hS.2.1 σ hσ)
  have a2 := rint_of_abs (fun x => x * Real.log x) (by fun_prop) σ (h5.2.1 σ hσ)
  have a3 := h5.1 1 σ hσ
  have hfun : (fun x : ℝ => Gz x * x ^ (-σ - 1)) = fun x =>
      (Sa (fun n => Λ n) x * x ^ (-σ - 1) - (x * Real.log x) * x ^ (-σ - 1))
        + (1 + Real.eulerMascheroniConstant) * (x ^ (1:ℝ) * x ^ (-σ - 1)) := by
    funext x
    simp only [Gz, Sz_eq_Sa, Real.rpow_one]
    ring
  rw [hfun]
  exact Integrable.add (Integrable.sub a1 a2) (Integrable.const_mul a3 _)

lemma rint_Gchi (h3 : MellinSgen) (h5 : MellinElem) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gchi χ x * x ^ (-σ - 1)) (Ioi 1) := by
  have hS := h3 _ 1 (twist_bound χ)
  have a1 := rint_of_abs _ hS.1 σ (hS.2.1 σ hσ)
  have a3 := h5.1 1 σ hσ
  have hfun : (fun x : ℝ => Gchi χ x * x ^ (-σ - 1)) = fun x =>
      Sa (fun n => Λ n * (χ n).re) x * x ^ (-σ - 1)
        + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
          * (x ^ (1:ℝ) * x ^ (-σ - 1)) := by
    funext x
    simp only [Gchi, Schi_eq_Sa, Real.rpow_one]
    ring
  rw [hfun]
  exact Integrable.add a1 (Integrable.const_mul a3 _)

lemma mellin_Gz (h3 : MellinSgen) (h5 : MellinElem) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1:ℝ), (Gz x : ℂ) * (x : ℂ) ^ (-s - 1) =
      (-deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + (1 + (Real.eulerMascheroniConstant : ℂ)) * (1 / (s - 1)) := by
  have hS := h3 _ 1 vM_bound
  have i1 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i2 := cint_of_abs (fun x => x * Real.log x) (by fun_prop) s (h5.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => (Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
      ((Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)
        - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        + ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
          (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [Gz, Sz_eq_Sa, Real.rpow_one]
    push_cast
    ring
  have j12 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)
        - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := Integrable.sub i1 i2
  have j3 := Integrable.const_mul i3 ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ)
  refine ⟨by rw [hfun]; exact j12.add j3, ?_⟩
  rw [hfun, integral_add j12 j3, integral_sub i1 i2, integral_const_mul, hS.2.2 s hs,
    h5.2.2.2 s hs, h5.2.2.1 1 s (by simpa using hs)]
  have hL : LSeries (fun n => ((Λ n : ℝ) : ℂ)) s = -deriv riemannZeta s / riemannZeta s :=
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [hL]
  push_cast
  ring

end Formalism
end
end


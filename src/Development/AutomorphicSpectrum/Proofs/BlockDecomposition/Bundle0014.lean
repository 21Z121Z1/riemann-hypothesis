import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtOfContinuousHom
section
namespace GlobalTheory.CompanionTheory.CharDeriv

theorem hasDerivAt_of_continuous_hom :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ 0 = 1 → (∀ s t, χ (s + t) = χ s * χ t) →
      ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t := by
  intro χ hc h0 hadd
  have hP : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) (χ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  obtain ⟨δ, hI⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, χ s) ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) = fun _ => (0 : ℂ) := funext h
    have h1 := hP 0
    rw [hz] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at h2
    exact one_ne_zero h2
  have key : ∀ t : ℝ, χ t = ((∫ s in (0 : ℝ)..(t + δ), χ s) - ∫ s in (0 : ℝ)..t, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s) := by
    intro t
    rw [eq_div_iff hI, ← intervalIntegral.integral_const_mul]
    have h1 : (∫ s in (0 : ℝ)..δ, χ t * χ s) = ∫ u in t..(t + δ), χ u := by
      have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := δ) (fun u => χ u) t
      rw [add_zero] at h2
      rw [← h2]
      exact intervalIntegral.integral_congr fun s _ => (hadd t s).symm
    rw [h1]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  refine ⟨(χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s), fun t => ?_⟩
  have hD : HasDerivAt (fun y : ℝ => ((∫ s in (0 : ℝ)..(y + δ), χ s) - ∫ s in (0 : ℝ)..y, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s)) ((χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s)) t := by
    have h3 : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..(y + δ), χ s) (χ (t + δ)) t := by
      simpa using (hP (t + δ)).comp_add_const t δ
    exact (h3.sub (hP t)).div_const _
  have hval : (χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s) * χ t =
      (χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s) := by
    rw [hadd t δ]
    ring
  rw [hval]
  exact hD.congr_of_eventuallyEq (Filter.Eventually.of_forall key)

end GlobalTheory.CompanionTheory.CharDeriv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasProdMoebiusConvOfNormLe
section
open scoped LSeries.notation ArithmeticFunction.Moebius
open LSeries

namespace GlobalTheory.CompanionTheory.SquareEuler

lemma natCast_pow_cpow (p e : ℕ) (s : ℂ) :
    (((p ^ e : ℕ) : ℂ)) ^ s = ((p : ℂ) ^ s) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

variable {M : ℕ} (c : DirichletCharacter ℂ M) {N : ℕ → ℂ} {s : ℂ}

lemma term_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    LSeries.term (↗c * N) s (p ^ e) = N (p ^ e) * (c p * (p : ℂ) ^ (-s)) ^ e := by
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hne, natCast_pow_cpow, Complex.cpow_neg]
  simp only [Pi.mul_apply, Nat.cast_pow, map_pow, mul_pow, inv_pow]
  rw [div_eq_mul_inv]
  ring

lemma norm_X_lt_one (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    ‖c p * (p : ℂ) ^ (-s)‖ < 1 := by
  have h1 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simpa using hs)
  calc ‖c p * (p : ℂ) ^ (-s)‖ = ‖c p‖ * ‖(p : ℂ) ^ (-s)‖ := norm_mul _ _
    _ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by gcongr; exact c.norm_le_one _
    _ < 1 := by simpa using h1

lemma term_mul (hNmul : ∀ {m n : ℕ}, m.Coprime n → N (m * n) = N m * N n)
    {m n : ℕ} (h : m.Coprime n) :
    LSeries.term (↗c * N) s (m * n) =
      LSeries.term (↗c * N) s m * LSeries.term (↗c * N) s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  simp only [Pi.mul_apply, hNmul h, Nat.cast_mul, map_mul]
  rw [div_mul_div_comm]
  ring_nf

lemma hasProd_twist (hN1 : N 1 = 1)
    (hNmul : ∀ {m n : ℕ}, m.Coprime n → N (m * n) = N m * N n)
    (hsum : LSeriesSummable N s) :
    HasProd (fun p : Nat.Primes => ∑' j : ℕ, N ((p : ℕ) ^ j) * (c p * ((p : ℕ) : ℂ) ^ (-s)) ^ j)
      (L (↗c * N) s) := by
  have hT : LSeriesSummable (↗c * N) s := DirichletCharacter.LSeriesSummable_mul c hsum
  have := EulerProduct.eulerProduct_hasProd (f := LSeries.term (↗c * N) s) ?_ ?_ hT.norm ?_
  · have h2 : L (↗c * N) s = ∑' n, LSeries.term (↗c * N) s n := rfl
    rw [h2]
    convert this using 2 with p
    exact tsum_congr fun j => (term_prime_pow c p.prop j).symm
  · simp [LSeries.term_of_ne_zero, hN1]
  · intro m n hmn
    exact term_mul c hNmul hmn
  · simp

lemma LSeries_twist_moebius_conv (hs : 1 < s.re) (hsum : LSeriesSummable N s) :
    L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s = (L ↗c s)⁻¹ * L (↗c * N) s := by
  have hμ : LSeriesSummable (↗c * (↗μ : ℕ → ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul c (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hT : LSeriesSummable (↗c * N) s := DirichletCharacter.LSeriesSummable_mul c hsum
  rw [← DirichletCharacter.mul_convolution_distrib, LSeries_convolution' hμ hT]
  have h1 := DirichletCharacter.LSeries.mul_mu_eq_one c hs
  rw [eq_inv_of_mul_eq_one_right h1]

lemma local_factor {A X : ℂ} (hX : ‖X‖ < 1) :
    A * (1 - X) * (1 - X ^ 2)⁻¹ = A / (1 + X) := by
  have h1 : 1 - X ≠ 0 := by
    intro h
    have : X = 1 := by linear_combination -h
    simp [this] at hX
  have h2 : 1 + X ≠ 0 := by
    intro h
    have : X = -1 := by linear_combination h
    simp [this] at hX
  have h3 : 1 - X ^ 2 = (1 - X) * (1 + X) := by ring
  rw [h3]
  field_simp

theorem hasProd_moebius_conv (hN1 : N 1 = 1)
    (hNmul : ∀ {m n : ℕ}, m.Coprime n → N (m * n) = N m * N n)
    (hs : 1 < s.re) (hsum : LSeriesSummable N s) :
    HasProd (fun p : Nat.Primes =>
        (∑' j : ℕ, N ((p : ℕ) ^ j) * (c p * ((p : ℕ) : ℂ) ^ (-s)) ^ j) /
          (1 + c p * ((p : ℕ) : ℂ) ^ (-s)))
      (L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s * L ↗(c ^ 2) (2 * s)) := by
  have h2s : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hA := hasProd_twist c hN1 hNmul hsum
  have hB := DirichletCharacter.LSeries_eulerProduct_hasProd (c ^ 2) h2s
  have hC := DirichletCharacter.LSeries_eulerProduct_hasProd c hs
  have hCne : L ↗c s ≠ 0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re c hs
  have hCi := hC.inv₀ hCne
  have hP := (hA.mul hCi).mul hB
  rw [LSeries_twist_moebius_conv c hs hsum]
  convert hP using 1
  · funext p
    have hX := norm_X_lt_one c (s := s) (by linarith) p.prop
    rw [← local_factor hX, inv_inv]
    have hsq : (c ^ 2) ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(2 * s)) =
        (c p * ((p : ℕ) : ℂ) ^ (-s)) ^ 2 := by
      have h3 : -(2 * s) = ((2 : ℕ) : ℂ) * (-s) := by push_cast; ring
      rw [h3, Complex.cpow_nat_mul, mul_pow]
      congr 1
      exact MulChar.pow_apply' c (by norm_num) _
    rw [hsq]
  · ring

theorem hasProd_moebius_conv_of_norm_le (hN1 : N 1 = 1)
    (hNmul : ∀ {m n : ℕ}, m.Coprime n → N (m * n) = N m * N n)
    (hNle : ∀ d : ℕ, d ≠ 0 → ‖N d‖ ≤ d) (hs : 2 < s.re) :
    HasProd (fun p : Nat.Primes =>
        (∑' j : ℕ, N ((p : ℕ) ^ j) * (c p * ((p : ℕ) : ℂ) ^ (-s)) ^ j) /
          (1 + c p * ((p : ℕ) : ℂ) ^ (-s)))
      (L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s * L ↗(c ^ 2) (2 * s)) := by
  refine hasProd_moebius_conv c hN1 hNmul (by linarith) ?_
  refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hs ⟨1, fun n hn => ?_⟩
  have : (n : ℝ) ^ ((2 : ℝ) - 1) = n := by norm_num
  rw [this, one_mul]
  exact hNle n hn

end GlobalTheory.CompanionTheory.SquareEuler
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumTaylorOfExpBounds
section
open Filter Topology Set

namespace GlobalTheory.CompanionTheory.TaylorGlobal

theorem hasSum_taylor_of_exp_bounds (n : ℕ) (c : (Fin n → ℝ) → ℂ) (C R M : ℝ)
    (hc : ContDiff ℝ ⊤ c)
    (hb : ∀ (k : ℕ) (H v : Fin n → ℝ),
      ‖iteratedFDeriv ℝ k c H (fun _ => v)‖ ≤ M * (C * ‖v‖) ^ k * Real.exp (R * ‖H‖))
    (H h : Fin n → ℝ) :
    HasSum (fun k : ℕ => ((Nat.factorial k : ℂ))⁻¹ * iteratedFDeriv ℝ k c H (fun _ => h))
      (c (H + h)) := by
  have hc' : ContDiff ℝ (⊤ : ℕ∞) c := hc.of_le (by exact_mod_cast le_top)
  set L : ℝ →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h with hL
  have hLt : ∀ t : ℝ, L t = t • h := fun t => by simp [hL]
  set cH : (Fin n → ℝ) → ℂ := fun z => c (H + z) with hcH
  have hcH' : ContDiff ℝ (⊤ : ℕ∞) cH := hc'.comp (contDiff_const.add contDiff_id)
  set g : ℝ → ℂ := cH ∘ L with hg
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := hcH'.comp L.contDiff
  have key : ∀ (j : ℕ) (t : ℝ),
      iteratedDeriv j g t = iteratedFDeriv ℝ j c (H + t • h) (fun _ => h) := by
    intro j t
    rw [iteratedDeriv_eq_iteratedFDeriv, hg,
      L.iteratedFDeriv_comp_right hcH' t (by exact_mod_cast le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, hcH,
      iteratedFDeriv_comp_add_left, hLt]
    simp [hLt]
  set A : ℝ := |C| * ‖h‖ with hA
  have hA0 : 0 ≤ A := by positivity
  set E : ℝ := Real.exp (|R| * (‖H‖ + ‖h‖)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have bnd : ∀ (k : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      ‖iteratedDeriv k g t‖ ≤ |M| * A ^ k * E := by
    intro k t ht
    rw [key]
    refine (hb k _ _).trans ?_
    have hn : ‖H + t • h‖ ≤ ‖H‖ + ‖h‖ := by
      refine (norm_add_le _ _).trans ?_
      have : ‖t • h‖ ≤ ‖h‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      linarith
    have hexp : Real.exp (R * ‖H + t • h‖) ≤ E := by
      refine Real.exp_le_exp.2 ?_
      calc R * ‖H + t • h‖ ≤ |R| * ‖H + t • h‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self R) (norm_nonneg _)
        _ ≤ |R| * (‖H‖ + ‖h‖) := mul_le_mul_of_nonneg_left hn (abs_nonneg R)
    have hpow : M * (C * ‖h‖) ^ k ≤ |M| * A ^ k := by
      calc M * (C * ‖h‖) ^ k ≤ |M * (C * ‖h‖) ^ k| := le_abs_self _
        _ = |M| * A ^ k := by
            rw [abs_mul, abs_pow, abs_mul, abs_norm]
    calc M * (C * ‖h‖) ^ k * Real.exp (R * ‖H + t • h‖)
        ≤ |M| * A ^ k * Real.exp (R * ‖H + t • h‖) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ ≤ |M| * A ^ k * E := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hD : ∀ k : ℕ, iteratedFDeriv ℝ k c H (fun _ => h) = iteratedDeriv k g 0 := by
    intro k
    rw [key]
    simp
  have hsum : Summable
      (fun k : ℕ => ((Nat.factorial k : ℂ))⁻¹ * iteratedFDeriv ℝ k c H (fun _ => h)) := by
    have hs0 : Summable (fun k : ℕ => |M| * E * (A ^ k / (Nat.factorial k : ℝ))) :=
      (Real.summable_pow_div_factorial A).mul_left _
    refine Summable.of_norm_bounded hs0 ?_
    intro k
    rw [norm_mul, hD, norm_inv, Complex.norm_natCast]
    have := bnd k 0 (by simp)
    have hf : (0 : ℝ) ≤ ((Nat.factorial k : ℝ))⁻¹ := by positivity
    calc ((Nat.factorial k : ℝ))⁻¹ * ‖iteratedDeriv k g 0‖
        ≤ ((Nat.factorial k : ℝ))⁻¹ * (|M| * A ^ k * E) := mul_le_mul_of_nonneg_left this hf
      _ = |M| * E * (A ^ k / (Nat.factorial k : ℝ)) := by ring
  have htay : ∀ m : ℕ, taylorWithinEval g m (Icc 0 1) 0 1 =
      ∑ k ∈ Finset.range (m + 1),
        ((Nat.factorial k : ℂ))⁻¹ * iteratedFDeriv ℝ k c H (fun _ => h) := by
    intro m
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hgs.of_le (by exact_mod_cast le_top)).contDiffAt) (by simp)]
    simp [Complex.real_smul]
  have hrem : ∀ m : ℕ, ‖g 1 - taylorWithinEval g m (Icc 0 1) 0 1‖ ≤
      |M| * E * A * (A ^ m / (Nat.factorial m : ℝ)) := by
    intro m
    have h1 := taylor_mean_remainder_bound (f := g) (a := 0) (b := 1) (x := 1) (n := m)
      (C := |M| * A ^ (m + 1) * E) zero_le_one
      ((hgs.of_le (by exact_mod_cast le_top)).contDiffOn) (by simp) (by
        intro y hy
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
          ((hgs.of_le (by exact_mod_cast le_top)).contDiffAt) hy]
        exact bnd _ y hy)
    refine h1.trans (le_of_eq ?_)
    simp only [sub_zero, one_pow, mul_one]
    ring
  have hlim : Tendsto (fun m : ℕ => taylorWithinEval g m (Icc 0 1) 0 1) atTop (𝓝 (g 1)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun m : ℕ => |M| * E * A * (A ^ m / (Nat.factorial m : ℝ)))
        atTop (𝓝 0) := by
      simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop A).const_mul (|M| * E * A)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) h0
    rw [norm_sub_rev]
    exact hrem m
  have hg1 : g 1 = c (H + h) := by simp [hg, hcH, hLt]
  rw [← hg1, hsum.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
  simpa only [htay] using hlim

end GlobalTheory.CompanionTheory.TaylorGlobal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPsdIsotropicRadical
section
namespace GlobalTheory.CompanionTheory.HermitianForm

theorem re_pairing_eq_zero_of_psd {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hpos : ∀ v, 0 ≤ (B v v).re) (v : V) (hv : B v v = 0) (u : V) : (B v u).re = 0 := by
  have hb : 0 ≤ (B u u).re := hpos u
  have key : ∀ t : ℝ, 0 ≤ 2 * t * (B v u).re + t ^ 2 * (B u u).re := by
    intro t
    have h := hpos (v + (t : ℂ) • u)
    have e : B (v + (t : ℂ) • u) (v + (t : ℂ) • u)
        = B v v + (t : ℂ) * B v u + (t : ℂ) * B u v + (t : ℂ) * (t : ℂ) * B u u := by
      simp only [map_add, LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Complex.conj_ofReal]
      ring
    rw [e, hv, hB v u] at h
    simp only [zero_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.mul_im, zero_mul, sub_zero, add_zero] at h
    nlinarith [h]
  set a := (B v u).re with ha
  set b := (B u u).re with hb'
  have hb1 : 0 < b + 1 := by linarith
  have h := key (-a / (b + 1))
  have e2 : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b
      = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    field_simp
    ring
  rw [e2] at h
  have h3 : 0 ≤ -(a ^ 2 * (b + 2)) := by
    by_contra hc
    push Not at hc
    have : -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 < 0 := div_neg_of_neg_of_pos hc (by positivity)
    linarith
  have h4 : a ^ 2 * (b + 2) ≤ 0 := by linarith
  have h5 : a ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < a ^ 2 * (b + 2) := mul_pos hc (by linarith)
    linarith
  have h6 : a ^ 2 = 0 := le_antisymm h5 (sq_nonneg a)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h6

theorem pairing_eq_zero_of_psd : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) →
    (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  intro V _ _ B hB hpos v hv w
  have hre := re_pairing_eq_zero_of_psd B hB hpos v hv w
  have him := re_pairing_eq_zero_of_psd B hB hpos v hv (Complex.I • w)
  have e : B v (Complex.I • w) = -Complex.I * B v w := by
    simp only [map_smulₛₗ, smul_eq_mul, Complex.conj_I]
  rw [e] at him
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at him
  apply Complex.ext
  · simpa using hre
  · simpa using him

end GlobalTheory.CompanionTheory.HermitianForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadical
section
open Matrix

namespace GlobalTheory.CompanionTheory.Herm

theorem apply_eq_zero_of_isotropic {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hs : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hp : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = B x w := ⟨_, rfl⟩
  have hwx : B w x = starRingEnd ℂ c := by rw [hc]; exact hs x w
  have key : ∀ t : ℝ, 0 ≤ -2 * t * Complex.normSq c
      + t ^ 2 * Complex.normSq c * (B w w).re := by
    intro t
    have h := hp (x - ((t : ℂ) * c) • w)
    have e : B (x - ((t : ℂ) * c) • w) (x - ((t : ℂ) * c) • w)
        = B x x - starRingEnd ℂ ((t : ℂ) * c) * c - ((t : ℂ) * c) * starRingEnd ℂ c
          + ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c) * B w w := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.map_smulₛₗ, smul_eq_mul, ← hc, hwx]
      ring
    have e1 : starRingEnd ℂ ((t : ℂ) * c) * c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, mul_comm (starRingEnd ℂ c) c,
        Complex.mul_conj]
      push_cast; ring
    have e2 : ((t : ℂ) * c) * starRingEnd ℂ c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [mul_assoc, Complex.mul_conj]
      push_cast; ring
    have e3 : ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c)
        = ((t ^ 2 * Complex.normSq c : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_mul, Complex.normSq_ofReal]
      push_cast; ring
    rw [e, e1, e2, e3] at h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, hx] at h
    linarith
  by_contra hne
  have hc0 : c ≠ 0 := by rw [hc]; exact hne
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc0
  have hr : 0 ≤ (B w w).re := hp w
  obtain ⟨r, hrdef⟩ : ∃ r, r = (B w w).re := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hk := key (1 / (r + 1))
  rw [← hrdef] at hk
  have hr1 : 0 < r + 1 := by linarith
  have hid : -2 * (1 / (r + 1)) * Complex.normSq c
      + (1 / (r + 1)) ^ 2 * Complex.normSq c * r
      = -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 := by
    field_simp
    ring
  rw [hid] at hk
  have : -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  linarith

end GlobalTheory.CompanionTheory.Herm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedGeneratedByKFinite
section
namespace GlobalTheory.CompanionTheory.CosetSum

theorem mem_of_translated_bumps : ∀ {Γ J : Type} [Group Γ] [AddCommGroup J] [Module ℂ J] (Q K K₁ : Subgroup Γ) (π : Representation ℂ Q J) (M : Submodule ℂ (Γ → J)) (Gf : Γ → J), K₁ ≤ K → K₁.relIndex K ≠ 0 → (∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) → (∀ g : Γ, ∃ q : Q, ∃ κ ∈ K, g = (q : Γ) * κ) → (∀ φ ∈ M, ∀ x : Γ, (fun g => φ (g * x)) ∈ M) → (∀ φ ∈ M, ∀ (q : Q) (g : Γ), φ ((q : Γ) * g) = π q (φ g)) → (∀ (q : Q) (g : Γ), Gf ((q : Γ) * g) = π q (Gf g)) → (∀ (g : Γ), ∀ b ∈ K₁, Gf (g * b) = Gf g) → (∀ κ ∈ K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧ ∀ g : Γ, (¬ ∃ q : Q, ∃ b ∈ K₁, g = (q : Γ) * b) → φ g = 0) → Gf ∈ M := by
  intro Γ J _ _ _ Q K K₁ π M Gf hle hidx hconj hdec htr hlawM hlaw hinv hb
  classical
  let H : Subgroup K := K₁.subgroupOf K
  haveI hHn : H.Normal := ⟨fun n hn g => by
    have hn' : (n : Γ) ∈ K₁ := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ?_
    simpa using hconj g g.2 n hn'⟩
  haveI : H.FiniteIndex := ⟨hidx⟩
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let P : Γ → Prop := fun x => ∃ q : Q, ∃ b ∈ K₁, x = (q : Γ) * b
  have hPmul : ∀ x, ∀ b ∈ K₁, P x → P (x * b) := by
    rintro x b hb' ⟨q, c, hc, rfl⟩
    exact ⟨q, c * b, K₁.mul_mem hc hb', by simp [mul_assoc]⟩
  have hb2 : ∀ κ : K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧
      ∀ g : Γ, (¬ P g) → φ g = 0 := fun κ => hb κ κ.2
  choose φ hφM hφ1 hφ0 using hb2
  have key : ∀ κ' κ : K, φ κ ((κ' : Γ) * (κ : Γ)⁻¹) =
      if P ((κ' : Γ) * (κ : Γ)⁻¹) then Gf κ' else 0 := by
    intro κ' κ
    split_ifs with h
    · obtain ⟨q, b, hbm, e⟩ := h
      rw [e, hφ1 κ q b hbm, ← hlaw]
      have hκ' : (κ' : Γ) = q * b * κ := by rw [← e]; group
      have e2 : (q : Γ) * κ = κ' * ((κ : Γ)⁻¹ * b⁻¹ * κ) := by rw [hκ']; group
      have hm : (κ : Γ)⁻¹ * b⁻¹ * κ ∈ K₁ := by
        simpa using hconj _ (K.inv_mem κ.2) _ (K₁.inv_mem hbm)
      rw [e2, hinv _ _ hm]
    · exact hφ0 κ _ h
  let r : K ⧸ H → K := Quotient.out
  have hr : ∀ δ : K ⧸ H, ((r δ : K) : K ⧸ H) = δ := fun δ => QuotientGroup.out_eq' δ
  have hPcl : ∀ x y : K, (x : K ⧸ H) = y → P x → P y := by
    intro x y hxy hx
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    have hm' : (x : Γ)⁻¹ * y ∈ K₁ := by simpa using Subgroup.mem_subgroupOf.1 hm
    have := hPmul _ _ hm' hx
    simpa using this
  let Pd : K ⧸ H → Prop := fun ε => P (r ε)
  have hPd : ∀ x : K, P x ↔ Pd (x : K ⧸ H) := fun x =>
    ⟨hPcl _ _ (hr _).symm, hPcl _ _ (hr _)⟩
  let Φ : Γ → J := ∑ δ : K ⧸ H, (fun g => φ (r δ) (g * ((r δ : K) : Γ)⁻¹))
  have hΦM : Φ ∈ M := M.sum_mem fun δ _ => htr _ (hφM _) _
  let n : ℕ := (Finset.univ.filter Pd).card
  have hΦ : ∀ κ' : K, Φ κ' = n • Gf κ' := by
    intro κ'
    have h1 : Φ κ' = ∑ δ : K ⧸ H, if Pd ((κ' : K ⧸ H) * δ⁻¹) then Gf κ' else 0 := by
      simp only [Φ, Finset.sum_apply]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [key]
      have hcl : (((κ' * (r δ)⁻¹ : K)) : K ⧸ H) = (κ' : K ⧸ H) * δ⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hr]
      have := hPd (κ' * (r δ)⁻¹)
      rw [hcl] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      simp only [this]
    rw [h1]
    have h2 := Equiv.sum_comp ((Equiv.inv (K ⧸ H)).trans (Equiv.mulLeft (κ' : K ⧸ H)))
      (fun ε => if Pd ε then Gf κ' else 0)
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft] at h2
    rw [h2, ← Finset.sum_filter, Finset.sum_const]
  have hn : n ≠ 0 := by
    have h1 : Pd 1 := by
      have : (r 1 : Γ) ∈ K₁ := by
        have : r 1 ∈ H := (QuotientGroup.eq_one_iff _).1 (hr 1)
        exact Subgroup.mem_subgroupOf.1 this
      exact ⟨1, _, this, by simp⟩
    exact (Finset.card_pos.2 ⟨1, by simpa using h1⟩).ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hΨM : (n : ℂ)⁻¹ • Φ ∈ M := M.smul_mem _ hΦM
  have hEq : (n : ℂ)⁻¹ • Φ = Gf := by
    funext g
    obtain ⟨q, κ, hκ, rfl⟩ := hdec g
    have hK : ((n : ℂ)⁻¹ • Φ) κ = Gf κ := by
      have := hΦ ⟨κ, hκ⟩
      simp only at this
      rw [Pi.smul_apply, this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hnC, one_smul]
    rw [hlawM _ hΨM, hK, hlaw]
  exact hEq ▸ hΨM

end GlobalTheory.CompanionTheory.CosetSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LtOneOfPowerBound
section
namespace GlobalTheory.CompanionTheory.Casselman

theorem lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one :
    ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  intro δ r hδ hr h
  have h2 : (Real.sqrt δ * r) ^ (2 : ℝ) = δ * r ^ 2 := by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le]
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] at h
  nlinarith

end GlobalTheory.CompanionTheory.Casselman
end


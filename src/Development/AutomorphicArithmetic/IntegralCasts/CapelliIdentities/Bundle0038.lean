import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialSecond
section
noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialSecond.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialSecond.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialSecond.intMv_mul.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv (F * G) := by
  intro p _ σ F G hF hG n
  classical
  change ‖MvPowerSeries.coeff n (F * G)‖ ≤ 1
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro q _
  rw [norm_mul]
  exact mul_le_one₀ (hF q.1) (norm_nonneg _) (hG q.2)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialSixth
section
noncomputable def UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.intMv_zero.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1}, UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := by
  intro p inst σ n
  show ‖(MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) 0‖ ≤ (1 : ℝ)
  rw [map_zero, norm_zero]
  exact zero_le_one
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialThird
section
noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialThird.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialThird.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialThird.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialThird.intMv_C.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {c : ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialThird.IsIntP c → UpperTheory.Reformulated.B.IntegralPolynomialThird.IntegralMv ((MvPowerSeries.C : ℂ_[p] → MvPowerSeries σ ℂ_[p]) c) := by
  intro p _ σ c hc n
  classical
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · show ‖(0 : ℂ_[p])‖ ≤ (1 : ℝ)
    rw [norm_zero]
    exact zero_le_one
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralQuadraticHalfInt
section
private lemma int_of_isIntegral_cast (q : ℚ) (h : IsIntegral ℤ (q : ℂ)) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : IsIntegral ℤ (algebraMap ℚ ℂ q) := by simpa using h
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨n, by simpa using hn⟩

private lemma int_of_sq_mul (d : ℕ) (hd : d.Prime) (q : ℚ) (m : ℤ)
    (h : q ^ 2 * (d : ℚ) = m) : ∃ n : ℤ, (n : ℚ) = q := by
  have hq : q * (q.den : ℚ) = q.num := Rat.mul_den_eq_num q
  have h1 : q.num ^ 2 * (d : ℤ) = m * (q.den : ℤ) ^ 2 := by
    have : ((q.num : ℚ)) ^ 2 * (d : ℚ) = (m : ℚ) * (q.den : ℚ) ^ 2 := by
      rw [← hq, ← h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    simpa [Int.gcd] using q.reduced
  have h2 : (q.den : ℤ) ^ 2 ∣ (d : ℤ) :=
    hc.dvd_of_dvd_mul_left ⟨m, by rw [h1]; ring⟩
  have h3 : q.den * q.den ∣ d := by
    have : q.den ^ 2 ∣ d := by exact_mod_cast h2
    rwa [sq] at this
  have h4 : q.den = 1 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h3)
  refine ⟨q.num, ?_⟩
  rw [← hq, h4]; simp

private lemma even_sub_of_norm (d : ℕ) (hd : d.Prime) (x y n : ℤ)
    (h : x ^ 2 + y ^ 2 * (d : ℤ) = 4 * n) : Even (x - y) := by
  obtain ⟨s, hs | hs⟩ := Int.even_or_odd' x <;> obtain ⟨t, ht | ht⟩ := Int.even_or_odd' y
  · exact ⟨s - t, by omega⟩
  · exfalso
    have h1 : (d : ℤ) = 4 * (n - s ^ 2 - (t ^ 2 + t) * d) := by
      rw [hs, ht] at h; linear_combination h
    have h2 : 2 * 2 ∣ d := by
      have : ((4 : ℕ) : ℤ) ∣ (d : ℤ) := ⟨_, by exact_mod_cast h1⟩
      exact_mod_cast this
    have h3 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h2)
    omega
  · exfalso
    have h1 : (1 : ℤ) = 4 * (n - s ^ 2 - s - t ^ 2 * d) := by
      rw [hs, ht] at h; linear_combination h
    omega
  · exact ⟨s - t, by omega⟩

theorem UpperTheory.integral_quadratic_half_int :
    ∀ (d : ℕ), d.Prime → ∀ (a b : ℚ), IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) → ∃ x y : ℤ, Even (x - y) ∧ (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) = ((x : ℂ) + (y : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) / 2 := by
  intro d hd a b h
  have hr : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    have : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
    exact_mod_cast this
  generalize Real.sqrt (d : ℝ) = r at h hr ⊢
  have h' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
    have h0 := map_isIntegral_int (starRingEnd ℂ) h
    have e : (starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        = (a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ)) := by
      simp only [map_add, map_mul, map_ratCast, Complex.conj_I, Complex.conj_ofReal]
      ring
    rwa [e] at h0
  obtain ⟨x, hx⟩ := int_of_isIntegral_cast (2 * a) (by
    have e : ((2 * a : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        + ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast; ring
    rw [e]; exact h.add h')
  obtain ⟨n, hn⟩ := int_of_isIntegral_cast (a ^ 2 + b ^ 2 * d) (by
    have e : ((a ^ 2 + b ^ 2 * d : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        * ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast
      linear_combination (b : ℂ) ^ 2 * (r : ℂ) ^ 2 * Complex.I_sq - (b : ℂ) ^ 2 * hr
    rw [e]; exact h.mul h')
  obtain ⟨y, hy⟩ := int_of_sq_mul d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hn, hx]; ring)
  refine ⟨x, y, even_sub_of_norm d hd x y n ?_, ?_⟩
  · have : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 * (d : ℚ) = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  · have hx' : (x : ℂ) = 2 * (a : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hx
    have hy' : (y : ℂ) = 2 * (b : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hy
    rw [hx', hy']; ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralSumCosets
section
theorem UpperTheory.Reformulated.B.IntegralSumCosets.integral_eq_measure_mul_sum_cosets :
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsMulRightInvariant] [MeasureTheory.IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      IsCompact (↑K : Set G) →
        ∀ (ι : Type) (R : ι → G) (S : Finset ι) (f : G → ℂ),
          (∀ (a b : ι), R a * (R b)⁻¹ ∈ K → a = b) →
            (∀ κ ∈ K, ∀ (g : G), f (κ * g) = f g) →
              (∀ (g : G), f g ≠ (0 : ℂ) → ∃ a ∈ S, g * (R a)⁻¹ ∈ K) →
                ∫ (g : G), f g ∂μ = (↑(μ.real (↑K : Set G)) : ℂ) * ∑ a ∈ S, f (R a) := by
  intro G _ _ _ _ _ μ _ _ K hKo hKc ι R S f hR hf hsupp
  classical
  have hmeas : ∀ a : ι, MeasurableSet ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)) := fun a =>
    (hKo.preimage (continuous_id.mul continuous_const)).measurableSet
  have hμ : ∀ a : ι, μ ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)) = μ (K : Set G) := fun a =>
    MeasureTheory.measure_preimage_mul_right μ _ _
  have hval : ∀ (a : ι) (g : G), g * (R a)⁻¹ ∈ K → f g = f (R a) := by
    intro a g hg
    have h := hf _ hg (R a)
    rwa [inv_mul_cancel_right] at h
  have hdec : f = fun g => ∑ a ∈ S,
      ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a)) g := by
    funext g
    by_cases hex : ∃ a ∈ S, g * (R a)⁻¹ ∈ K
    · obtain ⟨a, haS, ha⟩ := hex
      rw [Finset.sum_eq_single a]
      · rw [Set.indicator_of_mem (by exact ha)]
        exact hval a g ha
      · intro b _ hba
        apply Set.indicator_of_notMem
        intro hb
        apply hba
        apply hR
        have hb' : g * (R b)⁻¹ ∈ K := hb
        have h := K.mul_mem (K.inv_mem hb') ha
        have e : (g * (R b)⁻¹)⁻¹ * (g * (R a)⁻¹) = R b * (R a)⁻¹ := by group
        rwa [e] at h
      · intro h
        exact absurd haS h
    · have h0 : f g = 0 := by
        by_contra h
        exact hex (hsupp g h)
      rw [h0]
      symm
      apply Finset.sum_eq_zero
      intro a haS
      apply Set.indicator_of_notMem
      intro ha
      exact hex ⟨a, haS, ha⟩
  have hint : ∀ a ∈ S, MeasureTheory.Integrable
      (((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a))) μ := by
    intro a _
    rw [MeasureTheory.integrable_indicator_iff (hmeas a)]
    exact MeasureTheory.integrableOn_const (by rw [hμ a]; exact hKc.measure_lt_top.ne)
  calc ∫ g, f g ∂μ
      = ∫ g, ∑ a ∈ S,
          ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a)) g ∂μ :=
        congrArg (fun F : G → ℂ => ∫ g, F g ∂μ) hdec
    _ = ∑ a ∈ S, ∫ g,
          ((fun g : G => g * (R a)⁻¹) ⁻¹' (K : Set G)).indicator (fun _ => f (R a)) g ∂μ :=
        MeasureTheory.integral_finset_sum S hint
    _ = (↑(μ.real (↑K : Set G)) : ℂ) * ∑ a ∈ S, f (R a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [MeasureTheory.integral_indicator_const _ (hmeas a), MeasureTheory.measureReal_def,
          hμ a, MeasureTheory.measureReal_def, Complex.real_smul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntertwinerDiagonalization
section
private theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine {K : Type} [Field K]
    (M : GL (Fin 2) K) (D P : Matrix (Fin 2) (Fin 2) K) (hP : P.det ≠ 0)
    (h : (↑M : Matrix (Fin 2) (Fin 2) K) * P = P * D) :
    ∃ (g : GL (Fin 2) K), (↑(g * M * g⁻¹) : Matrix (Fin 2) (Fin 2) K) = D := by
  let u : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
  have hu : (↑u : Matrix (Fin 2) (Fin 2) K) = P := rfl
  refine ⟨u⁻¹, ?_⟩
  rw [inv_inv, Units.val_mul, Units.val_mul, mul_assoc, hu, h, ← hu, ← mul_assoc,
    Units.inv_mul, one_mul]

theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.exists_diag :
    ∀ {K : Type} [inst : Field K]
    (M : GL (Fin (2 : ℕ)) K) {x : K},
    x ≠ (1 : K) →
      (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).trace = (1 : K) + x →
        (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).det = x →
          ∃ (g : GL (Fin (2 : ℕ)) K),
            (↑(g * M * g⁻¹) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K) = Matrix.diagonal ![(1 : K), x] := by
  intro K _ M x hx ht hd
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  rw [Matrix.trace_fin_two] at ht
  rw [Matrix.det_fin_two] at hd
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : K, (↑M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hD : (Matrix.diagonal ![(1 : K), x] : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hM] at ht hd
  have ht' : a + d = 1 + x := by simpa using ht
  have hd' : a * d - b * c = x := by simpa using hd
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · have hq : (a - 1) * (a - x) = 0 := by
        rw [hb] at hd'
        linear_combination a * ht' - hd'
      rcases mul_eq_zero.mp hq with h | h
      · have ha : a = 1 := sub_eq_zero.mp h
        have hdx : d = x := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ 1 (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, mul_one, one_mul]
      · have ha : a = x := sub_eq_zero.mp h
        have hdx : d = 1 := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![0, 1; 1, 0] (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, Matrix.mul_fin_two, Matrix.mul_fin_two]
        simp
    · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![b, b; 1 - a, x - a] ?_ ?_
      · have : (!![b, b; 1 - a, x - a] : Matrix (Fin 2) (Fin 2) K).det = b * (x - 1) := by
          rw [Matrix.det_fin_two_of]; ring
        rw [this]
        exact mul_ne_zero hb hx'
      · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
        have e1 : a * b + b * (1 - a) = b * 1 + b * 0 := by ring
        have e2 : a * b + b * (x - a) = b * 0 + b * x := by ring
        have e3 : c * b + d * (1 - a) = (1 - a) * 1 + (x - a) * 0 := by
          linear_combination ht' - hd'
        have e4 : c * b + d * (x - a) = (1 - a) * 0 + (x - a) * x := by
          linear_combination x * ht' - hd'
        rw [e1, e2, e3, e4]
  · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![1 - d, x - d; c, c] ?_ ?_
    · have : (!![1 - d, x - d; c, c] : Matrix (Fin 2) (Fin 2) K).det = -(c * (x - 1)) := by
        rw [Matrix.det_fin_two_of]; ring
      rw [this]
      exact neg_ne_zero.mpr (mul_ne_zero hc hx')
    · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
      have e1 : a * (1 - d) + b * c = (1 - d) * 1 + (x - d) * 0 := by
        linear_combination ht' - hd'
      have e2 : a * (x - d) + b * c = (1 - d) * 0 + (x - d) * x := by
        linear_combination x * ht' - hd'
      have e3 : c * (1 - d) + d * c = c * 1 + c * 0 := by ring
      have e4 : c * (x - d) + d * c = c * 0 + c * x := by ring
      rw [e1, e2, e3, e4]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvOfUnitCoeffMem
section
theorem UpperTheory.invOfUnit_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (f : PowerSeries R), (∀ n, PowerSeries.coeff n f ∈ S) → PowerSeries.constantCoeff f = 1 → ∀ n, PowerSeries.coeff n (PowerSeries.invOfUnit f 1) ∈ S := by
  intro R _ S f hf _ n
  have h1 : ((1⁻¹ : Rˣ) : R) ∈ S := by
    rw [inv_one, Units.val_one]
    exact S.one_mem
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with hn
    · exact h1
    · refine S.mul_mem (S.neg_mem h1) (S.sum_mem fun x _ => ?_)
      split_ifs with hx
      · exact S.mul_mem (hf _) (ih _ hx)
      · exact S.zero_mem
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvolutionMapCompactFinite
section
theorem UpperTheory.involution_map_compact_finite :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : MeasureTheory.Measure X) (U : Set X) (ι : X → X), Measurable ι → IsClosed U → ContinuousOn ι U → (∀ x ∈ U, ι x ∈ U) → (∀ x ∈ U, ι (ι x) = x) → μ Uᶜ = 0 → (∀ K : Set X, IsCompact K → μ K < ⊤) → ∀ K : Set X, IsCompact K → (μ.map ι) K < ⊤ := by
  intro X _ _ _ _ μ U ι hm hU hc hmaps hinv h0 hfin K hK
  rw [MeasureTheory.Measure.map_apply hm hK.measurableSet]
  have hcomp : IsCompact (ι '' (K ∩ U)) :=
    (hK.inter_right hU).image_of_continuousOn (hc.mono Set.inter_subset_right)
  have hsub : ι ⁻¹' K ⊆ ι '' (K ∩ U) ∪ Uᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨ι x, ⟨hx, hmaps x hxU⟩, hinv x hxU⟩
    · exact Or.inr hxU
  calc μ (ι ⁻¹' K) ≤ μ (ι '' (K ∩ U) ∪ Uᶜ) := MeasureTheory.measure_mono hsub
    _ ≤ μ (ι '' (K ∩ U)) + μ Uᶜ := MeasureTheory.measure_union_le _ _
    _ = μ (ι '' (K ∩ U)) := by rw [h0, add_zero]
    _ < ⊤ := hfin _ hcomp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrCases
section
theorem UpperTheory.Reformulated.B.Qe20.irrCases :
    ∀ {G V : Type} [inst : Group G]
    [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V),
    ρ.IsIrreducible →
      ∀ (W : Submodule ℂ V), (∀ (g : G), ∀ v ∈ W, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G V _ _ _ ρ hρ W hW
  let S : Subrepresentation ρ := ⟨W, fun g v hv => hW g v hv⟩
  rcases hρ.eq_bot_or_eq_top S with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrIff
section
theorem UpperTheory.Reformulated.B.Ra6.irr_iff :
    ∀ {G W : Type} [inst : Group G] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module ℂ W] (ρ : Representation ℂ G W),
    ρ.IsIrreducible ↔
      Nontrivial W ∧
        ∀ (N : Submodule ℂ W), (∀ (g : G), ∀ v ∈ N, ((ρ : G → W →ₗ[ℂ] W) g : W → W) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro G W _ _ _ ρ
  constructor
  · intro h
    have h' : IsSimpleOrder (Subrepresentation ρ) := h
    refine ⟨?_, fun N hN => ?_⟩
    · have hne : (⊥ : Submodule ℂ W) ≠ ⊤ := fun e =>
        (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).mp ⟨⊥, ⊤, hne⟩
    · rcases h'.eq_bot_or_eq_top ⟨N, fun g v hv => hN g v hv⟩ with e | e
      · exact Or.inl (congrArg Subrepresentation.toSubmodule e)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule e)
  · rintro ⟨hW, h⟩
    have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun e =>
      (bot_ne_top (α := Submodule ℂ W)) (congrArg Subrepresentation.toSubmodule e)
    have h' : IsSimpleOrder (Subrepresentation ρ) :=
      { exists_pair_ne := ⟨⊥, ⊤, hne⟩
        eq_bot_or_eq_top := fun σ =>
          (h σ.toSubmodule fun g v hv => σ.apply_mem_toSubmodule g hv).imp
            (fun e => Subrepresentation.toSubmodule_injective e)
            (fun e => Subrepresentation.toSubmodule_injective e) }
    exact h'
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrIffSpan
section
private theorem UpperTheory.Reformulated.B.Qe4.subalgebra_eq_top {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ s ∈ S, ∀ v ∈ N, s v ∈ N) → N = ⊥ ∨ N = ⊤) : S = ⊤ := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [eq_top_iff]
    intro f _
    rw [Subsingleton.elim f 0]
    exact S.zero_mem
  haveI : IsSimpleModule S V := by
    refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun N => ?_ }
    rcases h (N.restrictScalars K) (fun s hs v hv => N.smul_mem (⟨s, hs⟩ : S) hv) with h1 | h1
    · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff K S V).1 h1)
    · exact Or.inr ((Submodule.restrictScalars_eq_top_iff K S V).1 h1)
  rw [eq_top_iff]
  intro f _
  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K
          (A := S) (V := V)).2 φ
        exact f.map_smul c v }
  classical
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density (R := S) F (Finset.univ.image b)
  have : f = (r : Module.End K V) :=
    b.ext fun i => hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]
  exact r.2

theorem UpperTheory.Reformulated.B.Qe4.irrIffSpan :
    ∀ {K G ι : Type} [inst : Field K] [IsAlgClosed K] [inst_2 : Group G]
    [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (ρ : G →* Matrix ι ι K),
    (∀ (N : Submodule K (ι → K)), (∀ (g : G), ∀ v ∈ N, ((ρ : G → Matrix ι ι K) g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) ↔
      Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) = ⊤ := by
  intro K G ι _ _ _ _ _ ρ
  constructor
  · intro h
    have hmul : ∀ x y : Matrix ι ι K, x ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) →
        y ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) →
        x * y ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) := by
      intro x y hx hy
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
      exact ⟨a * c, map_mul ρ a c⟩
    let A : Subalgebra K (Matrix ι ι K) :=
      (Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K))).toSubalgebra
        (Submodule.subset_span ⟨1, map_one ρ⟩) hmul
    let e : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K) := Matrix.toLinAlgEquiv'
    have hS : A.map (e : Matrix ι ι K →ₐ[K] Module.End K (ι → K)) = ⊤ := by
      refine UpperTheory.Reformulated.B.Qe4.subalgebra_eq_top _ fun N hN => h N fun g v hv => ?_
      exact hN (e (ρ g)) ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩ v hv
    rw [eq_top_iff]
    intro M _
    have hM : e M ∈ A.map (e : Matrix ι ι K →ₐ[K] Module.End K (ι → K)) := by
      rw [hS]; exact Algebra.mem_top
    obtain ⟨x, hx, hxe⟩ := hM
    have : x = M := e.injective hxe
    rw [← this]
    exact hx
  · intro h N hN
    have hall : ∀ M : Matrix ι ι K, ∀ v ∈ N, M.mulVec v ∈ N := by
      intro M v hv
      have hM : M ∈ Submodule.span K (Set.range (⇑ρ : G → Matrix ι ι K)) := by
        rw [h]; exact Submodule.mem_top
      induction hM using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hN g v hv
      | zero => rw [Matrix.zero_mulVec]; exact N.zero_mem
      | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact N.add_mem hx hy
      | smul c x _ hx => rw [Matrix.smul_mulVec]; exact N.smul_mem c hx
    by_cases hb : N = ⊥
    · exact Or.inl hb
    right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).1 hb
    rw [eq_top_iff]
    intro w _
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv0
    have := hall (LinearMap.toMatrix' (φ.smulRight w)) v hv
    rw [LinearMap.toMatrix'_mulVec] at this
    simpa [hφ] using this
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleIffStable
section
theorem UpperTheory.Reformulated.B.StableSubmoduleBotOrTopOfSpanEqTop.irrIff_stable :
    ∀ {H K : Type} [inst : Group H] [inst_1 : Field K] {n : ℕ}
    (r : H →* Matrix (Fin n) (Fin n) K),
    Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) = ⊤ →
      ∀ (W : Submodule K (Fin n → K)),
        (∀ (g : H), ∀ v ∈ W, ((r : H → Matrix (Fin n) (Fin n) K) g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro H K _ _ n r hspan W hW
  have hall : ∀ (A : Matrix (Fin n) (Fin n) K), ∀ v ∈ W, A.mulVec v ∈ W := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hW g v hv
    | zero => rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h := hall (Matrix.of fun a b => if b = i then w a / v i else 0) v hv
    have e : (Matrix.of fun a b => if b = i then w a / v i else 0 :
        Matrix (Fin n) (Fin n) K).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [e] at h
end


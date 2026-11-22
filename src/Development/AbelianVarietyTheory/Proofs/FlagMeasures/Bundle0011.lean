import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBoundByDyadicSummation
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.Dyadic

theorem lintegral_mul_le_of_sq {X : Type} [MeasurableSpace X] (μ : Measure X) (A B : X → ℝ)
    (hA : Measurable A) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (h1 : ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ ≤ ENNReal.ofReal (α ^ 2))
    (h2 : ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ ≤ ENNReal.ofReal (β ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ ≤ ENNReal.ofReal (α * β) := by
  have hc : 0 ≤ β / (2 * α) := by positivity
  have hd : 0 ≤ α / (2 * β) := by positivity
  calc ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (β / (2 * α)) * ENNReal.ofReal (A x ^ 2)
          + ENNReal.ofReal (α / (2 * β)) * ENNReal.ofReal (B x ^ 2)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hd,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : β / (2 * α) * A x ^ 2 + α / (2 * β) * B x ^ 2 - A x * B x
            = (β * A x - α * B x) ^ 2 / (2 * α * β) := by
          field_simp; ring
        have h3 : 0 ≤ (β * A x - α * B x) ^ 2 / (2 * α * β) := by positivity
        linarith
    _ = ENNReal.ofReal (β / (2 * α)) * ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ
          + ENNReal.ofReal (α / (2 * β)) * ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (β / (2 * α)) * ENNReal.ofReal (α ^ 2)
          + ENNReal.ofReal (α / (2 * β)) * ENNReal.ofReal (β ^ 2) := by gcongr
    _ = ENNReal.ofReal (α * β) := by
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hd,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp; ring

theorem exists_shell (s H : ℝ) (hH : 0 < H) :
    ∃ i : ℕ, s ≤ 2 ^ i * H ∧ (i = 0 ∨ 2 ^ i * H / 2 < s) := by
  have hex : ∃ i : ℕ, s ≤ 2 ^ i * H := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / H) (one_lt_two (α := ℝ))
    exact ⟨n, ((div_lt_iff₀ hH).1 hn).le⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | j
  · exact Or.inl rfl
  · right
    have := Nat.find_min hex (m := j) (by omega)
    push Not at this
    rw [pow_succ]; linarith

theorem exists_shell_down (y T : ℝ) (hy : 0 < y) (hT : y ≤ T) :
    ∃ a : ℕ, T / 2 ^ (a + 1) < y ∧ y ≤ 2 * (T / 2 ^ (a + 1)) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := T / y) (y := (2 : ℝ))
    ((one_le_div hy).2 hT) one_lt_two
  refine ⟨n, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hy] at h2; linarith
  · rw [le_div_iff₀ hy] at h1
    have : 2 * (T / 2 ^ (n + 1)) = T / 2 ^ n := by rw [pow_succ]; field_simp
    rw [this, le_div_iff₀ (by positivity)]; linarith

theorem piece_bound (r kk : ℕ) (H De D l l' u v : ℝ) (hr : 1 ≤ r) (hkk : 1 ≤ kk) (hH : 1 ≤ H)
    (hDe : 1 ≤ De) (hD : 0 < D) (hl : 1 ≤ l) (hl' : 1 ≤ l') (hu : 0 < u) (hv : 0 < v)
    (h1 : (r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u *
      ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) * D ≤ 2 ^ r)
    (h2 : D ≤ (l * l' * H) ^ (2 * r)) :
    ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u) ^ kk *
        (l ^ (24 * r ^ 3 + 1))⁻¹) *
      ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) ^ kk *
        (l' ^ (24 * r ^ 3 + 1))⁻¹) ≤
      (r : ℝ) ^ (2 * r) * H ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk *
        (l⁻¹ * l'⁻¹ * u⁻¹ * v⁻¹) := by
  have hR : 1 ≤ l * l' * H := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hl hl') hH
  have hRe : (l * l' * H) ^ (24 * r ^ 3) = l ^ (24 * r ^ 3) * l' ^ (24 * r ^ 3) * H ^ (24 * r ^ 3) := by
    rw [mul_pow, mul_pow]
  generalize l * l' * H = R at *
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hT2 : (r * R ^ (2 * r - 1) * De) ^ r * (r * R ^ (2 * r - 1) * De) ^ r * R ^ (2 * r)
      = (r : ℝ) ^ (2 * r) * De ^ (2 * r) * R ^ (4 * r ^ 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [this]
    generalize ((m + 1 : ℕ) : ℝ) = c
    ring
  have hTpos : 0 < (r * R ^ (2 * r - 1) * De) ^ r := by positivity
  generalize (r * R ^ (2 * r - 1) * De) ^ r = T at *
  set P : ℝ := 2 ^ r / D with hP
  have hPpos : 0 < P := by positivity
  set w : ℝ := T / u * (T / v) with hw
  have hwpos : 0 < w := by positivity
  have hwP : w ≤ P := by rw [hP, le_div_iff₀ hD]; exact h1
  have h3 : w ^ kk ≤ P ^ kk * (T * T * R ^ (2 * r) * (u⁻¹ * v⁻¹)) := by
    obtain ⟨m, rfl⟩ : ∃ m, kk = m + 1 := ⟨kk - 1, by omega⟩
    have h4 : w ^ m ≤ P ^ m := pow_le_pow_left₀ hwpos.le hwP m
    have h5 : 1 ≤ P * R ^ (2 * r) := by
      have : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ one_le_two
      calc (1 : ℝ) ≤ 2 ^ r := this
        _ = P * D := by rw [hP]; field_simp
        _ ≤ P * R ^ (2 * r) := by gcongr
    calc w ^ (m + 1) = w ^ m * w * 1 := by ring
      _ ≤ P ^ m * w * (P * R ^ (2 * r)) := by gcongr
      _ = _ := by rw [hw]; ring
  rw [hT2] at h3
  have h6 : R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * R ^ (4 * r ^ 2) ≤ R ^ (24 * r ^ 3) := by
    rw [← pow_add, ← pow_add]
    refine pow_le_pow_right₀ hR ?_
    have : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
    omega
  have hl0 : 0 < l := by linarith
  have hl0' : 0 < l' := by linarith
  have hR0 : 0 < R := by linarith
  have hDe0 : 0 < De := by linarith
  calc _ = R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * w ^ kk *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by
          rw [hw, mul_pow]; ring
    _ ≤ R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * R ^ (4 * r ^ 2) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by gcongr
    _ = (R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * R ^ (4 * r ^ 2)) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by ac_rfl
    _ ≤ R ^ (24 * r ^ 3) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by gcongr
    _ = _ := by
      rw [hRe, pow_succ l, pow_succ l']
      have e1 : 0 < l ^ (24 * r ^ 3) := by positivity
      have e2 : 0 < l' ^ (24 * r ^ 3) := by positivity
      generalize l ^ (24 * r ^ 3) = a at *
      generalize l' ^ (24 * r ^ 3) = b at *
      generalize H ^ (24 * r ^ 3) = c
      generalize P ^ kk = d
      generalize (r : ℝ) ^ (2 * r) = e
      generalize De ^ (2 * r) = f
      field_simp

theorem tsum_four (C : ℝ≥0∞) :
    ∑' p : ℕ × ℕ × ℕ × ℕ, C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2)))
      = C * 16 := by
  have h : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by
    rw [ENNReal.tsum_geometric]; simp
  simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, h]
  norm_num

theorem dyadic_summation : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r kk : ℕ) (H₁ De D K K' : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ r ∧ D ≤ max (S x) (S' x) ^ (2 * r) ∧ Y x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r ∧ Y' x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ i * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < S x) ∧ S' x ≤ 2 ^ i' * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ i' * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ / 2 < S' x) ∧ S x ≤ 2 ^ i * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (Real.sqrt (K * K') * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk) := by
  intro X _ ν A B S S' Y Y' r kk H De D K K' hA hB hS hS' hY hY' hr hkk hH hDe hD hK hK' hae h1 h2
  have hH0 : 0 < H := by linarith
  have hDe0 : 0 < De := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  let T : ℕ → ℕ → ℝ := fun i i' => (r * ((2 : ℝ) ^ i * 2 ^ i' * H) ^ (2 * r - 1) * De) ^ r
  have hT : ∀ i i', 0 < T i i' := fun i i' => by positivity
  let Q : ℕ × ℕ × ℕ × ℕ → Set X := fun p => {x | (0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ r ∧
      D ≤ ((2 : ℝ) ^ p.1 * 2 ^ p.2.1 * H) ^ (2 * r)) ∧
      S x ≤ 2 ^ p.1 * H ∧ (p.1 = 0 ∨ 2 ^ p.1 * H / 2 < S x) ∧
      S' x ≤ 2 ^ p.2.1 * H ∧ (p.2.1 = 0 ∨ 2 ^ p.2.1 * H / 2 < S' x) ∧
      (T p.1 p.2.1 / 2 ^ (p.2.2.1 + 1) < Y x ∧ Y x ≤ 2 * (T p.1 p.2.1 / 2 ^ (p.2.2.1 + 1))) ∧
      (T p.1 p.2.1 / 2 ^ (p.2.2.2 + 1) < Y' x ∧ Y' x ≤ 2 * (T p.1 p.2.1 / 2 ^ (p.2.2.2 + 1)))}
  have hcov : ∀ᵐ x ∂ν, x ∈ ⋃ p, Q p := by
    filter_upwards [hae] with x ⟨_, _, s1, s2, y1, y2, hyy, hd, t1, t2⟩
    obtain ⟨i, hi, hi2⟩ := exists_shell (S x) H hH0
    obtain ⟨i', hi', hi2'⟩ := exists_shell (S' x) H hH0
    have a1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
    have a2 : (1 : ℝ) ≤ 2 ^ i' := one_le_pow₀ one_le_two
    have hm : max (S x) (S' x) ≤ (2 : ℝ) ^ i * 2 ^ i' * H := by
      refine max_le (hi.trans ?_) (hi'.trans ?_)
      · gcongr; exact le_mul_of_one_le_right (by positivity) a2
      · gcongr; exact le_mul_of_one_le_left (by positivity) a1
    have hm0 : 0 ≤ max (S x) (S' x) := le_max_of_le_left (by linarith)
    have hmT : (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r ≤ T i i' := by
      simp only [T]; gcongr
    obtain ⟨a, ha⟩ := exists_shell_down (Y x) (T i i') y1 (t1.trans hmT)
    obtain ⟨b, hb⟩ := exists_shell_down (Y' x) (T i i') y2 (t2.trans hmT)
    exact Set.mem_iUnion.2 ⟨(i, i', a, b),
      ⟨y1, y2, hyy, hd.trans (pow_le_pow_left₀ hm0 hm _)⟩, hi, hi2, hi', hi2', ha, hb⟩
  set C : ℝ := Real.sqrt (K * K') * ((r : ℝ) ^ (2 * r) * H ^ (24 * r ^ 3) * De ^ (2 * r) *
    (2 ^ r / D) ^ kk) with hC
  have hC0 : 0 ≤ C := by positivity
  have hpiece : ∀ p : ℕ × ℕ × ℕ × ℕ, ∫⁻ x in Q p, ENNReal.ofReal (A x * B x) ∂ν ≤
      ENNReal.ofReal C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2))) := by
    rintro ⟨i, i', a, b⟩
    rcases (Q (i, i', a, b)).eq_empty_or_nonempty with h | ⟨x0, hx0⟩
    · rw [h]; simp
    obtain ⟨⟨y1, y2, hyy, hd⟩, -, -, -, -, ⟨ha, -⟩, ⟨hb, -⟩⟩ := hx0
    dsimp only at hd ha hb ⊢
    have hTi := hT i i'
    have hyy' : T i i' / 2 ^ (a + 1) * (T i i' / 2 ^ (b + 1)) * D ≤ 2 ^ r := by
      refine le_trans ?_ hyy
      gcongr
    have key := piece_bound r kk H De D (2 ^ i) (2 ^ i') (2 ^ (a + 1)) (2 ^ (b + 1)) hr hkk hH hDe hD
      (one_le_pow₀ one_le_two) (one_le_pow₀ one_le_two) (by positivity) (by positivity) hyy' hd
    have cs := lintegral_mul_le_of_sq (ν.restrict (Q (i, i', a, b))) A B hA
      (Real.sqrt K * (((2 : ℝ) ^ i * 2 ^ i' * H) ^ (10 * r ^ 3) * (T i i' / 2 ^ (a + 1)) ^ kk *
        (((2 : ℝ) ^ i) ^ (24 * r ^ 3 + 1))⁻¹))
      (Real.sqrt K' * (((2 : ℝ) ^ i * 2 ^ i' * H) ^ (10 * r ^ 3) * (T i i' / 2 ^ (b + 1)) ^ kk *
        (((2 : ℝ) ^ i') ^ (24 * r ^ 3 + 1))⁻¹)) (by positivity) (by positivity)
      (by
        refine (lintegral_mono_set ?_).trans
          ((h1 i i' (T i i' / 2 ^ (a + 1)) (by positivity)).trans (le_of_eq ?_))
        · rintro x ⟨-, q1, q2, q3, -, ⟨q4, q5⟩, -⟩
          exact ⟨q1, q2, q3, q4, q5⟩
        · congr 1
          rw [mul_pow (Real.sqrt K), Real.sq_sqrt hK.le, pow_add (2 : ℝ) i i']
          generalize (2 : ℝ) ^ i * 2 ^ i' * H = R
          generalize T i i' / 2 ^ (a + 1) = y
          generalize (2 : ℝ) ^ i = l
          generalize 24 * r ^ 3 + 1 = q
          ring)
      (by
        refine (lintegral_mono_set ?_).trans
          ((h2 i i' (T i i' / 2 ^ (b + 1)) (by positivity)).trans (le_of_eq ?_))
        · rintro x ⟨-, q1, -, q2, q3, -, ⟨q4, q5⟩⟩
          exact ⟨q2, q3, q1, q4, q5⟩
        · congr 1
          rw [mul_pow (Real.sqrt K'), Real.sq_sqrt hK'.le, pow_add (2 : ℝ) i i']
          generalize (2 : ℝ) ^ i * 2 ^ i' * H = R
          generalize T i i' / 2 ^ (b + 1) = y
          generalize (2 : ℝ) ^ i' = l
          generalize 24 * r ^ 3 + 1 = q
          ring)
    refine cs.trans ?_
    have e : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = ENNReal.ofReal ((2 ^ n)⁻¹) := fun n => by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.inv_pow]
      simp
    rw [e, e, e, e, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_mul_mul_comm, ← Real.sqrt_mul hK.le, hC, mul_assoc (Real.sqrt (K * K'))]
    refine mul_le_mul_of_nonneg_left (key.trans ?_) (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [mul_assoc, mul_assoc]
    gcongr <;> simp
  calc ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν
      = ∫⁻ x in ⋃ p, Q p, ENNReal.ofReal (A x * B x) ∂ν := by
        rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ ∑' p, ∫⁻ x in Q p, ENNReal.ofReal (A x * B x) ∂ν := lintegral_iUnion_le _ _
    _ ≤ _ := ENNReal.tsum_le_tsum hpiece
    _ = ENNReal.ofReal C * 16 := tsum_four _
    _ = ENNReal.ofReal (C * 16) := by rw [ENNReal.ofReal_mul hC0]; simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc C * 16 ≤ C * 24 := by gcongr; norm_num
          _ = _ := by rw [hC]; ring

end GlobalTheory.Dyadic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfLintegralSmoothEq
section
open MeasureTheory

namespace GlobalTheory

theorem measure_eq_of_isOpen_isBounded_of_lintegral_smooth_eq {N : ℕ} (m₁ m₂ : Measure (Fin N → ℝ))
    (h : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U) (hb : Bornology.IsBounded U) : m₁ U = m₂ U := by

  obtain ⟨f, hfs, hfd, hfr⟩ := hU.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfr ⟨x, rfl⟩).1
  have hfU : ∀ x, x ∉ U → f x = 0 := fun x hx => by
    rw [← hfs] at hx; simpa using hx
  have hfpos : ∀ x, x ∈ U → 0 < f x := fun x hx => by
    rw [← hfs] at hx; exact lt_of_le_of_ne (hf0 x) (Ne.symm hx)

  set φ : ℕ → (Fin N → ℝ) → ℝ := fun n x => Real.smoothTransition ((n : ℝ) * f x) with hφdef
  have hφd : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) := fun n =>
    Real.smoothTransition.contDiff.comp (contDiff_const.mul hfd)
  have hφU : ∀ n x, x ∉ U → φ n x = 0 := fun n x hx => by
    simp [hφdef, hfU x hx]
  have hK : IsCompact (closure U) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hφc : ∀ n, HasCompactSupport (φ n) := fun n =>
    HasCompactSupport.intro hK fun x hx => hφU n x fun hxU => hx (subset_closure hxU)
  have hφn : ∀ n x, 0 ≤ φ n x := fun n x => Real.smoothTransition.nonneg _
  have key : ∀ m : Measure (Fin N → ℝ),
      Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (φ n x) ∂m) Filter.atTop (nhds (m U)) := by
    intro m
    rw [← lintegral_indicator_one hU.measurableSet]
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hφd n).continuous.measurable.ennreal_ofReal.aemeasurable)
      (Filter.Eventually.of_forall fun x i j hij => ?_) (Filter.Eventually.of_forall fun x => ?_)
    · exact ENNReal.ofReal_le_ofReal (Real.smoothTransition.monotone
        (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) (hf0 x)))
    · by_cases hx : x ∈ U
      · have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) * f x) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop.atTop_mul_const (hfpos x hx)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [ht.eventually_ge_atTop 1] with n hn
        simp [hφdef, Real.smoothTransition.one_of_one_le hn, hx]
      · simp [hφU _ x hx, hx]
  exact tendsto_nhds_unique (key m₁)
    ((key m₂).congr fun n => (h (φ n) (hφd n) (hφc n) (hφn n)).symm)

theorem measure_eq_of_lintegral_smooth_eq :
    ∀ (N : ℕ) (m₁ m₂ : Measure (Fin N → ℝ)) [IsFiniteMeasureOnCompacts m₂],
      (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂) →
      m₁ = m₂ := by
  intro N m₁ m₂ _ h

  let C : Set (Set (Fin N → ℝ)) := {s | IsOpen s ∧ Bornology.IsBounded s}
  have hgen : (inferInstance : MeasurableSpace (Fin N → ℝ)) = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · rw [BorelSpace.measurable_eq (α := Fin N → ℝ)]
      refine MeasurableSpace.generateFrom_le fun s hs => ?_
      have hs' : s = ⋃ n : ℕ, s ∩ Metric.ball 0 ((n : ℝ) + 1) := by
        rw [← Set.inter_iUnion, Metric.iUnion_ball_nat_succ, Set.inter_univ]
      rw [hs']
      exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        ⟨by exact IsOpen.inter hs Metric.isOpen_ball, Metric.isBounded_ball.subset Set.inter_subset_right⟩
    · exact MeasurableSpace.generateFrom_le fun s hs => hs.1.measurableSet
  have hpi : IsPiSystem C := fun s hs t ht _ =>
    ⟨hs.1.inter ht.1, hs.2.subset Set.inter_subset_left⟩
  refine (Measure.ext_of_generateFrom_of_iUnion C (fun n : ℕ => Metric.ball (0 : Fin N → ℝ) ((n : ℝ) + 1))
    hgen hpi (Metric.iUnion_ball_nat_succ _) (fun n => ⟨Metric.isOpen_ball, Metric.isBounded_ball⟩)
    (fun n => measure_ball_lt_top.ne) fun s hs => ?_).symm
  exact (measure_eq_of_isOpen_isBounded_of_lintegral_smooth_eq m₁ m₂ h s hs.1 hs.2).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreimageReindexScaleComplexLe
section
namespace GlobalTheory.CoordScale
open MeasureTheory

theorem sigmaFinite_smul {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ENNReal}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  have h : c • μ = c.toNNReal • μ := by
    rw [ENNReal.smul_def, ENNReal.coe_toNNReal hc]
  rw [h]
  infer_instance

theorem pi_smul_ne_top {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → ENNReal) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  have : ∀ i, SigmaFinite (c i • μ i) := fun i => sigmaFinite_smul (μ i) (hc i)
  refine Measure.pi_eq (fun s hs => ?_)
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]

theorem measurePreserving_inv_mul (r : ℝ) (hr : 0 < r) :
    MeasurePreserving (fun z : ℂ => ((r : ℂ))⁻¹ * z) volume
      (ENNReal.ofReal (r ^ 2) • (volume : Measure ℂ)) := by
  refine ⟨measurable_id.const_mul _, ?_⟩
  have hfun : (fun z : ℂ => ((r : ℂ))⁻¹ * z) = fun z => (r⁻¹ : ℝ) • z := by
    funext z
    rw [Complex.real_smul, Complex.ofReal_inv]
  rw [hfun, Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), Complex.finrank_real_complex,
    inv_pow, inv_inv, abs_of_pos (by positivity)]

private theorem map_pi_reindex_eq_pi_of_map_eq {ι ι' β γ : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace β]
    [MeasurableSpace γ] (e : ι ≃ ι') (μ : Measure β) [SigmaFinite μ] (ν : ι → Measure γ)
    [∀ i, SigmaFinite (ν i)] (h : ι → β → γ) (hh : ∀ i, Measurable (h i))
    (hmap : ∀ i, Measure.map (h i) μ = ν i) :
    Measure.map (fun (x : ι' → β) (i : ι) => h i (x (e i))) (Measure.pi fun _ => μ) =
      Measure.pi ν := by
  have hm : Measurable (fun (x : ι' → β) (i : ι) => h i (x (e i))) :=
    measurable_pi_lambda _ (fun i => (hh i).comp (measurable_pi_apply (e i)))
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : ι' → β) (i : ι) => h i (x (e i))) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i' => h (e.symm i') ⁻¹' s (e.symm i')) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro hx i'
      have := hx (e.symm i')
      rwa [Equiv.apply_symm_apply] at this
    · intro hx i
      have := hx (e i)
      rwa [Equiv.symm_apply_apply] at this
  rw [hpre, Measure.pi_pi]
  refine (Finset.prod_congr rfl (fun i' _ => ?_)).trans (Equiv.prod_comp e.symm (fun i => ν i (s i)))
  rw [← hmap (e.symm i'), Measure.map_apply (hh _) (hs _)]

theorem measure_preimage_reindex_scale_le : ∀ (ι ι' κ κ' : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ') (ρ c : ℝ) (d : κ → ℕ), 1 ≤ ρ → c ≤ 1 → ∀ A : Set (ι → κ → ℂ), MeasurableSet A → (MeasureTheory.Measure.pi fun _ : ι' => MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ((fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
  intro ι ι' κ κ' _ _ _ _ e f ρ c d hρ hc A hA
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  set C : ENNReal := ENNReal.ofReal c with hCdef
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have : SigmaFinite (C • (volume : Measure ℂ)) := sigmaFinite_smul _ hCt
  set w : κ → ENNReal := fun q => C * ENNReal.ofReal ((ρ ^ d q) ^ 2) with hwdef
  have hwt : ∀ q, w q ≠ ⊤ := fun q => ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  have : ∀ q, SigmaFinite (w q • (volume : Measure ℂ)) := fun q => sigmaFinite_smul _ (hwt q)
  have hin : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) =
      Measure.pi fun q : κ => w q • (volume : Measure ℂ) := by
    refine map_pi_reindex_eq_pi_of_map_eq f (C • (volume : Measure ℂ)) (fun q => w q • (volume : Measure ℂ))
      (fun q z => ((ρ : ℂ) ^ d q)⁻¹ * z) (fun q => measurable_id.const_mul _) (fun q => ?_)
    show Measure.map (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) (C • volume) = w q • volume
    have hfun : (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) = fun z => (((ρ ^ d q : ℝ) : ℂ))⁻¹ * z := by
      funext z
      rw [Complex.ofReal_pow]
    rw [Measure.map_smul, hfun, (measurePreserving_inv_mul (ρ ^ d q) (pow_pos hρ0 _)).map_eq,
      smul_smul]
  set K : ENNReal := ∏ q, w q with hKdef
  have hKt : K ≠ ⊤ := ENNReal.prod_ne_top (fun q _ => hwt q)
  have hin' : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) = K • (volume : Measure (κ → ℂ)) := by
    rw [hin, pi_smul_ne_top (fun _ => (volume : Measure ℂ)) w hwt]
    rfl
  have : SigmaFinite (K • (volume : Measure (κ → ℂ))) := sigmaFinite_smul _ hKt
  have hinm : Measurable (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) :=
    measurable_pi_lambda _ (fun q => (measurable_pi_apply (f q)).const_mul _)
  have hout : Measure.map (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q))
      (MeasureTheory.Measure.pi fun _ : ι' =>
        MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) =
      (K ^ Fintype.card ι) • (volume : Measure (ι → κ → ℂ)) := by
    have h1 := map_pi_reindex_eq_pi_of_map_eq e (Measure.pi fun _ : κ' => C • (volume : Measure ℂ))
      (fun _ : ι => K • (volume : Measure (κ → ℂ)))
      (fun _ (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) (fun _ => hinm) (fun _ => hin')
    refine h1.trans ?_
    rw [pi_smul_ne_top (fun _ : ι => (volume : Measure (κ → ℂ))) (fun _ => K) (fun _ => hKt),
      Finset.prod_const, Finset.card_univ]
    rfl
  have hgm : Measurable (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) :=
    measurable_pi_lambda _ (fun i => hinm.comp (measurable_pi_apply (e i)))
  rw [← Measure.map_apply hgm hA, hout, Measure.smul_apply, smul_eq_mul, mul_comm]
  have hC1 : C ≤ 1 := ENNReal.ofReal_le_one.mpr hc
  have hK1 : K ≤ ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) := by
    refine Finset.prod_le_prod' (fun q _ => ?_)
    calc w q = C * ENNReal.ofReal ((ρ ^ d q) ^ 2) := rfl
      _ ≤ 1 * ENNReal.ofReal ((ρ ^ d q) ^ 2) := by gcongr
      _ = ENNReal.ofReal ((ρ ^ d q) ^ 2) := one_mul _
  have hprod : ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) = ENNReal.ofReal (∏ q, (ρ ^ d q) ^ 2) :=
    (ENNReal.ofReal_prod_of_nonneg (fun q _ => by positivity)).symm
  have hreal : (∏ q, (ρ ^ d q) ^ 2) ^ Fintype.card ι = ρ ^ (2 * Fintype.card ι * ∑ q, d q) := by
    rw [Finset.prod_pow, Finset.prod_pow_eq_pow_sum, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hK2 : K ^ Fintype.card ι ≤ ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
    rw [← hreal, ENNReal.ofReal_pow (by positivity), ← hprod]
    exact pow_le_pow_left' hK1 _
  gcongr

end GlobalTheory.CoordScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
section
open NumberField

namespace GlobalTheory

theorem ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
      (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) →
        Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) →
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  intro E _ _ p hp h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  haveI hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := Ideal.span {(p : ℤ)}) hp0
  rw [← hsum, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    simp [Ideal.map_span]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hmem : (p : 𝓞 E) ∈ P := by
    rw [hmap, Ideal.span_singleton_le_iff_mem] at hle
    exact hle
  have hPm : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  obtain ⟨hN, hsq⟩ := h P hPm hmem
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff hle).mp hne
    rw [hmap, Ideal.span_singleton_le_iff_mem] at this
    exact hsq this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hp
    rw [hN] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end GlobalTheory
end


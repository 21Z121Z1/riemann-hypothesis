import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeNatCastIff
section
namespace GlobalTheory.AxSen

variable {K : Type} [Field K]

def Ge (A : ValuationSubring K) (ϖ w : K) (q : ℚ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℚ) ≤ q * b → A.valuation w ^ b ≤ A.valuation ϖ ^ a

variable {A : ValuationSubring K} {ϖ : K}

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.ge_zero (q : ℚ) : _root_.GlobalTheory.AxSen.Ge A ϖ 0 q := by
  intro a b hb _
  rw [map_zero, zero_pow hb.ne']
  exact zero_le'

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.mono {w : K} {q q' : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (hq : q' ≤ q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w q' :=
  fun a b hb hab => h a b hb (hab.trans (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg b)))

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.of_le {w w' : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (hw : A.valuation w' ≤ A.valuation w) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w' q :=
  fun a b hb hab => (pow_le_pow_left' hw b).trans (h a b hb hab)

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.add {w w' : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (h' : _root_.GlobalTheory.AxSen.Ge A ϖ w' q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ (w + w') q := by
  rcases le_total (A.valuation w) (A.valuation w') with hle | hle
  · exact h'.of_le ((Valuation.map_add _ _ _).trans (max_le hle le_rfl))
  · exact h.of_le ((Valuation.map_add _ _ _).trans (max_le le_rfl hle))

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.symm {x y : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (x - y) q) : _root_.GlobalTheory.AxSen.Ge A ϖ (y - x) q :=
  h.of_le (by rw [Valuation.map_sub_swap])

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.trans {x y z : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (x - y) q) (h' : _root_.GlobalTheory.AxSen.Ge A ϖ (y - z) q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ (x - z) q := by
  have := h.add h'
  rwa [sub_add_sub_cancel] at this

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.mul (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1)
    {w w' : K} {q q' : ℚ} (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q)
    (h' : _root_.GlobalTheory.AxSen.Ge A ϖ w' q') :
    _root_.GlobalTheory.AxSen.Ge A ϖ (w * w') (q + q') := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hd : 0 < q.den := q.den_pos
  have hd' : 0 < q'.den := q'.den_pos
  have h₁ := h (q.num * q'.den * b) (q.den * q'.den * b) (by positivity)
    (le_of_eq (by push_cast; rw [← Rat.mul_den_eq_num q]; ring))
  have h₂ := h' (q'.num * q.den * b) (q.den * q'.den * b) (by positivity)
    (le_of_eq (by push_cast; rw [← Rat.mul_den_eq_num q']; ring))
  have hexp : a * ((q.den * q'.den : ℕ) : ℤ) ≤ (q.num * q'.den * b + q'.num * q.den * b) := by
    have hq : ((a * ((q.den * q'.den : ℕ) : ℤ) : ℤ) : ℚ)
        ≤ ((q.num * q'.den * b + q'.num * q.den * b : ℤ) : ℚ) := by
      push_cast
      rw [← Rat.mul_den_eq_num q, ← Rat.mul_den_eq_num q']
      have hdd : (0 : ℚ) ≤ q.den * q'.den := by positivity
      calc (a : ℚ) * (q.den * q'.den) ≤ ((q + q') * b) * (q.den * q'.den) :=
            mul_le_mul_of_nonneg_right hab hdd
        _ = _ := by ring
    exact_mod_cast hq
  have key : (A.valuation (w * w') ^ b) ^ (q.den * q'.den)
      ≤ (A.valuation ϖ ^ a) ^ (q.den * q'.den) := by
    calc (A.valuation (w * w') ^ b) ^ (q.den * q'.den)
        = A.valuation w ^ (q.den * q'.den * b) * A.valuation w' ^ (q.den * q'.den * b) := by
          rw [map_mul, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm b]
      _ ≤ A.valuation ϖ ^ (q.num * q'.den * b) * A.valuation ϖ ^ (q'.num * q.den * b) :=
          mul_le_mul' h₁ h₂
      _ = A.valuation ϖ ^ (q.num * q'.den * b + q'.num * q.den * b) := by
          rw [← zpow_add₀ hv]
      _ ≤ A.valuation ϖ ^ (a * ((q.den * q'.den : ℕ) : ℤ)) :=
          zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv) h1 hexp
      _ = (A.valuation ϖ ^ a) ^ (q.den * q'.den) := by rw [zpow_mul, zpow_natCast]
  exact (pow_le_pow_iff_left₀ zero_le' zero_le' (by positivity)).1 key

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.root {w : K} {q : ℚ} {N : ℕ} (hN : 0 < N)
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (w ^ N) (q * N)) : _root_.GlobalTheory.AxSen.Ge A ϖ w q := by
  intro a b hb hab
  have h₁ := h (a * N) b hb (by
    push_cast
    calc (a : ℚ) * N ≤ q * b * N := mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N)
      _ = q * N * b := by ring)
  refine (pow_le_pow_iff_left₀ zero_le' zero_le' hN.ne').1 ?_
  calc (A.valuation w ^ b) ^ N = A.valuation (w ^ N) ^ b := by
        rw [map_pow, ← pow_mul, ← pow_mul, mul_comm]
    _ ≤ A.valuation ϖ ^ (a * (N : ℤ)) := h₁
    _ = (A.valuation ϖ ^ a) ^ N := by rw [zpow_mul, zpow_natCast]

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.div (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1)
    {c w : K} {q : ℚ} {e : ℕ} (hc : A.valuation ϖ ^ e ≤ A.valuation c)
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (c * w) q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w (q - e) := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hc0 : A.valuation c ≠ 0 := by
    intro hc0
    rw [hc0] at hc
    exact pow_ne_zero e hv (le_zero_iff.1 hc)
  have h₁ := h (a + e * b) b hb (by push_cast; linarith [hab, sub_mul q (e : ℚ) b])
  rw [map_mul, mul_pow, zpow_add₀ hv] at h₁
  have h₂ : A.valuation ϖ ^ ((e : ℤ) * (b : ℤ)) ≤ A.valuation c ^ b := by
    rw [zpow_mul, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left' hc b
  refine (mul_le_mul_iff_of_pos_right (zero_lt_iff.2 (pow_ne_zero b hc0))).1 ?_
  calc A.valuation w ^ b * A.valuation c ^ b = A.valuation c ^ b * A.valuation w ^ b := mul_comm _ _
    _ ≤ A.valuation ϖ ^ a * A.valuation ϖ ^ ((e : ℤ) * (b : ℤ)) := h₁
    _ ≤ A.valuation ϖ ^ a * A.valuation c ^ b := mul_le_mul' le_rfl h₂

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.ge_natCast_iff (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) {w : K}
    {m : ℕ} : _root_.GlobalTheory.AxSen.Ge A ϖ w m ↔ ∃ z ∈ A, w = ϖ ^ m * z := by
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  constructor
  · intro h
    have h₁ := h m 1 one_pos (by simp)
    rw [pow_one, zpow_natCast, ← map_pow] at h₁
    refine ⟨w / ϖ ^ m, ?_, by field_simp⟩
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
    exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero m h0)))).2 h₁
  · rintro ⟨z, hz, rfl⟩ a b hb hab
    have hz' : A.valuation z ≤ 1 := (ValuationSubring.valuation_le_one_iff A z).2 hz
    have hab' : a ≤ ((m * b : ℕ) : ℤ) := by
      have : (a : ℚ) ≤ ((m * b : ℕ) : ℚ) := by push_cast; exact hab
      exact_mod_cast this
    rw [map_mul, mul_pow, map_pow]
    calc (A.valuation ϖ ^ m) ^ b * A.valuation z ^ b ≤ (A.valuation ϖ ^ m) ^ b * 1 :=
          mul_le_mul' le_rfl (pow_le_one' hz' b)
      _ = A.valuation ϖ ^ ((m * b : ℕ) : ℤ) := by rw [mul_one, ← pow_mul, zpow_natCast]
      _ ≤ A.valuation ϖ ^ a := zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv) h1 hab'

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in

theorem _root_.GlobalTheory.AxSen.Ge.map (h0 : ϖ ≠ 0) (f : K →+* K)
    (hf : ∀ x ∈ A, f x ∈ A) (hϖ : f ϖ = ϖ) {w : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) : _root_.GlobalTheory.AxSen.Ge A ϖ (f w) q := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h₁ := h a b hb hab
  have hpos : 0 < A.valuation ϖ ^ a := zero_lt_iff.2 (zpow_ne_zero a hv)
  rw [← div_le_one₀ hpos, ← map_pow, ← map_zpow₀, ← map_div₀,
    ValuationSubring.valuation_le_one_iff] at h₁ ⊢
  have := hf _ h₁
  rwa [map_div₀, map_pow, map_zpow₀, hϖ] at this

end GlobalTheory.AxSen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianLatticeNormOneOfNormOneModPrime
section
namespace GlobalTheory

theorem exists_lattice_norm_one_of_norm_one_mod (K V : Type) [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K)
    (O : Subring K) (L : AddSubgroup V) (hp : p.Prime) (_hd : d.Prime) (hθ : θ ^ 2 = -(d : K))
    (hσ : σ θ = -θ) (hK : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ)
    (hOσ : ∀ x ∈ O, σ x ∈ O) (hω : (1 + θ) / 2 ∈ O)
    (hO : ∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) (hh : ∀ x y : V, h y x = σ (h x y))
    (_hdef : ∀ x : V, h x x = 0 → x = 0) (hL : ∀ a ∈ O, ∀ x ∈ L, a • x ∈ L)
    (_hint : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) (hfull : ∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L)
    (W : Submodule K V) (he : ∃ e ∈ W, h e e = 1)
    (hy : ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1) :
    ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, heW, hee⟩ := he
  obtain ⟨y₀, hy₀L, hy₀W, u₀, hu₀, hr⟩ := hy
  have hσω : σ ((1 + θ) / 2) = (1 - θ) / 2 := by
    rw [map_div₀, map_add, map_one, hσ, map_ofNat, sub_eq_add_neg]
  have hn : padicNorm p ((1 + d) / 4) ≤ 1 := by
    rw [← hO]
    have := O.mul_mem hω (hOσ _ hω)
    rw [hσω] at this
    convert this using 1
    push_cast
    linear_combination (1 / 4 : K) * hθ

  have step : ∀ y ∈ L, y ∈ W → ∀ u : ℚ, h y y = (u : K) → padicNorm p (u - 1) ≤ 1 →
      ∃ y' ∈ L, y' ∈ W ∧ ∃ u' : ℚ, h y' y' = (u' : K) ∧
        padicNorm p (u' - 1) ≤ padicNorm p (u - 1) * padicNorm p (u - 1) := by
    intro y hyL hyW u hu hu1
    have hc : ((1 - u : ℚ) : K) ∈ O := by
      rw [hO, ← padicNorm.neg]; simpa using hu1
    have hu' : padicNorm p u ≤ 1 := by
      have := padicNorm.nonarchimedean (p := p) (q := u - 1) (r := 1)
      rw [sub_add_cancel, padicNorm.one] at this
      exact this.trans (max_le hu1 le_rfl)
    refine ⟨(1 + ((1 - u : ℚ) : K) * ((1 + θ) / 2)) • y,
      hL _ (O.add_mem O.one_mem (O.mul_mem hc hω)) y hyL, W.smul_mem _ hyW,
      1 + (u - 1) * (u - 1) * ((1 + d) / 4 * u - 1), ?_, ?_⟩
    · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hu, map_add, map_mul,
        map_one, hσω, map_ratCast]
      push_cast
      linear_combination (-(1 - (u : K)) ^ 2 * u / 4) * hθ
    · rw [add_sub_cancel_left, padicNorm.mul, padicNorm.mul]
      have h1 : padicNorm p ((1 + d) / 4 * u - 1) ≤ 1 := by
        refine padicNorm.sub.trans (max_le ?_ (by rw [padicNorm.one]))
        rw [padicNorm.mul]
        exact mul_le_one₀ hn (padicNorm.nonneg _) hu'
      exact mul_le_of_le_one_right
        (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)) h1
  have hr0 : 0 ≤ padicNorm p (u₀ - 1) := padicNorm.nonneg _
  have iter : ∀ k : ℕ, ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧
      padicNorm p (u - 1) ≤ padicNorm p (u₀ - 1) ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨y₀, hy₀L, hy₀W, u₀, hu₀, by simp⟩
    | succ k ih =>
      obtain ⟨y, hyL, hyW, u, hu, hk⟩ := ih
      have hk1 : padicNorm p (u - 1) ≤ padicNorm p (u₀ - 1) :=
        hk.trans (by
          rw [pow_succ]
          exact mul_le_of_le_one_left hr0 (pow_le_one₀ hr0 hr.le))
      obtain ⟨y', hy'L, hy'W, u', hu', hle⟩ := step y hyL hyW u hu (hk1.trans hr.le)
      refine ⟨y', hy'L, hy'W, u', hu', hle.trans ?_⟩
      rw [pow_succ _ (k + 1)]
      exact mul_le_mul hk hk1 (padicNorm.nonneg _) (pow_nonneg hr0 _)
  obtain ⟨m, hm⟩ := hfull e
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpos : ∀ q : ℚ, q ≠ 0 → 0 < padicNorm p q := fun q hq =>
    lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hq).symm
  have hP0 : 0 < padicNorm p ((p : ℚ) ^ m) := hpos _ (pow_ne_zero _ hp0)
  have hP1 : padicNorm p ((p : ℚ) ^ m) ≤ 1 := by
    have := padicNorm.of_nat (p := p) (p ^ m)
    rwa [Nat.cast_pow] at this
  have h40 : 0 < padicNorm p 4 := hpos _ (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos h40 hP0) hr
  obtain ⟨y, hyL, hyW, u, hu, hyk⟩ := iter k
  have hsmall : padicNorm p (u - 1) < padicNorm p 4 * padicNorm p ((p : ℚ) ^ m) := by
    refine lt_of_le_of_lt (hyk.trans ?_) hk
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hr0 _) hr.le

  have secant : ∀ y ∈ L, y ∈ W → h y y = (u : K) → ∀ T : ℚ, h e y + h y e = (T : K) →
      padicNorm p 4 ≤ padicNorm p (u + 1 - T) → ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
    intro y hyL hyW hu T hT hQ
    have hQpos : 0 < padicNorm p (u + 1 - T) := h40.trans_le hQ
    have hQ0 : u + 1 - T ≠ 0 := by
      intro h0; rw [h0, padicNorm.zero] at hQpos; exact lt_irrefl _ hQpos
    set t : ℚ := (1 - u) / ((u + 1 - T) * (p : ℚ) ^ m) with ht
    have htO : (t : K) ∈ O := by
      rw [hO, ht, padicNorm.div, padicNorm.mul, div_le_one (mul_pos hQpos hP0), ← padicNorm.neg,
        neg_sub]
      exact hsmall.le.trans (mul_le_mul_of_nonneg_right hQ hP0.le)
    have hpO : (p : K) ^ m ∈ O := O.pow_mem (natCast_mem O p) m
    have hs : t * (p : ℚ) ^ m * (u + 1 - T) = 1 - u := by
      rw [ht]; field_simp
    have hs' : (t : K) * (p : K) ^ m * (u + 1 - T) = 1 - u := by
      exact_mod_cast congrArg (fun q : ℚ => (q : K)) hs
    refine ⟨y + ((t : K) * (p : K) ^ m) • y - (t : K) • ((p : K) ^ m • e),
      L.sub_mem (L.add_mem hyL (hL _ (O.mul_mem htO hpO) y hyL)) (hL _ htO _ hm),
      W.sub_mem (W.add_mem hyW (W.smul_mem _ hyW)) (W.smul_mem _ (W.smul_mem _ heW)), ?_⟩
    simp only [map_smul, map_smulₛₗ, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, smul_eq_mul, hu, hee, map_mul, map_pow, map_ratCast, map_natCast,
      RingHom.id_apply]
    linear_combination (1 + (t : K) * (p : K) ^ m) * hs' -
      ((t : K) * (p : K) ^ m) * (1 + (t : K) * (p : K) ^ m) * hT
  obtain ⟨T, hT⟩ : ∃ T : ℚ, h e y + h y e = (T : K) := by
    obtain ⟨a, b, hab⟩ := hK (h e y)
    refine ⟨2 * a, ?_⟩
    rw [hh e y, hab, map_add, map_mul, map_ratCast, map_ratCast, hσ]
    push_cast
    ring
  by_cases hQ : padicNorm p 4 ≤ padicNorm p (u + 1 - T)
  · exact secant y hyL hyW hu T hT hQ
  · refine secant (-y) (L.neg_mem hyL) (W.neg_mem hyW) (by simpa using hu) (-T)
      (by
        simp only [map_neg, LinearMap.neg_apply]
        push_cast
        linear_combination -hT) ?_
    by_contra hQ'
    push Not at hQ hQ'
    have h2 : padicNorm p (2 * (u - 1)) < padicNorm p 4 := by
      rw [padicNorm.mul]
      have h21 : padicNorm p 2 ≤ 1 := by simpa using padicNorm.of_nat (p := p) 2
      refine lt_of_le_of_lt (mul_le_of_le_one_left (padicNorm.nonneg _) h21) ?_
      exact hsmall.trans_le (mul_le_of_le_one_right h40.le hP1)
    have h3 : padicNorm p 4 < padicNorm p 4 := by
      calc padicNorm p 4
          = padicNorm p ((u + 1 - T) + (u + 1 - -T) - 2 * (u - 1)) := by congr 1; ring
        _ ≤ _ := padicNorm.sub
        _ < padicNorm p 4 :=
          max_lt (lt_of_le_of_lt padicNorm.nonarchimedean (max_lt hQ hQ')) h2
    exact lt_irrefl _ h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsBis
section
namespace GlobalTheory.AlgebraicIntegerNormBound

theorem main : ∀ {A : Type} [inst : CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Ideal.IsPrime Q], Q ≠ ⊥ → ∀ {π : A}, π ∈ Q → π ∉ Q ^ (2 : ℕ) → ∀ (m : ℕ), π ^ m ∉ Q ^ (m + (1 : ℕ)) := by
  intro A _ _ Q hQ hQ0 π h1 h2 m hm
  have hP : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
  rw [← Ideal.dvd_span_singleton] at h1 h2 hm
  obtain ⟨J, hJ⟩ := h1
  have hJQ : ¬ Q ∣ J := by
    rintro ⟨K, hK⟩
    apply h2
    exact ⟨K, by rw [hJ, hK, pow_two, mul_assoc]⟩
  rw [← Ideal.span_singleton_pow, hJ, mul_pow, pow_succ] at hm
  have hQm : Q ^ m ≠ 0 := pow_ne_zero _ hQ0
  rw [mul_dvd_mul_iff_left hQm] at hm
  exact hJQ (hP.dvd_of_dvd_pow hm)

end GlobalTheory.AlgebraicIntegerNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsFurther
section
namespace GlobalTheory.DeterminantSimpLemma

open NumberField

theorem main {K : Type} [inst : Field K] [NumberField K] {n : ℕ}
    {M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)} {x : Fin n → K} :
    x ∈ Submodule.span K (↑M : Set (Fin n → K)) →
      ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ M := by
  intro hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (algebraMap (𝓞 K) K b) ≠ 0 := by
      simpa using hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have key : (b * d) • (c • y) = a • (d • y) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d,
        smul_smul, smul_smul]
      congr 1
      rw [← hab, map_mul]
      field_simp
    rw [key]
    exact M.smul_mem _ h

end GlobalTheory.DeterminantSimpLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsMore
section
namespace GlobalTheory.ComplexValueBound

open Finset

theorem main : ∀ {ι κ M : Type} [inst : AddCommGroup M] [inst_1 : Module ℂ M] (T : κ → M →ₗ[ℂ] M) (l : ι → κ → ℂ), (∀ (i j : ι), i ≠ j → ∃ (k : κ), l i k ≠ l j k) → ∀ (s : Finset ι) (u : ι → M), (∀ (i : ι) (k : κ), (T k : M → M) (u i) = l i k • u i) → ∑ i ∈ s, u i = (0 : M) → ∀ i ∈ s, u i = (0 : M) := by
  intro ι κ M _ _ T l hl s
  classical
  induction s using Finset.induction_on with
  | empty => intro u _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro u hu hsum
    rw [Finset.sum_insert ha] at hsum
    have hsa : ∑ i ∈ s, u i = -u a := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hsum
    have hs : ∀ j ∈ s, u j = 0 := by
      intro j hj
      have hne : a ≠ j := fun h => ha (h ▸ hj)
      obtain ⟨k, hk⟩ := hl a j hne
      have hvu : ∀ (i : ι) (k' : κ), (T k' : M → M) ((l i k - l a k) • u i)
          = l i k' • ((l i k - l a k) • u i) := by
        intro i k'
        rw [LinearMap.map_smul, hu, smul_comm]
      have hvsum : ∑ i ∈ s, (l i k - l a k) • u i = 0 := by
        have h1 : ∑ i ∈ s, (l i k - l a k) • u i
            = T k (∑ i ∈ s, u i) - l a k • ∑ i ∈ s, u i := by
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hu, sub_smul]
        rw [h1, hsa, map_neg, hu, smul_neg, sub_neg_eq_add, neg_add_cancel]
      have h := ih (fun i => (l i k - l a k) • u i) hvu hvsum j hj
      exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hk))
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have h0 : ∑ i ∈ s, u i = 0 := Finset.sum_eq_zero hs
      rw [h0, add_zero] at hsum; exact hsum
    · exact hs i hi

end GlobalTheory.ComplexValueBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsTer
section
namespace GlobalTheory.SpanScalarMembership

open NumberField

theorem exists_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (T : Submodule (RingOfIntegers K) V) {x : V} (hx : x ∈ Submodule.span K (T : Set V)) :
    ∃ s : RingOfIntegers K, s ≠ 0 ∧ s • x ∈ T := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact T.smul_mem t hsy
    · rw [mul_smul]; exact T.smul_mem s htz
  | smul a y _ hy =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers K) a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap (RingOfIntegers K) K q ≠ 0 := by
      intro h
      exact hq0 ((IsFractionRing.injective (RingOfIntegers K) K) (by rw [h, map_zero]))
    refine ⟨s * q, mul_ne_zero hs hq0, ?_⟩
    have key : (s * q) • ((algebraMap (RingOfIntegers K) K p / algebraMap (RingOfIntegers K) K q) • y)
        = p • (s • y) := by
      rw [← algebraMap_smul K (s * q), ← algebraMap_smul K p, ← algebraMap_smul K s,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact T.smul_mem p hsy

end GlobalTheory.SpanScalarMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsMemSubalgebraOfFiniteTypeAlgebra
section
open Polynomial

namespace GlobalTheory

theorem jets_mem_subalgebra_of_finiteType : ∀ (k A R : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (N : ℕ) (Δ : ℕ → A →ₗ[k] R), Δ 0 1 = 1 → (∀ l, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w)) →
 ∃ T : Finset R, ∀ S : Subalgebra k R, (∀ t ∈ T, t ∈ S) → ∀ l < N, ∀ u, Δ l u ∈ S := by
  intro k A R _ _ _ _ _ _ N Δ _ hL
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  refine ⟨(Finset.range N ×ˢ insert 1 s).image (fun x => Δ x.1 x.2), ?_⟩
  intro S hT l hl u
  have key : ∀ u ∈ Algebra.adjoin k (s : Set A), ∀ l < N, Δ l u ∈ S := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx =>
      intro l hl
      exact hT _ (Finset.mem_image.2 ⟨(l, x), by simp [hl, Finset.mem_coe.1 hx], rfl⟩)
    | algebraMap c =>
      intro l hl
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
      exact S.smul_mem (hT _ (Finset.mem_image.2 ⟨(l, 1), by simp [hl], rfl⟩)) c
    | add x y _ _ hx hy =>
      intro l hl
      rw [map_add]
      exact S.add_mem (hx l hl) (hy l hl)
    | mul x y _ _ hx hy =>
      intro l hl
      rw [hL]
      refine S.sum_mem (fun p hp => nsmul_mem (S.mul_mem (hx p ?_) (hy (l - p) ?_)) _)
      · have := Finset.mem_range.1 hp; omega
      · omega
  exact key u (hs ▸ Algebra.mem_top) l hl

end GlobalTheory
end


import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefect
section
namespace GlobalTheory.FrobeniusDefect

open Matrix

variable {R : Type} [CommRing R] {d : ℕ}

theorem nzd_mul {a b : R} (ha : ∀ x : R, a * x = 0 → x = 0) (hb : ∀ x : R, b * x = 0 → x = 0) :
    ∀ x : R, (a * b) * x = 0 → x = 0 :=
  fun x h => hb x (ha _ (by rw [← mul_assoc]; exact h))

theorem nzd_pow {a : R} (ha : ∀ x : R, a * x = 0 → x = 0) :
    ∀ n : ℕ, ∀ x : R, a ^ n * x = 0 → x = 0
  | 0 => fun x h => by simpa using h
  | n + 1 => by rw [pow_succ]; exact nzd_mul (nzd_pow ha n) ha

theorem nzd_unit {a : R} (ha : ∀ x : R, a * x = 0 → x = 0) (v : Rˣ) :
    ∀ x : R, (a * v) * x = 0 → x = 0 :=
  nzd_mul ha (fun x h => by simpa using congrArg (fun y => (↑v⁻¹ : R) * y) h)

theorem smul_cancel {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {M N : Matrix (Fin d) (Fin d) R} (h : c • M = c • N) : M = N := by
  ext i j
  have := congrArg (fun P => P i j) h
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.mp (hc _ (by rw [mul_sub, this, sub_self]))

theorem mul_left_of {c : R} {P P' : Matrix (Fin d) (Fin d) R} (h : P * P' = c • 1)
    (X : Matrix (Fin d) (Fin d) R) : P * (P' * X) = c • X := by
  rw [← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul]

theorem left_cancel {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {P P' : Matrix (Fin d) (Fin d) R} (h : P' * P = c • 1)
    {X Y : Matrix (Fin d) (Fin d) R} (hXY : P * X = P * Y) : X = Y :=
  smul_cancel hc (by rw [← mul_left_of h X, ← mul_left_of h Y, hXY])

theorem mul_comm_of_nzd {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {M M' : Matrix (Fin d) (Fin d) R} (h : M * M' = c • 1) : M' * M = c • 1 := by
  have hdet : M.det * M'.det = c ^ d := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hdM : ∀ x : R, M.det * x = 0 → x = 0 := fun x hx =>
    nzd_pow hc d x (by rw [← hdet, mul_comm M.det, mul_assoc, hx, mul_zero])
  have h0 : M * (M' * M - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self]
  have h1 : M.det • (M' * M - c • 1) = M.det • (0 : Matrix (Fin d) (Fin d) R) := by
    calc M.det • (M' * M - c • 1)
          = (M.det • (1 : Matrix (Fin d) (Fin d) R)) * (M' * M - c • 1) := by
            rw [Matrix.smul_mul, Matrix.one_mul]
      _ = M.adjugate * M * (M' * M - c • 1) := by rw [Matrix.adjugate_mul]
      _ = M.det • (0 : Matrix (Fin d) (Fin d) R) := by rw [Matrix.mul_assoc, h0, Matrix.mul_zero, smul_zero]
  exact sub_eq_zero.mp (smul_cancel hdM h1)

theorem map_smul_one (f : R →+* R) (c : R) :
    (c • (1 : Matrix (Fin d) (Fin d) R)).map f = f c • (1 : Matrix (Fin d) (Fin d) R) := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem map_smul' (f : R →+* R) (c : R) (M : Matrix (Fin d) (Fin d) R) :
    (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobenius_defect_eq (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R)
    (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R)
    (hlr : ∀ x : R, lr * x = 0 → x = 0) (hev : ∃ v : Rˣ, e = lr * v) (he₀v : ∃ v : Rˣ, e₀ = lr * v)
    (hφσ : ∀ x, φ (σ x) = σ (φ x)) (hφlr : φ lr = lr) (hσlr : σ lr = lr) (hσe₀ : σ e₀ = e₀)
    (hA₀σ : A₀.map σ = A₀)
    (hQQ' : Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R))
    (hBB' : B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hAA' : A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hQA : e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ))
    (hεB : e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ)) :
    e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) =
      A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  obtain ⟨v, hv⟩ := hev
  obtain ⟨v₀, hv₀⟩ := he₀v
  have he : ∀ x : R, e * x = 0 → x = 0 := by rw [hv]; exact nzd_unit hlr v
  have he₀ : ∀ x : R, e₀ * x = 0 → x = 0 := by rw [hv₀]; exact nzd_unit hlr v₀
  have hσe : ∀ x : R, σ e * x = 0 → x = 0 := by
    have : σ e = lr * ((Units.map (σ : R →* R) v : Rˣ) : R) := by
      rw [hv, map_mul, hσlr]; rfl
    rw [this]; exact nzd_unit hlr _
  have hL := nzd_pow hlr (2 * k)
  have hB'B : B' * B = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) :=
    mul_comm_of_nzd (nzd_pow he _) hBB'
  have hσBB' : B.map σ * B'.map σ = σ e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, hBB', map_smul_one, map_pow]
  have hφQ'Q : Q'.map φ * Q.map φ = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, mul_comm_of_nzd hL hQQ', map_smul_one, map_pow, hφlr]

  have h1 : B' * (Q * A₀) = (e * e₀) ^ N • Q.map φ := by
    apply smul_cancel (nzd_pow he N)
    calc e ^ N • (B' * (Q * A₀)) = B' * (e ^ N • (Q * A₀)) := by rw [Matrix.mul_smul]
      _ = B' * (e₀ ^ N • (B * Q.map φ)) := by rw [hQA]
      _ = e₀ ^ N • (B' * (B * Q.map φ)) := by rw [Matrix.mul_smul]
      _ = e₀ ^ N • (e ^ (2 * N) • Q.map φ) := by rw [mul_left_of hB'B]
      _ = e ^ N • ((e * e₀) ^ N • Q.map φ) := by rw [smul_smul, smul_smul]; congr 1; ring

  have h2 : (e * e₀) ^ N • Q'.map φ = A₀' * (Q' * B) := by
    apply left_cancel hL hφQ'Q
    apply smul_cancel (nzd_pow (nzd_mul he he₀) N)
    have lhs : (e * e₀) ^ N • (Q.map φ * ((e * e₀) ^ N • Q'.map φ)) =
        ((e * e₀) ^ (2 * N) * lr ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [Matrix.mul_smul, ← Matrix.map_mul, hQQ', map_smul_one, map_pow, hφlr, smul_smul,
        smul_smul]
      congr 1; ring
    have rhs : (e * e₀) ^ N • (Q.map φ * (A₀' * (Q' * B))) =
        ((e * e₀) ^ (2 * N) * lr ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [← Matrix.smul_mul, ← h1, Matrix.mul_assoc, Matrix.mul_assoc, mul_left_of hAA',
        Matrix.mul_smul, Matrix.mul_smul, mul_left_of hQQ', Matrix.mul_smul, hB'B, smul_smul,
        smul_smul]
      congr 1; ring
    rw [lhs, rhs]

  have hcomm : (Q.map φ).map σ = (Q.map σ).map φ := by
    ext i j; simp [hφσ]
  have h3 : B'.map σ * (Q.map σ * A₀) = (σ e * e₀) ^ N • (Q.map σ).map φ := by
    have := congrArg (fun M => M.map σ) h1
    simp only [Matrix.map_mul, map_smul', map_pow, map_mul, hA₀σ, hσe₀, hcomm] at this
    exact this

  have h4 : B' * (ε * B.map σ) = (σ e * e) ^ N • ε.map φ := by
    apply smul_cancel (nzd_pow he N)
    calc e ^ N • (B' * (ε * B.map σ)) = B' * (e ^ N • (ε * B.map σ)) := by rw [Matrix.mul_smul]
      _ = B' * (σ e ^ N • (B * ε.map φ)) := by rw [hεB]
      _ = σ e ^ N • (B' * (B * ε.map φ)) := by rw [Matrix.mul_smul]
      _ = σ e ^ N • (e ^ (2 * N) • ε.map φ) := by rw [mul_left_of hB'B]
      _ = e ^ N • ((σ e * e) ^ N • ε.map φ) := by rw [smul_smul, smul_smul]; congr 1; ring

  have h5 : A₀ * (Q' * ε * Q.map σ).map φ * A₀' = e₀ ^ (2 * N) • (Q' * ε * Q.map σ) := by
    have hc := nzd_mul (nzd_mul (nzd_pow (nzd_mul he he₀) N) (nzd_pow (nzd_mul hσe he) N))
      (nzd_pow (nzd_mul hσe he₀) N)
    apply smul_cancel hc
    calc ((e * e₀) ^ N * (σ e * e) ^ N * (σ e * e₀) ^ N) • (A₀ * (Q' * ε * Q.map σ).map φ * A₀')
        = A₀ * (((e * e₀) ^ N • Q'.map φ) * (((σ e * e) ^ N • ε.map φ) *
            (((σ e * e₀) ^ N • (Q.map σ).map φ) * A₀'))) := by
          simp only [Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
          congr 1; ring
      _ = A₀ * ((A₀' * (Q' * B)) * ((B' * (ε * B.map σ)) * ((B'.map σ * (Q.map σ * A₀)) * A₀'))) := by
          rw [h2, h4, h3]
      _ = ((e * e₀) ^ N * (σ e * e) ^ N * (σ e * e₀) ^ N) • (e₀ ^ (2 * N) • (Q' * ε * Q.map σ)) := by
          simp only [Matrix.mul_assoc, mul_left_of hAA', mul_left_of hBB', mul_left_of hσBB', hAA',
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          congr 1; ring
  have hLφ : A₀ * (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' =
      e₀ ^ (2 * N) • (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) := by
    rw [map_smul_one, map_pow, hφlr, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAA',
      smul_smul, smul_smul, mul_comm]
  have hsub : (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ =
      (Q' * ε * Q.map σ).map φ - (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ := by
    ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  rw [hsub, Matrix.mul_sub, Matrix.sub_mul, h5, hLφ, smul_sub]

end GlobalTheory.FrobeniusDefect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixComatrixDivisible
section
open Matrix

namespace GlobalTheory

theorem frobenius_matrix_comatrix_divisible {R : Type} [CommRing R] [IsDomain R] (d N N₀ q : ℕ) (p : Fin d → ℕ) (ξ : R)
    (A A' B B' c c' V₀ V₀' : Matrix (Fin d) (Fin d) R) (hξ : ξ ≠ 0) (hB : B * B' = 1) (hc : c * c' = 1)
    (hV : V₀ * V₀' = 1) (hA : A * A' = ξ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hid : ξ ^ q • (A * B * c) = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j)))
    (hN : N₀ ≤ N) (hp : ∀ i, |(p i : ℤ) - q| ≤ N₀) :
    (∀ i j, ξ ^ (N - N₀) ∣ A i j) ∧ ∀ i j, ξ ^ (N - N₀) ∣ A' i j := by
  have hp1 : ∀ k, q ≤ p k + N₀ := fun k => by
    have := (abs_le.mp (hp k)).1; omega
  have hp2 : ∀ k, p k ≤ q + N₀ := fun k => by
    have := (abs_le.mp (hp k)).2; omega
  have hq0 : ξ ^ q ≠ 0 := pow_ne_zero _ hξ
  have cancel : ∀ (s : R), s ≠ 0 → ∀ M M' : Matrix (Fin d) (Fin d) R, s • M = s • M' → M = M' := by
    intro s hs M M' h
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hs this
  have hA1 : ξ ^ q • A = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j) * (c' * B')) := by
    have : A = A * B * c * (c' * B') := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (A * B) c c', hc, Matrix.mul_one, Matrix.mul_assoc, hB,
        Matrix.mul_one]
    conv_lhs => rw [this]
    rw [← Matrix.smul_mul, hid, Matrix.smul_mul]
  constructor
  · intro i j
    have e := congrFun (congrFun hA1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal] at e
    have hdiv : ξ ^ q * ξ ^ (N - N₀) ∣ ξ ^ q * A i j := by
      rw [e, Finset.mul_sum]
      apply Finset.dvd_sum
      intro k _
      have h1 : ξ ^ q * ξ ^ (N - N₀) ∣ ξ ^ N * ξ ^ p k := by
        rw [← pow_add, ← pow_add]; exact pow_dvd_pow _ (by have := hp1 k; omega)
      exact h1.trans ⟨V₀ i k * (c' * B') k j, by ring⟩
    exact (mul_dvd_mul_iff_left hq0).mp hdiv
  · set D' : Matrix (Fin d) (Fin d) R := Matrix.diagonal (fun k => ξ ^ (N₀ + q - p k)) with hD'
    have hDD : Matrix.diagonal (fun j => ξ ^ p j) * D' = ξ ^ (N₀ + q) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [hD', Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        rw [← pow_add]; congr 1; have := hp2 i; omega
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    set Z := B * c * D' * V₀' with hZ
    have hAZ : ξ ^ q • (A * Z) = ξ ^ (N + (N₀ + q)) • (1 : Matrix (Fin d) (Fin d) R) := by
      have : A * Z = A * B * c * D' * V₀' := by simp only [hZ, Matrix.mul_assoc]
      rw [this, Matrix.mul_assoc (A * B * c), ← Matrix.smul_mul, hid, Matrix.smul_mul,
        Matrix.mul_assoc V₀, ← Matrix.mul_assoc _ D', hDD, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, hV, smul_smul, ← pow_add]
    have hAZ2 : A * (ξ ^ (N - N₀) • Z) = A * A' := by
      apply cancel _ hq0
      rw [Matrix.mul_smul, smul_comm, hAZ, smul_smul, hA, smul_smul, ← pow_add, ← pow_add]
      congr 2; omega
    have hdetA : A.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hA
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
      exact pow_ne_zero _ (pow_ne_zero _ hξ) this.symm
    have hA' : A' = ξ ^ (N - N₀) • Z := by
      apply cancel _ hdetA
      rw [← Matrix.one_mul A', ← Matrix.one_mul (ξ ^ (N - N₀) • Z), ← Matrix.smul_mul, ← Matrix.smul_mul,
        ← Matrix.adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, hAZ2]
    intro i j
    rw [hA', Matrix.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowEquationDvdAllPow
section
open scoped NNReal

namespace GlobalTheory

theorem phiEq_iterate (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [ExpChar R l] (u : R)
    (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ)
    (hD : ∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) (k : ℕ) :
    ∃ a : ℕ, a + h ≤ h * l ^ k ∧ ∃ e : κ → κ → R,
      ∀ j, u ^ a * D j = ∑ i, D i ^ (l ^ k) * e i j := by
  classical
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  induction k with
  | zero =>
    refine ⟨0, by simp, fun i j => if i = j then 1 else 0, fun j => ?_⟩
    simp
  | succ k ih =>
    obtain ⟨a, ha, e, he⟩ := ih
    refine ⟨h + l * a, ?_, fun i' j => ∑ i, e i' i ^ l * c i j, fun j => ?_⟩
    · have h1 : l * (a + h) ≤ l * (h * l ^ k) := Nat.mul_le_mul_left _ ha
      have h2 : 2 * h ≤ l * h := Nat.mul_le_mul_right _ hl2
      calc h + l * a + h = 2 * h + l * a := by ring
        _ ≤ l * h + l * a := by omega
        _ = l * (a + h) := by ring
        _ ≤ l * (h * l ^ k) := h1
        _ = h * l ^ (k + 1) := by ring
    · calc u ^ (h + l * a) * D j = ∑ i, (u ^ a * D i) ^ l * c i j := by
            rw [pow_add, mul_comm (u ^ h) (u ^ (l * a)), mul_assoc, hD j, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_pow, ← pow_mul, mul_comm a l]; ring
        _ = ∑ i, (∑ i', D i' ^ (l ^ k) * e i' i) ^ l * c i j := by
            simp only [he]
        _ = ∑ i, ∑ i', D i' ^ (l ^ (k + 1)) * (e i' i ^ l * c i j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [sum_pow_char, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [mul_pow, ← pow_mul, pow_succ]; ring
        _ = ∑ i', D i' ^ (l ^ (k + 1)) * ∑ i, e i' i ^ l * c i j := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]

theorem phiEq_dvd_all_pow : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R),
    ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R)
    (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) →
    (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h hD hnil m j
  classical
  have hlp : l.Prime := Fact.out
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hchar : ringChar R = l := by
    rcases (Nat.dvd_prime hlp).1 (ringChar.dvd hl) with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact h1
  haveI : CharP R l := hchar ▸ ringChar.charP R
  haveI : ExpChar R l := ExpChar.prime hlp
  choose C hC using fun i => hnil i (h + 1)
  set Cm := ∑ i, C i with hCm
  obtain ⟨k, hk⟩ : ∃ k, m + Cm < l ^ k := ⟨m + Cm, Nat.lt_pow_self hlp.one_lt⟩
  obtain ⟨a, ha, e, he⟩ := phiEq_iterate l R u κ D c h hD k
  have hdiv : u ^ ((h + 1) * l ^ k) ∣ u ^ (Cm + a) * D j := by
    rw [pow_add, mul_assoc, he j, Finset.mul_sum]
    refine Finset.dvd_sum fun i _ => ?_
    rw [← mul_assoc]
    refine Dvd.dvd.mul_right ?_ _
    have hCi : C i ≤ Cm := Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ i)
    refine (hC i (l ^ k)).trans ?_
    have hsp : u ^ Cm = u ^ C i * u ^ (Cm - C i) := by rw [← pow_add, Nat.add_sub_cancel' hCi]
    rw [hsp]
    exact ⟨u ^ (Cm - C i), by ring⟩
  have hle : Cm + a + m ≤ (h + 1) * l ^ k := by
    have : h * l ^ k + l ^ k = (h + 1) * l ^ k := by ring
    omega
  obtain ⟨y, hy⟩ := hdiv
  have hsplit : (h + 1) * l ^ k = (Cm + a) + ((h + 1) * l ^ k - (Cm + a)) := by omega
  rw [hsplit, pow_add u (Cm + a), mul_assoc] at hy
  have hreg : u ^ (Cm + a) ∈ nonZeroDivisors R := pow_mem hu _
  have hDj := (mul_cancel_left_mem_nonZeroDivisors hreg).1 hy
  rw [hDj]
  refine Dvd.dvd.mul_right (pow_dvd_pow u ?_) _
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjoint
section
open Polynomial

namespace GlobalTheory.GalDisj

section
variable {k M F D : Type*} [Field k] [Field M] [Field F] [Field D] [Algebra k M] [Algebra k F]
  [Algebra k D] [Algebra M D] [Algebra F D] [IsScalarTower k M D] [IsScalarTower k F D]

end

open Polynomial in
private theorem natDegree_minpoly_le_natDegree_minpoly_map {k Ω D : Type} [Field k] [Field Ω] [Field D]
    [Algebra k Ω] (o : Ω →+* D) (F : Subfield D)
    (hF : ∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) (α : Ω) (hα : IsIntegral k α)
    (hsplit : ((minpoly k α).map (algebraMap k Ω)).Splits) :
    (minpoly k α).natDegree ≤ (minpoly F (o α)).natDegree := by
  set ψ : k →+* F := (o.comp (algebraMap k Ω)).codRestrict F (fun c => (hF _).2 ⟨c, rfl⟩)
  have hcomp : F.subtype.comp ψ = o.comp (algebraMap k Ω) := by ext; rfl
  have hcomp' : (algebraMap F D).comp ψ = o.comp (algebraMap k Ω) := by ext; rfl
  have hmon : ((minpoly k α).map ψ).Monic := (minpoly.monic hα).map ψ
  have hroot : aeval (o α) ((minpoly k α).map ψ) = 0 := by
    rw [aeval_def, eval₂_map, hcomp', ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hβ : IsIntegral F (o α) := ⟨_, hmon, hroot⟩
  have hdvd : minpoly F (o α) ∣ (minpoly k α).map ψ := minpoly.dvd F _ hroot
  have hP : ((minpoly k α).map ψ).map F.subtype = ((minpoly k α).map (algebraMap k Ω)).map o := by
    rw [map_map, map_map, hcomp]
  have hP0 : ((minpoly k α).map ψ).map F.subtype ≠ 0 := (hmon.map _).ne_zero
  have hGdvd : (minpoly F (o α)).map F.subtype ∣ ((minpoly k α).map ψ).map F.subtype :=
    Polynomial.map_dvd _ hdvd
  have hGs : ((minpoly F (o α)).map F.subtype).Splits := by
    refine Splits.of_dvd ?_ hP0 hGdvd
    rw [hP]
    exact hsplit.map o
  have hGm : ((minpoly F (o α)).map F.subtype).Monic := (minpoly.monic hβ).map _
  have hlift : (minpoly F (o α)).map F.subtype ∈ lifts o := by
    refine hGs.mem_lift_of_roots_mem_range hGm o fun a ha => ?_
    have h1 := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hP0 hGdvd) ha
    rw [hP, hsplit.roots_map o] at h1
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 h1
    exact ⟨r, rfl⟩
  have hlift' : (minpoly F (o α)).map F.subtype ∈ lifts (o.comp (algebraMap k Ω)) := by
    rw [lifts_iff_coeff_lifts] at hlift ⊢
    intro n
    obtain ⟨y, hy⟩ := hlift n
    have hyF : o y ∈ F := by
      rw [hy, coeff_map]
      exact ((minpoly F (o α)).coeff n).2
    obtain ⟨c, rfl⟩ := (hF y).1 hyF
    exact ⟨c, hy⟩
  obtain ⟨g, hg⟩ := (mem_lifts _).1 hlift'
  have hinj : Function.Injective (o.comp (algebraMap k Ω)) := RingHom.injective _
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hg
    exact hGm.ne_zero hg.symm
  have hgα : aeval α g = 0 := by
    apply o.injective
    rw [map_zero, aeval_def, hom_eval₂, ← eval_map, hg, eval_map]
    exact minpoly.aeval F (o α)
  calc (minpoly k α).natDegree ≤ g.natDegree := natDegree_le_of_dvd (minpoly.dvd k α hgα) hg0
    _ = ((minpoly F (o α)).map F.subtype).natDegree := by
        rw [← hg, natDegree_map_eq_of_injective hinj]
    _ = (minpoly F (o α)).natDegree := natDegree_map_eq_of_injective (RingHom.injective _) _

open Polynomial in

theorem _root_.GlobalTheory.GalDisj.galois_linearDisjoint : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by
  intro k Ω D _ _ _ _ _ o F hF m x hx b hb hsum
  classical
  set M := IntermediateField.adjoin k (Set.range x)
  haveI : FiniteDimensional k M :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  obtain ⟨α', hα'⟩ := Field.exists_primitive_element k M
  set α : Ω := (α' : Ω) with hαdef
  have hxα : ∀ i, x i ∈ IntermediateField.adjoin k {α} := by
    intro i
    have h1 : (IntermediateField.adjoin k {α'}).map M.val = IntermediateField.adjoin k {α} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
    rw [← h1, hα']
    exact ⟨⟨x i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩, trivial, rfl⟩
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim ≤ (minpoly F (o α)).natDegree := by
    rw [IntermediateField.adjoin.powerBasis_dim]
    exact natDegree_minpoly_le_natDegree_minpoly_map o F hF α hint (IsGalois.splits k α)
  have hli : LinearIndependent F (fun j : Fin pb.dim => o α ^ (j : ℕ)) :=
    (linearIndependent_pow (o α)).comp (Fin.castLE hdim) (Fin.castLE_injective hdim)
  set c : Fin m → Fin pb.dim → k := fun i j => pb.basis.repr ⟨x i, hxα i⟩ j
  have hexp : ∀ i, x i = ∑ j, c i j • α ^ (j : ℕ) := by
    intro i
    have h := congrArg Subtype.val (pb.basis.sum_repr ⟨x i, hxα i⟩)
    refine h.symm.trans ?_
    simp [c, pb, IntermediateField.adjoin.powerBasis_gen]
  have hd : ∀ j, ∑ i, o (algebraMap k Ω (c i j)) * b i = 0 := by
    have hmem : ∀ j, ∑ i, o (algebraMap k Ω (c i j)) * b i ∈ F := fun j =>
      F.sum_mem fun i _ => F.mul_mem ((hF _).2 ⟨_, rfl⟩) (hb i)
    intro j
    have := Fintype.linearIndependent_iff.1 hli (fun j => ⟨_, hmem j⟩) ?_ j
    · exact congrArg Subtype.val this
    rw [← hsum]
    simp only [hexp, Subfield.smul_def, map_sum, map_smul, Algebra.smul_def, map_mul, map_pow,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (∑ i, o (algebraMap k Ω (c i j)) * b i) * o α ^ (j : ℕ) = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨g, hg⟩ := LinearMap.exists_extend hx.repr
  have hgx : ∀ i, g (x i) = Finsupp.single i 1 := by
    intro i
    have := LinearMap.congr_fun hg ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hx.repr_eq_single i _ rfl]
  intro l
  calc b l = ∑ i, o (algebraMap k Ω (g (x i) l)) * b i := by
        simp [hgx, Finsupp.single_apply]
    _ = ∑ j : Fin pb.dim, o (algebraMap k Ω (g (α ^ (j : ℕ)) l)) *
          ∑ i, o (algebraMap k Ω (c i j)) * b i := by
        simp only [hexp, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
          Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 0 := by simp [hd]

end GlobalTheory.GalDisj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorOfGaloisRelations
section
open Matrix

theorem GlobalTheory.ht_operator_of_galois_relations : ∀ {k : Type} [Field k] (d N q : ℕ) (p : Fin d → ℕ) (a b z w : k) (y y' v v₀ e r sy sv : Matrix (Fin d) (Fin d) k), a ≠ 0 → b ≠ 0 → z * w = 1 → y * y' = a ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) k) → y * v₀ = a ^ N • v → a ^ N • (r * sy) = b ^ N • (y * e) → r * sv * Matrix.diagonal (fun j => w ^ p j) = w ^ q • v → sy * v₀ = b ^ N • sv → ∃ u : Matrix (Fin d) (Fin d) k, u * y = y * e ∧ u * v = v * Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
  intro k _ d N q p a b z w y y' v v₀ e r sy sv ha hb hzw hy hyv hr hsv hsy
  have hz : z ≠ 0 := left_ne_zero_of_mul_eq_one hzw
  have hw : w = z⁻¹ := eq_inv_of_mul_eq_one_right hzw
  have haN : a ^ N ≠ 0 := pow_ne_zero _ ha
  have hbN : b ^ N ≠ 0 := pow_ne_zero _ hb
  have ha2 : a ^ (2 * N) ≠ 0 := pow_ne_zero _ ha
  have hy' : y' * y = a ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) k) := by
    have h1 : y * ((a ^ (2 * N))⁻¹ • y') = 1 := by
      rw [Matrix.mul_smul, hy, smul_smul, inv_mul_cancel₀ ha2, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h2
    calc y' * y = a ^ (2*N) • ((a ^ (2 * N))⁻¹ • (y' * y)) := by
          rw [smul_smul, mul_inv_cancel₀ ha2, one_smul]
      _ = _ := by rw [h2]
  have hD : r * sv = v * Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
    have hdd : Matrix.diagonal (fun j => w ^ p j) * Matrix.diagonal (fun j => z ^ p j) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext j; rw [← mul_pow, mul_comm, hzw, one_pow]
    have hdiag : w ^ q • Matrix.diagonal (fun j => z ^ p j)
        = Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
        rw [zpow_sub₀ hz, zpow_natCast, zpow_natCast, hw, inv_pow, div_eq_mul_inv, mul_comm]
      · simp [Matrix.diagonal_apply_ne _ hij]
    calc r * sv = r * sv * (Matrix.diagonal (fun j => w ^ p j) * Matrix.diagonal (fun j => z ^ p j)) := by
          rw [hdd, Matrix.mul_one]
      _ = (w ^ q • v) * Matrix.diagonal (fun j => z ^ p j) := by rw [← Matrix.mul_assoc, hsv]
      _ = _ := by rw [Matrix.smul_mul, ← Matrix.mul_smul, hdiag]
  have hyev : y * e * v₀ = a ^ N • (r * sv) := by
    have h1 : b ^ N • (y * e * v₀) = b ^ N • (a ^ N • (r * sv)) := by
      rw [← Matrix.smul_mul, ← hr, Matrix.smul_mul, Matrix.mul_assoc, hsy, Matrix.mul_smul, smul_comm]
    exact smul_right_injective _ hbN h1
  have hy'v : y' * v = a ^ N • v₀ := by
    have h1 : a ^ N • (y' * v) = a ^ N • (a ^ N • v₀) := by
      rw [← Matrix.mul_smul, ← hyv, ← Matrix.mul_assoc, hy', Matrix.smul_mul, Matrix.one_mul, smul_smul,
        ← pow_add, two_mul]
    exact smul_right_injective _ haN h1
  refine ⟨(a ^ (2 * N))⁻¹ • (y * e * y'), ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_assoc, hy', Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ ha2, one_smul]
  · have hc : (a ^ (2 * N))⁻¹ * a ^ N * a ^ N = 1 := by
      rw [mul_assoc, ← pow_add, ← two_mul, inv_mul_cancel₀ ha2]
    rw [Matrix.smul_mul, Matrix.mul_assoc, hy'v, Matrix.mul_smul, hyev, smul_smul, smul_smul, hc, one_smul, hD]
end


import Mathlib

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.CommonDenominator
section
namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_common_denominator {K : Type} [Field K] [NumberField K] {N : ℕ}
    {M : Submodule (𝓞 K) (Fin N → K)} (hM : M.FG) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ v ∈ M, ∀ i : Fin N,
      ∃ w : 𝓞 K, algebraMap (𝓞 K) K w = algebraMap (𝓞 K) K c * v i := by
  obtain ⟨s, rfl⟩ := hM
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    (s ×ˢ (Finset.univ : Finset (Fin N))) (fun p : (Fin N → K) × Fin N => p.1 p.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    intro i
    obtain ⟨w, hw⟩ := hb (x, i) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
    exact ⟨w, by rw [← Algebra.smul_def]; exact hw⟩
  | zero => intro i; exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨w₁, h₁⟩ := hx i
    obtain ⟨w₂, h₂⟩ := hy i
    exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, Pi.add_apply, mul_add]⟩
  | smul a x _ hx =>
    intro i
    obtain ⟨w, h⟩ := hx i
    exact ⟨a * w, by rw [map_mul, h, Pi.smul_apply, Algebra.smul_def]; ring⟩

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.DescentPowerSubgroups
section
namespace GroundTheory.Variant₂.N1

theorem exists_pow_apply_eq_self_of_aeval_eq_zero {K : Type*} [Field K] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (σ : Gal(Ω/K)) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x := by
  have hmem : ∀ n : ℕ, (σ ^ n) x ∈ p.rootSet Ω := fun n => by
    rw [Polynomial.mem_rootSet_of_ne hp, Polynomial.aeval_algHom_apply, hx, map_zero]
  have : Finite (p.rootSet Ω) := (Polynomial.rootSet_finite p Ω).to_subtype
  let f : ℕ → p.rootSet Ω := fun n => ⟨(σ ^ n) x, hmem n⟩
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : (σ ^ i) x = (σ ^ j) x := congrArg Subtype.val hij
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨j - i, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ i).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]
  · refine ⟨i - j, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ j).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsMaxMinorNeZeroOfLinearIndependentAlt
section
namespace GroundTheory.Variant₂.N1

def KSubset (n k : ℕ) : Type := { s : Finset (Fin n) // s.card = k }

def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n :=
  (s.1).orderEmbOfFin s.2

def maxMinor {R : Type*} [CommRing R] {n k : ℕ} (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) : R :=
  (B.submatrix (⇑s.emb) id).det

theorem exists_maxMinor_ne_zero_of_linearIndependent_alt {R : Type*} [CommRing R] {n k : ℕ}
    [IsDomain R] (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 := by
  classical
  set K := FractionRing R
  set B' : Matrix (Fin n) (Fin k) K := B.map (algebraMap R K) with hB'
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h1 : LinearIndependent R B'.col := by
    have hker : LinearMap.ker ((Algebra.linearMap R K).compLeft (Fin n)) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      funext i
      exact hinj (congr_fun hxy i)
    have := hB.map' ((Algebra.linearMap R K).compLeft (Fin n)) hker
    have heq : B'.col = ((Algebra.linearMap R K).compLeft (Fin n)) ∘ B.col := by
      funext j i
      rfl
    rw [heq]
    exact this
  have h2 : LinearIndependent K B'.col := (LinearIndependent.iff_fractionRing R K).mp h1
  have hrank : B'.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card h2, Fintype.card_fin]
  rw [Matrix.rank_eq_finrank_span_row] at hrank
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K B'.row
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← hrank, ← hspan, finrank_span_eq_card hli]
  let t : Finset (Fin n) := Finset.univ.map ⟨a, ha⟩
  have ht : t.card = k := by simp [t, hcard]
  let s : KSubset n k := ⟨t, ht⟩
  refine ⟨s, ?_⟩
  have hmem : ∀ i : Fin k, ∃ c : κ, a c = s.emb i := by
    intro i
    have h : s.emb i ∈ t := Finset.orderEmbOfFin_mem t ht i
    simp only [t, Finset.mem_map, Finset.mem_univ, true_and] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc⟩
  choose e he using hmem
  have he_inj : Function.Injective e := by
    intro i j hij
    apply s.emb.injective
    rw [← he i, ← he j, hij]
  have hrows : LinearIndependent K (B'.submatrix s.emb id).row := by
    have hfam : (B'.submatrix s.emb id).row = (B'.row ∘ a) ∘ e := by
      funext i j
      show B' (s.emb i) j = B' (a (e i)) j
      rw [he i]
    rw [hfam]
    exact hli.comp e he_inj
  have hdet : (B'.submatrix s.emb id).det ≠ 0 := by
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  intro h
  apply hdet
  have hmap : B'.submatrix s.emb id = (B.submatrix s.emb id).map (algebraMap R K) := rfl
  rw [hmap]
  show ((algebraMap R K).mapMatrix (B.submatrix s.emb id)).det = 0
  rw [← RingHom.map_det]
  unfold maxMinor at h
  rw [h, map_zero]

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsSmulMemFamilyOfSpanEqTop
section
namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_smul_mem_of_span_eq_top {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (RingOfIntegers K) (Fin N → K))
    (hM : Submodule.span K (M : Set (Fin N → K)) = ⊤) (x : Fin N → K) :
    ∃ t : RingOfIntegers K, t ≠ 0 ∧ algebraMap (RingOfIntegers K) K t • x ∈ M := by
  have hx : x ∈ Submodule.span K (M : Set (Fin N → K)) := by rw [hM]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have h1 : algebraMap (RingOfIntegers K) K (s * t) • y
        = t • (algebraMap (RingOfIntegers K) K s • y) := by
      rw [map_mul, mul_comm, mul_smul, algebraMap_smul]
    have h2 : algebraMap (RingOfIntegers K) K (s * t) • z
        = s • (algebraMap (RingOfIntegers K) K t • z) := by
      rw [map_mul, mul_smul, algebraMap_smul]
    rw [smul_add, h1, h2]
    exact M.add_mem (M.smul_mem t hsy) (M.smul_mem s htz)
  | smul c y _ hy =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
    simp only at hab
    refine ⟨(b : RingOfIntegers K) * t, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) ht, ?_⟩
    have key : algebraMap (RingOfIntegers K) K ((b : RingOfIntegers K) * t) • (c • y)
        = a • (algebraMap (RingOfIntegers K) K t • y) := by
      rw [← algebraMap_smul K a (algebraMap (RingOfIntegers K) K t • y), smul_smul, smul_smul,
        ← hab, map_mul]
      congr 1
      ring
    rw [key]
    exact M.smul_mem a hty

theorem exists_smul_mem_family_of_span_eq_top {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (RingOfIntegers K) (Fin N → K))
    (hM : Submodule.span K (M : Set (Fin N → K)) = ⊤)
    {ι : Type*} [Fintype ι] (v : ι → Fin N → K) :
    ∃ t : RingOfIntegers K, t ≠ 0 ∧ ∀ i, algebraMap (RingOfIntegers K) K t • v i ∈ M := by
  classical
  choose s hs hsv using fun i => exists_smul_mem_of_span_eq_top M hM (v i)
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.mpr fun i _ => hs i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), mul_comm, map_mul, mul_smul,
    algebraMap_smul]
  exact M.smul_mem _ (hsv i)

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.FontainePhiPowerSubgroups
section
namespace GroundTheory.Variant₂.N1

theorem mem_span_singleton_pow_smul_top_iff {A : Type*} [CommRing A] (a x : A) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule A A) ↔ a ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_limit_sum_pow_mul {A : Type*} [CommRing A] {a : A}
    [IsPrecomplete (Ideal.span {a}) A] (b : ℕ → A) :
    ∃ L : A, ∀ n : ℕ, a ^ n ∣ (∑ k ∈ Finset.range n, a ^ k * b k) - L := by
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (Ideal.span {a}) A).prec'
    (fun n => ∑ k ∈ Finset.range n, a ^ k * b k) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff,
        ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow a (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun n => (mem_span_singleton_pow_smul_top_iff a _ n).1 ((SModEq.sub_mem).1 (hL n))⟩

theorem exists_eq_add_mul_of_forall' {A : Type*} {R : Type*} {ι : Type*} [CommRing A]
    [CommRing R] {a : A} {r : R} [IsAdicComplete (Ideal.span {a}) A]
    [IsAdicComplete (Ideal.span {r}) R] (f : A →+* R) :
    f a = r →
      ∀ (X : R) (ψ : ι → R),
        (∀ (y : ι), ∃ (b : A) (s : R) (y' : ι), ψ y = f b + X * s + r * ψ y') →
          ∀ (y : ι), ∃ (b : A) (s : R), ψ y = f b + X * s := by
  intro hfa X ψ h
  choose b s nx hstep using h
  intro y
  obtain ⟨B, hB⟩ := exists_limit_sum_pow_mul (a := a) (fun k => b (nx^[k] y))
  obtain ⟨S, hS⟩ := exists_limit_sum_pow_mul (a := r) (fun k => s (nx^[k] y))
  refine ⟨B, S, ?_⟩
  have key : ∀ n : ℕ, ψ y = f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) +
      X * (∑ k ∈ Finset.range n, r ^ k * s (nx^[k] y)) + r ^ n * ψ (nx^[n] y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hstep (nx^[n] y)
      rw [Function.iterate_succ_apply', Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [map_add, map_mul, map_pow, hfa] at ih ⊢
      linear_combination ih + r ^ n * h1
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {r}) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_span_singleton_pow_smul_top_iff]
  obtain ⟨c, hc⟩ := hB n
  obtain ⟨d, hd⟩ := hS n
  have hfB : f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) = f B + r ^ n * f c := by
    rw [← hfa, ← map_pow, ← map_mul, ← map_add]
    congr 1
    linear_combination hc
  exact ⟨f c + X * d + ψ (nx^[n] y), by linear_combination key n + hfB + X * hd⟩

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.NormZpow
section
namespace GroundTheory.Variant₂.N1

theorem eq_one_of_forall_norm_zpow_sub_one_lt {z : ℂ} (h : ∀ m : ℤ, ‖z ^ m - 1‖ < 1) :
    z = 1 := by
  have hpow : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 := fun n => by simpa using h n
  have hle : ‖z‖ ≤ 1 := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hlt
    have h1 := hpow n
    have h2 : ‖z ^ n‖ - ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ := norm_sub_norm_le _ _
    rw [norm_pow, norm_one] at h2
    linarith
  have hz0 : z ≠ 0 := by
    rintro rfl
    have := hpow 1
    simp at this
  have hge : 1 ≤ ‖z‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have h1 : 1 < ‖z⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ hpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) h1
    have h3 := h (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h3
    have h2 : ‖z⁻¹ ^ n‖ - ‖(1 : ℂ)‖ ≤ ‖z⁻¹ ^ n - 1‖ := norm_sub_norm_le _ _
    rw [norm_pow, norm_one] at h2
    linarith
  have hn1 : ‖z‖ = 1 := le_antisymm hle hge
  have key : ∀ w : ℂ, ‖w‖ = 1 → ‖w - 1‖ < 1 → 3 * ‖w - 1‖ ^ 2 ≤ ‖w ^ 2 - 1‖ ^ 2 := by
    intro w hw hw1
    have e : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [e, norm_mul, mul_pow]
    have hw' : w.re ^ 2 + w.im ^ 2 = 1 := by
      have := Complex.sq_norm w
      rw [hw, Complex.normSq_apply] at this
      nlinarith
    have a1 : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have a2 : ‖w + 1‖ ^ 2 = (w.re + 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have a3 : 3 ≤ ‖w + 1‖ ^ 2 := by
      have : ‖w - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (w - 1)]
      nlinarith
    nlinarith [sq_nonneg ‖w - 1‖]
  have hk : ∀ k : ℕ, 3 ^ k * ‖z - 1‖ ^ 2 ≤ ‖z ^ (2 ^ k) - 1‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h4 := key (z ^ (2 ^ k)) (by rw [norm_pow, hn1, one_pow]) (hpow _)
      rw [pow_succ 2 k, pow_mul]
      calc (3 : ℝ) ^ (k + 1) * ‖z - 1‖ ^ 2 = 3 * (3 ^ k * ‖z - 1‖ ^ 2) := by ring
        _ ≤ 3 * ‖z ^ (2 ^ k) - 1‖ ^ 2 := by gcongr
        _ ≤ _ := h4
  by_contra hne
  have hd : 0 < ‖z - 1‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖ ^ 2) (by norm_num : (1 : ℝ) < 3)
  have h5 := hk k
  have h6 := hpow (2 ^ k)
  have h7 : ‖z ^ (2 ^ k) - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (z ^ (2 ^ k) - 1)]
  have h8 : 1 < 3 ^ k * ‖z - 1‖ ^ 2 := by rwa [div_lt_iff₀ hd] at hk'
  linarith

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.PowInvariant
section
namespace GroundTheory.Variant₂.N1

def mulZPowers (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ)) (s : Gal(AlgebraicClosure ℚ/ℚ))
    (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    Subgroup Gal(AlgebraicClosure ℚ/ℚ) where
  carrier := {x | ∃ k : ℤ, ∃ u ∈ U, x = s ^ k * u}
  one_mem' := ⟨0, 1, U.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, u, hu, rfl⟩ ⟨b, v, hv, rfl⟩
    refine ⟨a + b, s ^ (-b) * u * (s ^ (-b))⁻¹ * v, U.mul_mem (hU (-b) u hu) hv, ?_⟩
    rw [zpow_add, zpow_neg, inv_inv]
    group
  inv_mem' := by
    rintro _ ⟨k, u, hu, rfl⟩
    refine ⟨-k, s ^ k * u⁻¹ * (s ^ k)⁻¹, hU k _ (U.inv_mem hu), ?_⟩
    rw [zpow_neg]
    group

theorem le_powerSubgroup₂ (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    U ≤ mulZPowers U s hU := fun u hu => ⟨0, u, hu, by simp⟩

theorem mem_mulZPowers_self (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    s ∈ mulZPowers U s hU := ⟨1, 1, U.one_mem, by simp⟩

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.PrecompleteOfSurjective
section
namespace GroundTheory.Variant₂.N1

theorem smodEq_span_singleton_pow_iff {R : Type*} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • (⊤ : Submodule R R))] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem isPrecomplete_of_surjective {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) [IsPrecomplete (Ideal.span {a}) A] :
    IsPrecomplete (Ideal.span {f a}) B := by
  refine ⟨fun b hb => ?_⟩
  have hb' : ∀ {m n : ℕ}, m ≤ n → f a ^ m ∣ b m - b n := fun hmn =>
    (smodEq_span_singleton_pow_iff (f a) _ _ _).1 (hb hmn)
  have hstep : ∀ n : ℕ, ∃ x : A, b (n + 1) = b n + f (a ^ n * x) := by
    intro n
    obtain ⟨c, hc⟩ := hb' (Nat.le_add_right n 1)
    obtain ⟨x, rfl⟩ := hf c
    refine ⟨-x, ?_⟩
    rw [map_mul, map_pow, map_neg]
    linear_combination -hc
  choose x hx using hstep
  obtain ⟨y₀, hy₀⟩ := hf (b 0)
  let y : ℕ → A := fun n => y₀ + ∑ k ∈ Finset.range n, a ^ k * x k
  have hy_succ : ∀ n, y (n + 1) = y n + a ^ n * x n := by
    intro n
    simp only [y, Finset.sum_range_succ, add_assoc]
  have hy : ∀ n, f (y n) = b n := by
    intro n
    induction n with
    | zero => simp [y, hy₀]
    | succ n ih => rw [hy_succ, map_add, ih, hx]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → a ^ m ∣ y m - y n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hy_succ, sub_add_eq_sub_sub]
      exact dvd_sub ih (Dvd.dvd.mul_right (pow_dvd_pow a hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {a}) inferInstance (f := y)
    (fun {m n} hmn => (smodEq_span_singleton_pow_iff a m _ _).2 (hcauchy hmn))
  refine ⟨f L, fun n => (smodEq_span_singleton_pow_iff (f a) n _ _).2 ?_⟩
  have h := map_dvd f ((smodEq_span_singleton_pow_iff a n _ _).1 (hL n))
  rwa [map_pow, map_sub, hy] at h

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.RelIndexSup
section
namespace GroundTheory.Variant₂.N1

open Subgroup

theorem relIndex_sup_of_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) : H.relIndex (H ⊔ N) = H.relIndex N := by
  symm
  let f : N →* (H ⊔ N : Subgroup G) := Subgroup.inclusion le_sup_right
  let g : N ⧸ H.subgroupOf N → (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N) :=
    fun q => Quotient.liftOn' q (fun n => ((f n : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N))) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab
      rw [QuotientGroup.eq, mem_subgroupOf]
      simpa [f] using hab)
  have hinj : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    have h1 : ((f a : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) =
        ((f b : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) := hxy
    rw [QuotientGroup.eq, mem_subgroupOf] at h1
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using h1
  have hsurj : Function.Surjective g := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
    obtain ⟨y, hy⟩ := k
    have hy' : y ∈ ((N ⊔ H : Subgroup G) : Set G) := by
      rw [sup_comm]; exact hy
    rw [coe_mul_of_right_le_normalizer_left N H hLE] at hy'
    obtain ⟨n, hn, h, hh, rfl⟩ := hy'
    refine ⟨((⟨n, hn⟩ : N) : N ⧸ H.subgroupOf N), ?_⟩
    change ((f ⟨n, hn⟩ : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) = _
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using hh
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  exact Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.SpanEqTopSmul
section
namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_smul_mem_of_span_eq_top_alt {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → K))
    (hΛ : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (v : Fin n → K) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set (Fin n → K)) := hΛ ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem b hax
    · rw [mul_smul]; exact Λ.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) c
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hsK : algebraMap (𝓞 K) K s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs0
    refine ⟨s * a, mul_ne_zero hs0 ha, ?_⟩
    have e : (s * a) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • x) = r • (a • x) := by
      rw [← algebraMap_smul K (s * a), ← algebraMap_smul K r, ← algebraMap_smul K a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]; exact Λ.smul_mem r hax

end GroundTheory.Variant₂.N1
end


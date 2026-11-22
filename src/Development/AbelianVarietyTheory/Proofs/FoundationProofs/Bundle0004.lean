import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralPolyOfPrimitiveRootTotallyRamified
section
namespace GlobalTheory

open Polynomial

theorem valuation_term_le_sum_of_distinct {Ω Γ : Type} [Field Ω] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) (s : Finset ℕ) (f : ℕ → Ω)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ≠ 0 → v (f i) ≠ v (f j)) :
    ∀ j ∈ s, v (f j) ≤ v (∑ i ∈ s, f i) := by
  classical
  intro j hj
  by_cases hall : ∀ i ∈ s, f i = 0
  · rw [hall j hj, map_zero]
    exact zero_le'
  push_neg at hall
  obtain ⟨i0, hi0, hfi0⟩ := hall
  obtain ⟨k, hk, hkmax⟩ := s.exists_max_image (fun i => v (f i)) ⟨i0, hi0⟩
  have hk0 : v (f k) ≠ 0 := by
    intro h0
    have h1 := hkmax i0 hi0
    rw [h0] at h1
    exact hfi0 ((Valuation.zero_iff v).1 (le_antisymm h1 zero_le'))
  have hsum : v (∑ i ∈ s, f i) = v (f k) := by
    apply v.map_sum_eq_of_lt hk
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    refine lt_of_le_of_ne (hkmax i hi.1) ?_
    by_cases hfi : f i = 0
    · rw [hfi, map_zero]
      exact hk0.symm
    · exact h i hi.1 k hk hi.2 hfi
  rw [hsum]
  exact hkmax j hj

theorem exists_integral_poly_of_primitiveRoot_totally_ramified :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (K : Subfield Ω), (∀ x ∈ K, x ≠ 0 → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k) → ∀ (m : ℕ), 1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) → ∀ u ∈ A, (∃ Q : Polynomial Ω, (∀ x ∈ Q.coeffs, x ∈ K) ∧ Q.eval ζ = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ x ∈ K) ∧ P.eval ζ = u := by
  classical
  intro l hfact Ω _ _ A hl K hK m hm ζ hζ hζv u hu hQ
  obtain ⟨Q, hQK, hQu⟩ := hQ
  have hp : l.Prime := hfact.out
  set e := Nat.totient (l ^ m) with he_def
  have hlm : 0 < l ^ m := pow_pos hp.pos m
  have he : 0 < e := Nat.totient_pos.2 hlm
  set v := A.valuation with hv_def
  set w := ζ - 1 with hw_def
  set γ := v w with hγ_def
  have hvl0 : v (l : Ω) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  have hγ0 : γ ≠ 0 := by
    intro h
    apply hvl0
    rw [← hζv, h, zero_pow he.ne']
  have hγ1 : γ < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : 1 ≤ γ ^ e := one_le_pow₀ hc
    rw [hζv] at h1
    exact absurd hl (not_lt.2 h1)
  have hγpos : 0 < γ := lt_of_le_of_ne zero_le' hγ0.symm
  set T : Subring Ω := K.toSubring with hT_def
  have hQT : (↑Q.coeffs : Set Ω) ⊆ T := fun x hx => hQK x hx
  set Q' := Q.toSubring T hQT with hQ'_def
  set Φ := Polynomial.cyclotomic (l ^ m) T with hΦ_def
  have hΦ : Φ.Monic := Polynomial.cyclotomic.monic _ _
  have hΦdeg : Φ.natDegree = e := Polynomial.natDegree_cyclotomic _ _
  have hΦ1 : Φ ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hΦdeg
    omega
  set R1 := Q' %ₘ Φ with hR1_def
  have hR1 : R1.natDegree < e := by
    rw [← hΦdeg]
    exact Polynomial.natDegree_modByMonic_lt _ hΦ hΦ1
  set R2 := R1.comp (Polynomial.X + Polynomial.C 1) with hR2_def
  have hR2 : R2.natDegree < e := by
    rw [hR2_def, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    exact hR1
  set f := T.subtype with hf_def
  have hΦζ : Φ.eval₂ f ζ = 0 := by
    rw [← Polynomial.eval_map, hΦ_def, Polynomial.map_cyclotomic]
    exact (hζ.isRoot_cyclotomic hlm).eq_zero
  have hu1 : R2.eval₂ f w = u := by
    rw [hR2_def, Polynomial.eval₂_comp]
    have h1 : (Polynomial.X + Polynomial.C 1 : Polynomial T).eval₂ f w = ζ := by
      simp [hw_def]
    rw [h1, hR1_def, Polynomial.eval₂_modByMonic_eq_self_of_root hΦζ, ← hQu,
      ← Polynomial.eval_map, hQ'_def, Polynomial.map_toSubring]
  set c : ℕ → Ω := fun i => f (R2.coeff i) with hc_def
  have hsum : ∑ i ∈ Finset.range e, c i * w ^ i = u := by
    rw [← hu1, Polynomial.eval₂_eq_sum_range' f hR2]
  have hcK : ∀ i, c i ∈ K := fun i => (R2.coeff i).2
  have hcv : ∀ i, c i ≠ 0 → ∃ k : ℤ, v (c i) = γ ^ ((e : ℤ) * k) := by
    intro i hi
    obtain ⟨k, hk⟩ := hK _ (hcK i) hi
    refine ⟨k, ?_⟩
    rw [hk, zpow_mul, zpow_natCast, hζv]
  have hterm : ∀ i ∈ Finset.range e, ∀ j ∈ Finset.range e, i ≠ j →
      c i * w ^ i ≠ 0 → v (c i * w ^ i) ≠ v (c j * w ^ j) := by
    intro i hi j hj hij hne h
    have hci : c i ≠ 0 := left_ne_zero_of_mul hne
    obtain ⟨ki, hki⟩ := hcv i hci
    rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_mul, Valuation.map_pow, hki] at h
    by_cases hcj : c j = 0
    · rw [hcj, map_zero, zero_mul] at h
      exact mul_ne_zero (zpow_ne_zero _ hγ0) (pow_ne_zero _ hγ0) h
    obtain ⟨kj, hkj⟩ := hcv j hcj
    rw [hkj, ← zpow_natCast γ i, ← zpow_natCast γ j, ← zpow_add₀ hγ0, ← zpow_add₀ hγ0] at h
    have hx := zpow_right_injective₀ hγpos hγ1.ne h
    rw [Finset.mem_range] at hi hj
    have hi' : (i : ℤ) < e := by exact_mod_cast hi
    have hj' : (j : ℤ) < e := by exact_mod_cast hj
    have hd : (e : ℤ) * (ki - kj) = (j : ℤ) - i := by linarith
    apply hij
    rcases lt_trichotomy (ki - kj) 0 with h' | h' | h'
    · have h2 : (e : ℤ) * (ki - kj) ≤ -e := by nlinarith
      omega
    · rw [h', mul_zero] at hd
      omega
    · have h2 : (e : ℤ) ≤ (e : ℤ) * (ki - kj) := by nlinarith
      omega
  have hvu : v u ≤ 1 := A.valuation_le_one ⟨u, hu⟩
  have hcA : ∀ i ∈ Finset.range e, c i ∈ A := by
    intro i hi
    by_cases hci : c i = 0
    · rw [hci]
      exact A.zero_mem
    have hle := valuation_term_le_sum_of_distinct v (Finset.range e) (fun i => c i * w ^ i) hterm i hi
    rw [hsum] at hle
    rw [← A.valuation_le_one_iff]
    obtain ⟨k, hk⟩ := hcv i hci
    rw [Finset.mem_range] at hi
    have hi' : (i : ℤ) < e := by exact_mod_cast hi
    have hk0 : 0 ≤ k := by
      by_contra hneg
      push_neg at hneg
      have h1 : v (c i * w ^ i) = γ ^ ((e : ℤ) * k + i) := by
        rw [Valuation.map_mul, Valuation.map_pow, hk, zpow_add₀ hγ0, zpow_natCast]
      have h2 : (e : ℤ) * k + i < 0 := by
        nlinarith [mul_nonneg (Int.natCast_nonneg e) (by omega : (0 : ℤ) ≤ -1 - k)]
      have h3 : 1 < γ ^ ((e : ℤ) * k + i) := one_lt_zpow_of_neg₀ hγpos hγ1 h2
      rw [← h1] at h3
      exact absurd (hle.trans hvu) (not_le.2 h3)
    rw [hk]
    have h4 := zpow_le_zpow_right_of_le_one₀ hγpos hγ1.le
      (mul_nonneg (Int.natCast_nonneg e) hk0 : (0 : ℤ) ≤ (e : ℤ) * k)
    rwa [zpow_zero] at h4
  set S : Subring Ω := A.toSubring ⊓ K.toSubring with hS_def
  have hcS : ∀ i, c i ∈ S := by
    intro i
    by_cases hi : i < e
    · exact Subring.mem_inf.2 ⟨hcA i (Finset.mem_range.2 hi), hcK i⟩
    · have h0 : R2.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h1 : c i = 0 := by simp [hc_def, h0]
      rw [h1]
      exact S.zero_mem
  set R3 : Polynomial Ω := R2.map f with hR3_def
  have hR3 : (↑R3.coeffs : Set Ω) ⊆ S := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
    rw [hR3_def, Polynomial.coeff_map]
    exact hcS n
  set R4 := R3.toSubring S hR3 with hR4_def
  refine ⟨(R4.comp (Polynomial.X - Polynomial.C 1)).map S.subtype, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
    rw [Polynomial.coeff_map]
    exact Subring.mem_inf.1 ((R4.comp (Polynomial.X - Polynomial.C 1)).coeff n).2
  · rw [Polynomial.eval_map, Polynomial.eval₂_comp]
    have h1 : (Polynomial.X - Polynomial.C 1 : Polynomial S).eval₂ S.subtype ζ = w := by
      simp [hw_def]
    rw [h1, ← Polynomial.eval_map, hR4_def, Polynomial.map_toSubring, hR3_def,
      Polynomial.eval_map, hu1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLowDegreeCoordsModMul
section
open Polynomial

namespace GlobalTheory

theorem algebraMap_norm_dvd_polyX {k A : Type} [Field k] [CommRing A] [Algebra k[X] A] {n : ℕ}
    (b : Module.Basis (Fin n) k[X] A) (g : A) : g ∣ algebraMap k[X] A (Algebra.norm k[X] g) := by
  classical
  set M := Algebra.leftMulMatrix b g with hM
  have hCH : Polynomial.aeval g M.charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, map_zero, ← hM, Matrix.aeval_self_charpoly]
  have hsplit := Polynomial.X_mul_divX_add M.charpoly
  have h0 : g * Polynomial.aeval g M.charpoly.divX + algebraMap k[X] A (M.charpoly.coeff 0) = 0 := by
    have := congrArg (Polynomial.aeval g) hsplit
    rw [hCH, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at this
    exact this
  have hdet : Algebra.norm k[X] g = (-1) ^ n * M.charpoly.coeff 0 := by
    rw [Algebra.norm_eq_matrix_det b, ← hM, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
  rw [hdet, map_mul, eq_neg_of_add_eq_zero_right h0]
  exact ⟨-(algebraMap k[X] A ((-1) ^ n) * Polynomial.aeval g M.charpoly.divX), by ring⟩

theorem exists_lowDegree_coords_mod : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (g : A) (q : k[X]) (d : ℕ), g ≠ 0 → q ≠ 0 → (Algebra.norm k[X] g).natDegree + q.natDegree ≤ d + 1 →
 ∀ w : A, ∃ p : Fin n → k[X], (∀ i, (p i).natDegree ≤ d) ∧ w - ∑ i, p i • b i ∈ Ideal.span {g * algebraMap k[X] A q} := by
  intro k A _ _ _ _ n b g q d hg hq hdeg w
  classical
  haveI : Module.Free k[X] A := Module.Free.of_basis b
  haveI : Module.Finite k[X] A := Module.Finite.of_basis b
  have hN : Algebra.norm k[X] g ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  set p₀ := Algebra.norm k[X] g * q with hp₀
  have hp₀0 : p₀ ≠ 0 := mul_ne_zero hN hq
  have hp₀deg : p₀.natDegree ≤ d + 1 := by rw [hp₀, natDegree_mul hN hq]; exact hdeg
  refine ⟨fun i => b.repr w i % p₀, ?_, ?_⟩
  · intro i
    by_cases h0 : b.repr w i % p₀ = 0
    · simp [h0]
    · have hlt : (b.repr w i % p₀).degree < p₀.degree := EuclideanDomain.mod_lt _ hp₀0
      have := Polynomial.natDegree_lt_natDegree h0 hlt
      show (b.repr w i % p₀).natDegree ≤ d
      omega
  · have key : w - ∑ i, (b.repr w i % p₀) • b i
        = algebraMap k[X] A p₀ * ∑ i, (b.repr w i / p₀) • b i := by
      set a := b.repr w with ha
      have hw : w = ∑ i, a i • b i := (b.sum_repr w).symm
      rw [hw, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ← eq_sub_of_add_eq (EuclideanDomain.div_add_mod (a i) p₀), mul_smul,
        Algebra.smul_def]
    rw [key, Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := algebraMap_norm_dvd_polyX b g
    refine ⟨c * ∑ i, (b.repr w i / p₀) • b i, ?_⟩
    rw [hp₀, map_mul, hc]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulOfDetZero
section
namespace GlobalTheory.DetZeroFactorization

theorem exists_mul_of_det_zero {K : Type*} [Field K] (a b c d : K) (h : a * d - b * c = 0)
    (hn : ¬ (a = 0 ∧ c = 0)) : ∃ u : K, b = a * u ∧ d = c * u := by
  by_cases ha : a = 0
  · have hc : c ≠ 0 := fun hc => hn ⟨ha, hc⟩
    subst ha
    have hb : b = 0 := by
      have hbc : b * c = 0 := by linear_combination -h
      exact (mul_eq_zero.mp hbc).resolve_right hc
    refine ⟨d / c, by simp [hb], ?_⟩
    field_simp
  · refine ⟨b / a, by field_simp, ?_⟩
    rw [eq_comm, mul_div_assoc', div_eq_iff ha]
    linear_combination -h

theorem main : (let d1 : (q : ℕ) → Option (Fin q) → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ := @(fun (q : ℕ) (x : Option (Fin q)) ↦ match x with | Option.none => !![(↑q : ℤ), (0 : ℤ); (0 : ℤ), (1 : ℤ)] | Option.some u => !![(1 : ℤ), (↑(↑u : ℕ) : ℤ); (0 : ℤ), (↑q : ℤ)]); ∀ {q : ℕ}, Nat.Prime q → ∀ (δ : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ), Matrix.det δ = (↑q : ℤ) → ∃ (γ : Matrix.SpecialLinearGroup (Fin (2 : ℕ)) ℤ) (y : Option (Fin q)), δ = (↑γ : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ) * d1 q y) := by
  intro d1 q hq δ hdet
  have : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hdet' : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = q := by rw [← hdet, Matrix.det_fin_two]
  by_cases hdiv : (q : ℤ) ∣ δ 0 0 ∧ (q : ℤ) ∣ δ 1 0
  ·
    obtain ⟨⟨a', ha'⟩, ⟨c', hc'⟩⟩ := hdiv
    have h1 : a' * δ 1 1 - δ 0 1 * c' = 1 := by
      apply mul_left_cancel₀ hq0
      linear_combination hdet' - δ 1 1 * ha' + δ 0 1 * hc'
    refine ⟨⟨!![a', δ 0 1; c', δ 1 1], by rw [Matrix.det_fin_two_of]; exact h1⟩, none, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d1, Matrix.mul_apply, Fin.sum_univ_two, ha', hc'] <;> ring
  ·
    have h0 : (δ 0 0 : ZMod q) * δ 1 1 - δ 0 1 * δ 1 0 = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod q) hdet'
      push_cast at this
      rw [this, ZMod.natCast_self]
    have hn : ¬ ((δ 0 0 : ZMod q) = 0 ∧ (δ 1 0 : ZMod q) = 0) := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨u, hb, hd⟩ := exists_mul_of_det_zero (δ 0 0 : ZMod q) (δ 0 1) (δ 1 0) (δ 1 1) h0 hn
    obtain ⟨n, hnq, hnu⟩ : ∃ n : ℕ, n < q ∧ (n : ZMod q) = u :=
      ⟨u.val, ZMod.val_lt u, ZMod.natCast_zmod_val u⟩
    obtain ⟨b', hb'⟩ : (q : ℤ) ∣ δ 0 1 - δ 0 0 * (n : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hnu, hb, sub_self]
    obtain ⟨d', hd'⟩ : (q : ℤ) ∣ δ 1 1 - δ 1 0 * (n : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hnu, hd, sub_self]
    have h1 : δ 0 0 * d' - b' * δ 1 0 = 1 := by
      apply mul_left_cancel₀ hq0
      linear_combination hdet' - δ 0 0 * hd' + δ 1 0 * hb'
    refine ⟨⟨!![δ 0 0, b'; δ 1 0, d'], by rw [Matrix.det_fin_two_of]; exact h1⟩,
      some ⟨n, hnq⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d1, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

end GlobalTheory.DetZeroFactorization
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNatCoeffsDetSumSmulNeZero
section
open scoped Matrix
open Polynomial

namespace GlobalTheory

theorem det_affine_eval {K : Type} [Field K] {m : ℕ} (U V : Matrix (Fin m) (Fin m) K) (t : K) :
    ((X : K[X]) • V.map C + U.map C).det.eval t = (U + t • V).det := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [add_comm]
  ring

theorem exists_nat_det_ne_zero_affine {K : Type} [Field K] [CharZero K] {m : ℕ}
    (U V : Matrix (Fin m) (Fin m) K) (t : K) (h : (U + t • V).det ≠ 0) :
    ∃ k : ℕ, (U + (k : K) • V).det ≠ 0 := by
  classical
  set p : K[X] := ((X : K[X]) • V.map C + U.map C).det
  have hp : p ≠ 0 := by
    intro h0
    apply h
    rw [← det_affine_eval]
    simp [p, h0]
  by_contra hall
  push_neg at hall
  have hsub : Set.range (fun k : ℕ => (k : K)) ⊆ (p.roots.toFinset : Set K) := by
    rintro _ ⟨k, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot, det_affine_eval]
    exact hall k
  have hinf : (Set.range (fun k : ℕ => (k : K))).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  exact hinf ((p.roots.toFinset.finite_toSet).subset hsub)

theorem exists_nat_coeffs_on_finset_det_sum_ne_zero {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (s : Finset (Fin n)) :
    ∀ b : Fin n → K, (∑ i, b i • T i).det ≠ 0 →
      ∃ b' : Fin n → K, (∑ i, b' i • T i).det ≠ 0 ∧ ∀ i ∈ s, ∃ k : ℕ, b' i = k := by
  classical
  induction s using Finset.induction_on with
  | empty => intro b hb; exact ⟨b, hb, by simp⟩
  | insert j s hj ih =>
    intro b hb
    obtain ⟨b₁, hb₁, hs⟩ := ih b hb
    have key : ∀ t : K, ∑ i, Function.update b₁ j t i • T i
        = (∑ i, Function.update b₁ j 0 i • T i) + t • T j := by
      intro t
      have h1 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j t i • T i) (Finset.mem_univ j)
      have h2 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j 0 i • T i) (Finset.mem_univ j)
      have h3 : ∑ i ∈ Finset.univ.erase j, Function.update b₁ j t i • T i
          = ∑ i ∈ Finset.univ.erase j, Function.update b₁ j 0 i • T i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
          Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [← h1, ← h2, h3]
      simp
    have hb₁' : ((∑ i, Function.update b₁ j 0 i • T i) + b₁ j • T j).det ≠ 0 := by
      rw [← key, Function.update_eq_self]; exact hb₁
    obtain ⟨k, hk⟩ := exists_nat_det_ne_zero_affine _ _ _ hb₁'
    refine ⟨Function.update b₁ j (k : K), by rw [key]; exact hk, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ⟨k, by simp⟩
    · obtain ⟨k', hk'⟩ := hs i hi'
      refine ⟨k', ?_⟩
      rw [Function.update_of_ne (by rintro rfl; exact hj hi')]
      exact hk'

theorem exists_nat_coeffs_det_ne_zero : ∀ {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (b : Fin n → K),
    (∑ i, b i • T i).det ≠ 0 → ∃ a : Fin n → ℕ, (∑ i, (a i : K) • T i).det ≠ 0 := by
  intro K _ _ m n T b hb
  obtain ⟨b', hb', hs⟩ := exists_nat_coeffs_on_finset_det_sum_ne_zero T Finset.univ b hb
  choose a ha using fun i => hs i (Finset.mem_univ i)
  refine ⟨a, ?_⟩
  simp_rw [← ha]; exact hb'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimeDvdMem
section
universe u_1

namespace GlobalTheory.PrimeDivisorMembership

theorem exists_prime_dvd_mem : ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R), Ideal.IsPrime P → ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : R) ∈ P → ∃ (q : ℕ), Nat.Prime q ∧ q ∣ n ∧ (↑q : R) ∈ P := by
  intro R _ P hP n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      rw [Nat.cast_one] at hmem
      exact absurd ((Ideal.eq_top_iff_one P).2 hmem) hP.ne_top
    · have hmin := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hmem' : (n.minFac : R) * (m : R) ∈ P := by
        rw [← Nat.cast_mul, ← hm]
        exact hmem
      rcases hP.mem_or_mem hmem' with hq | hq
      · exact ⟨n.minFac, hmin, Nat.minFac_dvd n, hq⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm
          exact hn hm
        have hlt : m < n := by
          calc m < 2 * m := by omega
            _ ≤ n.minFac * m := Nat.mul_le_mul_right _ hmin.two_le
            _ = n := hm.symm
        obtain ⟨q, hq1, hq2, hq3⟩ := ih m hlt hm0 hq
        exact ⟨q, hq1, hq2.trans (Dvd.intro_left _ hm.symm), hq3⟩

end GlobalTheory.PrimeDivisorMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimeNatCastMem
section
namespace GlobalTheory.PrimeNatCastMembership

theorem exists_prime_natCast_mem {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P)
    (n : ℕ) (hn : n ≠ (0 : ℕ)) (hmem : (↑n : A) ∈ P) :
    ∃ (q : ℕ), Nat.Prime q ∧ (↑q : A) ∈ P := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hmem)) hP.ne_top
    · obtain ⟨q, hq, m, hm⟩ := Nat.exists_prime_and_dvd h1
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hn (by simpa using hm)
      have hlt : m < n := by
        have h2 := hq.two_le
        have h3 := Nat.pos_of_ne_zero hm0
        rw [hm]
        nlinarith
      have hprod : (q : A) * (m : A) ∈ P := by
        rw [← Nat.cast_mul, ← hm]
        exact hmem
      rcases hP.mem_or_mem hprod with h | h
      · exact ⟨q, hq, h⟩
      · exact ih m hlt hm0 h

end GlobalTheory.PrimeNatCastMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtension
section
open scoped NNReal TensorProduct

namespace GlobalTheory

open Polynomial

theorem exists_spectralValuation (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (f : AbsoluteValue K ℝ) (hna : IsNonarchimedean f) (hnt : f.IsNontrivial)
    (hc : CompleteSpace (WithAbs f)) :
    ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧
      ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  obtain ⟨a, ha⟩ := hnt.exists_abv_gt_one
  letI : NontriviallyNormedField (WithAbs f) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by
      intro h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by
      rw [WithAbs.norm_toAbs_eq]; exact ha.ne'⟩
  haveI : IsUltrametricDist (WithAbs f) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs
  haveI : IsScalarTower K (WithAbs f) Ω := inferInstance
  haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)
  have hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f)) := by
    intro x
    have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmap : (minpoly K x).map (algebraMap K (WithAbs f)) =
        Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x) := by
      rw [Polynomial.mapEquiv_apply]; rfl
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · rw [hmap]; exact (MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)
    · rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K x
    · exact (minpoly.monic hx).map _
  let v : Valuation Ω ℝ≥0 :=
    { toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩
      map_zero' := by ext; exact spectralNorm_zero
      map_one' := by ext; exact spectralNorm_one
      map_mul' := fun x y => by
        ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y
      map_add_le_max' := fun x y => by
        show spectralNorm (WithAbs f) Ω (x + y) ≤ max (spectralNorm (WithAbs f) Ω x) (spectralNorm (WithAbs f) Ω y)
        exact isNonarchimedean_spectralNorm x y }
  have hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x := fun _ => rfl
  refine ⟨v, fun x => ?_, fun x => ?_⟩
  · rw [hv]
    have : algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x) := rfl
    rw [this, spectralNorm_extends, WithAbs.norm_toAbs_eq]
  · have hx : IsIntegral (WithAbs f) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hv]
    show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _
    rw [spectralValue_le_one_iff (minpoly.monic hx), hmin x]
    refine forall_congr' fun i => ?_
    rw [Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
    rfl

end GlobalTheory
end


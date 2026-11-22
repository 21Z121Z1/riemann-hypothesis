import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyLeftMulBasis
section
open Polynomial

namespace GlobalTheory.TraceDetSplit

theorem det_aeval_prod {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (s : Multiset K) :
    (aeval N (s.map fun r => X - C r).prod).det
      = (-1) ^ (n * s.card) * (s.map N.charpoly.eval).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have h1 : (aeval N (X - C r)).det = (-1) ^ n * N.charpoly.eval r := by
      have e : Matrix.scalar (Fin n) r - N = -(N - algebraMap K (Matrix (Fin n) (Fin n) K) r) := by
        rw [neg_sub, Matrix.algebraMap_eq_diagonal]
        rfl
      rw [Matrix.eval_charpoly, e, Matrix.det_neg, Fintype.card_fin, map_sub, aeval_X, aeval_C,
        ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, map_mul, Matrix.det_mul, ih, h1]
    ring

theorem det_aeval {E : Type} [Field E] {n : ℕ} (N : Matrix (Fin n) (Fin n) E) (p : E[X])
    (hp : p.Monic) :
    (aeval N p).det = (-1) ^ (n * p.natDegree) * resultant p N.charpoly := by
  classical
  let φ := algebraMap E (AlgebraicClosure E)
  apply φ.injective
  have hp' : (p.map φ).Monic := hp.map φ
  have hs : (p.map φ).Splits := IsAlgClosed.splits _
  have hd : (p.map φ).natDegree = p.natDegree := natDegree_map φ
  have key : φ.mapMatrix (aeval N p) = aeval (N.map φ) (p.map φ) := by
    rw [aeval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId E (AlgebraicClosure E))) N p).symm
  rw [RingHom.map_det, key, map_mul, map_pow, map_neg, map_one, ← resultant_map_map,
    ← Matrix.charpoly_map]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hp']
  rw [det_aeval_prod, ← hs.natDegree_eq_card_roots, hd, ← hd,
    resultant_eq_prod_eval _ _ _ (by rw [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim]) hs,
    hp'.leadingCoeff, one_pow, one_mul]

theorem det_trace_monic {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (g : A)
    (e : Fin n → A) (q : Fin n → E[X]) (hd : ∀ k, (q k).natDegree = k) (hm : ∀ k, (q k).Monic) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l)).det
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)).det := by
  classical
  have hM : (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)) =
      (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)) *
        Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [aeval_eq_sum_range' (n := n) (by rw [hd k]; exact k.isLt), Finset.sum_mul, map_sum,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul]
  have hC : (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun k _ => ?_
      simp only [Matrix.of_apply]
      have := (hm k).coeff_natDegree
      rwa [hd k] at this
    · intro i j hij
      simp only [Matrix.of_apply]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hd i]
      exact hij
  rw [hM, Matrix.det_mul, hC, one_mul]

theorem charpoly_leftMul_basis {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] {n : ℕ} (g : A) (w : Module.Basis (Fin n) E A) :
    (Algebra.leftMulMatrix w g).charpoly = (LinearMap.mulLeft E g).charpoly := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  rfl

theorem trace_mul_eq {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (x : Fin n → A)
    (h : A) (w : Module.Basis (Fin n) E A) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * h * w l))
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * w l)) * Algebra.leftMulMatrix w h := by
  ext k l
  simp only [Matrix.of_apply, Matrix.mul_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [mul_assoc, ← w.sum_repr (h * w l)]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.TraceDetSplit

open GlobalTheory.TraceDetSplit in

theorem GlobalTheory.det_trace_pow_prod : ∀ (E A₁ A₂ : Type) [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) (a b : ℕ) (u : Module.Basis (Fin a) E A₁) (w : Module.Basis (Fin b) E A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → ∃ ε : E, ε * ε = 1 ∧ (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂) ((g₁, g₂) ^ (k : ℕ) * Fin.addCases (fun i => (u i, 0)) (fun j => (0, w j)) l)).det = ε * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly * (Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)).det * (Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)).det := by
  intro E A₁ A₂ _ _ _ _ _ _ _ g₁ g₂ a b u w _
  classical
  have hdeg₁ : (LinearMap.mulLeft E g₁).charpoly.natDegree = a := by
    rw [LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis u, Fintype.card_fin]
  have hCH : aeval g₁ (LinearMap.mulLeft E g₁).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g₁)
    have h2 : aeval (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₁).charpoly =
        Algebra.lmul E A₁ (aeval g₁ (LinearMap.mulLeft E g₁).charpoly) :=
      Polynomial.aeval_algHom_apply (Algebra.lmul E A₁) g₁ _
    rw [h2] at h
    simpa using LinearMap.congr_fun h 1
  let q : Fin (a + b) → E[X] := fun k =>
    if (k : ℕ) < a then X ^ (k : ℕ) else X ^ ((k : ℕ) - a) * (LinearMap.mulLeft E g₁).charpoly
  have hd : ∀ k, (q k).natDegree = k := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp [q, hk]
    · simp only [q, hk, if_false]
      rw [(monic_X_pow _).natDegree_mul (LinearMap.charpoly_monic _), natDegree_X_pow, hdeg₁]
      omega
  have hm : ∀ k, (q k).Monic := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp only [q, hk, if_true]
      exact monic_X_pow _
    · simp only [q, hk, if_false]
      exact (monic_X_pow _).mul (LinearMap.charpoly_monic _)
  refine ⟨(-1) ^ (a * b), by rw [← mul_pow, neg_one_mul, neg_neg, one_pow], ?_⟩
  rw [det_trace_monic (g₁, g₂) _ q hd hm]
  let M := Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
    (aeval (g₁, g₂) (q k) * Fin.addCases (fun i => ((u i, 0) : A₁ × A₂)) (fun j => (0, w j)) l)
  let T₁ := Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)
  let T₂ := Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)
  let S := Matrix.of fun k l : Fin b =>
    Algebra.trace E A₂ (g₂ ^ (k : ℕ) * aeval g₂ (LinearMap.mulLeft E g₁).charpoly * w l)
  have hblock : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks T₁ (Matrix.of fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)) 0 S := by
    ext (i | i) (l | l)
    · simp [M, T₁, q, Algebra.trace_prod_apply, aeval_prod_apply]
    · simp [M]
    · simp [M, q, Algebra.trace_prod_apply, aeval_prod_apply, hCH]
    · simp [M, S, q, Algebra.trace_prod_apply, aeval_prod_apply, mul_assoc]
  have hS : S = T₂ * Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly) :=
    trace_mul_eq (fun k : Fin b => g₂ ^ (k : ℕ)) _ w
  have hres : (Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly)).det =
      (-1) ^ (b * a) * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly := by
    rw [← Polynomial.aeval_algHom_apply, det_aeval _ _ (LinearMap.charpoly_monic _),
      charpoly_leftMul_basis, hdeg₁]
  calc M.det = (M.submatrix finSumFinEquiv finSumFinEquiv).det :=
        (Matrix.det_submatrix_equiv_self _ _).symm
    _ = T₁.det * S.det := by rw [hblock, Matrix.det_fromBlocks_zero₂₁]
    _ = _ := by
      rw [hS, Matrix.det_mul, hres]
      ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffAevalOneAddXPowSubOneNeZero
section
open scoped BigOperators

namespace GlobalTheory

private lemma one_add_X_pow_prime_pow_sub_one {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]
    (m : ℕ) : (1 + Polynomial.X : Polynomial k) ^ (l ^ m) - 1 = Polynomial.X ^ (l ^ m) := by
  rw [add_pow_char_pow, one_pow, add_sub_cancel_left]

private lemma coeff_zero_aeval_of_coeff_zero_eq_zero {k σ : Type} [Field k] (g : σ → Polynomial k)
    (hg : ∀ q, (g q).coeff 0 = 0) (p : MvPolynomial σ k) :
    (MvPolynomial.aeval g p).coeff 0 = p.coeff 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p q hp =>
    classical
    rw [map_mul, MvPolynomial.aeval_X, Polynomial.mul_coeff_zero, hg, mul_zero,
      MvPolynomial.coeff_mul_X']
    simp

theorem coeff_aeval_one_add_X_pow_sub_one_ne_zero :
    ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by
  intro k σ _ _ l M _ _ D u n e hu hD hlt
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hgX : ∀ q, ((1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) = Polynomial.X ^ (l ^ e q) :=
    fun q => one_add_X_pow_prime_pow_sub_one l (e q)
  simp only [hgX]

  have hideal : ∀ r ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)),
      (Polynomial.X : Polynomial k) ^ (l ^ M) ∣
        MvPolynomial.aeval (fun q => (Polynomial.X : Polynomial k) ^ (l ^ e q)) r := by
    intro r hr
    have hle : Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) ≤
        Ideal.comap (MvPolynomial.aeval (fun q => (Polynomial.X : Polynomial k) ^ (l ^ e q)))
          (Ideal.span {(Polynomial.X : Polynomial k) ^ (l ^ M)}) := by
      rw [Ideal.span_le]
      rintro _ ⟨q, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, MvPolynomial.aeval_X, ← pow_mul, pow_mul',
        Ideal.mem_span_singleton]
      exact dvd_pow_self _ (pow_pos hl _).ne'
    exact Ideal.mem_span_singleton.mp (hle hr)
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)),
      D = u * ∏ q, MvPolynomial.X q ^ n q + r := ⟨_, hD, by ring⟩
  rw [map_add, Polynomial.coeff_add, (Polynomial.X_pow_dvd_iff.mp (hideal r hr)) _ hlt, add_zero,
    map_mul, map_prod]
  simp only [map_pow, MvPolynomial.aeval_X, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ q, l ^ e q * n q = ∑ q, n q * l ^ e q :=
    Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [hsum, Polynomial.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, coeff_zero_aeval_of_coeff_zero_eq_zero _ _ u]
  · exact hu
  · intro q
    rw [Polynomial.coeff_X_pow, if_neg (pow_pos hl _).ne]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemOfCharpolyCoeffMem
section
open scoped BigOperators

namespace GlobalTheory

namespace Amitsur

open Matrix Polynomial

theorem det_one_sub_smul_mem_of_nilpotent {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (U : Subring A) (t : A) (N : ℕ) (ht : t ^ N = 0) (S : Set (Matrix ι ι A))
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hsm : ∀ a ∈ S, t • a ∈ S)
    (hdet : ∀ a ∈ S, (1 - a).det ∈ U) :
    ∀ B ∈ AddSubmonoid.closure S, (1 - t • B).det ∈ U := by
  have hpow : ∀ (k : ℕ), ∀ a ∈ S, t ^ k • a ∈ S := by
    intro k a ha
    induction k with
    | zero => simpa using ha
    | succ k ih => rw [pow_succ', mul_smul]; exact hsm _ ih
  have hM1 : ∀ a ∈ S, ∀ y ∈ AddSubmonoid.closure S, a * y ∈ AddSubmonoid.closure S := by
    intro a ha y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem x hx => exact AddSubmonoid.subset_closure (hmul a ha x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  have hM2 : ∀ y ∈ AddSubmonoid.closure S, t • y ∈ AddSubmonoid.closure S := by
    intro y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem x hx => exact AddSubmonoid.subset_closure (hsm x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  have hM3 : ∀ a ∈ S, ∀ (j : ℕ), ∀ y ∈ AddSubmonoid.closure S,
      a ^ j * y ∈ AddSubmonoid.closure S := by
    intro a ha j y hy
    induction j with
    | zero => simpa using hy
    | succ j ih => rw [pow_succ', mul_assoc]; exact hM1 a ha _ ih
  have step : ∀ e : ℕ, (∀ C ∈ AddSubmonoid.closure S, (1 - t ^ (e + 2) • C).det ∈ U) →
      ∀ B ∈ AddSubmonoid.closure S, (1 - t ^ (e + 1) • B).det ∈ U := by
    intro e ih
    have key : ∀ B ∈ AddSubmonoid.closure S, ∀ C ∈ AddSubmonoid.closure S,
        (1 - t ^ (e + 1) • (B + t • C)).det ∈ U := by
      intro B hB
      induction hB using AddSubmonoid.closure_induction_left with
      | zero =>
        intro C hC
        have := ih C hC
        rwa [zero_add, smul_smul, ← pow_succ]
      | add_left s hs B hB ihB =>
        intro C hC
        set a : Matrix ι ι A := t ^ (e + 1) • s with ha
        have haS : a ∈ S := hpow _ _ hs
        have haN : a ^ N = 0 := by
          rw [ha, _root_.smul_pow, ← pow_mul, add_mul, one_mul, pow_add, ht, mul_zero, zero_smul]
        set g : Matrix ι ι A := ∑ j ∈ Finset.range N, a ^ j with hg
        have hga : (1 - a) * g = 1 := by
          rw [hg, mul_neg_geom_sum, haN, sub_zero]
        set y : Matrix ι ι A := B + t • C with hy
        have hyM : y ∈ AddSubmonoid.closure S := add_mem hB (hM2 C hC)
        have hgy : g * y ∈ AddSubmonoid.closure S := by
          rw [hg, Finset.sum_mul]
          exact sum_mem fun j _ => hM3 a haS j y hyM
        have hC' : C + (t ^ e • s) * (g * y) ∈ AddSubmonoid.closure S :=
          add_mem hC (hM1 _ (hpow _ _ hs) _ hgy)
        have h1 := ihB _ hC'
        have e1 : B + t • (C + (t ^ e • s) * (g * y)) = g * y := by
          have h2 : t • ((t ^ e • s) * (g * y)) = a * (g * y) := by
            rw [← smul_mul_assoc, smul_smul, ← pow_succ']
          have h3 : g * y = (1 - a) * g * y + a * (g * y) := by noncomm_ring
          rw [smul_add, h2, ← add_assoc, ← hy]
          conv_rhs => rw [h3, hga, one_mul]
        rw [e1] at h1
        have e2 : 1 - t ^ (e + 1) • (s + B + t • C) = (1 - a) * (1 - t ^ (e + 1) • (g * y)) := by
          rw [mul_sub, mul_one, mul_smul_comm, ← mul_assoc, hga, one_mul, add_assoc, ← hy,
            smul_add, ← ha, sub_sub]
        rw [e2, det_mul]
        exact U.mul_mem (hdet a haS) h1
    intro B hB
    simpa using key B hB 0 (zero_mem _)
  have all : ∀ k e : ℕ, N ≤ e + k → ∀ B ∈ AddSubmonoid.closure S,
      (1 - t ^ (e + 1) • B).det ∈ U := by
    intro k
    induction k with
    | zero =>
      intro e he B _
      have : t ^ (e + 1) = 0 := pow_eq_zero_of_le (by omega) ht
      simp [this]
    | succ k ih =>
      intro e he
      exact step e (ih (e + 1) (by omega))
  intro B hB
  simpa using all N 0 (by omega) B hB

theorem eval₂_charpolyRev {R A ι : Type*} [CommRing R] [CommRing A] [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (u : A) (s : Matrix ι ι R) :
    (1 - u • s.map φ).det = s.charpolyRev.eval₂ φ u := by
  rw [← coe_eval₂RingHom, Matrix.charpolyRev, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring

theorem det_sum_smul_mem {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (T : Subring R) (S : Set (Matrix ι ι R)) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hchar : ∀ a ∈ S, ∀ j, a.charpoly.coeff j ∈ T)
    (F : Finset κ) (c : κ → R) (s : κ → Matrix ι ι R) (hc : ∀ k, c k ∈ T) (hs : ∀ k, s k ∈ S) :
    (∑ k ∈ F, c k • s k).det ∈ T := by
  nontriviality R
  set n := Fintype.card ι with hn
  let I : Ideal R[X] := Ideal.span {X ^ (n + 1)}
  let π : R[X] →+* R[X] ⧸ I := Ideal.Quotient.mk I
  let φ : R →+* R[X] ⧸ I := π.comp C
  let U : Subring (R[X] ⧸ I) := (π.comp (Polynomial.mapRingHom T.subtype)).range
  have hφ : ∀ x ∈ T, φ x ∈ U := fun x hx => ⟨C ⟨x, hx⟩, by simp [φ]⟩
  have htU : π X ∈ U := ⟨X, by simp⟩
  have ht : π X ^ (n + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  let S' : Set (Matrix ι ι (R[X] ⧸ I)) := {a | ∃ u ∈ U, ∃ b ∈ S, a = u • b.map φ}
  have main := det_one_sub_smul_mem_of_nilpotent U (π X) (n + 1) ht S' (by
      rintro _ ⟨u, hu, a, ha, rfl⟩ _ ⟨v, hv, b, hb, rfl⟩
      refine ⟨u * v, U.mul_mem hu hv, a * b, hmul a ha b hb, ?_⟩
      rw [Matrix.map_mul, smul_mul_smul_comm]) (by
      rintro _ ⟨u, hu, a, ha, rfl⟩
      exact ⟨π X * u, U.mul_mem htU hu, a, ha, by rw [smul_smul]⟩) (by
      rintro _ ⟨u, hu, a, ha, rfl⟩
      rw [eval₂_charpolyRev, eval₂_eq_sum, Polynomial.sum]
      refine U.sum_mem fun j _ => U.mul_mem (hφ _ ?_) (U.pow_mem hu _)
      rw [← reverse_charpoly, coeff_reverse]
      exact hchar a ha _)
    ((∑ k ∈ F, c k • s k).map φ) (by
      have : (∑ k ∈ F, c k • s k).map φ = ∑ k ∈ F, φ (c k) • (s k).map φ := by
        ext i j
        simp [Matrix.sum_apply]
      rw [this]
      exact sum_mem fun k _ => AddSubmonoid.subset_closure ⟨_, hφ _ (hc k), _, hs k, rfl⟩)
  set B := ∑ k ∈ F, c k • s k
  rw [eval₂_charpolyRev] at main
  have h1 : B.charpolyRev.eval₂ φ (π X) = π B.charpolyRev := by
    rw [← Polynomial.hom_eval₂, eval₂_C_X]
  rw [h1] at main
  obtain ⟨p, hp⟩ := main
  have h2 : X ^ (n + 1) ∣ p.map T.subtype - B.charpolyRev :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hp)
  have h3 := X_pow_dvd_iff.1 h2 n (by omega)
  rw [coeff_sub, sub_eq_zero, coeff_map, ← reverse_charpoly, coeff_reverse,
    charpoly_natDegree_eq_dim, ← hn, revAt_le le_rfl, Nat.sub_self] at h3
  rw [det_eq_sign_charpoly_coeff, ← h3]
  exact T.mul_mem (T.pow_mem (T.neg_mem T.one_mem) _) (p.coeff n).2

end Amitsur

theorem coeff_det_generic_sum_mem_of_charpoly_coeff_mem :
    ∀ {O X G : Type} [CommRing O] [Monoid G] (T : Subalgebra O (X → O)) (n : ℕ)
      (r : X → G →* Matrix (Fin n) (Fin n) O),
      (∀ g j, (fun x => (r x g).charpoly.coeff j) ∈ T) →
      ∀ (m : ℕ) (g : Fin m → G) (d : Fin m →₀ ℕ),
        (fun x => MvPolynomial.coeff d (Matrix.det (∑ k,
          (MvPolynomial.X k : MvPolynomial (Fin m) O) • (r x (g k)).map MvPolynomial.C))) ∈ T := by
  intro O X G _ _ T n r h m g d
  let ρ : G → Matrix (Fin n) (Fin n) (X → O) := fun a => Matrix.of fun i j x => r x a i j
  have hρx : ∀ a x, (ρ a).map (Pi.evalRingHom (fun _ : X => O) x) = r x a := by
    intro a x; ext i j; simp [ρ]
  have hρ : ∀ a b, ρ (a * b) = ρ a * ρ b := by
    intro a b
    ext i j x
    simp [ρ, Matrix.mul_apply]
  have hch : ∀ a j, (ρ a).charpoly.coeff j ∈ T := by
    intro a j
    convert h a j using 1
    funext x
    rw [← hρx, Matrix.charpoly_map, Polynomial.coeff_map]
    rfl
  let T' : Subring (MvPolynomial (Fin m) (X → O)) :=
    (MvPolynomial.map (σ := Fin m) T.toSubring.subtype).range
  have main := Amitsur.det_sum_smul_mem T'
    (Set.range fun a => (ρ a).map (MvPolynomial.C (σ := Fin m))) (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨a * b, by simp only [hρ, Matrix.map_mul]⟩) (by
      rintro _ ⟨a, rfl⟩ j
      rw [Matrix.charpoly_map, Polynomial.coeff_map]
      exact ⟨MvPolynomial.C ⟨_, hch a j⟩, MvPolynomial.map_C _ _⟩)
    Finset.univ (fun k => MvPolynomial.X k) (fun k => (ρ (g k)).map MvPolynomial.C)
    (fun k => ⟨MvPolynomial.X k, by simp⟩) (fun k => ⟨g k, rfl⟩)
  obtain ⟨p, hp⟩ := main
  have h1 : MvPolynomial.coeff d (MvPolynomial.map T.toSubring.subtype p) ∈ T := by
    rw [MvPolynomial.coeff_map]
    exact (MvPolynomial.coeff d p).2
  rw [hp] at h1
  convert h1 using 1
  funext x
  change _ = Pi.evalRingHom (fun _ : X => O) x (MvPolynomial.coeff d _)
  rw [← MvPolynomial.coeff_map, RingHom.map_det]
  congr 2
  ext1 i j
  simp [Matrix.sum_apply, ρ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffMemOfPowMul
section
namespace GlobalTheory.OrdMul

open MvPolynomial

theorem coeff_mem_of_mul {O : Type} [CommRing O] (I : Ideal O) {ι : Type} (K : Set ι) (q : ι)
    (hq : q ∉ K) (a F : MvPolynomial ι O) (N : ℕ) (h0 : a.coeff 0 = 0)
    (hu : IsUnit (a.coeff (Finsupp.single q 1)))
    (H : ∀ m : ι →₀ ℕ, m.degree < N + 1 → (∀ j ∈ K, m j = 0) → (a * F).coeff m ∈ I) :
    ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  classical

  have key : ∀ n : ℕ, ∀ m : ι →₀ ℕ, m q + 2 * (m.erase q).degree = n → m.degree < N →
      (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hμ hm hK
      set m' : ι →₀ ℕ := m + Finsupp.single q 1 with hm'
      have hdeg' : m'.degree < N + 1 := by
        rw [hm', map_add, Finsupp.degree_single]; omega
      have hK' : ∀ j ∈ K, m' j = 0 := by
        intro j hj
        have hqj : q ≠ j := fun h => hq (h ▸ hj)
        simp [hm', hK j hj, Finsupp.single_apply, hqj]
      have hH := H m' hdeg' hK'
      rw [MvPolynomial.coeff_mul] at hH
      have hmem : (Finsupp.single q 1, m) ∈ Finset.HasAntidiagonal.antidiagonal m' := by
        rw [Finset.HasAntidiagonal.mem_antidiagonal, hm']; exact add_comm _ _
      rw [← Finset.add_sum_erase _ _ hmem] at hH
      have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m').erase (Finsupp.single q 1, m),
          a.coeff x.1 * F.coeff x.2 ∈ I := by
        refine Ideal.sum_mem _ (fun x hx => ?_)
        obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        by_cases hi : x.1 = 0
        · rw [hi, h0, zero_mul]; exact I.zero_mem
        · apply I.mul_mem_left
          have hiq : x.1 ≠ Finsupp.single q 1 := by
            intro h
            apply hne
            refine Prod.ext h ?_
            rw [h, hm', add_comm m] at hx
            exact add_left_cancel hx
          have hxq : x.1 q + x.2 q = m q + 1 := by
            have := congrArg (fun f : ι →₀ ℕ => f q) hx
            simpa [hm'] using this
          have hxe : x.1.erase q + x.2.erase q = m.erase q := by
            have := congrArg (Finsupp.erase q) hx
            simpa [hm', Finsupp.erase_add] using this
          have hD : (x.1.erase q).degree + (x.2.erase q).degree = (m.erase q).degree := by
            rw [← map_add, hxe]
          have hdx : x.1.degree + x.2.degree = m.degree + 1 := by
            have := congrArg Finsupp.degree hx
            simpa [hm'] using this
          have hd1 : x.1.degree ≠ 0 := fun h => hi ((Finsupp.degree_eq_zero_iff _).mp h)

          have hw : 2 ≤ x.1 q + 2 * (x.1.erase q).degree := by
            by_cases he : x.1.erase q = 0
            · have hs : Finsupp.single q (x.1 q) = x.1 := by
                simpa [he] using Finsupp.single_add_erase q x.1
              have h0' : x.1 q ≠ 0 := by
                intro h; apply hi; rw [← hs, h, Finsupp.single_zero]
              have h1' : x.1 q ≠ 1 := by
                intro h; apply hiq; rw [← hs, h]
              omega
            · have : (x.1.erase q).degree ≠ 0 := fun h => he ((Finsupp.degree_eq_zero_iff _).mp h)
              omega
          refine ih (x.2 q + 2 * (x.2.erase q).degree) (by omega) x.2 rfl (by omega) ?_
          intro j hj
          have h1 := hK' j hj
          rw [← hx] at h1
          simp only [Finsupp.add_apply] at h1
          omega
      have hmain : a.coeff (Finsupp.single q 1) * F.coeff m ∈ I :=
        (Ideal.add_mem_iff_left I hrest).mp hH
      exact (Ideal.unit_mul_mem_iff_mem I hu).mp hmain
  exact fun m hm hK => key _ m rfl hm hK

theorem coeff_mem_of_pow_mul : ∀ (O : Type) [CommRing O] (I : Ideal O) (ι : Type) (K : Set ι) (q : ι), q ∉ K → ∀ (a F : MvPolynomial ι O) (N k : ℕ), a.coeff 0 = 0 → IsUnit (a.coeff (Finsupp.single q 1)) → (∀ m : ι →₀ ℕ, m.degree < N + k → (∀ j ∈ K, m j = 0) → (a ^ k * F).coeff m ∈ I) → ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  intro O _ I ι K q hq a F N k h0 hu H
  induction k generalizing F N with
  | zero =>
    intro m hm hK
    simpa using H m (by simpa using hm) hK
  | succ k ih =>
    refine coeff_mem_of_mul I K q hq a F N h0 hu ?_
    refine ih (a * F) (N + 1) ?_
    intro m hm hK
    have := H m (by omega) hK
    rwa [pow_succ, mul_assoc] at this

end GlobalTheory.OrdMul
end


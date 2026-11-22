import Formalism.PolynomialDimension.Bundle0001

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.ExistsNonzeroExchangedMinorHolds
section
open scoped BigOperators
open Finset Matrix

namespace Formalism.CountingSumsFrames

theorem submatrix_swapCol {R : Type} [CommRing R] {r k : ℕ} (h : r ≤ k) (H : Matrix (Fin r) (Fin k) R)
    (i : Fin r) (c : Fin k) :
    H.submatrix id (swapCol r k h i c) = (H.submatrix id (Fin.castLE h)).updateCol i (fun m => H m c) := by
  ext m j
  by_cases hj : j = i
  · subst hj
    simp [swapCol]
  · simp [swapCol, hj]

theorem piMinor_map {p r k : ℕ} [Fact p.Prime] {F A : Type} [Field F] [CharP F p] [CommRing A] [Algebra F A]
    [Nontrivial A] (H : Matrix (Fin r) (Fin k) F) (pos : Fin r → ℕ) (t : Fin r → Fin r → A) (zj : ℕ)
    (cols : Fin r → Fin k) (hpos : ∀ l, pos l ≤ zj) :
    piMinor p r k (H.map (algebraMap F A)) pos t zj cols =
      (Matrix.of fun l m => t l m ^ p ^ (zj - pos l)).det *
        algebraMap F A ((H.submatrix id cols).det ^ p ^ zj) := by
  have : CharP A p := charP_of_injective_algebraMap (algebraMap F A).injective p
  have : ExpChar A p := ExpChar.prime (Fact.out : p.Prime)
  have : ExpChar F p := ExpChar.prime (Fact.out : p.Prime)
  let g : F →+* A := (algebraMap F A).comp (iterateFrobenius F p zj)
  have hg : ∀ x, g x = algebraMap F A (x ^ p ^ zj) := fun x => by
    simp [g, iterateFrobenius_def]
  have hmat : (Matrix.of fun l c' => (frameRow p r k (H.map (algebraMap F A)) (pos l) (t l) (cols c')) ^ p ^ (zj - pos l)) =
      (Matrix.of fun l m => t l m ^ p ^ (zj - pos l)) * (g.mapMatrix (H.submatrix id cols)) := by
    ext l c'
    simp only [Matrix.of_apply, frameRow, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply,
      RingHom.mapMatrix_apply, Matrix.submatrix_apply, id, hg]
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le (hpos l), map_pow]
  unfold piMinor
  rw [hmat, Matrix.det_mul, ← RingHom.map_det, hg]

end Formalism.CountingSumsFrames
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.FockGaussComparisonHolds
section
open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem fock_mult_fact_le {α : Type*} (p : ℕ) (f : α → ℕ) (s : Finset α) :
    (Nat.multinomial s f).factorization p ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
  have h1 := Nat.factorization_choose_le_log (p := p) (n := f a + ∑ i ∈ s, f i) (k := f a)
  have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
    Nat.log_mono_right (Nat.le_add_left _ _)
  have h3 := Nat.mul_le_mul_left s.card h2
  rw [add_one_mul]
  omega

theorem fock_mult_val_le {α : Type*} (p : ℕ) [hp : Fact p.Prime] (f : α → ℕ) (s : Finset α) :
    padicValNat p (Nat.multinomial s f) ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  rw [← Nat.factorization_def _ hp.out]
  exact fock_mult_fact_le p f s

theorem fock_val_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h1 : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have h2 : ∏ i ∈ s, f i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [padicValNat.mul h1 h2, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem fock_L_nonneg (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (a : ℝ) (ha : 0 ≤ a) (hk : 1 ≤ k) :
    0 ≤ Real.logb p (2 * a + k) + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hx : (1 : ℝ) ≤ 2 * a + k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have := Real.logb_nonneg hp1 hx
  linarith

theorem fock_log_le (p : ℕ) [hp : Fact p.Prime] (k D : ℕ) (a : ℝ) (ha : 0 ≤ a) (hk : 1 ≤ k)
    (hD : (D : ℝ) ≤ 2 * a) : (Nat.log p D : ℝ) ≤ Real.logb p (2 * a + k) + 1 := by
  have h0 := fock_L_nonneg p k a ha hk
  rcases Nat.eq_zero_or_pos D with hD0 | hD0
  · subst hD0; simpa using h0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < 2 * a + k := by linarith
  have hle : (Nat.log p D : ℝ) ≤ Real.logb p (2 * a + k) := by
    rw [Real.le_logb_iff_rpow_le hp1 hpos, Real.rpow_natCast]
    have : p ^ Nat.log p D ≤ D := Nat.pow_log_le_self p hD0.ne'
    have : ((p ^ Nat.log p D : ℕ) : ℝ) ≤ D := by exact_mod_cast this
    push_cast at this
    linarith
  linarith

theorem factProd_ne_zero {σ : Type} [Fintype σ] (α : σ →₀ ℕ) : factProd α ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _

theorem fock_key {σ Z : Type} [Fintype σ] [Fintype Z] [DecidableEq Z] (letter : σ → Z)
    (d : Z → ℕ) (α : σ →₀ ℕ)
    (h : ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z) :
    ∏ z, (d z).factorial =
      factProd α * ∏ z, Nat.multinomial (univ.filter (fun i => letter i = z)) α := by
  classical
  unfold factProd
  rw [← Finset.prod_fiberwise Finset.univ letter (fun i => (α i).factorial), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun z _ => ?_
  rw [Nat.multinomial_spec, h z]

theorem fock_core (p : ℕ) [Fact p.Prime] {σ Z : Type} [Fintype σ] [Fintype Z] [DecidableEq Z]
    (letter : σ → Z) (d : Z → ℕ) (N k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hcard : Fintype.card σ ≤ N * k) (hd : ∀ z, (d z : ℝ) ≤ 2 * a) (α : σ →₀ ℕ)
    (hh : ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z) :
    padicValNat p (factProd α) ≤ padicValNat p (∏ z, (d z).factorial) ∧
      (padicValNat p (∏ z, (d z).factorial) : ℝ) - N * k * (Real.logb p (2 * a + k) + 1) ≤
        padicValNat p (factProd α) := by
  classical
  have hkey := fock_key letter d α hh
  have hne : ∏ z, Nat.multinomial (univ.filter (fun i => letter i = z)) α ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun z _ => (Nat.multinomial_pos _ _).ne'
  set S := ∑ z, padicValNat p (Nat.multinomial (univ.filter (fun i => letter i = z)) α) with hS
  have hV : padicValNat p (∏ z, (d z).factorial) = padicValNat p (factProd α) + S := by
    rw [hkey, padicValNat.mul (factProd_ne_zero α) hne, hS,
      fock_val_prod p univ _ (fun z _ => (Nat.multinomial_pos _ _).ne')]
  refine ⟨by rw [hV]; omega, ?_⟩
  set T := ∑ z, (univ.filter (fun i => letter i = z)).card * Nat.log p (d z) with hT
  have hST : S ≤ T := by
    refine Finset.sum_le_sum fun z _ => ?_
    have := fock_mult_val_le p (⇑α) (univ.filter fun i => letter i = z)
    rwa [hh z] at this
  have hcardsum : ∑ z, (univ.filter (fun i => letter i = z)).card = Fintype.card σ := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (letter x))).symm
  have hTR : (T : ℝ) ≤ N * k * (Real.logb p (2 * a + k) + 1) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hc : ∀ z, (univ.filter (fun i => letter i = z)).card = 0 := by
        intro z
        have := Finset.card_le_univ (univ.filter (fun i => letter i = z))
        subst hk0
        omega
      have : T = 0 := by rw [hT]; simp [hc]
      rw [this, hk0]; simp
    · have hL0 := fock_L_nonneg p k a ha hk0
      rw [hT]; push_cast
      calc ∑ z, ((univ.filter (fun i => letter i = z)).card : ℝ) * (Nat.log p (d z) : ℝ)
          ≤ ∑ z, ((univ.filter (fun i => letter i = z)).card : ℝ) * (Real.logb p (2 * a + k) + 1) :=
            Finset.sum_le_sum fun z _ =>
              mul_le_mul_of_nonneg_left (fock_log_le p k (d z) a ha hk0 (hd z)) (Nat.cast_nonneg _)
        _ = (Fintype.card σ : ℝ) * (Real.logb p (2 * a + k) + 1) := by
            rw [← Finset.sum_mul, ← Nat.cast_sum, hcardsum]
        _ ≤ N * k * (Real.logb p (2 * a + k) + 1) := by
            apply mul_le_mul_of_nonneg_right _ hL0
            exact_mod_cast hcard
  have e1 : (padicValNat p (∏ z, (d z).factorial) : ℝ) = padicValNat p (factProd α) + S := by
    exact_mod_cast hV
  have e2 : (S : ℝ) ≤ T := by exact_mod_cast hST
  linarith

theorem frame_val (p : ℕ) [Fact p.Prime] (D : ℕ) {r : ℕ} (m : Fin r → ℕ) (hm : ∑ i, m i ≤ D) :
    padicValNat p (D.choose (∑ i, m i) * Nat.multinomial univ m) ≤ (r + 1) * Nat.log p D := by
  have hc : D.choose (∑ i, m i) ≠ 0 := (Nat.choose_pos hm).ne'
  have hm0 : Nat.multinomial univ m ≠ 0 := (Nat.multinomial_pos _ _).ne'
  rw [padicValNat.mul hc hm0]
  have h1 : padicValNat p (D.choose (∑ i, m i)) ≤ Nat.log p D := by
    rw [← Nat.factorization_def _ (Fact.out : p.Prime)]
    exact Nat.factorization_choose_le_log
  have h2 := fock_mult_val_le p m univ
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : Nat.log p (∑ i, m i) ≤ Nat.log p D := Nat.log_mono_right hm
  have h4 := Nat.mul_le_mul_left r h3
  rw [add_mul, one_mul]
  omega

end Formalism.CountingSumsFrames
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.FrobeniusDetVanishingHolds
section
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Formalism.CountingSumsFrames

theorem detMulEqSumAdjugate_holds : DetMulEqSumAdjugate := by
  intro R _ r T s a
  have h : (T.adjugate *ᵥ (T *ᵥ s)) a = (T.det • s) a := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  generalize T *ᵥ s = v
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

lemma borderedMatrix_castSucc {R : Type} [CommRing R] (r : ℕ) (ts : Fin r → R) (u : R)
    (T : Matrix (Fin r) (Fin r) R) (b : Fin r → R) (i : Fin (r + 1)) (j : Fin r) :
    borderedMatrix r ts u T b i (Fin.castSucc j) = borderedMatrix r ts 0 T 0 i (Fin.castSucc j) := by
  cases i using Fin.cases <;> simp [borderedMatrix]

theorem borderedDetLinear_holds : BorderedDetLinear := by
  intro R _ r ts T
  refine ⟨fun l => (-1) ^ ((l.succ : ℕ) + r) *
    ((borderedMatrix r ts 0 T 0).submatrix (Fin.succ l).succAbove Fin.castSucc).det, fun u b => ?_⟩
  have hsub : ∀ i : Fin (r + 1), (borderedMatrix r ts u T b).submatrix i.succAbove (Fin.last r).succAbove =
      (borderedMatrix r ts 0 T 0).submatrix i.succAbove Fin.castSucc := by
    intro i
    ext x y
    simp only [Matrix.submatrix_apply, Fin.succAbove_last]
    exact borderedMatrix_castSucc r ts u T b _ y
  have h0 : (borderedMatrix r ts 0 T 0).submatrix (Fin.succAbove 0) Fin.castSucc = T := by
    ext x y
    simp [borderedMatrix]
  have hl0 : borderedMatrix r ts u T b 0 (Fin.last r) = u := by simp [borderedMatrix]
  have hls : ∀ l : Fin r, borderedMatrix r ts u T b l.succ (Fin.last r) = b l := by
    intro l
    simp [borderedMatrix]
  rw [Matrix.det_succ_column _ (Fin.last r), Fin.sum_univ_succ]
  simp only [hsub, h0, hl0, hls, Fin.val_zero, Fin.val_last, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma frob_row {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p] {k : ℕ}
    (h : Matrix (Fin k) (Fin k) F) (a s : ℕ) (ha : a ≤ s) (t : Fin k → F) (c : Fin k) :
    ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
      ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) c := by
  haveI : ExpChar F p := ExpChar.prime (Fact.out)
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
  rw [sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le ha]

theorem frobeniusDetVanishing_holds : KeyVanish := by
  intro p _ F _ _ r k h hdet s
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨fun A t cols hA ht => ?_, fun a t v ha ht hv => ?_⟩
  · have hM : (Matrix.of fun l c =>
        ((t l ᵥ* h.map (fun x => x ^ p ^ A l)) (cols c)) ^ p ^ (s - A l)) =
        (Matrix.of fun (l : Fin (r + 1)) (i : {i : Fin k // i.val < r}) =>
          t l i.1 ^ p ^ (s - A l)) *
        (Matrix.of fun (i : {i : Fin k // i.val < r}) (c : Fin (r + 1)) =>
          (h.map (fun x => x ^ p ^ s)) i.1 (cols c)) := by
      ext l c
      rw [Matrix.of_apply, frob_row h (A l) s (hA l) (t l) (cols c), Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.vecMul, dotProduct]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i.val < r)]
      have hz : ∑ i : {i : Fin k // ¬ i.val < r},
          t l i.1 ^ p ^ (s - A l) * (h.map (fun x => x ^ p ^ s)) i.1 (cols c) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [ht l i.1 (not_lt.mp i.2), zero_pow (pow_ne_zero _ hp.ne'), zero_mul]
      rw [hz, add_zero]
    rw [hM]
    by_contra hne
    have hu := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
    have hcard : Fintype.card {i : Fin k // i.val < r} ≤ r := by
      have := Fintype.card_le_of_injective (fun i : {i : Fin k // i.val < r} => (⟨i.1.val, i.2⟩ : Fin r))
        (fun x y hxy => by
          simp only [Fin.mk.injEq] at hxy
          exact Subtype.ext (Fin.ext hxy))
      simpa using this
    have h2 := (Matrix.rank_mul_le_left
      (Matrix.of fun (l : Fin (r + 1)) (i : {i : Fin k // i.val < r}) => t l i.1 ^ p ^ (s - A l))
      (Matrix.of fun (i : {i : Fin k // i.val < r}) (c : Fin (r + 1)) =>
        (h.map (fun x => x ^ p ^ s)) i.1 (cols c))).trans ((Matrix.rank_le_card_width _).trans hcard)
    rw [hu, Fintype.card_fin] at h2
    omega
  · have hH : IsUnit (h.map (fun x => x ^ p ^ s)).det := by
      haveI : ExpChar F p := ExpChar.prime (Fact.out)
      have e : h.map (fun x => x ^ p ^ s) = (iterateFrobenius F p s).mapMatrix h := by
        ext i j
        simp [iterateFrobenius_def]
      rw [e, ← RingHom.map_det]
      exact hdet.map _
    have e1 : ∀ c, ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
        ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) c :=
      fun c => frob_row h a s ha t c
    simp only [e1]
    change ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) ⬝ᵥ
      (v ᵥ* (h.map (fun x => x ^ p ^ s))⁻¹ᵀ) = 0
    rw [Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    show t i ^ p ^ (s - a) * v i = 0
    by_cases hi : i.val < r
    · rw [hv i hi, mul_zero]
    · rw [ht i (not_lt.mp hi), zero_pow (pow_ne_zero _ hp.ne'), zero_mul]

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.PairingAdjointLaplacianHolds
section
set_option linter.unusedSimpArgs false

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames

section Gen

variable (K : Type) [Field K] (k : ℕ)

def eulX_har (f : PolXY K k) : PolXY K k := ∑ i : Fin k, X (Sum.inl i) * pderiv (Sum.inl i) f

def eulY (f : PolXY K k) : PolXY K k := ∑ i : Fin k, X (Sum.inr i) * pderiv (Sum.inr i) f

variable {K k}

theorem ctrF_apply (f : PolXY K k) :
    ctrF K k f = ∑ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by
  simp [ctrF, LinearMap.sum_apply]

theorem pderiv_inl_h (i : Fin k) : pderiv (Sum.inl i) (hXY K k) = X (Sum.inr i) := by
  classical
  simp [hXY, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']

theorem pderiv_inr_h (i : Fin k) : pderiv (Sum.inr i) (hXY K k) = X (Sum.inl i) := by
  classical
  simp [hXY, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']

theorem ctrF_h_mul (f : PolXY K k) :
    ctrF K k (hXY K k * f) = hXY K k * ctrF K k f + (k : K) • f + eulX_har K k f + eulY K k f := by
  classical
  have key : ∀ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) (hXY K k * f)) =
      hXY K k * pderiv (Sum.inl i) (pderiv (Sum.inr i) f) + f +
        X (Sum.inl i) * pderiv (Sum.inl i) f + X (Sum.inr i) * pderiv (Sum.inr i) f := by
    intro i
    rw [pderiv_mul, pderiv_inr_h, map_add, pderiv_mul, pderiv_mul, pderiv_inl_h, pderiv_X_self]
    ring
  rw [ctrF_apply, ctrF_apply, eulX_har, eulY, Finset.sum_congr rfl (fun i _ => key i)]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K]

theorem coeff_X_mul_pderiv (v : XY k) (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (X v * pderiv v f) = (m v : K) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial n a =>
    rw [X_mul_pderiv_monomial, coeff_smul, coeff_monomial]
    by_cases h : n = m
    · subst h; simp
    · simp [h]

theorem coeff_eulX (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (eulX_har K k f) = (xDeg m : K) * coeff m f := by
  simp [eulX_har, coeff_sum, coeff_X_mul_pderiv, xDeg, Finset.sum_mul]

theorem coeff_eulY (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (eulY K k f) = (yDeg m : K) * coeff m f := by
  simp [eulY, coeff_sum, coeff_X_mul_pderiv, yDeg, Finset.sum_mul]

theorem eulX_of_mem {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    eulX_har K k f = (A : K) • f := by
  ext m
  rw [coeff_eulX, coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ f.support
  · rw [(hf m hm).1]
  · rw [notMem_support_iff.1 hm]; simp

theorem eulY_of_mem {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    eulY K k f = (B : K) • f := by
  ext m
  rw [coeff_eulY, coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ f.support
  · rw [(hf m hm).2]
  · rw [notMem_support_iff.1 hm]; simp

end Gen

theorem slTwoCommutator_holds : SlTwo := by
  intro K _ _ k A B f hf
  rw [ctrF_h_mul, eulX_of_mem hf, eulY_of_mem hf]
  simp only [Algebra.smul_def, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero, map_add, map_mul,
      map_one, map_zero, map_natCast]
  ring

section Gen2

variable {K : Type} [Field K] {k : ℕ}

end Gen2

section Fis

variable {K : Type} [Field K] {k : ℕ}

end Fis

section Can

variable {K : Type} [Field K] {k : ℕ}

end Can

end Formalism.CountingSumsFrames
end
end


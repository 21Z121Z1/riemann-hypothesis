import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentOnHyperbolicComplement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0016

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentSubOneMajorantBound
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma normSq_sub_le_two (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]

namespace Data

variable {r : ℕ} (X : Data E r)

lemma Jp_sub (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jp x τ (u - v) = X.Jp x τ u - X.Jp x τ v := by
  unfold Jp
  rw [X.ppos_sub, smul_sub]
  abel

section perTau

variable {x : Frame X.Ψ r} {τ : X.Ψ}

lemma maj_smul (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = Complex.normSq c * X.maj x τ v := by
  have hJ : X.Jp x τ (c • v) = c • X.Jp x τ v := by
    unfold Jp; rw [X.ppos_smul, smul_comm (2 : ℂ) c, ← smul_sub]
  have hH : ∀ u w, hermC τ.1 X.Gm (c • u) (c • w) = (Complex.normSq c : ℂ) * hermC τ.1 X.Gm u w := by
    intro u w
    unfold hermC
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have h1 := hself (c • v)
  rw [show X.Hf x τ (c • v) (c • v) = hermC τ.1 X.Gm (X.Jp x τ (c • v)) (c • v) from rfl, hJ, hH,
    show hermC τ.1 X.Gm (X.Jp x τ v) v = X.Hf x τ v v from rfl, hself v] at h1
  exact_mod_cast h1.symm

lemma maj_zero' (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) : X.maj x τ 0 = 0 := by
  have h1 := X.maj_smul hself (0 : ℂ) 0
  simpa using h1

lemma maj_nonneg' (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
    (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, X.maj_zero' hself]
  · exact (hpos v hv).le

variable {e : Fin r → ℂ} (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0)
  (hq : X.d2q x τ e ≠ 0) (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
include hx he hq hself

lemma maj_Ce_bz (C b : ℂ) :
    X.maj x τ (C • e - b • X.d2z x τ e δ) =
      Complex.normSq C * X.maj x τ e + Complex.normSq b * X.maj x τ (X.d2z x τ e δ) := by
  have hfz : hermC τ.1 X.Gm (X.Jp x τ e) (X.d2z x τ e δ) = 0 := by
    rw [hsym, unipotent_shift_orthogonal_Je X δ hx he hq, map_zero]
  have hze : hermC τ.1 X.Gm (X.Jp x τ (X.d2z x τ e δ)) e = 0 := by
    rw [Jp_adj X hx, unipotent_shift_orthogonal_Je X δ hx he hq]
  have h3 : X.Hf x τ (C • e - b • X.d2z x τ e δ) (C • e - b • X.d2z x τ e δ) =
      C * conj C * X.Hf x τ e e + b * conj b * X.Hf x τ (X.d2z x τ e δ) (X.d2z x τ e δ) := by
    show hermC τ.1 X.Gm (X.Jp x τ (C • e - b • X.d2z x τ e δ)) (C • e - b • X.d2z x τ e δ) =
      C * conj C * hermC τ.1 X.Gm (X.Jp x τ e) e +
        b * conj b * hermC τ.1 X.Gm (X.Jp x τ (X.d2z x τ e δ)) (X.d2z x τ e δ)
    rw [Jp_sub, Jp_smul, Jp_smul]
    simp only [hC_sub_left, hC_smul_left, hC_sub_right, hC_smul_right, hfz, hze]
    ring
  rw [hself, hself, hself, Complex.mul_conj, Complex.mul_conj] at h3
  exact_mod_cast h3

lemma maj_decomp (w : Fin r → ℂ) (hw1 : hermC τ.1 X.Gm w e = 0)
    (hw2 : hermC τ.1 X.Gm w (X.Jp x τ e) = 0) (a b : ℂ) :
    X.maj x τ (w + a • e + b • X.Jp x τ e) =
      Complex.normSq a * X.maj x τ e + Complex.normSq b * X.maj x τ e + X.maj x τ w := by
  have k1 : hermC τ.1 X.Gm (X.Jp x τ w) e = 0 := by rw [Jp_adj X hx, hw2]
  have k2 : hermC τ.1 X.Gm (X.Jp x τ w) (X.Jp x τ e) = 0 := by
    rw [Jp_adj X hx, Jp_Jp X hx, hw1]
  have k3 : hermC τ.1 X.Gm (X.Jp x τ e) w = 0 := by rw [hsym, hw2, map_zero]
  have k4 : hermC τ.1 X.Gm e w = 0 := by rw [hsym, hw1, map_zero]
  have k5 := hermitian_pairing_Je_Je_zero X hx he
  have k6 : hermC τ.1 X.Gm (X.Jp x τ e) e = X.Hf x τ e e := rfl
  have k7 : hermC τ.1 X.Gm e (X.Jp x τ e) = X.Hf x τ e e := hermitian_pairing_e_Je X hx
  have h3 : X.Hf x τ (w + a • e + b • X.Jp x τ e) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + X.Hf x τ w w := by
    show hermC τ.1 X.Gm (X.Jp x τ (w + a • e + b • X.Jp x τ e)) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + hermC τ.1 X.Gm (X.Jp x τ w) w
    rw [Jp_add, Jp_add, Jp_smul, Jp_smul, Jp_Jp X hx]
    simp only [hC_add_left, hC_smul_left, hC_add_right, hC_smul_right, k1, k2, k3, k4, k5, k6, k7,
      he]
    ring
  rw [hself, hself, hself, Complex.mul_conj, Complex.mul_conj] at h3
  exact_mod_cast h3

lemma unipotent_sub_one_majorant_bound (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hδ : ∀ u, hermC τ.1 X.Gm u e = 0 → hermC τ.1 X.Gm u (X.Jp x τ e) = 0 →
      X.maj x τ (δ u • e) ≤ κ ^ 2 * X.maj x τ u) (v : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.d2n x τ e δ - 1) v) ≤ (3 * κ) ^ 2 * X.maj x τ v := by
  have hnn := maj_nonneg' X hself hpos
  have hqQ : X.d2q x τ e = (X.maj x τ e : ℂ) := hself e
  have hQ : 0 < X.maj x τ e := by
    rcases (hnn e).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hqQ, ← h]; simp) hq
  set Q := X.maj x τ e with hQdef
  set z := X.d2z x τ e δ with hzdef

  have hA : Matrix.mulVec (X.d2n x τ e δ - 1) v =
      (δ (X.d2pi x τ e v) - δ z / 2 * X.d2b x τ e v) • e - X.d2b x τ e v • z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, unipotent_mulVec_formula]
    abel
  rw [hA, maj_Ce_bz X δ hx he hq hself]

  have hv : v = X.d2pi x τ e v + X.d2a x τ e v • e + X.d2b x τ e v • X.Jp x τ e := by
    rw [hyperbolic_projection_apply]; abel
  have hw1 := hyperbolic_projection_perp_e X hx he hq v
  have hw2 := hyperbolic_projection_perp_Je X hx he hq v
  conv_rhs => rw [hv, maj_decomp X hx he hq hself _ hw1 hw2]

  have hz1 : hermC τ.1 X.Gm (X.Jp x τ z) e = 0 := by rw [Jp_adj X hx, unipotent_shift_orthogonal_Je X δ hx he hq]
  have hz2 : hermC τ.1 X.Gm (X.Jp x τ z) (X.Jp x τ e) = 0 := by
    rw [Jp_adj X hx, Jp_Jp X hx, unipotent_shift_orthogonal_e X δ hx he hq]
  have hmJz : X.maj x τ (X.Jp x τ z) = X.maj x τ z := by
    have h1 := hself (X.Jp x τ z)
    have h2 := hself z
    have h3 : X.Hf x τ (X.Jp x τ z) (X.Jp x τ z) = X.Hf x τ z z := by
      show hermC τ.1 X.Gm (X.Jp x τ (X.Jp x τ z)) (X.Jp x τ z) = X.Hf x τ z z
      rw [Jp_Jp X hx, Hf_eq X x hx]
      rfl
    rw [h1, h2] at h3
    exact_mod_cast h3
  have hZc : (X.maj x τ z : ℂ) = (Q : ℂ) * δ (X.Jp x τ z) := by
    rw [← hself z, ← hqQ]
    show hermC τ.1 X.Gm (X.Jp x τ z) z = _
    rw [unipotent_shift_spec X δ hx he hq, hyperbolic_projection_of_perp X hx he hq hz1 hz2]
  have hdJ : δ (X.Jp x τ z) = ((X.maj x τ z / Q : ℝ) : ℂ) := by
    have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
    push_cast
    rw [hZc]
    field_simp
  have hZ0 := hnn z
  have hZ : X.maj x τ z ≤ κ ^ 2 * Q := by
    have h := hδ _ hz1 hz2
    rw [maj_smul X hself, hdJ, Complex.normSq_ofReal, hmJz] at h

    have h' : X.maj x τ z * X.maj x τ z ≤ κ ^ 2 * Q * X.maj x τ z := by
      have e1 : X.maj x τ z / Q * (X.maj x τ z / Q) * Q = X.maj x τ z * X.maj x τ z / Q := by
        field_simp
      rw [e1, div_le_iff₀ hQ] at h
      nlinarith
    rcases hZ0.lt_or_eq with h0 | h0
    · exact le_of_mul_le_mul_right h' h0
    · rw [← h0]; positivity
  have hDz : Complex.normSq (δ z) ≤ κ ^ 4 := by
    have h := hδ z (unipotent_shift_orthogonal_e X δ hx he hq) (unipotent_shift_orthogonal_Je X δ hx he hq)
    rw [maj_smul X hself] at h
    have h2 : Complex.normSq (δ z) * Q ≤ κ ^ 4 * Q := by nlinarith
    exact le_of_mul_le_mul_right h2 hQ
  have hw := hyperbolic_projection_perp_e X hx he hq v
  have hD := hδ (X.d2pi x τ e v) hw1 hw2
  rw [maj_smul X hself] at hD
  have hC : Complex.normSq (δ (X.d2pi x τ e v) - δ z / 2 * X.d2b x τ e v) ≤
      2 * Complex.normSq (δ (X.d2pi x τ e v)) +
        Complex.normSq (δ z) * Complex.normSq (X.d2b x τ e v) / 2 := by
    have h1 := normSq_sub_le_two (δ (X.d2pi x τ e v)) (δ z / 2 * X.d2b x τ e v)
    have h2 : Complex.normSq (δ z / 2 * X.d2b x τ e v) =
        Complex.normSq (δ z) * Complex.normSq (X.d2b x τ e v) / 4 := by
      rw [Complex.normSq_mul, Complex.normSq_div]
      norm_num
      ring
    linarith
  have hWn := hnn (X.d2pi x τ e v)
  have hAn := Complex.normSq_nonneg (X.d2a x τ e v)
  have hBn := Complex.normSq_nonneg (X.d2b x τ e v)
  have hDn := Complex.normSq_nonneg (δ (X.d2pi x τ e v))
  have hDzn := Complex.normSq_nonneg (δ z)
  have hk4 : κ ^ 4 ≤ κ ^ 2 := pow_le_pow_of_le_one hκ0 hκ1 (by norm_num)
  have t1 := mul_le_mul_of_nonneg_right hC hQ.le
  have t2 := mul_le_mul_of_nonneg_left hZ hBn
  have t3 := mul_le_mul_of_nonneg_right hDz (mul_nonneg hBn hQ.le)
  have t4 := mul_le_mul_of_nonneg_right hk4 (mul_nonneg hBn hQ.le)
  have t5 := mul_nonneg (sq_nonneg κ) (mul_nonneg hAn hQ.le)
  have t6 := mul_nonneg (sq_nonneg κ) hWn
  have t7 := mul_nonneg (sq_nonneg κ) (mul_nonneg hBn hQ.le)
  nlinarith

end perTau

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentVectorGroup
section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private theorem tau_cc_eq_conj_tau (τ : E →+* ℂ) (x : E) : τ (cc x) = starRingEnd ℂ (τ x) :=
  NumberField.IsCMField.complexEmbedding_complexConj E τ x

private theorem hermC_emb_emb_eq_zero_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (τ : E →+* ℂ) (i k : Fin 2) :
    hermC τ X.Gm (Data.emb τ (u i)) (Data.emb τ (u k)) = 0 := by
  have h := congrArg τ (hiso.1 i k)
  simp only [herm, map_sum, map_mul, map_zero, tau_cc_eq_conj_tau] at h
  simp only [hermC, Data.emb]
  exact h

private theorem sum_gram_emb_mul_emb_eq_zero_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (τ : E →+* ℂ) (i k : Fin 2) :
    ∑ j, (∑ l, τ (X.Gm j l) * starRingEnd ℂ (Data.emb τ (u k) l)) * Data.emb τ (u i) j = 0 := by
  refine Eq.trans ?_ (hermC_emb_emb_eq_zero_of_isIsoPair X u hiso τ i k)
  simp only [hermC]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem zmat_eq_one_sub_smul {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ = 1 - (Complex.I * (X.c τ : ℂ)) •
      ((Matrix.of fun a i => Data.emb τ.1 (u i) a) * Matrix.of (b τ) *
        Matrix.of fun k j => ∑ l, τ.1 (X.Gm j l) * starRingEnd ℂ (Data.emb τ.1 (u k) l)) := by
  ext a j
  simp only [Data.zmat, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.mul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring

private theorem gram_conj_emb_mul_emb_eq_zero_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (τ : X.Ψ) :
    (Matrix.of fun k j => ∑ l, τ.1 (X.Gm j l) * starRingEnd ℂ (Data.emb τ.1 (u k) l)) *
      (Matrix.of fun a i => Data.emb τ.1 (u i) a) = 0 := by
  ext k i
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  exact sum_gram_emb_mul_emb_eq_zero_of_isIsoPair X u hiso τ.1 i k

private theorem one_sub_smul_mul_one_sub_smul_of_mul_eq_zero {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n (Fin 2) ℂ)
    (P : Matrix (Fin 2) n ℂ) (hPV : P * V = 0) (s : ℂ) (B B' : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 - s • (V * B * P)) * (1 - s • (V * B' * P)) = 1 - s • (V * (B + B') * P) := by
  have h : V * B * P * (V * B' * P) = 0 := by
    calc V * B * P * (V * B' * P) = V * B * (P * V) * B' * P := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPV]; simp
  simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h, smul_zero,
    Matrix.mul_add, Matrix.add_mul, smul_add, sub_zero]
  abel

private theorem det_one_sub_smul_mul_of_mul_eq_zero {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n (Fin 2) ℂ)
    (P : Matrix (Fin 2) n ℂ) (hPV : P * V = 0) (s : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 - s • (V * B * P)).det = 1 := by
  have e : (1 : Matrix n n ℂ) - s • (V * B * P) = 1 + (-(s • (V * B))) * P := by
    rw [Matrix.neg_mul, Matrix.smul_mul, sub_eq_add_neg]
  have h : P * (-(s • (V * B))) = 0 := by
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, hPV, Matrix.zero_mul, smul_zero,
      neg_zero]
  rw [e, Matrix.det_one_add_mul_comm, h, add_zero, Matrix.det_one]

private theorem zmat_mulVec_eq {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (w : Fin r → ℂ) :
    Matrix.mulVec (X.zmat u b τ) w = fun p => w p - ∑ i, (Complex.I * (X.c τ : ℂ) *
      ∑ k, b τ i k * hermC τ.1 X.Gm w (Data.emb τ.1 (u k))) * Data.emb τ.1 (u i) p := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Data.zmat, Matrix.of_apply, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  congr 1
  simp only [hermC, Fin.sum_univ_two, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem hermC_sub_sum_smul_expand {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (w w' : Fin r → ℂ)
    (v : Fin 2 → Fin r → ℂ) (α β : Fin 2 → ℂ) :
    hermC τ G (fun p => w p - ∑ i, α i * v i p) (fun p => w' p - ∑ i, β i * v i p) =
      hermC τ G w w' - ∑ i, starRingEnd ℂ (β i) * hermC τ G w (v i) -
        ∑ i, α i * hermC τ G (v i) w' +
          ∑ i, ∑ k, α i * starRingEnd ℂ (β k) * hermC τ G (v i) (v k) := by
  simp only [hermC, Fin.sum_univ_two, map_sub, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

private theorem hermC_Gm_eq_starRingEnd_swap {r : ℕ} (X : Data E r) (τ : E →+* ℂ) (v w : Fin r → ℂ) :
    hermC τ X.Gm v w = starRingEnd ℂ (hermC τ X.Gm w v) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← X.Gm_herm y x, tau_cc_eq_conj_tau]
  ring

private theorem hermC_zmat_mulVec_of_isIsoPair {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ) (w w' : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.zmat u b τ) w) (Matrix.mulVec (X.zmat u b τ) w') =
      hermC τ.1 X.Gm w w' := by
  have e := hermC_sub_sum_smul_expand τ.1 X.Gm w w' (fun i => Data.emb τ.1 (u i))
    (fun i => Complex.I * (X.c τ : ℂ) * ∑ k, b τ i k * hermC τ.1 X.Gm w (Data.emb τ.1 (u k)))
    (fun i => Complex.I * (X.c τ : ℂ) * ∑ k, b τ i k * hermC τ.1 X.Gm w' (Data.emb τ.1 (u k)))
  beta_reduce at e
  rw [zmat_mulVec_eq, zmat_mulVec_eq, e]
  simp only [Fin.sum_univ_two, hermC_emb_emb_eq_zero_of_isIsoPair X u hiso τ.1, mul_zero, add_zero,
    hermC_Gm_eq_starRingEnd_swap X τ.1 (Data.emb τ.1 (u 0)) w', hermC_Gm_eq_starRingEnd_swap X τ.1 (Data.emb τ.1 (u 1)) w',
    map_mul, map_add, Complex.conj_I, Complex.conj_ofReal]
  rw [← hb τ 0 0, ← hb τ 0 1, ← hb τ 1 0, ← hb τ 1 1]
  ring

private theorem zmat_mulVec_emb_eq_self {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E) (hiso : IsIsoPair X.Gm u)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (i : Fin 2) :
    Matrix.mulVec (X.zmat u b τ) (Data.emb τ.1 (u i)) = Data.emb τ.1 (u i) := by
  rw [zmat_mulVec_eq]
  funext p
  simp only [hermC_emb_emb_eq_zero_of_isIsoPair X u hiso τ.1, mul_zero, Finset.sum_const_zero, zero_mul, sub_zero]

private theorem col_mul_eq_mulVec_col_natDim {r : ℕ} (M N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (M * N) a = Matrix.mulVec M (col N a) := by
  funext k
  simp only [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

private theorem gram_zmat_mul_eq_gram {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (hiso : IsIsoPair X.Gm u) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.zmat u b τ * M) = gram τ.1 X.Gm M := by
  ext a c
  simp only [gram, Matrix.of_apply, col_mul_eq_mulVec_col_natDim, hermC_zmat_mulVec_of_isIsoPair X u hiso b hb τ]

private theorem mat_Zb_eq_zmat_mul_mat {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.Zb u b x) τ = X.zmat u b τ * mat x τ := rfl

private theorem dmin_Zb_eq_dmin {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (hiso : IsIsoPair X.Gm u) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b)
    (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (X.Zb u b x) τ i = dmin X.Gm x τ i := by
  simp only [dmin, mat_Zb_eq_zmat_mul_mat, gram_zmat_mul_eq_gram X u hiso b hb τ]

private theorem zmat_mul_zmat_eq_zmat_add {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (hiso : IsIsoPair X.Gm u) (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ * X.zmat u b' τ = X.zmat u (b + b') τ := by
  rw [zmat_eq_one_sub_smul X u b τ, zmat_eq_one_sub_smul X u b' τ, zmat_eq_one_sub_smul X u (b + b') τ,
    one_sub_smul_mul_one_sub_smul_of_mul_eq_zero _ _ (gram_conj_emb_mul_emb_eq_zero_of_isIsoPair X u hiso τ), Matrix.of_add_of, Pi.add_apply]

private theorem det_zmat_eq_one {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (hiso : IsIsoPair X.Gm u) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    (X.zmat u b τ).det = 1 := by
  rw [zmat_eq_one_sub_smul X u b τ]
  exact det_one_sub_smul_mul_of_mul_eq_zero _ _ (gram_conj_emb_mul_emb_eq_zero_of_isIsoPair X u hiso τ) _ _

private theorem flowMatV_uvec_eq_zmat {r : ℕ} (X : Data E r) (u : Fin 2 → Fin r → E)
    (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) (τ : X.Ψ) :
    X.flowMatV (X.uvec u a τ) τ (s τ) =
      X.zmat u (fun τ' i k => s τ' * a τ' i * starRingEnd ℂ (a τ' k)) τ := by
  ext p j
  simp only [Data.flowMatV, Data.zmat, Data.uvec, Matrix.of_apply, Fin.sum_univ_two,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add, add_mul,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem unipotent_vector_group : UnipotentVectorGroup (E := E) := by
  unfold UnipotentVectorGroup
  intro r X u hiso
  refine ⟨fun b b' x => ?_, fun b hb => ?_⟩
  · funext τ
    show X.zmat u b τ * (X.zmat u b' τ * mat x τ) = X.zmat u (b + b') τ * mat x τ
    rw [← Matrix.mul_assoc, zmat_mul_zmat_eq_zmat_add X u hiso]
  · have hfix := zmat_mulVec_emb_eq_self X u hiso b
    have hdom : ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom := by
      intro x hx
      simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
      intro τ
      refine ⟨?_, fun i => ?_⟩
      · rw [mat_Zb_eq_zmat_mul_mat, Matrix.det_mul, det_zmat_eq_one X u hiso b, one_mul]
        exact (hx τ).1
      · rw [dmin_Zb_eq_dmin X u hiso b hb]
        exact (hx τ).2 i
    have hmaj : ∀ (x : Frame X.Ψ r) (τ : X.Ψ), x ∈ X.dom →
        X.maj (X.Zb u b x) τ (Data.emb τ.1 (u 0)) = X.maj x τ (Data.emb τ.1 (u 0)) := by
      intro x τ _
      have hv0 : ∀ w, hermC τ.1 X.Gm (Data.emb τ.1 (u 0)) (Matrix.mulVec (X.zmat u b τ) w) =
          hermC τ.1 X.Gm (Data.emb τ.1 (u 0)) w := by
        intro w
        have h := hermC_zmat_mulVec_of_isIsoPair X u hiso b hb τ (Data.emb τ.1 (u 0)) w
        rwa [hfix τ 0] at h
      simp only [Data.maj, Data.posPart, Data.gramPos, mat_Zb_eq_zmat_mul_mat, col_mul_eq_mulVec_col_natDim,
        gram_zmat_mul_eq_gram X u hiso b hb τ, hv0]
    have hD1 : ∀ x ∈ X.FramesOverBasis (u 0), X.Zb u b x ∈ X.FramesOverBasis (u 0) := by
      intro x hx
      simp only [Data.FramesOverBasis, Set.mem_setOf_eq] at hx ⊢
      refine ⟨hdom x hx.1, fun τ => ?_⟩
      rw [hmaj x τ hx.1]
      exact hx.2 τ
    refine ⟨?_, hfix, fun τ => det_zmat_eq_one X u hiso b τ, hdom, ?_, ?_, hmaj, hD1, ?_, ?_⟩
    · intro τ w w'
      exact hermC_zmat_mulVec_of_isIsoPair X u hiso b hb τ w w'
    · intro x x' h τ
      have key : ∀ y : Frame X.Ψ r,
          Set.range (fun a : Fin X.p0 => col (mat (X.Zb u b y) τ) (Fin.castLE X.p0_le a)) =
            (Matrix.mulVecLin (X.zmat u b τ)) ''
              Set.range (fun a : Fin X.p0 => col (mat y τ) (Fin.castLE X.p0_le a)) := by
        intro y
        rw [← Set.range_comp]
        congr 1
      rw [key x, key x', Submodule.span_image, Submodule.span_image, h τ]
    · intro la x _
      simp only [Data.nfac, dmin_Zb_eq_dmin X u hiso b hb x]
    · intro a s x
      funext τ
      show X.zmat u b τ * (X.flowMatV (X.uvec u a τ) τ (s τ) * mat x τ) =
        X.flowMatV (X.uvec u a τ) τ (s τ) * (X.zmat u b τ * mat x τ)
      rw [flowMatV_uvec_eq_zmat X u a s τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, zmat_mul_zmat_eq_zmat_add X u hiso,
        zmat_mul_zmat_eq_zmat_add X u hiso, add_comm]
    · intro a s x
      funext τ
      exact congrArg (fun M => M * mat x τ) (flowMatV_uvec_eq_zmat X u a (fun τ => (s τ : ℂ)) τ)

end ReciprocityTheory.ChartRestriction.G.FD
end


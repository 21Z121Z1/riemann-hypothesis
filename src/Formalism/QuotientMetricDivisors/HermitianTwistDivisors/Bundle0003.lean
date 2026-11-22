import Mathlib
import Formalism.QuotientMetricDivisors.Bundle0001

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SpecDet
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section SpecDetAux

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def metMat {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((X v)⁻¹).conjTranspose * (X v)⁻¹

def cv {d : ℕ} (σ : K →+* ℂ) (x : Fin d → K) : Fin d → ℂ := fun i => σ (x i)

lemma star_mulVec_dot {d : ℕ} (A N : Matrix (Fin d) (Fin d) ℂ) (u w : Fin d → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (N *ᵥ (A *ᵥ w)) = star u ⬝ᵥ ((Aᴴ * N * A) *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

lemma majAt_eq {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y =
      star (cv v.embedding x) ⬝ᵥ (metMat X v *ᵥ cv v.embedding y) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
  rw [metMat, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl

lemma cv_mulVec {d : ℕ} (σ : K →+* ℂ) (φ : Matrix (Fin d) (Fin d) K) (x : Fin d → K) :
    cv σ (φ *ᵥ x) = (φ.map σ) *ᵥ cv σ x := by
  ext i
  exact RingHom.map_mulVec σ φ x i

lemma cv_single {d : ℕ} (σ : K →+* ℂ) (a : Fin d) :
    cv σ (Pi.single a (1 : K)) = Pi.single a (1 : ℂ) := by
  ext i
  rcases eq_or_ne i a with rfl | h
  · simp [cv]
  · simp [cv, Pi.single_eq_of_ne h]

lemma single_dot_single {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    star (Pi.single a (1 : ℂ)) ⬝ᵥ (N *ᵥ Pi.single b (1 : ℂ)) = N a b := by
  have hs : star (Pi.single a (1 : ℂ) : Fin d → ℂ) = Pi.single a 1 := by
    ext i
    rcases eq_or_ne i a with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  rw [hs]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

lemma conjT_mul_mul_apply {n : ℕ} (A N : Matrix (Fin n) (Fin n) ℂ) (a a' : Fin n) :
    (Aᴴ * N * A) a a' = star (fun i => A i a) ⬝ᵥ (N *ᵥ fun i => A i a') := by
  have hcol : ∀ c, A *ᵥ Pi.single c (1 : ℂ) = fun i => A i c := by
    intro c
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← single_dot_single (Aᴴ * N * A) a a', ← star_mulVec_dot, hcol, hcol]

lemma detRatio_eq {d : ℕ} (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (φ : Matrix (Fin d) (Fin d) K) (v : InfinitePlace K) :
    detRatio XS XT φ v =
      ((φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding).det.re / (metMat XS v).det.re := by
  have h1 : gram XT v (fun i => φ.mulVec (Pi.single i 1)) =
      (φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding := by
    ext a c
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply]
    rw [majAt_eq, cv_mulVec, cv_mulVec, cv_single, cv_single, star_mulVec_dot, single_dot_single]
  have h2 : gram XS v (fun i => (Pi.single i 1 : Fin d → K)) = metMat XS v := by
    ext a c
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply]
    rw [majAt_eq, cv_single, cv_single, single_dot_single]
  rw [detRatio, h1, h2]

lemma metMat_det_re_ne {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (hX : IsUnit (X v).det) : (metMat X v).det.re ≠ 0 := by
  have hY : ((X v)⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det (X v) hX).ne_zero
  have hm : (metMat X v).det = (Complex.normSq ((X v)⁻¹).det : ℂ) := by
    rw [metMat, Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hm, Complex.ofReal_re]
  exact (Complex.normSq_pos.mpr hY).ne'

lemma det_of_scalar {D : ℕ} (σ : K →+* ℂ) {Ix : Type} [Fintype Ix]
    (Qp : Ix → Submodule K (Fin D → K)) (hind : iSupIndep Qp) (htop : (⨆ p, Qp p) = ⊤)
    (N1 N2 : Matrix (Fin D) (Fin D) ℂ) (c : Ix → ℂ)
    (h : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      star (cv σ x) ⬝ᵥ (N1 *ᵥ cv σ y) = c p * (star (cv σ x) ⬝ᵥ (N2 *ᵥ cv σ y))) :
    N1.det = (∏ p, c p ^ finrank K (Qp p)) * N2.det ∧ ∑ p, finrank K (Qp p) = D := by
  classical
  have hint : DirectSum.IsInternal Qp :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Qp).mpr ⟨hind, htop⟩
  let b := hint.collectedBasis (fun p => Module.finBasis K (Qp p))
  have hcard : Fintype.card (Σ p, Fin (finrank K (Qp p))) = D := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  have hsum : ∑ p, finrank K (Qp p) = D := by
    have hc := hcard
    rw [Fintype.card_sigma] at hc
    simpa using hc
  refine ⟨?_, hsum⟩
  let e := Fintype.equivFinOfCardEq hcard
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin D) (Fin D) K,
      Q = (Pi.basisFun K (Fin D)).toMatrix (b.reindex e) := ⟨_, rfl⟩
  have hQ : Q.det ≠ 0 := by
    have hu := (Pi.basisFun K (Fin D)).isUnit_det (b.reindex e)
    rw [Module.Basis.det_apply, ← hQdef] at hu
    exact hu.ne_zero
  obtain ⟨Qs, hQs⟩ : ∃ M : Matrix (Fin D) (Fin D) ℂ, M = Q.map σ := ⟨_, rfl⟩
  have hQs_det : Qs.det ≠ 0 := by
    rw [hQs, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero σ).mpr hQ
  have hcol : ∀ a, (fun i => Qs i a) = cv σ (b (e.symm a)) := by
    intro a
    ext i
    simp [hQs, hQdef, cv, Module.Basis.toMatrix_apply, Module.Basis.reindex_apply]
  have hmem : ∀ a, b (e.symm a) ∈ Qp (e.symm a).1 := fun a => hint.collectedBasis_mem _ _
  have key : Qsᴴ * N1 * Qs = Matrix.diagonal (fun a => c (e.symm a).1) * (Qsᴴ * N2 * Qs) := by
    ext a a'
    rw [Matrix.diagonal_mul, conjT_mul_mul_apply, conjT_mul_mul_apply, hcol, hcol]
    exact h _ _ (hmem a) _
  have hdet := congrArg Matrix.det key
  simp only [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose] at hdet
  have hne : star Qs.det * Qs.det ≠ 0 := mul_ne_zero (star_ne_zero.mpr hQs_det) hQs_det
  have hprod : ∏ a, c (e.symm a).1 = ∏ p, c p ^ finrank K (Qp p) := by
    rw [Equiv.prod_comp e.symm (fun s => c s.1), Fintype.prod_sigma]
    simp
  rw [← hprod]
  apply mul_right_cancel₀ hne
  linear_combination hdet

lemma detRatio_of_scalar (v : InfinitePlace K) {d : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hS : IsUnit (XS v).det)
    (φ : Matrix (Fin d) (Fin d) K) {Ix : Type} [Fintype Ix]
    (Qp : Ix → Submodule K (Fin d → K)) (hind : iSupIndep Qp) (htop : (⨆ p, Qp p) = ⊤)
    (c : Ix → ℝ)
    (h : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin d → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v (φ.mulVec x) (φ.mulVec y) =
        ((c p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XS v x y) :
    detRatio XS XT φ v = ∏ p, c p ^ finrank K (Qp p) ∧ ∑ p, finrank K (Qp p) = d := by
  obtain ⟨hdet, hsum⟩ := det_of_scalar v.embedding Qp hind htop
    ((φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding) (metMat XS v)
    (fun p => ((c p : ℝ) : ℂ)) (by
      intro p x hx y
      rw [← star_mulVec_dot, ← cv_mulVec, ← cv_mulVec, ← majAt_eq, ← majAt_eq]
      exact h p x hx y)
  refine ⟨?_, hsum⟩
  rw [detRatio_eq, hdet]
  have hm := metMat_det_re_ne XS v hS
  have hc : (∏ p, ((c p : ℝ) : ℂ) ^ finrank K (Qp p)) =
      ((∏ p, c p ^ finrank K (Qp p) : ℝ) : ℂ) := by
    simp [Complex.ofReal_prod]
  rw [hc, Complex.re_ofReal_mul]
  field_simp

end SpecDetAux

theorem spectral_determinant_formula : SpecDet := by
  unfold SpecDet
  intro K _ _ _ v D XQ XE hXQ hXE ι hι J _ d XT XW hXT hXW θ hθ Ix _ Qp Tq hind htop hindT htopT
    hdim s lam hQ hT
  obtain ⟨h1, hsum⟩ :=
    detRatio_of_scalar v XQ XE (hXQ v) ι Qp hind htop (fun p => s * ∏ j, lam j p) hQ
  have h2 : ∀ j, detRatio (XT j) (XW j) (θ j) v = ∏ p, lam j p ^ finrank K (Qp p) := by
    intro j
    obtain ⟨h, -⟩ := detRatio_of_scalar v (XT j) (XW j) (hXT j v) (θ j) (Tq j) (hindT j)
      (htopT j) (lam j) (hT j)
    rw [h]
    exact Finset.prod_congr rfl (fun p _ => by rw [hdim j p])
  rw [h1, Finset.prod_congr rfl (fun j _ => h2 j)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, Finset.prod_pow]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [Finset.prod_pow]

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ValuationRepresentative

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cO_apply (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem cO_cO (x : 𝓞 K) : cO K (cO K x) = x := by
  apply RingOfIntegers.ext
  rw [cO_apply, cO_apply, star_star]

theorem map_cO_map_cO (I : Ideal (𝓞 K)) : (I.map (cO K)).map (cO K) = I := by
  ext y
  simp only [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    rwa [cO_cO]
  · intro hy
    exact ⟨cO K y, ⟨y, hy, rfl⟩, cO_cO y⟩

theorem conjPl_conjPl (w : HeightOneSpectrum (𝓞 K)) : conjPl (conjPl w) = w := HeightOneSpectrum.ext (map_cO_map_cO w.asIdeal)

theorem map_cO_le_iff (I J : Ideal (𝓞 K)) : I.map (cO K) ≤ J.map (cO K) ↔ I ≤ J := by
  constructor
  · intro h
    have h2 := Ideal.map_mono (f := cO K) h
    rwa [map_cO_map_cO, map_cO_map_cO] at h2
  · intro h
    exact Ideal.map_mono (f := cO K) h

theorem dvd_map_iff (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (n : ℕ) :
    (v.asIdeal.map (cO K)) ^ n ∣ J.map (cO K) ↔ v.asIdeal ^ n ∣ J := by
  rw [← Ideal.map_pow, Ideal.dvd_iff_le, Ideal.dvd_iff_le, map_cO_le_iff]

theorem count_map (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (hJ : J ≠ 0) :
    FractionalIdeal.count K (conjPl v) ((J.map (cO K) : Ideal (𝓞 K)) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
    FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  have hJ' : J.map (cO K) ≠ 0 := fun h =>
    hJ ((Ideal.map_eq_bot_iff_of_injective (cO K).injective).mp h)
  rw [FractionalIdeal.count_coe K (conjPl v) hJ', FractionalIdeal.count_coe K v hJ]
  congr 1
  apply eq_of_forall_le_iff
  intro n
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ')
      (Associates.irreducible_mk.mpr (conjPl v).irreducible),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
      (Associates.irreducible_mk.mpr v.irreducible),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Associates.mk_le_mk_iff_dvd]
  exact dvd_map_iff v J n

theorem vw_zero (w : HeightOneSpectrum (𝓞 K)) : vw w (0 : K) = 0 := by
  simp only [vw, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]

theorem vw_mul (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) b ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul K w h1 h2

theorem vw_inv (w : HeightOneSpectrum (𝓞 K)) (a : K) : vw w a⁻¹ = - vw w a := by
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

theorem vw_one (w : HeightOneSpectrum (𝓞 K)) : vw w (1 : K) = 0 := by
  simp only [vw]
  rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem vw_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (x : K) = FractionalIdeal.count K w
      ((Ideal.span {x} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  rw [FractionalIdeal.coeIdeal_span_singleton]
  rfl

theorem vw_int_nonneg (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) : 0 ≤ vw w (x : K) := by
  rw [vw_int]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_star_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (star (x : K)) = vw (conjPl w) (x : K) := by
  by_cases hx : x = 0
  · subst hx
    simp [vw_zero]
  · have hJ : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by
      rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have key := count_map (conjPl w) (Ideal.span {x}) hJ
    rw [conjPl_conjPl] at key
    rw [← cO_apply, vw_int, vw_int, ← key, Ideal.map_span, Set.image_singleton]

private theorem vw_div (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a / b) = vw w a - vw w b := by
  rw [div_eq_mul_inv, vw_mul w a b⁻¹ ha (inv_ne_zero hb), vw_inv, sub_eq_add_neg]

theorem vw_star (w : HeightOneSpectrum (𝓞 K)) (a : K) :
    vw w (star a) = vw (conjPl w) a := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have e : ∀ z : 𝓞 K, algebraMap (𝓞 K) K z = (z : K) := fun _ => rfl
  have hy0 : (y : K) ≠ 0 := by
    rw [Ne, ← e, ← map_zero (algebraMap (𝓞 K) K)]
    exact (IsFractionRing.injective (𝓞 K) K).ne (nonZeroDivisors.ne_zero hy)
  rw [e, e]
  by_cases hx0 : (x : K) = 0
  · rw [hx0, zero_div, star_zero, vw_zero, vw_zero]
  · rw [star_div₀, vw_div w _ _ (star_ne_zero.mpr hx0) (star_ne_zero.mpr hy0),
      vw_div _ _ _ hx0 hy0, vw_star_int, vw_star_int]

theorem absNorm_map_ringEquiv {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S] (g : S ≃+* S) (I : Ideal S) :
    Ideal.absNorm (I.map g) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map g) g rfl).toEquiv).symm

theorem lw_conjPl (w : HeightOneSpectrum (𝓞 K)) : lw (conjPl w) = lw w := by
  unfold lw
  rw [show (conjPl w).asIdeal = w.asIdeal.map (cO K) from rfl, absNorm_map_ringEquiv]

theorem gramR_eq {K : Type} [Field K] [StarRing K] {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) :
    gramR Γ e = ((Matrix.of e).map star * Γ * (Matrix.of e).transpose).det := by
  unfold gramR
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end ValuationRepresentative

open ValuationRepresentative

theorem valuation_basic_properties : ValBasic := by
  intro K _ _ _ w
  exact ⟨fun a b ha hb => vw_mul w a b ha hb, vw_star w, lw_conjPl w, conjPl_conjPl w,
    vw_one w, vw_inv w, vw_int_nonneg w⟩

theorem gram_matrix_change : GramChange := by
  intro K _ _ D m Γ e γ
  have h : Matrix.of (fun i => ∑ k, γ k i • e k) = γᵀ * Matrix.of e := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have hm : (γᵀ * Matrix.of e).map star = γᵀ.map star * (Matrix.of e).map star := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      star_sum, star_mul']
  have hd : (γᵀ.map star).det = star γ.det := Matrix.det_conjTranspose γ
  have hr : γᵀ.map star * (Matrix.of e).map star * Γ * ((Matrix.of e)ᵀ * γ) =
      γᵀ.map star * ((Matrix.of e).map star * Γ * (Matrix.of e)ᵀ) * γ := by
    simp only [Matrix.mul_assoc]
  rw [gramR_eq, gramR_eq, h, hm, Matrix.transpose_mul, Matrix.transpose_transpose, hr,
    Matrix.det_mul, Matrix.det_mul, hd]
  ring

theorem finite_sum_conjugation : FinsumConj := by
  intro K _ _ _ f
  exact finsum_comp_equiv (Function.Involutive.toPerm _ (fun w => conjPl_conjPl w))

end Formalism.DivisionValues
end
end


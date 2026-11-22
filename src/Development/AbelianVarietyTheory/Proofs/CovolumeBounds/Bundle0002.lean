import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroMemFractionalIdealNormSqLe
section
namespace GlobalTheory

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped nonZeroDivisors NNReal ENNReal

section General

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

theorem exists_ne_zero_mem_fractionalIdeal_place_le (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (g : InfinitePlace K → ℝ≥0) (h : minkowskiBound K I ≤ volume (convexBodyLT K g)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a ≤ g w := by
  set S : Set (mixedSpace K) :=
    (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => Metric.closedBall 0 (g w))) ×ˢ
    (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => Metric.closedBall 0 (g w)))
    with hS
  have hsub : convexBodyLT K g ⊆ S :=
    Set.prod_mono (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall)
      (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall)
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simp only [hS, Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
      mem_closedBall_zero_iff, norm_neg, forall_true_left, Prod.snd_neg] at hx ⊢
    exact hx
  have hconv : Convex ℝ S :=
    Convex.prod (convex_pi (fun _ _ => convex_closedBall _ _))
      (convex_pi (fun _ _ => convex_closedBall _ _))
  have hcomp : IsCompact S :=
    IsCompact.prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
      (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (Submodule.span ℤ
      (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      h_fund hneg hconv hcomp (h.trans (measure_mono hsub))
  rw [Submodule.mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, by simpa using h_nz, fun w => ?_⟩
  simp only [hS, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_closedBall_zero_iff] at h_mem
  rw [← normAtPlace_apply]
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw]
    exact h_mem.1 ⟨w, hw⟩
  · rw [normAtPlace_apply_of_isComplex hw]
    exact h_mem.2 ⟨w, hw⟩

end General

section TotallyComplex

variable {E : Type*} [Field E] [NumberField E] [IsTotallyComplex E] {f : ℕ}

theorem exists_ne_zero_mem_fractionalIdeal_norm_sq_le (hf : finrank ℚ E = 2 * f)
    (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0) :
    ∃ a ∈ J, a ≠ 0 ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ^ 2 ≤
      2 / Real.pi * ((FractionalIdeal.absNorm J : ℝ) * √|(discr E : ℝ)|) ^ ((f : ℝ)⁻¹) := by
  classical
  have hc : nrComplexPlaces E = f := by
    have := IsTotallyComplex.finrank E
    omega
  have hr : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have hf0 : f ≠ 0 := by
    have : 0 < finrank ℚ E := finrank_pos
    omega
  set X : ℝ := (FractionalIdeal.absNorm J : ℝ) * √|(discr E : ℝ)| with hX
  have hN : (0 : ℝ) ≤ (FractionalIdeal.absNorm J : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  have hX0 : 0 ≤ X := mul_nonneg hN (Real.sqrt_nonneg _)
  set B : ℝ := 2 / Real.pi * X ^ ((f : ℝ)⁻¹) with hB
  have hB0 : 0 ≤ B := by positivity
  let R : ℝ≥0 := ⟨√B, Real.sqrt_nonneg _⟩
  have hR : (R : ℝ) ^ 2 = B := Real.sq_sqrt hB0
  obtain ⟨a, ha, ha0, hle⟩ := exists_ne_zero_mem_fractionalIdeal_place_le E
    (Units.mk0 J hJ) (fun _ => R) (by
      rw [convexBodyLT_volume, minkowskiBound,
        volume_fundamentalDomain_fractionalIdealLatticeBasis,
        volume_fundamentalDomain_latticeBasis, mixedEmbedding.finrank,
        Finset.prod_pow_eq_pow_sum, sum_mult_eq, hf, convexBodyLTFactor, hc, hr]
      refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp (le_of_eq ?_)
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.coe_toReal,
        ENNReal.toReal_ofNat, Units.val_mk0, ENNReal.toReal_ofReal hN, pow_zero, one_mul,
        NNReal.coe_pow, NNReal.coe_real_pi, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
      rw [pow_mul (R : ℝ), hR, hB, mul_pow, Real.rpow_inv_natCast_pow hX0 hf0, hX, pow_mul,
        div_pow, show ((2 : ℝ) ^ 2) ^ f = 2 ^ f * 2 ^ f by rw [← mul_pow]; norm_num, inv_pow]
      have := Real.pi_pos
      field_simp)
  refine ⟨a, ha, ha0, fun τ => ?_⟩
  rw [← hR]
  have := hle (InfinitePlace.mk τ)
  rw [InfinitePlace.apply] at this
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

end TotallyComplex

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
section
open Matrix Module
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.Hadamard

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem norm_orthonormalBasis_det_le (b : OrthonormalBasis ι 𝕜 E) (x : ι → E) :
    ‖b.toBasis.det x‖ ≤ ∏ k, ‖x k‖ := by
  classical
  haveI : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  letI : LocallyFiniteOrderBot ι :=
    LocallyFiniteOrderBot.ofIic ι (fun a => Finset.univ.filter (· ≤ a)) (by simp)
  have h : finrank 𝕜 E = Fintype.card ι := finrank_eq_card_basis b.toBasis
  set c := InnerProductSpace.gramSchmidtOrthonormalBasis h x with hc
  have h1 : b.toBasis.det x = b.toBasis.det c * c.toBasis.det x := by
    conv_lhs => rw [b.toBasis.det.eq_smul_basis_det c.toBasis]
    simp
  have h2 : c.toBasis.det x = ∏ i, ⟪c i, x i⟫_𝕜 := by
    convert InnerProductSpace.gramSchmidtOrthonormalBasis_det h x
  rw [h1, norm_mul, b.det_to_matrix_orthonormalBasis c, one_mul, h2, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  simpa [c.orthonormal.1 i] using norm_inner_le_norm (𝕜 := 𝕜) (c i) (x i)

theorem norm_det_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖ ^ 2) := by
  have h := norm_orthonormalBasis_det_le (EuclideanSpace.basisFun ι 𝕜)
    (fun j => (WithLp.toLp 2 fun i => A i j : EuclideanSpace 𝕜 ι))
  simp only [EuclideanSpace.norm_eq] at h
  convert h using 2
  rw [Basis.det_apply]
  congr 1

theorem norm_det_le_prod_row (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ i, √(∑ j, ‖A i j‖ ^ 2) := by
  rw [← det_transpose]
  exact norm_det_le_prod_col Aᵀ

theorem norm_det_sq_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_prod_col A) 2).trans_eq ?_
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ => Real.sq_sqrt (by positivity)

theorem norm_det_sq_le_prod_row (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [← det_transpose]
  exact norm_det_sq_le_prod_col Aᵀ

theorem det_gram_nonneg (x : ι → E) : 0 ≤ (gram 𝕜 x).det :=
  (posSemidef_gram 𝕜 x).det_nonneg

theorem re_det_gram_nonneg (x : ι → E) : 0 ≤ RCLike.re (gram 𝕜 x).det :=
  (RCLike.nonneg_iff.mp (det_gram_nonneg x)).1

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in

theorem gram_sum_smul [Fintype κ] (e : ι → E) (m : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j => ∑ i, m i j • e i) = mᴴ * gram 𝕜 e * m := by
  ext j k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_apply,
    conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem re_det_gram_sum_smul (e : ι → E) (m : Matrix ι ι 𝕜) :
    RCLike.re (gram 𝕜 (fun j => ∑ i, m i j • e i)).det
      = ‖m.det‖ ^ 2 * RCLike.re (gram 𝕜 e).det := by
  rw [gram_sum_smul, det_mul, det_mul, det_conjTranspose, mul_right_comm, RCLike.star_def,
    RCLike.conj_mul]
  norm_cast
  rw [RCLike.re_ofReal_mul]

theorem exists_orthonormal_of_linearIndependent {x : ι → E} (hx : LinearIndependent 𝕜 x) :
    ∃ (e : ι → E) (m : Matrix ι ι 𝕜), Orthonormal 𝕜 e ∧ ∀ j, x j = ∑ i, m i j • e i := by
  set S := Submodule.span 𝕜 (Set.range x)
  haveI : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range x)
  have h : finrank 𝕜 S = Fintype.card ι := finrank_span_eq_card hx
  let b : OrthonormalBasis ι 𝕜 S :=
    (stdOrthonormalBasis 𝕜 S).reindex (Fintype.equivFinOfCardEq h.symm).symm
  let y : ι → S := fun j => ⟨x j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨fun i => (b i : E), of fun i j => b.repr (y j) i,
    b.orthonormal.comp_linearIsometry S.subtypeₗᵢ, fun j => ?_⟩
  have := congrArg (fun s : S => (s : E)) (b.sum_repr (y j))
  simpa using this.symm

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem norm_sum_smul_sq {e : ι → E} (he : Orthonormal 𝕜 e) (c : ι → 𝕜) :
    ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have h := he.inner_sum c c Finset.univ
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [RCLike.conj_mul] at h
  exact_mod_cast h

theorem re_det_gram_le_prod (x : ι → E) : RCLike.re (gram 𝕜 x).det ≤ ∏ k, ‖x k‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he]
    simp only [det_one, RCLike.one_re, mul_one, norm_sum_smul_sq he]
    exact norm_det_sq_le_prod_col m
  · rw [← det_gram_ne_zero_iff_linearIndependent, not_not] at hx
    rw [hx, map_zero]
    positivity

omit [DecidableEq ι] in

theorem det_gram_comp_equiv [DecidableEq ι] (x : ι → E) (σ : κ ≃ ι) :
    (gram 𝕜 (x ∘ σ)).det = (gram 𝕜 x).det :=
  det_submatrix_equiv_self σ (gram 𝕜 x)

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in

theorem sum_norm_apply_sq_le {e : ι → E} (he : Orthonormal 𝕜 e) (φ : E →L[𝕜] 𝕜) :
    ∑ i, ‖φ (e i)‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
  set s := ∑ i, ‖φ (e i)‖ ^ 2 with hs
  set v := ∑ i, (starRingEnd 𝕜) (φ (e i)) • e i with hv
  have hs0 : 0 ≤ s := by positivity
  have h1 : ‖v‖ ^ 2 = s := by simp [hv, norm_sum_smul_sq he, hs]
  have h2 : φ v = (s : 𝕜) := by
    simp [hv, hs, RCLike.conj_mul]
  have h3 : s ≤ ‖φ‖ * ‖v‖ := by
    have := φ.le_opNorm v
    rwa [h2, RCLike.norm_ofReal, abs_of_nonneg hs0] at this
  nlinarith [sq_nonneg (‖φ‖ - ‖v‖)]

theorem norm_det_apply_sq_le (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ^ 2 ≤ RCLike.re (gram 𝕜 x).det * ∏ j, ‖φ j‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    have h : (of fun j k => φ j (x k)) = (of fun j i => φ j (e i)) * m := by
      ext j k
      simp [hm, mul_apply, mul_comm]
    rw [h]
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he, det_mul, norm_mul, mul_pow,
      det_one, RCLike.one_re, mul_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ((norm_det_sq_le_prod_row _).trans ?_) (by positivity)
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun j _ => sum_norm_apply_sq_le he (φ j)
  · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hx
    have h0 : (of fun j k => φ j (x k)).det = 0 := by
      refine exists_mulVec_eq_zero_iff.mp ⟨g, fun h => hi (congrFun h i), ?_⟩
      funext j
      have := congrArg (φ j) hg
      simpa [mulVec, dotProduct, mul_comm] using this
    rw [h0, norm_zero]
    exact (by norm_num : (0 : ℝ) ^ 2 ≤ 0).trans
      (mul_nonneg (re_det_gram_nonneg x) (by positivity))

theorem norm_det_apply_le (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ≤ (∏ k, ‖x k‖) * ∏ j, ‖φ j‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
  exact (norm_det_apply_sq_le φ x).trans
    (mul_le_mul_of_nonneg_right (re_det_gram_le_prod x) (by positivity))

end GlobalTheory.Hadamard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsQr
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.QRDecomp

open Matrix in
open scoped ComplexOrder in

theorem _root_.GlobalTheory.QRDecomp.exists_qr (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    ∃ (Q : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ),
      Qᴴ * Q = 1 ∧ u.BlockTriangular id ∧ IsUnit u.det ∧ A = Q * u := by
  classical
  have hinj : Function.Injective A.mulVec := by
    intro v w h
    have h2 : (Aᴴ * A) *ᵥ v = (Aᴴ * A) *ᵥ w := by rw [← mulVec_mulVec, ← mulVec_mulVec, h]
    exact (mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hA)) h2
  have hS : (Aᴴ * A).PosDef := PosDef.conjTranspose_mul_self A hinj
  set L := LDL.lowerInv hS
  set d := LDL.diagEntries hS
  haveI : Invertible L := LDL.invertibleLowerInv hS
  have hLu : IsUnit L.det := isUnit_det_of_invertible L
  have hD : diagonal d = L * (Aᴴ * A) * Lᴴ := LDL.diag_eq_lowerInv_conj hS
  have hDpos : (diagonal d).PosDef := by
    rw [hD]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hLu))
  have hd : ∀ i, 0 < d i := fun i => by simpa using hDpos.diag_pos (i := i)
  have hdre : ∀ i, d i = ((d i).re : ℂ) ∧ 0 < (d i).re := fun i => by
    have h := hd i
    rw [Complex.pos_iff] at h
    exact ⟨Complex.ext (by simp) (by simp [h.2]), h.1⟩
  let r : Fin m → ℂ := fun i => ((Real.sqrt (d i).re : ℝ) : ℂ)
  have hr0 : ∀ i, r i ≠ 0 := fun i => by
    simp only [r, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (hdre i).2).ne'
  have hrr : ∀ i, star (r i) * r i = d i := fun i => by
    simp only [r, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hdre i).2.le, ← (hdre i).1]
  have hLt : Lᴴ.BlockTriangular id := fun i j hij => by
    have h : LDL.lowerInv hS j i = 0 := LDL.lowerInv_triangular hS hij
    simp [conjTranspose_apply, L, h]
  refine ⟨A * Lᴴ * diagonal (fun i => (r i)⁻¹), diagonal r * (Lᴴ)⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : (A * Lᴴ * diagonal fun i => (r i)⁻¹)ᴴ * (A * Lᴴ * diagonal fun i => (r i)⁻¹)
        = (diagonal fun i => star (r i)⁻¹) * (L * (Aᴴ * A) * Lᴴ) * diagonal fun i => (r i)⁻¹ := by
      simp only [conjTranspose_mul, diagonal_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rfl
    rw [h1, ← hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← hrr i]
    have h0 := hr0 i
    have h0' : star (r i) ≠ 0 := star_ne_zero.mpr h0
    rw [star_inv₀]
    field_simp
  · exact (blockTriangular_diagonal r).mul (blockTriangular_inv_of_blockTriangular hLt)
  · rw [det_mul, det_diagonal]
    exact (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hr0 i)).mul
      (isUnit_nonsing_inv_det _ (isUnit_det_of_invertible Lᴴ))
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have h1 : (fun i => (r i)⁻¹ * r i) = fun _ => (1 : ℂ) :=
      funext fun i => inv_mul_cancel₀ (hr0 i)
    rw [h1, diagonal_one, Matrix.one_mul, mul_inv_of_invertible, Matrix.mul_one]

end GlobalTheory.QRDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
section
open MeasureTheory Filter Metric Set
open scoped Topology Interval

namespace GlobalTheory

variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem aestronglyMeasurable_fderiv_apply_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) (v : E) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀ v) μ := by
  classical
  let f : ℂ → T → V := fun c t =>
    if AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ then
      c⁻¹ • (F t (x₀ + c • v) - F t x₀) else 0
  have h0 : AEStronglyMeasurable (fun t => F t x₀) μ := hmeas.self_of_nhds
  have hev : ∀ᶠ c : ℂ in 𝓝[≠] 0, AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ := by
    have hc : Tendsto (fun c : ℂ => x₀ + c • v) (𝓝 0) (𝓝 x₀) := by
      have : Continuous (fun c : ℂ => x₀ + c • v) := by fun_prop
      simpa using this.tendsto 0
    exact (hc.eventually hmeas).filter_mono nhdsWithin_le_nhds
  refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ)) (f := f) (fun c => ?_) ?_
  · by_cases h : AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ
    · simp only [f, if_pos h]
      exact (h.sub h0).const_smul c⁻¹
    · simp only [f, if_neg h]
      exact aestronglyMeasurable_const
  · filter_upwards [hdiff] with t ht
    have h1 := hasLineDerivAt_iff_tendsto_slope_zero.1 (ht.hasFDerivAt.hasLineDerivAt v)
    refine h1.congr' ?_
    filter_upwards [hev] with c hc
    simp only [f, if_pos hc]

variable [FiniteDimensional ℂ E]

theorem aestronglyMeasurable_fderiv_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀) μ := by
  let b := Module.finBasis ℂ E
  have key : (fun t => fderiv ℂ (F t) x₀) = fun t =>
      ∑ i, ContinuousLinearMap.smulRightL ℂ E V
        (LinearMap.toContinuousLinearMap (b.coord i)) (fderiv ℂ (F t) x₀ (b i)) := by
    funext t
    ext v
    have h : fderiv ℂ (F t) x₀ v = ∑ i, (b.repr v) i • fderiv ℂ (F t) x₀ (b i) := by
      conv_lhs => rw [← b.sum_repr v]
      simp only [map_sum, map_smul]
    simpa using h
  rw [key]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℂ E V
    (LinearMap.toContinuousLinearMap (b.coord i))).continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_fderiv_apply_of_param hmeas hdiff (b i))

set_option linter.unusedSectionVars false

variable [CompleteSpace V]

theorem hasFDerivAt_integral_of_holomorphic_of_dominated {F : T → E → V} {x₀ : E} {s : Set E}
    {bound : T → ℝ} (hs : s ∈ 𝓝 x₀)
    (hmeas : ∀ y ∈ s, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) s)
    (hbound : ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) (hint : Integrable bound μ) :
    Integrable (fun t => F t x₀) μ ∧ Integrable (fun t => fderiv ℂ (F t) x₀) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x₀ ∂μ) x₀ := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  have hat : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀ := hdiff.mono fun t ht => ht.differentiableAt hs
  have hF₀ : Integrable (fun t => F t x₀) μ :=
    hint.mono' (hmeas x₀ hx₀) (hbound.mono fun t ht => ht x₀ hx₀)
  refine ⟨hF₀, ?_⟩
  refine hasFDerivAt_integral_of_dominated_loc_of_lip' (𝕜 := ℂ) (F := fun y t => F t y)
    (F' := fun t => fderiv ℂ (F t) x₀) (bound := fun t => 2 * bound t / r)
    (ball_mem_nhds x₀ hr) (fun y hy => hmeas y (hrs hy)) hF₀
    (aestronglyMeasurable_fderiv_of_param (Filter.mem_of_superset hs hmeas) hat) ?_
    ((hint.const_mul 2).div_const r) (hat.mono fun t ht => ht.hasFDerivAt)
  filter_upwards [hdiff, hbound] with t ht hb y hy
  have hmaps : MapsTo (F t) (ball x₀ r) (closedBall (F t x₀) (2 * bound t)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hb z (hrs hz)
    have h2 := hb x₀ hx₀
    linarith [norm_sub_le (F t z) (F t x₀)]
  simpa [dist_eq_norm] using
    Complex.dist_le_div_mul_dist_of_mapsTo_ball (ht.mono hrs) hmaps hy

theorem differentiableOn_integral_of_holomorphic_of_locally_dominated {F : T → E → V}
    {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ y ∈ U, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) U)
    (hdom : ∀ x ∈ U, ∃ s ∈ 𝓝 x, ∃ bound : T → ℝ, Integrable bound μ ∧
      ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  have key : ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
    intro x hx
    obtain ⟨s, hs, bound, hint, hb⟩ := hdom x hx
    exact hasFDerivAt_integral_of_holomorphic_of_dominated (s := s ∩ U)
      (inter_mem hs (hU.mem_nhds hx)) (fun y hy => hmeas y hy.2)
      (hdiff.mono fun t ht => ht.mono inter_subset_right)
      (hb.mono fun t ht y hy => ht y hy.1) hint
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩

theorem differentiableOn_setIntegral_of_holomorphic_of_continuousOn [TopologicalSpace T]
    [OpensMeasurableSpace T] {F : T → E → V} {U : Set E} (hU : IsOpen U) {S K : Set T}
    (hK : IsCompact K) (hSK : S ⊆ K) (hS : MeasurableSet S) (hfin : μ S ≠ ⊤)
    (hcont : ContinuousOn (Function.uncurry F) (K ×ˢ U))
    (hdiff : ∀ t ∈ S, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in S, F t y ∂μ) U ∧
      ∀ x ∈ U, IntegrableOn (fun t => F t x) S μ ∧
        IntegrableOn (fun t => fderiv ℂ (F t) x) S μ ∧
        HasFDerivAt (fun y => ∫ t in S, F t y ∂μ) (∫ t in S, fderiv ℂ (F t) x ∂μ) x := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hfin.lt_top⟩
  refine differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ.restrict S) hU
    (fun y hy => ?_) (ae_restrict_of_forall_mem hS hdiff) (fun x hx => ?_)
  · have : ContinuousOn (fun t => F t y) K :=
      hcont.comp (f := fun t => (t, y)) (by fun_prop) fun t ht => ⟨ht, hy⟩
    exact this.aestronglyMeasurable_of_subset_isCompact hK hS hSK
  · obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
    obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall x r)).exists_bound_of_continuousOn
      (hcont.mono (prod_mono subset_rfl hrU))
    refine ⟨closedBall x r, closedBall_mem_nhds x hr, fun _ => C, integrable_const C, ?_⟩
    exact ae_restrict_of_forall_mem hS fun t ht y hy => hC (t, y) ⟨hSK ht, hy⟩

theorem differentiableOn_integral_of_holomorphic_of_continuousOn [TopologicalSpace T]
    [OpensMeasurableSpace T] [CompactSpace T] [IsFiniteMeasure μ] {F : T → E → V} {U : Set E}
    (hU : IsOpen U) (hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ U))
    (hdiff : ∀ t, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  simpa only [Measure.restrict_univ, integrableOn_univ] using
    differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := μ) hU isCompact_univ
      subset_rfl MeasurableSet.univ (measure_ne_top μ _) hcont fun t _ => hdiff t

theorem differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn {F : ℝ → E → V}
    {U : Set E} (hU : IsOpen U) {a b : ℝ}
    (hcont : ContinuousOn (Function.uncurry F) ([[a, b]] ×ˢ U))
    (hdiff : ∀ t ∈ [[a, b]], DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in a..b, F t y) U ∧
      ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
        IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
        HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
  have h := differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := volume) hU
    (isCompact_uIcc (a := a) (b := b)) uIoc_subset_uIcc measurableSet_uIoc
    (by simp [uIoc]) hcont fun t ht => hdiff t (uIoc_subset_uIcc ht)
  have key : ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
      IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
      HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := h.2 x hx
    refine ⟨intervalIntegrable_iff.2 h1, intervalIntegrable_iff.2 h2, ?_⟩
    simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    split_ifs
    · simpa using h3
    · simpa using h3.fun_neg
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩

end GlobalTheory
end


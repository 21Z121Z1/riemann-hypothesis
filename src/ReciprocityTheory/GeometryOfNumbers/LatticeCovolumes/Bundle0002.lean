import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle0001
import Mathlib

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.DegStA
section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder Matrix

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem IsFrame.ds_spanK_eq {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    Submodule.span K (Set.range v) = Submodule.span K (E : Set V) := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hv.1 i)
  · exact Submodule.span_le.mpr hv.2.2

theorem IsFrame.length_eq_latticeRank {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    r = latRank K E := by
  unfold latRank
  rw [← hv.ds_spanK_eq, finrank_span_eq_card hv.2.1, Fintype.card_fin]

theorem exists_isFullRankFamily_of_fg (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ r, ∃ v : Fin r → V, IsFrame K E v := by
  obtain ⟨S, hS⟩ := hE
  obtain ⟨b, hbE, hspan, hli⟩ := exists_linearIndependent K (E : Set V)
  have hEle : ∀ x ∈ E, x ∈ Submodule.span K (S : Set V) := by
    intro x hx
    rw [← hS] at hx
    exact Submodule.span_le_restrictScalars (𝓞 K) K (S : Set V) hx
  have hfin : Finite b := by
    refine hli.finite_of_le_span_finite _ (S : Set V) ?_
    rintro _ ⟨x, rfl⟩
    exact hEle _ (hbE x.2)
  let _ := Fintype.ofFinite b
  refine ⟨Fintype.card b, fun i => ((Fintype.equivFin b).symm i : V), ?_, ?_, ?_⟩
  · intro i; exact hbE ((Fintype.equivFin b).symm i).2
  · exact hli.comp _ (Fintype.equivFin b).symm.injective
  · intro x hx
    have : x ∈ Submodule.span K (b : Set V) := hspan ▸ Submodule.subset_span hx
    have hr : Set.range (fun i => ((Fintype.equivFin b).symm i : V)) = b := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin b).symm i).2
      · intro hy; exact ⟨Fintype.equivFin b ⟨y, hy⟩, by simp⟩
    rw [SetLike.mem_coe, hr]
    exact this

theorem IsFrame.relIndex_span_frame_ne_zero {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := by
  classical
  set S := Submodule.span (𝓞 K) (Set.range v) with hSdef
  set H := S.toAddSubgroup.addSubgroupOf E.toAddSubgroup with hH
  have : Module.Finite (𝓞 K) E := Module.Finite.iff_fg.mpr hE
  have : Module.Finite ℤ E := Module.Finite.trans (𝓞 K) E
  have hfg : AddGroup.FG E := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hfg' : AddGroup.FG E.toAddSubgroup := hfg
  have : Module.Finite ℤ E.toAddSubgroup := Module.Finite.iff_addGroup_fg.mpr hfg'
  have : Module.Finite ℤ (E.toAddSubgroup ⧸ H) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' H).toIntLinearMap
      (QuotientAddGroup.mk'_surjective H)
  have : Finite (E.toAddSubgroup ⧸ H) := by
    apply Module.finite_of_fg_torsion
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hv.2.2 x.2)
      obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
      have hd : ∀ i, IsIntegral ℤ (y • c i) := fun i => hy _ (Finset.mem_image_of_mem c (Finset.mem_univ i))
      let d : Fin r → 𝓞 K := fun i => ⟨y • c i, hd i⟩
      refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
      have hmem : (y • (x : V)) ∈ S := by
        have : y • (x : V) = ∑ i, d i • v i := by
          rw [← hc, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← algebraMap_smul K (d i) (v i), ← smul_assoc]
          rfl
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      show (y : ℤ) • (QuotientAddGroup.mk x : E.toAddSubgroup ⧸ H) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact hmem
  exact AddSubgroup.index_ne_zero_of_finite

section
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem HermFam.ds_form_zero_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) : h.form σ x 0 = 0 := by
  have := h.add_right σ x 0 0
  rw [add_zero] at this
  linear_combination -this

theorem HermFam.ds_form_sum_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.ds_form_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, ih]

theorem HermFam.ds_form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by
  rw [← h.conj_symm, h.ds_form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => h.conj_symm σ y (f i)

theorem HermFam.ds_form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]

theorem HermFam.ds_gram_comb (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    h.gram σ (fun j => ∑ i, G i j • v i) = (G.map σ)ᴴ * h.gram σ v * G.map σ := by
  ext a b
  simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, h.ds_form_sum_left, h.ds_form_sum_right, h.ds_form_smul_left, h.smul_right,
    Finset.sum_mul, Complex.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem HermFam.ds_gram_det_re_pos (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) : 0 < (h.gram σ v).det.re := by
  have := (h.posDef σ r v hv).det_pos
  exact (Complex.pos_iff.mp this).1

theorem HermFam.ds_gram_comb_det_re (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Complex.normSq (σ G.det) * (h.gram σ v).det.re := by
  rw [h.ds_gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, RingHom.map_det]
  have : star (σ.mapMatrix G).det * (h.gram σ v).det * (σ.mapMatrix G).det =
      (Complex.normSq (σ.mapMatrix G).det : ℂ) * (h.gram σ v).det := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
  rw [RingHom.mapMatrix_apply] at this ⊢
  rw [this, Complex.re_ofReal_mul]

theorem HermFam.ds_log_gram_comb (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) (G : Matrix (Fin r) (Fin r) K) (hG : G.det ≠ 0) :
    Real.log (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Real.log (Complex.normSq (σ G.det)) + Real.log (h.gram σ v).det.re := by
  rw [h.ds_gram_comb_det_re, Real.log_mul]
  · exact (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hG)).ne'
  · exact (h.ds_gram_det_re_pos σ hv).ne'

end

section
variable {K : Type*} [Field K] [NumberField K]

theorem ds_prod_embeddings_eq_norm (x : K) :
    ∏ σ : K →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => by simp [RingHom.equivRatAlgHom_apply])

theorem ds_sum_log_normSq_embeddings (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) = 2 * Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Real.log_prod (fun σ _ => (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)).ne'),
    ← map_prod, ds_prod_embeddings_eq_norm]
  have hn : (Algebra.norm ℚ x : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.normSq_ofReal, Real.log_mul hn hn,
    Real.log_abs]
  ring

end

end ReciprocityTheory.GeometryOfNumbersTheory
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidSt
section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

noncomputable def qC {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * G i j * y j).re

noncomputable def qR {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, y i * G i j * y j

private lemma exists_factor_C {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, G = Bᴴ * B := by
  first
  | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
  | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
  | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
  | (refine ⟨hG.posSemidef.sqrt, ?_⟩
     rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
  | (refine ⟨CFC.sqrt G, ?_⟩
     have h0 : 0 ≤ G := hG.posSemidef.nonneg
     have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
     rw [hs, CFC.sqrt_mul_sqrt_self G h0])

private lemma exists_factor_R {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᵀ * B := by
  have hC : ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᴴ * B := by
    first
    | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
    | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
    | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
    | (refine ⟨hG.posSemidef.sqrt, ?_⟩
       rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
    | (refine ⟨CFC.sqrt G, ?_⟩
       have h0 : 0 ≤ G := hG.posSemidef.nonneg
       have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
       rw [hs, CFC.sqrt_mul_sqrt_self G h0])
  obtain ⟨B, hB⟩ := hC
  exact ⟨B, by rw [hB, Matrix.conjTranspose_eq_transpose_of_trivial]⟩

private lemma qC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) :
    qC (Bᴴ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : (∑ i, ∑ j, starRingEnd ℂ (y i) * (Bᴴ * B) i j * y j) =
      dotProduct (star y) ((Bᴴ * B) *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, RCLike.star_def]
  unfold qC
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  refine Finset.sum_congr rfl (fun k _ => by ring)

private lemma qR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) :
    qR (Bᵀ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : qR (Bᵀ * B) y = dotProduct y ((Bᵀ * B) *ᵥ y) := by
    simp only [qR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, Real.norm_eq_abs, sq_abs, sq, abs_mul_abs_self]

private lemma setC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    {y | qC (Bᴴ * B) y ≤ R ^ 2} = ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qC_eq, LinearMap.restrictScalars_apply,
    Matrix.toLin'_apply, sqBall]

private lemma setR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    {y | qR (Bᵀ * B) y ≤ R ^ 2} = (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qR_eq, Matrix.toLin'_apply, sqBall]
  skip

private lemma detC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) :
    (Bᴴ * B).det = (Complex.normSq B.det : ℂ) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
  rfl

private theorem isBounded_preimage_sqBall_complex_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hS : IsCompact (sqBall r ℂ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous ((Matrix.toLin' B⁻¹).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨(Matrix.toLin' B).restrictScalars ℝ y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    Convex ℝ (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℂ) r R) ((Matrix.toLin' B).restrictScalars ℝ)

private theorem neg_mem_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    ∀ y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R,
      -y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℂ) r R _ hy

private theorem measurableSet_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    MeasurableSet (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hc : Continuous ((Matrix.toLin' B).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma hermitianEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : G = Bᴴ * B) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [detC_eq, h0] at h1
    simp at h1
  rw [setC_eq]
  exact ⟨convex_preimage_sqBall_complex B R, neg_mem_preimage_sqBall_complex B R, isBounded_preimage_sqBall_complex_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_complex B R⟩

theorem ellipsoidC_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_C hG
  exact hermitianEllipsoid_props_of_eq hG B hB R

theorem le_volume_ellipsoidC {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) {R : ℝ}
    (hR : 0 < R) :
    (2 * R ^ 2 / r) ^ r / G.det.re ≤ (volume {y : Fin r → ℂ | qC G y ≤ R ^ 2}).toReal := by
  obtain ⟨B, rfl⟩ := exists_factor_C hG
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [detC_eq, h0] at h1
    simp at h1
  have hN : 0 < Complex.normSq B.det := Complex.normSq_pos.2 hdet
  have hT : LinearMap.det ((Matrix.toLin' B).restrictScalars ℝ) = Complex.normSq B.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin']
    first
    | exact Algebra.norm_complex_apply _
    | simp [Algebra.norm_complex_apply]
  have hfin : volume (sqBall r ℂ R) ≠ ⊤ := (sqBall_isBounded (E := ℂ) r R).measure_lt_top.ne
  have hρ : 0 ≤ R / Real.sqrt r := div_nonneg hR.le (Real.sqrt_nonneg _)
  have hdisc : (volume (Metric.closedBall (0 : ℂ) (R / Real.sqrt r))).toReal
      = Real.pi * (R / Real.sqrt r) ^ 2 := by
    first
    | (simp only [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hρ, ENNReal.coe_toReal, NNReal.coe_real_pi] <;> ring_nf <;> done)
    | (simp [Complex.volume_closedBall, ENNReal.toReal_ofReal hρ] <;> ring_nf <;> done)
    | (simp [Complex.volume_closedBall, ENNReal.toReal_ofReal hρ, mul_comm] <;> done)
  have hbox : (2 * R ^ 2 / r) ^ r ≤ (volume (sqBall r ℂ R)).toReal := by
    have hmono := MeasureTheory.measure_mono (μ := volume) (box_subset_sqBall (E := ℂ) r (R := R))
    rw [MeasureTheory.volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hmono
    have h2 := ENNReal.toReal_mono hfin hmono
    rw [ENNReal.toReal_pow, hdisc] at h2
    refine le_trans ?_ h2
    have hq : (R / Real.sqrt r) ^ 2 = R ^ 2 / r := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg r)]
    rw [hq]
    have hR2 : 0 ≤ R ^ 2 / (r : ℝ) := div_nonneg (sq_nonneg R) (Nat.cast_nonneg r)
    have hle : 2 * R ^ 2 / (r : ℝ) ≤ Real.pi * (R ^ 2 / r) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hR2
    exact pow_le_pow_left₀ (by rw [mul_div_assoc]; exact mul_nonneg zero_le_two hR2) hle r
  rw [setC_eq, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rw [hT]; exact hN.ne'), hT,
    detC_eq, Complex.ofReal_re, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_inv, abs_of_pos hN, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hbox (inv_nonneg.2 hN.le)

private theorem isBounded_preimage_sqBall_real_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hS : IsCompact (sqBall r ℝ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous (Matrix.toLin' B⁻¹) := LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨Matrix.toLin' B y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    Convex ℝ ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℝ) r R) (Matrix.toLin' B)

private theorem neg_mem_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    ∀ y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R, -y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℝ) r R _ hy

private theorem measurableSet_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    MeasurableSet ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hc : Continuous (Matrix.toLin' B) := LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma realEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℝ)
    (hB : G = Bᵀ * B) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [setR_eq]
  exact ⟨convex_preimage_sqBall_real B R, neg_mem_preimage_sqBall_real B R, isBounded_preimage_sqBall_real_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_real B R⟩

theorem ellipsoidR_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_R hG
  exact realEllipsoid_props_of_eq hG B hB R

theorem le_volume_ellipsoidR {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) {R : ℝ}
    (hR : 0 < R) :
    (2 * R / Real.sqrt r) ^ r / Real.sqrt G.det ≤
      (volume {y : Fin r → ℝ | qR G y ≤ R ^ 2}).toReal := by
  obtain ⟨B, rfl⟩ := exists_factor_R hG
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h1
    exact lt_irrefl _ h1
  have hsq : Real.sqrt (Bᵀ * B).det = |B.det| := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]
  have habs : 0 < |B.det| := abs_pos.2 hdet
  have hfin : volume (sqBall r ℝ R) ≠ ⊤ := (sqBall_isBounded (E := ℝ) r R).measure_lt_top.ne
  have hbox : (2 * R / Real.sqrt r) ^ r ≤ (volume (sqBall r ℝ R)).toReal := by
    have hmono := MeasureTheory.measure_mono (μ := volume) (box_subset_sqBall (E := ℝ) r (R := R))
    rw [MeasureTheory.volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Real.volume_closedBall] at hmono
    have h2 := ENNReal.toReal_mono hfin hmono
    rw [ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (mul_nonneg zero_le_two (div_nonneg hR.le (Real.sqrt_nonneg _)))] at h2
    rw [mul_div_assoc]
    exact h2
  rw [setR_eq, MeasureTheory.Measure.addHaar_preimage_linearMap _
      (by rw [LinearMap.det_toLin']; exact hdet), LinearMap.det_toLin', hsq,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hbox (inv_nonneg.2 habs.le)

end ReciprocityTheory.GeometryOfNumbersTheory
end


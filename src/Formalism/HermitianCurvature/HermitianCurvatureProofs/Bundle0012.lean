import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CuspidalIrreducibleSubrep
section
open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7

noncomputable def geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j ∈ Finset.range n, t ^ (n - 1 - j) • (-X) ^ j

theorem geom {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * geoS X t = t ^ n • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hnil : ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) < i + k → (X ^ k) i j = 0 := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      rw [pow_zero, Matrix.one_apply_ne]
      intro h; rw [h] at hij; omega
    | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < i + k
      · rw [ih i l hl, zero_mul]
      · rw [hX l j (by rw [Fin.le_def]; omega), mul_zero]
  have hXn : X ^ n = 0 := by
    ext i j
    have hj := j.isLt
    simp [hnil n i j (by omega)]
  have hc : Commute (-X) (t • (1 : Matrix (Fin n) (Fin n) ℂ)) := (Commute.one_right _).smul_right t
  have h := hc.mul_geom_sum₂ n
  have hS : ∑ i ∈ Finset.range n, (-X) ^ i * (t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (n - 1 - i) = geoS X t := by
    unfold geoS
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, one_pow, Matrix.mul_smul, mul_one]
  rw [hS, smul_pow, one_pow, neg_pow, hXn, mul_zero, zero_sub] at h
  have e : t • (1 : Matrix (Fin n) (Fin n) ℂ) + X = -(-X - t • 1) := by rw [neg_sub, sub_neg_eq_add]
  rw [e, neg_mul, h, neg_neg]

theorem det_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det = t ^ n := by
  rw [Matrix.det_of_upperTriangular]
  · simp [hX _ _ le_rfl]
  · intro i j hij
    have hne : i ≠ j := (ne_of_lt hij).symm
    simp [Matrix.one_apply_ne hne, hX i j hij.le]

theorem sum_eq_geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (t : ℂ) :
    ∑ j ∈ Finset.range n, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) = ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  unfold geoS
  have key : ∀ m : ℕ, ∑ j ∈ Finset.range m, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) =
      ρ ⬝ᵥ ((∑ j ∈ Finset.range m, t ^ (n - 1 - j) • (-X) ^ j) *ᵥ B) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Matrix.add_mulVec, dotProduct_add,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_comm (t ^ (n - 1 - k))]
  exact key n

theorem Mcoord_eq {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Mcoord t X B ρ σ = blk (wMat n) 0 0 1 * blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ := by
  unfold Mcoord blk
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.mul_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply]
  · ext i j; simp [Matrix.mul_apply]

theorem det_blk_ne {n : ℕ} (t : ℂ) (ht : t ≠ 0) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det = t ^ n * σ - ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have hdet : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det = t ^ n := det_shift X hX t
  have ht' : t ^ n ≠ 0 := pow_ne_zero n ht
  have hinv : IsUnit (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det := by rw [hdet]; exact ht'.isUnit
  letI := (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).invertibleOfIsUnitDet hinv
  have hA : ⅟(t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) = (t ^ n)⁻¹ • geoS X t := by
    apply invOf_eq_right_inv
    rw [Matrix.mul_smul, geom X hX t, smul_smul, inv_mul_cancel₀ ht', one_smul]
  rw [Matrix.det_fromBlocks₁₁, hdet, hA, Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  rw [mul_sub]
  congr 1
  rw [Finset.mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  field_simp
  try ring

theorem continuous_blk_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Continuous fun t : ℂ => blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ := by
  unfold blk
  fun_prop

theorem continuous_geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Continuous fun t : ℂ => geoS X t := by
  unfold geoS
  fun_prop

theorem det_blk {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det = t ^ n * σ - ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  by_cases ht : t = 0
  swap
  · exact det_blk_ne t ht X hX B ρ σ
  have hc1 : Continuous fun s : ℂ => (blk (s • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det :=
    (continuous_blk_shift X B ρ σ).matrix_det
  have hc2 : Continuous fun s : ℂ => s ^ n * σ - ρ ⬝ᵥ (geoS X s *ᵥ B) :=
    ((continuous_pow n).mul continuous_const).sub
      (continuous_const.dotProduct ((continuous_geoS X).matrix_mulVec continuous_const))
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc1 hc2 (fun s hs => det_blk_ne s hs X hX B ρ σ)
  exact congrFun heq t

theorem det_Mcoord {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (Mcoord t X B ρ σ).det = (wMat n).det *
      (t ^ n * σ - ∑ j ∈ Finset.range n, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j)) := by
  have hW : (blk (wMat n) 0 0 1).det = (wMat n).det := by
    unfold blk
    rw [Matrix.det_reindex_self]
    simp only [Pi.zero_apply]
    rw [show (Matrix.of fun _ _ => (0 : ℂ) : Matrix _ (Fin n) ℂ) = 0 from rfl, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [Mcoord_eq, Matrix.det_mul, det_blk t X hX, sum_eq_geoS, hW]

theorem detMXY : DetMXY := by
  intro m D t p hC
  have hX := isStrictUpper_strictUpper (redOf m p).2.2.1
  have h := det_Mcoord t (strictUpper (redOf m p).2.2.1) hX (redOf m p).2.2.2
    (Fin.cons (rhoXY m D t p) (redOf m p).2.1) (redOf m p).1
  rw [cornerSplit m _ _ _ _ t] at h
  have e : detM (MXY m D t p) = (Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
      (Fin.cons (rhoXY m D t p) (redOf m p).2.1) (redOf m p).1).det := rfl
  rw [e, h]
  congr 1
  have hC' : Cof (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 t ≠ 0 := hC
  rw [rhoXY, rho1, mul_div_cancel₀ _ hC']
  ring

theorem redIntegrable : RedIntegrable := by
  intro m β t c ht V _ _ _ Φ hint
  have hemb := embedding_coordMap (m + 1) t ht
  have hJ := jacobian (m + 1) β t ht
  have hfun : blockIntegrand β (m + 1) Φ t c = Fint β m Φ t c ∘ coordMap (m + 1) t :=
    funext (blockIntegrand_eq β m Φ t c ht)
  have hpos : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  set κ : NNReal := Real.toNNReal ((‖t‖ ^ ((m + 1) * (m + 1 + 3)))⁻¹) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact (Real.toNNReal_pos.2 (by positivity)).ne'
  have hF : Integrable (Fint β m Φ t c) (muBlock β (m + 1)) := by
    have h : Integrable (Fint β m Φ t c) (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) :=
      hemb.integrable_map_iff.2 (hfun ▸ hint)
    rw [hJ, ENNReal.smul_def] at h
    exact (integrable_smul_measure (by simpa using hκ0) ENNReal.coe_ne_top).1 h
  have hmp := mp_consMap β m
  have hG : Integrable (fun q => Fint β m Φ t c (consMap m q)) (muRed β m) :=
    hmp.integrable_comp_of_integrable hF
  have hcC : Measurable (fun y : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) =>
      Cof (strictUpper y.2.1) y.2.2 t) := ((continuous_cof m t).comp continuous_snd).measurable
  set α : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) → ℂ :=
    fun y => t ^ (m + 1) / Cof (strictUpper y.2.1) y.2.2 t with hα
  set γ : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) → ℂ :=
    fun y => (-(c * t ^ (m + 1)) - R0 (strictUpper y.2.1) y.2.2 y.1 t) / Cof (strictUpper y.2.1) y.2.2 t with hγ
  have hαm : Measurable α := measurable_const.div hcC
  have hγm : Measurable γ := (measurable_const.sub (continuous_remainder m t).measurable).div hcC
  have hm := affine_fibre ((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))) β
    α γ hαm hγm ((ae_cof_ne' β t ht m).mono fun y hy => div_ne_zero (pow_ne_zero _ ht) hy)
  have hT : Measurable (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m)) := by fun_prop
  have hd : Measurable (fun p : RedCoord m => (‖α p.2‖₊ ^ 2 : NNReal)) := by fun_prop
  have hG' : Integrable (fun q => Fint β m Φ t c (consMap m q))
      (Measure.map (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m))
        ((muRed β m).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal)))) := by
    have : Measure.map (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m))
        ((muRed β m).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal))) = muRed β m := hm
    rw [this]; exact hG
  have h5 := hG'.comp_measurable hT
  have h6 := (integrable_withDensity_iff_integrable_smul hd).1 h5
  have h7 : Integrable (fun q : RedCoord m => ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) •
      redIntegrand β m Φ (c * t ^ (m + 1)) t q) (muRed β m) := by
    refine h6.congr (Filter.Eventually.of_forall fun q => ?_)
    have := pointwise_red β m Φ t c ht q
    simp only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm, Function.comp]
    rw [← Complex.coe_smul]
    exact this
  have hne : ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  exact (integrable_smul_iff hne _).1 h7

theorem innerXYOfReduced : InnerXYOfReduced := by
  intro hOm hRI hSplit hAmp m β t c ht V _ _ _ Φ hint
  have hmp := (hSplit m β).2
  have i1 : PolishSpace (XY m) := inferInstance
  have i2 : StandardBorelSpace (XY m) := inferInstance
  have i3 : SecondCountableTopology (RedCoord m) := inferInstance
  have i4 : MeasurableSpace.CountablyGenerated (RedCoord m) := inferInstance
  have i5 : MeasurableSpace.CountablySeparated (RedCoord m) := inferInstance
  have hemb : MeasurableEmbedding (redOf m) := hmp.measurable.measurableEmbedding (hSplit m β).1.injective
  have hfun : (fun p : XY m =>
      psi β (g0 ((-1) ^ (m + 3) * (c * t ^ (m + 1))) p.1 / t) • amp β m Φ (c * t ^ (m + 1)) t p) =
      redIntegrand β m Φ (c * t ^ (m + 1)) t ∘ redOf m :=
    funext fun p => hAmp m β (c * t ^ (m + 1)) t ht V Φ p
  have h1 := hRI m β t c ht V Φ hint
  have h2 := hOm m β t c ht V Φ hint
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hmp.integrable_comp_emb hemb).2 h1
  · rw [h2, hfun]
    exact (hmp.integral_comp hemb _).symm

end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep

namespace Formalism.FourierDecayAlt.P

theorem det_matrix_xy : Formalism.FourierDecayAlt.G.DetMXY := CuspidalIrreducibleSubrep.detMXY

theorem reduced_integrand_integrable : Formalism.FourierDecayAlt.G.RedIntegrable := CuspidalIrreducibleSubrep.redIntegrable

theorem inner_xy_of_reduced : Formalism.FourierDecayAlt.G.InnerXYOfReduced := CuspidalIrreducibleSubrep.innerXYOfReduced

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteClassesPositiveSums
section
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums

section gen

variable {α : Type}

theorem psd_congr {F : Finset α} {k k' : α → α → ℂ} (h : IsPSD F k)
    (e : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) : IsPSD F k' := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y :=
    sum_congr rfl fun x hx => sum_congr rfl fun y hy => by rw [e x hx y hy]
  rw [this]; exact h a

theorem psd_zero (F : Finset α) : IsPSD F (fun _ _ => (0 : ℂ)) := by
  intro a; simp

theorem psd_add {F : Finset α} {k k' : α → α → ℂ} (h : IsPSD F k) (h' : IsPSD F k') :
    IsPSD F (fun x y => k x y + k' x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y + ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y := by
    simp only [mul_add, sum_add_distrib]
  rw [this, Complex.add_im, Complex.add_re, (h a).1, (h' a).1]
  exact ⟨by simp, add_nonneg (h a).2 (h' a).2⟩

theorem psd_sum {ι : Type} {F : Finset α} (s : Finset ι) (k : ι → α → α → ℂ)
    (h : ∀ i ∈ s, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ s, k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero F
  | insert i s hi ih =>
    have := psd_add (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj))
    exact psd_congr this fun x _ y _ => by rw [sum_insert hi]

end gen

section classes

variable {K : Type} [CommRing K] (R : Subring K)

theorem out_mk (x : K) :
    ∃ r ∈ R, (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup) : K) = x + r := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R.toAddSubgroup x
  exact ⟨r.1, r.2, hr⟩

theorem periodic_out {β : Type} (f : K → β) (h1 : ∀ x, ∀ r ∈ R, f (x + r) = f x) (x : K) :
    f (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = f x := by
  obtain ⟨r, hr, e⟩ := out_mk R x
  rw [e, h1 x r hr]

theorem finite_classes [TopologicalSpace K] [IsTopologicalRing K] (hR : IsOpen (R : Set K))
    (Lc : Set K) (hLc : IsCompact Lc) :
    {y : K ⧸ R.toAddSubgroup | (Quotient.out y : K) ∈ Lc}.Finite := by
  have : DiscreteTopology (K ⧸ R.toAddSubgroup) := QuotientAddGroup.discreteTopology hR
  have h := (hLc.image (QuotientAddGroup.continuous_mk (N := R.toAddSubgroup))).finite_of_discrete
  refine h.subset ?_
  intro y hy
  exact ⟨Quotient.out y, hy, Quotient.out_eq' y⟩

variable {R} {F : Finset (Point K)} {Lc : Set K} {S : Finset (K ⧸ R.toAddSubgroup)}

theorem finsum_classes (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    {Θ : K → Point K → Point K → ℂ}
    (h3 : ∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0) {h h' : Point K} (hh : h ∈ F)
    (hh' : h' ∈ F) :
    ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h' = ∑ y ∈ S, Θ (Quotient.out y) h h' := by
  apply finsum_eq_sum_of_support_subset
  intro y hy
  by_contra hyS
  exact hy (h3 _ (fun hc => hyS (hS y hc)) h hh h' hh')

theorem psd_single (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    {M : Point K → Point K → ℂ} {Θ : K → Point K → Point K → ℂ}
    (h1 : ∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) (h2 : ∀ x, IsPSD F (Θ x))
    (h3 : ∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0)
    (h5 : IsPSD F (fun h h' => M h h' - ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h'))
    (x : K) : IsPSD F (fun h h' => M h h' - Θ x h h') := by
  classical
  have key := psd_add h5 (psd_sum (S.erase ((x : K) : K ⧸ R.toAddSubgroup))
    (fun y => Θ (Quotient.out y)) (fun y _ => h2 _))
  refine psd_congr key ?_
  intro h hh h' hh'
  have e1 := finsum_classes hS h3 hh hh'
  have e2 : Θ (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = Θ x := periodic_out R Θ h1 x
  simp only [e1]
  by_cases hx : ((x : K) : K ⧸ R.toAddSubgroup) ∈ S
  · rw [← add_sum_erase S (fun y => Θ (Quotient.out y) h h') hx, e2]
    ring
  · rw [erase_eq_of_notMem hx]
    have : Θ x h h' = 0 := by
      rw [← e2]
      exact h3 _ (fun hc => hx (hS _ hc)) h hh h' hh'
    rw [this]; ring

theorem limit_core (hEntry : PSDEntryBound) (hSubseq : BoundedSubseq)
    (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    (M : Point K → Point K → ℂ) (Th : ℕ → K → Point K → Point K → ℂ)
    (h1 : ∀ j x, ∀ r ∈ R, Th j (x + r) = Th j x) (h2 : ∀ j x, IsPSD F (Th j x))
    (h3 : ∀ j x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Th j x h h' = 0)
    (h5 : ∀ j, IsPSD F (fun h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Th j (Quotient.out y) h h')) :
    ∃ (φ : ℕ → ℕ) (Θ : K → Point K → Point K → ℂ), StrictMono φ ∧
      (∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) ∧
      ∀ x, ∀ h ∈ F, ∀ h' ∈ F, Tendsto (fun j => Th (φ j) x h h') atTop (𝓝 (Θ x h h')) := by
  classical
  let T : Finset ((K ⧸ R.toAddSubgroup) × Point K × Point K) := S ×ˢ F ×ˢ F
  let θ : ℕ → T → ℂ := fun j i => Th j (Quotient.out i.1.1) i.1.2.1 i.1.2.2
  let B : ℝ := ∑ h ∈ F, |(M h h).re|
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  have hBh : ∀ h ∈ F, |(M h h).re| ≤ B := fun h hh =>
    single_le_sum (f := fun h => |(M h h).re|) (fun _ _ => abs_nonneg _) hh
  have hb : ∀ j i, ‖θ j i‖ ≤ B := by
    rintro j ⟨⟨y, h, h'⟩, hi⟩
    simp only [T, mem_product] at hi
    have hE := hEntry _ F (Th j (Quotient.out y)) M (h2 j _)
      (psd_single hS (h1 j) (h2 j) (h3 j) (h5 j) _) h hi.2.1 h' hi.2.2
    have hle : (M h h).re * (M h' h').re ≤ B ^ 2 := by
      calc (M h h).re * (M h' h').re ≤ |(M h h).re * (M h' h').re| := le_abs_self _
        _ = |(M h h).re| * |(M h' h').re| := abs_mul _ _
        _ ≤ B * B := mul_le_mul (hBh h hi.2.1) (hBh h' hi.2.2) (abs_nonneg _) hB0
        _ = B ^ 2 := (sq B).symm
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).1 (hE.trans hle)
  obtain ⟨φ, l, hφ, hl⟩ := hSubseq T θ B hb
  refine ⟨φ, fun x h h' => if hx : (((x : K) : K ⧸ R.toAddSubgroup), h, h') ∈ T then l ⟨_, hx⟩
    else 0, hφ, ?_, ?_⟩
  · intro x r hr
    have e : (((x + r : K)) : K ⧸ R.toAddSubgroup) = ((x : K) : K ⧸ R.toAddSubgroup) := by
      rw [QuotientAddGroup.eq]
      have : -(x + r) + x = -r := by ring
      rw [this]
      exact neg_mem hr
    funext h h'
    simp only [e]
  · intro x h hh h' hh'
    have e2 : ∀ j, Th j (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = Th j x :=
      fun j => periodic_out R (Th j) (h1 j) x
    by_cases hx : (((x : K) : K ⧸ R.toAddSubgroup), h, h') ∈ T
    · simp only [dif_pos hx]
      have := hl ⟨_, hx⟩
      simp only [θ, e2] at this
      exact this
    · simp only [dif_neg hx]
      have hxS : ((x : K) : K ⧸ R.toAddSubgroup) ∉ S := by
        intro hc
        exact hx (by simp only [T, mem_product]; exact ⟨hc, hh, hh'⟩)
      have : ∀ j, Th (φ j) x h h' = 0 := by
        intro j
        rw [← e2]
        exact h3 _ _ (fun hc => hxS (hS _ hc)) h hh h' hh'
      simp only [this]
      exact tendsto_const_nhds

end classes

end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums

theorem thetaExistsStepOfSteps : Formalism.FourierDecayAlt.A6.ThetaExistenceInductive := by
  intro hThOm hSupp hNsS hCOne hExh _hLF hEntry hClosed hSubseq hA2 hN1 K _ _ _ R ψ hD hch s hs hAt
    n₀ F hF
  classical
  obtain ⟨Lc, hcut, hGL⟩ := hSupp hNsS K R ψ hD (s + 1) F (by omega)
  obtain ⟨Om, hOm, hmono, hex⟩ := hExh K R ψ hD hch (s + 1) (by omega)
  choose Th hTh using fun j => hThOm hA2 hN1 K R ψ hD hch s hs hAt n₀ F Lc (Om j) hF hcut (hOm j)
  obtain ⟨hLo, hLk, -, -⟩ := hcut
  have hfin := finite_classes R hD.isOpen (Lc : Set K) hLk
  have hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ (Lc : Set K) → y ∈ hfin.toFinset :=
    fun y hy => hfin.mem_toFinset.2 hy
  let M : Point K → Point K → ℂ := fun h h' =>
    ((cSize R h ^ (s + 1) * cSize R h' ^ (s + 1) : ℝ) : ℂ) * N0 R ψ h h'
  obtain ⟨φ, Θ, hφ, h1, hlim⟩ := limit_core hEntry hSubseq hS M Th (fun j => (hTh j).1)
    (fun j => (hTh j).2.1) (fun j => (hTh j).2.2.1) (fun j => (hTh j).2.2.2.2.1)
  have h2 : ∀ x, IsPSD F (Θ x) := fun x =>
    hClosed _ F (fun j => Th (φ j) x) (Θ x) (fun j => (hTh _).2.1 x) (hlim x)
  have h3 : ∀ x, x ∉ (Lc : Set K) → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0 := by
    intro x hx h hh h' hh'
    have := hlim x h hh h' hh'
    simp only [(hTh _).2.2.1 x hx h hh h' hh'] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  have h4 : ∀ t : Kˣ, IsPSD F (fun h h' => Θ (t : K) h h' - Ns R ψ (s + 1) h h' t t) := by
    intro t
    obtain ⟨j0, hj0⟩ := hex t
    have hmono' : ∀ j, j0 ≤ j → (t : K) ∈ Om j := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact hj0
      | succ j _ ih => exact hmono j ih
    refine hClosed _ F (fun j h h' => Th (φ (j + j0)) (t : K) h h' - Ns R ψ (s + 1) h h' t t) _
      (fun j => (hTh _).2.2.2.1 t (hmono' _ ((Nat.le_add_left _ _).trans hφ.le_apply))) ?_
    intro h hh h' hh'
    exact ((hlim (t : K) h hh h' hh').comp (tendsto_add_atTop_nat j0)).sub tendsto_const_nhds
  have h5 : IsPSD F (fun h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h') := by
    refine hClosed _ F (fun j h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Th (φ j) (Quotient.out y) h h') _
      (fun j => (hTh _).2.2.2.2.1) ?_
    intro h hh h' hh'
    simp only [finsum_classes hS h3 hh hh', finsum_classes hS ((hTh _).2.2.1) hh hh']
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun y _ => hlim _ h hh h' hh')
  have h6 : ∀ x, ∀ h ∈ F, ∀ h' ∈ F, modK R (pt h.1 h.2).det ≠ modK R (pt h'.1 h'.2).det →
      Θ x h h' = 0 := by
    intro x h hh h' hh' hne
    have := hlim x h hh h' hh'
    simp only [(hTh _).2.2.2.2.2 x h hh h' hh' hne] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  refine ⟨Θ, h1, h2, ⟨Lc, hLo, hLk, h3⟩, h4, h5, h6, ?_⟩
  intro hG x
  by_cases hx : x ∈ R
  · simp only [if_pos hx]
    refine psd_congr (psd_single hS h1 h2 h3 h5 x) ?_
    intro h hh h' hh'
    simp only [M, hCOne K R ψ hD h (hG h hh), hCOne K R ψ hD h' (hG h' hh')]
    simp
  · simp only [if_neg hx]
    refine psd_congr (psd_zero F) ?_
    intro h hh h' hh'
    rw [h3 x (fun hc => hx ((hGL hG x).1 hc)) h hh h' hh']
    simp

end Formalism.FourierDecayAlt.P
end
end


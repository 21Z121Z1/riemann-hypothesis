import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartPowNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace AddBlockData

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem chartPow_ne_zero {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (a : ι → ℤ) :
    P.chartPow c a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)

theorem elt_div_elt {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (i j : Fin (D.size + 1)) :
    D.elt i / D.elt j = D.xi c i * (D.xi c j)⁻¹ := by
  have hp := chartPow_ne_zero hc D.deg
  simp only [xi]
  field_simp

end AddBlockData

theorem ChartRingDescription.proof : ChartRingDescription.Statement := by
  intro ι _ _ n P D c hc j hj
  have hp := AddBlockData.chartPow_ne_zero hc D.deg
  set S := Subring.closure (insert (D.xi c j)⁻¹ (P.chartRing c : Set P.FunField))
  have hA : (P.chartRing c : Set P.FunField) ⊆ S := fun x hx ↦
    Subring.subset_closure (Set.mem_insert_of_mem _ hx)
  have hinv : (D.xi c j)⁻¹ ∈ S := Subring.subset_closure (Set.mem_insert _ _)
  apply le_antisymm
  · rw [AddBlockData.extChartRing, Subring.closure_le]
    rintro x (⟨v, rfl⟩ | ⟨i, rfl⟩)
    · exact hA (Subring.subset_closure ⟨v, rfl⟩)
    · show D.elt i / D.elt j ∈ S
      rw [D.elt_div_elt hc i j]
      exact S.mul_mem (hA (D.chart_mem c hc i)) hinv
  · have hA' : P.chartRing c ≤ D.extChartRing c j := by
      rw [ArithVariety.chartRing]
      exact Subring.closure_mono Set.subset_union_left
    rw [Subring.closure_le]
    rintro x (rfl | hx)
    · obtain ⟨u, hu, hsum⟩ := D.generating c hc
      have h : (D.xi c j)⁻¹ = ∑ i, u i * (D.elt i / D.elt j) := by
        rw [← one_mul (D.xi c j)⁻¹, ← hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [D.elt_div_elt hc i j, mul_assoc]
        rfl
      rw [h]
      refine Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (hA' (hu i)) ?_
      exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)
    · exact hA' hx

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DetGramLeProdNormSq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace HadamardGramBound

theorem det_gram_le_prod_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (w : Fin n → V) (hw : LinearIndependent ℝ w) :
    (Matrix.gram ℝ w).det ≤ ∏ i, ‖w i‖ ^ 2 := by
  set K := Submodule.span ℝ (Set.range w)
  have hK : Module.finrank ℝ K = Fintype.card (Fin n) := finrank_span_eq_card hw
  have : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  let w' : Fin n → K := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hg : Matrix.gram ℝ w = Matrix.gram ℝ w' := by
    ext i j
    simp [Matrix.gram_apply, w']
  let gb := InnerProductSpace.gramSchmidtOrthonormalBasis hK w'
  have hdet : gb.toBasis.det w' = ∏ i, inner ℝ (gb i) (w' i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hK w'
  rw [hg, Matrix.gram_eq_conjTranspose_mul gb, Matrix.det_mul, Matrix.det_conjTranspose]
  have hM : (Matrix.of fun i j => gb.repr (w' j) i) = gb.toBasis.toMatrix w' := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [hM, ← Module.Basis.det_apply, hdet, star_trivial, ← sq, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun i _ => sq_nonneg _) (fun i _ => ?_)
  have h1 := abs_real_inner_le_norm (gb i) (w' i)
  rw [gb.orthonormal.1 i, one_mul] at h1
  have h2 : ‖w' i‖ = ‖w i‖ := rfl
  rw [← h2, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

theorem gram_comb {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → V) :
    Matrix.gram ℝ (fun i => ∑ j, M i j • b j) = M * Matrix.gram ℝ b * M.transpose := by
  ext i k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem proof : HadamardGramBound.Statement := by
  intro V _ _ r v b hv hn hb
  choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hb i)
  set N : Matrix (Fin r) (Fin r) ℝ := (Matrix.of M).map (Int.cast : ℤ → ℝ) with hNdef
  have hvN : v = fun i => ∑ j, N i j • b j := by
    funext i
    rw [← hM i]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [N, Int.cast_smul_eq_zsmul]
  have hG : Matrix.gram ℝ v = N * Matrix.gram ℝ b * N.transpose := by
    rw [hvN]
    exact gram_comb N b
  have hdet : (Matrix.gram ℝ v).det = N.det ^ 2 * (Matrix.gram ℝ b).det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hvpos : 0 < (Matrix.gram ℝ v).det := (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  have hbnn : 0 ≤ (Matrix.gram ℝ b).det := (Matrix.posSemidef_gram ℝ b).det_nonneg
  have hNdet : N.det = (((Matrix.of M).det : ℤ) : ℝ) := by
    rw [hNdef]
    exact ((Int.castRingHom ℝ).map_det (Matrix.of M)).symm
  have hN0 : N.det ≠ 0 := by
    intro h
    rw [hdet, h] at hvpos
    simp at hvpos
  have hN1 : 1 ≤ N.det ^ 2 := by
    rw [hNdet] at hN0 ⊢
    have hd : (Matrix.of M).det ≠ 0 := by exact_mod_cast hN0
    have : (1 : ℤ) ≤ (Matrix.of M).det ^ 2 := by
      rcases lt_or_gt_of_ne hd with h | h <;> nlinarith
    exact_mod_cast this
  have hHad := det_gram_le_prod_norm_sq v hv
  have hprod : ∏ i, ‖v i‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one (fun i _ => sq_nonneg _) fun i _ => pow_le_one₀ (norm_nonneg _) (hn i)
  change 0 < (Matrix.gram ℝ b).det ∧ (Matrix.gram ℝ b).det ≤ 1
  refine ⟨lt_of_le_of_ne hbnn fun h => ?_, ?_⟩
  · rw [hdet, ← h] at hvpos
    simp at hvpos
  · nlinarith

end HadamardGramBound

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace SectionNorm

omit [DecidableEq ι] in

theorem evalCone_chartMonomial (z : Cone n ℂ) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by
  simp [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]

theorem evalCone_liftOld {P : ArithVariety n} (D : AddBlockData P) (w : Cone D.extSizes ℂ)
    (f : MvPolynomial (Coord n) ℤ) : evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by
  simp only [evalCone, AddBlockData.liftOld, eval₂_rename]
  rfl

theorem chartMonomial_ne_zero {P : ArithVariety n} (D : AddBlockData P) {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (D.size + 1)) (hgz : evalCone z (g c j) ≠ 0) :
    evalCone z (chartMonomial c d) ≠ 0 := by
  intro hm
  have hc : P.IsLive c := by
    by_contra hc
    exact hgz (by rw [hg.dead c hc j]; simp [evalCone])
  have hex : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c' hc' using hex
  have hlive : P.IsLive c' := by
    intro k hk
    apply hc' k
    have := hz.2 _ hk
    simpa [evalCone, eval₂_X] using this
  have hmem : chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc j, hg.value c' hlive j]
    ring
  have h0 := hz.2 _ hmem
  have hsub : evalCone z (chartMonomial c' d * g c j - chartMonomial c d * g c' j) =
      evalCone z (chartMonomial c' d) * evalCone z (g c j) -
        evalCone z (chartMonomial c d) * evalCone z (g c' j) := by
    simp [evalCone, eval₂_sub, eval₂_mul]
  rw [hsub, hm, zero_mul, sub_zero] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · rw [evalCone_chartMonomial] at h
    exact Finset.prod_ne_zero_iff.mpr (fun k _ ↦ pow_ne_zero _ (hc' k)) h
  · exact hgz h

end SectionNorm

theorem SectionNorm.proof (hP : ConePoints.Statement) (hM : ChartMetric.Statement) :
    SectionNorm.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG c j _ w hw hgz
  obtain ⟨hz, la, hla, hform⟩ := (hP ι n P D d g hg).2 w hw
  have hm := SectionNorm.chartMonomial_ne_zero D hg hz c j hgz
  have hmet := (hM ι n P D N hN d g hg r G δ hG).2 w hw c la hm (hform c hm)
  have hNpos : 0 < N.metric (D.basePart₂ w) := N.metric_pos _ hz.1
  have heval : evalCone w (X (D.newCoord j) * D.liftOld (chartMonomial c d)) =
      D.newPart w j * evalCone (D.basePart₂ w) (chartMonomial c d) := by
    rw [show evalCone w (X (D.newCoord j) * D.liftOld (chartMonomial c d)) =
        evalCone w (X (D.newCoord j)) * evalCone w (D.liftOld (chartMonomial c d)) by
      simp [evalCone, eval₂_mul], SectionNorm.evalCone_liftOld]
    simp [evalCone, eval₂_X, AddBlockData.newCoord, AddBlockData.newPart]
  rw [heval, SectionNorm.evalCone_liftOld, hmet, hform c hm j, div_mul_cancel₀ _ hm,
    mul_div_assoc, div_self hNpos.ne', mul_one, norm_mul]
  have h1 : ‖la‖ ≠ 0 := norm_ne_zero_iff.mpr hla
  have h2 : ‖evalCone (D.basePart₂ w) (g c j)‖ ≠ 0 := norm_ne_zero_iff.mpr hgz
  field_simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace BoundedMonomials

def chartNorm (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (e : MvPolynomial (Coord n) ℤ) (z : Cone n ℂ) : ℝ :=
  ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z)

omit [Fintype ι] in

theorem prod_pow_weight [Fintype ι] {F : Type*} [CommRing F] (u : ι → F) (m : Coord n →₀ ℕ) :
    (m.prod fun v e ↦ u v.1 ^ e) = ∏ k, u k ^ Finsupp.weight (coordDeg n) m k := by
  simp only [Finsupp.weight_apply, coordDeg, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finsupp.prod]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [Finset.prod_eq_single v.1 (fun k _ hk ↦ by simp [hk]) (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp

theorem evalCone_scale {F : Type*} [CommRing F] (u : ι → F) (z : Cone n F)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    evalCone (fun k i ↦ u k * z k i) f = (∏ k, u k ^ δ k) * evalCone z f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [evalCone, eval₂_sum, eval₂_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hw : Finsupp.weight (coordDeg n) m = δ := hf (mem_support_iff.mp hm)
  rw [← hw, ← prod_pow_weight u m]
  simp only [mul_pow, Finsupp.prod_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in

theorem continuous_evalCone (f : MvPolynomial (Coord n) ℤ) :
    Continuous fun z : Cone n ℂ ↦ evalCone z f := by
  have h : (fun z : Cone n ℂ ↦ evalCone z f) =
      fun z ↦ eval (fun v : Coord n ↦ z v.1 v.2) (map (Int.castRingHom ℂ) f) := by
    funext z
    rw [eval_map]
    rfl
  rw [h]
  exact (continuous_eval _).comp
    (continuous_pi fun v ↦ (continuous_apply v.2).comp (continuous_apply v.1))

omit [Fintype ι] [DecidableEq ι] in
theorem evalCone_X {F : Type*} [CommRing F] (z : Cone n F) (k : ι) (i : Fin (n k + 1)) :
    evalCone z (X ⟨k, i⟩) = z k i := by
  simp [evalCone]

omit [DecidableEq ι] in
theorem evalCone_chartMonomial' {F : Type*} [CommRing F] (z : Cone n F)
    (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by
  simp [evalCone, chartMonomial, eval₂_prod]

omit [DecidableEq ι] in
theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)} (d : ι → ℕ)
    (hc : ∀ k, z k (c k) ≠ 0) : evalCone z (chartMonomial c d) ≠ 0 := by
  rw [evalCone_chartMonomial']
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

theorem chartNorm_eq {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg) {z : Cone n ℂ}
    (hz : z ∈ P.points ℂ) {c c' : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ} {e e' : MvPolynomial (Coord n) ℤ}
    (he : IsChartForm P A.deg s.num s.den c d e) (he' : IsChartForm P A.deg s.num s.den c' d' e')
    (hc : ∀ k, z k (c k) ≠ 0) (hc' : ∀ k, z k (c' k) ≠ 0) :
    chartNorm A c d e z = chartNorm A c' d' e' z := by
  set m := chartMonomial c d
  set m' := chartMonomial c' d'
  have hmem : e * m' - e' * m ∈ P.ideal := by
    have h : s.den * (e * m' - e' * m) =
        (s.den * e - s.num * m) * m' - (s.den * e' - s.num * m') * m := by ring
    have h2 : s.den * (e * m' - e' * m) ∈ P.ideal := by
      rw [h]
      exact P.ideal.sub_mem (P.ideal.mul_mem_right _ he.2) (P.ideal.mul_mem_right _ he'.2)
    exact (P.isPrime.mem_or_mem h2).resolve_left s.den_not_mem
  have h0 : evalCone z (e * m' - e' * m) = 0 := hz.2 _ hmem
  simp only [evalCone, eval₂_sub, eval₂_mul, sub_eq_zero] at h0
  have hn : ‖evalCone z e‖ * ‖evalCone z m'‖ = ‖evalCone z e'‖ * ‖evalCone z m‖ := by
    rw [← norm_mul, ← norm_mul]
    exact congrArg norm h0
  have hh : 0 < A.metric z := A.metric_pos z hz.1
  have hm : ‖evalCone z m‖ ≠ 0 := norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d hc)
  have hm' : ‖evalCone z m'‖ ≠ 0 := norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d' hc')
  unfold chartNorm
  rw [div_eq_div_iff (mul_ne_zero hm hh.ne') (mul_ne_zero hm' hh.ne')]
  calc ‖evalCone z e‖ * (‖evalCone z m'‖ * A.metric z)
      = (‖evalCone z e‖ * ‖evalCone z m'‖) * A.metric z := by ring
    _ = (‖evalCone z e'‖ * ‖evalCone z m‖) * A.metric z := by rw [hn]
    _ = ‖evalCone z e'‖ * (‖evalCone z m‖ * A.metric z) := by ring

theorem chartNorm_scale (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    {e : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (he : IsWeightedHomogeneous (coordDeg n) e δ)
    (hδ : ∀ k, (δ k : ℤ) = A.deg k + d k) {u : ι → ℂ} (hu : ∀ k, u k ≠ 0) {z : Cone n ℂ}
    (hz : BlockNonzero z) :
    chartNorm A c d e (fun k i ↦ u k * z k i) = chartNorm A c d e z := by
  unfold chartNorm
  rw [evalCone_scale u z he, evalCone_scale u z (isWeightedHomogeneous_chartMonomial c d),
    A.metric_smul u z hu hz, norm_mul, norm_mul, norm_prod, norm_prod]
  simp only [norm_pow]
  have hQ : ∏ k, ‖u k‖ ^ δ k = (∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    have hk : ‖u k‖ ≠ 0 := norm_ne_zero_iff.mpr (hu k)
    rw [← zpow_natCast, ← zpow_natCast, hδ k, zpow_add₀ hk, mul_comm]
  have hD : (∏ k, ‖u k‖ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))
  have hH : (∏ k, ‖u k‖ ^ A.deg k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))
  rw [hQ]
  have h : (∏ k, ‖u k‖ ^ d k) * ‖evalCone z (chartMonomial c d)‖ *
      ((∏ k, ‖u k‖ ^ A.deg k) * A.metric z) =
      ((∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k) *
        (‖evalCone z (chartMonomial c d)‖ * A.metric z) := by ring
  rw [h, mul_div_mul_left _ _ (mul_ne_zero hD hH)]

def unitChart (c : (k : ι) → Fin (n k + 1)) : Set (Cone n ℂ) :=
  {z | (∀ k, z k (c k) = 1) ∧ ∀ k i, ‖z k i‖ ≤ 1}

omit [DecidableEq ι] in
theorem isCompact_unitChart (c : (k : ι) → Fin (n k + 1)) : IsCompact (unitChart c) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h : unitChart c = (⋂ k, {z : Cone n ℂ | z k (c k) = 1}) ∩
        ⋂ k, ⋂ i, {z : Cone n ℂ | ‖z k i‖ ≤ 1} := by
      ext z
      simp [unitChart]
    rw [h]
    refine (isClosed_iInter fun k ↦ ?_).inter (isClosed_iInter fun k ↦ isClosed_iInter fun i ↦ ?_)
    · exact isClosed_eq ((continuous_apply (c k)).comp (continuous_apply k)) continuous_const
    · exact isClosed_le ((continuous_apply i).comp (continuous_apply k)).norm continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Cone n ℂ)) (r := 1)).subset fun z hz ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    exact hz.2 k

omit [DecidableEq ι] in

theorem exists_bound_unitChart (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (e : MvPolynomial (Coord n) ℤ) : ∃ B : ℝ, ∀ z ∈ unitChart c, chartNorm A c d e z ≤ B := by
  have hnz : ∀ z ∈ unitChart c, BlockNonzero z := fun z hz k h0 ↦ by
    have := hz.1 k
    rw [h0] at this
    exact zero_ne_one this
  have hcont : ContinuousOn (chartNorm A c d e) (unitChart c) := by
    refine ContinuousOn.div (continuous_evalCone e).norm.continuousOn
      (((continuous_evalCone _).norm.continuousOn).mul
        (A.metric_smooth.continuousOn.mono fun z hz ↦ hnz z hz)) fun z hz ↦ ?_
    refine mul_ne_zero (norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d fun k ↦ ?_))
      (A.metric_pos z (hnz z hz)).ne'
    rw [hz.1 k]
    exact one_ne_zero
  obtain ⟨B, hB⟩ := (isCompact_unitChart c).exists_bound_of_continuousOn hcont
  exact ⟨B, fun z hz ↦ (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z hz))⟩

theorem exists_bound_chart {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg)
    (c : (k : ι) → Fin (n k + 1)) :
    ∃ B : ℝ, ∀ z ∈ P.points ℂ, (∀ k, z k (c k) ≠ 0) → (∀ k i, ‖z k i‖ ≤ ‖z k (c k)‖) →
      ∀ (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsChartForm P A.deg s.num s.den c d e →
        chartNorm A c d e z ≤ B := by
  by_cases hlive : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal
  · obtain ⟨d₀, e₀, he₀⟩ := s.regular c hlive
    obtain ⟨B, hB⟩ := exists_bound_unitChart A c d₀ e₀
    refine ⟨B, fun z hz hc hmax d e he ↦ ?_⟩
    obtain ⟨δ, hδe, hδ⟩ := he₀.1
    set u : ι → ℂ := fun k ↦ (z k (c k))⁻¹
    have hu : ∀ k, u k ≠ 0 := fun k ↦ inv_ne_zero (hc k)
    rw [chartNorm_eq s hz he he₀ hc hc, ← chartNorm_scale A c d₀ hδe hδ hu hz.1]
    refine hB _ ⟨fun k ↦ inv_mul_cancel₀ (hc k), fun k i ↦ ?_⟩
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr (hc k)), mul_one]
    exact hmax k i
  · refine ⟨0, fun z hz hc _ d e _ ↦ ?_⟩
    simp only [not_forall, not_not] at hlive
    obtain ⟨k, hk⟩ := hlive
    have h0 := hz.2 _ hk
    rw [evalCone_X] at h0
    exact absurd h0 (hc k)

theorem proof : BoundedMonomials.Statement := by
  intro ι _ _ n P A s
  refine ⟨fun z hz c c' d d' e e' he he' hc hc' ↦ chartNorm_eq s hz he he' hc hc', ?_⟩
  choose B hB using exists_bound_chart s
  refine ⟨Real.log (∑ c, |B c| + 1), fun z hz c d e he hc ↦ ?_⟩
  have hS : 0 < ∑ c, |B c| + 1 := by positivity
  rw [Real.exp_log hS]

  have hmax : ∀ k, ∃ i, ∀ j, ‖z k j‖ ≤ ‖z k i‖ := fun k ↦ by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j ↦ ‖z k j‖) Finset.univ_nonempty
    exact ⟨i, fun j ↦ hi j (Finset.mem_univ j)⟩
  choose c₀ hc₀ using hmax
  have hc₀z : ∀ k, z k (c₀ k) ≠ 0 := fun k h0 ↦ by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hz.1 k)
    have := hc₀ k j
    rw [h0, norm_zero] at this
    exact hj (norm_le_zero_iff.mp this)
  have hlive : ∀ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦ by
    have h0 := hz.2 _ hk
    rw [evalCone_X] at h0
    exact hc₀z k h0
  obtain ⟨d₀, e₀, he₀⟩ := s.regular c₀ hlive
  change chartNorm A c d e z ≤ _
  rw [chartNorm_eq s hz he he₀ hc hc₀z]
  calc chartNorm A c₀ d₀ e₀ z ≤ B c₀ := hB c₀ z hz hc₀z hc₀ d₀ e₀ he₀
    _ ≤ |B c₀| := le_abs_self _
    _ ≤ ∑ c, |B c| := Finset.single_le_sum (fun c _ ↦ abs_nonneg (B c)) (Finset.mem_univ c₀)
    _ ≤ ∑ c, |B c| + 1 := by linarith

end BoundedMonomials

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

theorem ChartCrossRatio.equiv :
    GroundTheory.Heights₂.Heights.ChartCrossRatio.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartCrossRatio.Statement := by
  constructor
  · intro h ι _ _ n P D G c c' j
    exact h ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem c c' j
  · intro h ι _ _ n P D d g hg c c' j
    exact h ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg) c c' j

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open AddBlockEq

theorem ConePointsConverse.equiv :
    GroundTheory.Heights₂.Heights.ConePointsConverse.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ConePointsConverse.Statement := by
  constructor
  · intro hA ι _ _ n P D G z hz c hc
    have h := hA ι n P (split_model_to_place_model D) G.d G.g G.isFormSystem z hz c hc
    rw [addBlockEquiv_symm_conePoints] at h
    have e : (D.join z fun j ↦ evalCone z (G.g c j)) = (split_model_to_place_model D).joinPt z fun j ↦ evalCone z (G.g c j) := by
      funext o
      cases o <;> rfl
    rw [e]
    exact h
  · intro hB ι _ _ n P D d g hg z hz c hc
    have h := hB ι n P (toIndefiniteRowSideFullHecke D) (ChartForms.ofFormSystem hg) z hz c hc
    rw [extPoints_eq, ← addBlockEquiv_join]
    exact h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end


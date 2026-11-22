import ReciprocityTheory.SemistableReduction.Bundle0003
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import Lemmata.IterateZero.IterZero
import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom

-- bundled from ReciprocityTheory.SemistableReduction.LemmaH
section
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix InnerProductSpace

theorem exists_unitary_mul_upper {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    ∃ k b : Matrix (Fin n) (Fin n) ℂ, k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ b.BlockTriangular id ∧
      x = k * b ∧ ∀ j, ‖b j j‖ ^ 2 ≤ colNormSq x j := by
  classical
  let std := EuclideanSpace.basisFun (Fin n) ℂ
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun j => (EuclideanSpace.equiv (Fin n) ℂ).symm (fun i => x i j)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis hdim f
  have hstd : std.toBasis.toMatrix f = x := by
    ext i j
    simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, f, std]
  have hnorm : ∀ j, ‖f j‖ ^ 2 = colNormSq x j := by
    intro j
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [colNormSq, f]
  refine ⟨std.toBasis.toMatrix e.toBasis, e.toBasis.toMatrix f, ?_, ?_, ?_, ?_⟩
  · simpa [OrthonormalBasis.coe_toBasis] using OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary std e
  · exact gramSchmidtOrthonormalBasis_inv_blockTriangular hdim f
  · rw [Module.Basis.toMatrix_mul_toMatrix, hstd]
  · intro j
    rw [← hnorm j, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    have h1 : ‖inner ℂ (e j) (f j)‖ ≤ ‖f j‖ := by
      calc ‖inner ℂ (e j) (f j)‖ ≤ ‖e j‖ * ‖f j‖ := norm_inner_le_norm _ _
        _ = ‖f j‖ := by rw [e.orthonormal.1 j, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

private theorem P_ite_mul_eq_prod_triChar_mul {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (a : ∀ s, Fin (p s) → ℕ) (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ)
    (hP : ∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x)
    (k b : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (hk : ∀ s, (k s).det ≠ 0)
    (hb : ∀ s, (b s).det ≠ 0) (hbt : ∀ s, (b s).BlockTriangular id) (S : Finset ι) :
    P (fun t => if t ∈ S then k t * b t else k t) =
      (∏ s ∈ S, triChar (a s) (b s)) * P k := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert s S hs ih =>
    have hy : ∀ t, ((fun t => if t ∈ S then k t * b t else k t) t).det ≠ 0 := by
      intro t
      by_cases ht : t ∈ S
      · simp only [ht, if_true, Matrix.det_mul]
        exact mul_ne_zero (hk t) (hb t)
      · simp only [ht, if_false]
        exact hk t
    have heq : (fun t => if t ∈ insert s S then k t * b t else k t) =
        Function.update (fun t => if t ∈ S then k t * b t else k t) s
          ((fun t => if t ∈ S then k t * b t else k t) s * b s) := by
      funext t
      by_cases hts : t = s
      · subst hts
        simp [hs]
      · simp [hts]
    rw [heq, hP _ s (b s) hy (hb s) (hbt s), ih, Finset.prod_insert hs, mul_assoc]

theorem lemmaH_holds : LemmaHStatement := by
  intro ι _ _ p a P C R hP hC hR x hx hcol
  classical
  choose k b hk hbt hkb hdiag using fun s => exists_unitary_mul_upper (x s)
  have hkdet : ∀ s, (k s).det ≠ 0 := by
    intro s
    exact (Matrix.UnitaryGroup.det_isUnit ⟨k s, hk s⟩).ne_zero
  have hbdet : ∀ s, (b s).det ≠ 0 := by
    intro s h
    apply hx s
    rw [hkb s, Matrix.det_mul, h, mul_zero]
  have hxk : x = fun t => if t ∈ (Finset.univ : Finset ι) then k t * b t else k t := by
    funext t
    simp [← hkb t]
  have hmain := P_ite_mul_eq_prod_triChar_mul p a P hP k b hkdet hbdet hbt Finset.univ
  rw [← hxk] at hmain
  have hC0 : 0 ≤ C := by
    have h1 := hC (fun s => 1) (fun s => one_mem _)
    exact (norm_nonneg _).trans h1
  have hbR : ∀ s i, ‖b s i i‖ ≤ R := by
    intro s i
    have h1 := (hdiag s i).trans (hcol s i)
    nlinarith [norm_nonneg (b s i i)]
  have hprod : ‖∏ s, triChar (a s) (b s)‖ ≤ R ^ (∑ s, ∑ i, a s i) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro s _
    rw [triChar, norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbR s i) _
  rw [hmain, norm_mul, mul_comm C]
  exact mul_le_mul hprod (hC k hk) (norm_nonneg _) (pow_nonneg hR _)

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.MeasurePreservingSphereMap
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric
open scoped Pointwise

def sphereMap {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
    (z : UnitSphereC n) : UnitSphereC n :=
  ⟨U z, by rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
           exact mem_sphere_zero_iff_norm.mp z.2⟩

theorem continuous_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    Continuous (sphereMap U) :=
  (U.continuous.comp continuous_subtype_val).subtype_mk _

theorem toSphere_map_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    Measure.map (sphereMap U) (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere =
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  have hmeas := (continuous_sphereMap U).measurable
  ext s hs
  rw [Measure.map_apply hmeas hs, Measure.toSphere_apply' _ (hmeas hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hset : (Set.Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap U ⁻¹' s) :
      Set (EuclideanSpace ℂ (Fin n)))) = U ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨r, hr, U z, ⟨sphereMap U z, hz, rfl⟩, (map_smul U r (z : EuclideanSpace ℂ (Fin n))).symm⟩
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hxy⟩
      refine ⟨r, hr, U.symm z, ⟨sphereMap U.symm z, ?_, rfl⟩, ?_⟩
      · have : sphereMap U (sphereMap U.symm z) = z := Subtype.ext (by simp [sphereMap])
        rw [this]; exact hz
      · rw [← map_smul, hxy]; simp
  rw [hset]
  have hU : MeasurePreserving (U.toHomeomorph.toMeasurableEquiv) volume volume :=
    U.measurePreserving
  exact hU.measure_preimage_equiv _

theorem measurePreserving_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (sphereMap U) (sphereProb n) (sphereProb n) := by
  refine ⟨(continuous_sphereMap U).measurable, ?_⟩
  unfold sphereProb ProbabilityTheory.cond
  rw [Measure.restrict_univ, Measure.map_smul, toSphere_map_sphereMap]

def rotCL {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (innerSL ℂ u).smulRight u + t • (ContinuousLinearMap.id ℂ _ - (innerSL ℂ u).smulRight u)

theorem rotCL_apply {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (t : ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    rotCL u t x = inner ℂ u x • u + t • (x - inner ℂ u x • u) := by
  simp [rotCL]

theorem norm_rotCL {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1)
    (x : EuclideanSpace ℂ (Fin n)) : ‖rotCL u t x‖ = ‖x‖ := by
  have huu : inner ℂ u u = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have horth : inner ℂ u (x - inner ℂ u x • u) = 0 := by
    rw [inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
  have h1 : inner ℂ (inner ℂ u x • u) (t • (x - inner ℂ u x • u)) = 0 := by
    rw [inner_smul_left, inner_smul_right, horth]; simp
  have h2 : inner ℂ (inner ℂ u x • u) (x - inner ℂ u x • u) = 0 := by
    rw [inner_smul_left, horth]; simp
  have hx : x = inner ℂ u x • u + (x - inner ℂ u x • u) := by abel
  have key : ‖rotCL u t x‖ * ‖rotCL u t x‖ = ‖x‖ * ‖x‖ := by
    rw [rotCL_apply, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h1,
      norm_smul t (x - inner ℂ u x • u), ht, one_mul]
    conv_rhs => rw [hx, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h2]
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp key

def rotIso {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := ((rotCL u t : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)
      norm_map' := norm_rotCL hu ht } rfl

def rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    UnitSphereC n → UnitSphereC n :=
  sphereMap (rotIso hu (t := circleMap 0 1 θ) (by simp [norm_circleMap_zero]))

theorem coe_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ)
    (z : UnitSphereC n) :
    (rotS hu θ z : EuclideanSpace ℂ (Fin n)) =
      inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u +
        circleMap 0 1 θ • ((z : EuclideanSpace ℂ (Fin n)) - inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u) :=
  rotCL_apply u _ _

theorem measurePreserving_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    MeasurePreserving (rotS hu θ) (sphereProb n) (sphereProb n) :=
  measurePreserving_sphereMap _

theorem continuous_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) :
    Continuous (fun p : ℝ × UnitSphereC n => rotS hu p.1 p.2) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_rotS]
  have hc : Continuous fun p : ℝ × UnitSphereC n => (p.2 : EuclideanSpace ℂ (Fin n)) :=
    continuous_subtype_val.comp continuous_snd
  have hθ : Continuous fun p : ℝ × UnitSphereC n => circleMap 0 1 p.1 :=
    (continuous_circleMap 0 1).comp continuous_fst
  have hi : Continuous fun p : ℝ × UnitSphereC n => inner ℂ u (p.2 : EuclideanSpace ℂ (Fin n)) :=
    continuous_const.inner hc
  exact (hi.smul continuous_const).add (hθ.smul (hc.sub (hi.smul continuous_const)))

theorem sphereProb_inner_eq_zero {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : u ≠ 0) :
    sphereProb n {z | inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0} = 0 := by
  set s : Set (UnitSphereC n) := {z | inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0}
  have hs : MeasurableSet s :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  let P : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.ker (((innerSL ℂ u : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ).restrictScalars ℝ)
  have hP : P ≠ ⊤ := by
    intro h
    have hmem : u ∈ P := h ▸ Submodule.mem_top
    simp only [P, LinearMap.mem_ker, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply] at hmem
    exact hu (inner_self_eq_zero.mp hmem)
  have hsub : Set.Ioo (0 : ℝ) 1 • ((↑) '' s : Set (EuclideanSpace ℂ (Fin n))) ⊆ (P : Set (EuclideanSpace ℂ (Fin n))) := by
    rintro _ ⟨r, -, y, ⟨z, hz, rfl⟩, rfl⟩
    show (((innerSL ℂ u : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ).restrictScalars ℝ) (r • (z : EuclideanSpace ℂ (Fin n))) = 0
    rw [map_smul]
    simp only [LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    rw [show inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0 from hz, smul_zero]
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere s = 0 := by
    rw [Measure.toSphere_apply' _ hs]
    rw [measure_mono_null hsub (Measure.addHaar_submodule _ P hP), mul_zero]
  simp [sphereProb, ProbabilityTheory.cond, h0]

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.OnePolyGrowth
section
namespace ReciprocityTheory.MultiplicativeHeights

open Filter Topology Function Metric Polynomial

theorem entire_poly_of_growth (k : ℕ) : ∀ (g : ℂ → ℂ) (A : ℝ), Differentiable ℂ g →
    (∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t, g t = P.eval t := by
  first | exact Bl.IterateZero.goal1 .. | (apply Bl.IterateZero.goal1 <;> assumption) | (intros; apply Bl.IterateZero.goal1 <;> assumption)

theorem exists_entire_of_finite_growth (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ) (hB : B.Finite)
    (hf : DifferentiableOn ℂ f Bᶜ) (hb : ∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ t ∉ B, g t = f t := by
  classical
  let g : ℂ → ℂ := fun t => if t ∈ B then limUnder (𝓝[≠] t) f else f t
  refine ⟨g, fun c => ?_, fun t ht => if_neg ht⟩
  by_cases hc : c ∈ B
  · have hU : IsOpen (B \ {c})ᶜ := (hB.sdiff).isClosed.isOpen_compl
    set s : Set ℂ := (B \ {c})ᶜ ∩ ball c 1 with hs
    have hsn : s ∈ 𝓝 c := inter_mem (hU.mem_nhds (fun h => h.2 rfl)) (ball_mem_nhds c one_pos)
    have hsub : s \ {c} ⊆ Bᶜ := by
      rintro t ⟨⟨h1, -⟩, h2⟩ htB
      exact h1 ⟨htB, h2⟩
    have hbdd : BddAbove (norm ∘ f '' (s \ {c})) := by
      refine ⟨|A| * (2 + ‖c‖) ^ k, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have htc : ‖t‖ ≤ ‖c‖ + 1 := by
        have h := ht.1.2
        rw [mem_ball, dist_eq_norm] at h
        have := norm_le_norm_add_norm_sub' t c
        linarith [norm_sub_rev t c]
      calc ‖f t‖ ≤ A * (1 + ‖t‖) ^ k := hb t (hsub ht)
        _ ≤ |A| * (1 + ‖t‖) ^ k := mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * (2 + ‖c‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k)
              (abs_nonneg A)
    have hdiff := Complex.differentiableOn_update_limUnder_of_bddAbove hsn
      (hf.mono hsub) hbdd
    refine (hdiff.differentiableAt hsn).congr_of_eventuallyEq ?_
    filter_upwards [hsn] with t ht
    by_cases htc : t = c
    · subst htc
      simp [g, hc]
    · have htB : t ∉ B := fun h => ht.1 ⟨h, htc⟩
      simp [g, htB, update_of_ne htc]
  · have hO : IsOpen Bᶜ := hB.isClosed.isOpen_compl
    refine (hf.differentiableAt (hO.mem_nhds hc)).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hc] with t ht
    exact if_neg ht

theorem onePolyGrowth_holds : OnePolyGrowthStatement := by
  intro f B A k hB hf hb
  obtain ⟨g, hg, hgf⟩ := exists_entire_of_finite_growth f B A k hB hf hb
  have hclosed : IsClosed {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} :=
    isClosed_le (continuous_norm.comp hg.continuous)
      (continuous_const.mul ((continuous_const.add continuous_norm).pow k))
  have hsub : Bᶜ ⊆ {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} := fun t ht => by
    simpa [hgf t ht] using hb t ht
  have hall : ∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k := by
    have hd : Dense Bᶜ := hB.countable.dense_compl ℂ
    intro t
    have : t ∈ closure Bᶜ := by rw [hd.closure_eq]; trivial
    exact closure_minimal hsub hclosed this
  obtain ⟨P, hPd, hP⟩ := entire_poly_of_growth k g A hg hall
  exact ⟨P, hPd, fun t ht => by rw [← hgf t ht, hP t]⟩

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.RankEqualityHolds
section
namespace ReciprocityTheory.MultiplicativeHeights

open scoped TensorProduct

theorem rank_equality_holds : RankStatement := by
  intro K L V _ _ _ _ _ _ W ι v hvW hspan
  have hU : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.mpr hne) inferInstance
    let g : L ⊗[K] V →ₗ[L] L := (Algebra.linearMap K L ∘ₗ f).liftBaseChange L
    have hv : ∀ i, f (v i) = 0 := by
      intro i
      have : f (v i) ∈ (Submodule.span K (Set.range v)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
      rw [hf] at this
      exact (Submodule.mem_bot K).mp this
    have hg : g = 0 := by
      have hle : Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[K] v i) ≤ LinearMap.ker g := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simp [g, hv i]
      rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hle
      exact hle
    apply hf0
    ext x
    have h1 : g ((1 : L) ⊗ₜ[K] x) = 0 := by rw [hg]; rfl
    have h2 : g ((1 : L) ⊗ₜ[K] x) = algebraMap K L (f x) := by
      simp [g]
    rw [h2] at h1
    simpa using (FaithfulSMul.algebraMap_injective K L) (h1.trans (map_zero _).symm)
  refine ⟨?_, hU⟩
  rw [eq_top_iff, ← hU, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact hvW i

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.TorsionNonvanish
section
namespace ReciprocityTheory.MultiplicativeHeights

open Metric
open scoped InnerProductSpace

theorem torsionNonvanish_holds (hS : BalancedSchwarzStatement) : TorsionNonvanishStatement := by
  intro V _ _ _ θ Λ ρ n hθ hne hper hcov hn

  set f : V → ℝ := fun z => ‖θ z‖ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) with hf
  have hfc : Continuous f := by
    have := hθ.continuous
    fun_prop
  have hρ : 0 ≤ ρ := by
    obtain ⟨l, -, hl⟩ := hcov 0
    exact (norm_nonneg _).trans hl

  obtain ⟨z₀, -, hz₀⟩ := (isCompact_closedBall (0 : V) ρ).exists_isMaxOn
    ⟨0, mem_closedBall_self hρ⟩ hfc.continuousOn
  have hmax : ∀ v, f v ≤ f z₀ := by
    intro v
    obtain ⟨l, hl, hvl⟩ := hcov v
    have h1 : f (v - l) ≤ f z₀ := hz₀ (by simpa [mem_closedBall, dist_zero_right] using hvl)
    have h2 : f v = f (v - l) := by
      have := hper l hl (v - l)
      simpa [hf] using this
    rw [h2]; exact h1
  set M := f z₀ with hM
  have hMpos : 0 < M := by
    obtain ⟨z, hz⟩ := hne
    have : 0 < f z := mul_pos (norm_pos_iff.mpr hz) (Real.exp_pos _)
    exact this.trans_le (hmax z)

  set h : V → ℂ := fun w => θ (z₀ + w) *
    Complex.exp (-(Real.pi : ℂ) * innerSL ℂ z₀ w - ((Real.pi / 2 * ‖z₀‖ ^ 2 : ℝ) : ℂ)) with hh
  have hdiff : Differentiable ℂ h := by
    have h1 : Differentiable ℂ fun w : V => θ (z₀ + w) :=
      hθ.comp (differentiable_const _ |>.add differentiable_id)
    have h2 : Differentiable ℂ fun w : V => innerSL ℂ z₀ w := (innerSL ℂ z₀).differentiable
    exact h1.mul ((h2.const_mul _ |>.sub_const _).cexp)
  have hnorm : ∀ w, ‖h w‖ = f (z₀ + w) * Real.exp (Real.pi / 2 * ‖w‖ ^ 2) := by
    intro w
    simp only [hh, hf, norm_mul, Complex.norm_exp]
    rw [norm_add_sq (𝕜 := ℂ), mul_assoc, ← Real.exp_add]
    congr 1
    rw [Complex.sub_re, Complex.ofReal_re]
    simp [innerSL_apply_apply]
    ring

  have hexp : ∀ w : V, ‖w‖ < 3 / 5 → Real.exp (Real.pi / 2 * ‖w‖ ^ 2) ≤ 2 := by
    intro w hw
    have hw2 : ‖w‖ ^ 2 ≤ (3 / 5) ^ 2 := by
      have := norm_nonneg w
      nlinarith
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have hlog := Real.log_two_gt_d9
    have : Real.pi / 2 * ‖w‖ ^ 2 < Real.log 2 := by nlinarith
    calc Real.exp (Real.pi / 2 * ‖w‖ ^ 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr this.le
      _ = 2 := Real.exp_log (by norm_num)
  have hbd : ∀ w ∈ ball (0 : V) (3 / 5), ‖h w‖ ≤ 2 * M := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    rw [hnorm w]
    calc f (z₀ + w) * Real.exp (Real.pi / 2 * ‖w‖ ^ 2) ≤ M * 2 :=
          mul_le_mul (hmax _) (hexp w hw) (Real.exp_pos _).le hMpos.le
      _ = 2 * M := by ring
  have h0 : ‖h 0‖ = M := by rw [hnorm 0]; simp [hM]
  have hsch := hS V (ball (0 : V) (3 / 5)) h (2 * M) isOpen_ball balanced_ball_zero
    hdiff.differentiableOn hbd

  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨l, hl, hzl⟩ := hcov ((n : ℂ) • z₀)
  refine ⟨l, hl, ?_⟩
  set w : V := (n : ℂ)⁻¹ • l - z₀ with hw
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hwn : ‖w‖ ≤ ρ / n := by
    have : w = (n : ℂ)⁻¹ • (l - (n : ℂ) • z₀) := by
      rw [hw, smul_sub, smul_smul, inv_mul_cancel₀ hnC, one_smul]
    rw [this, norm_smul, norm_inv, Complex.norm_natCast, norm_sub_rev, le_div_iff₀ hnpos]
    rw [inv_mul_eq_div, div_mul_cancel₀ _ hnpos.ne']
    exact hzl
  have hw5 : ‖w‖ < 1 / 5 := by
    refine hwn.trans_lt ?_
    rw [div_lt_iff₀ hnpos]; linarith
  have hwb : w ∈ ball (0 : V) (3 / 5) := by
    rw [mem_ball, dist_zero_right]; linarith
  have key := hsch w hwb
  rw [gauge_ball (by norm_num : (0 : ℝ) ≤ 3 / 5), h0] at key
  have hhw : h w ≠ 0 := by
    intro hz
    rw [hz, zero_sub, norm_neg, h0] at key
    have : (2 * M + M) * (‖w‖ / (3 / 5)) < M := by
      have : (2 * M + M) * (‖w‖ / (3 / 5)) = M * (5 * ‖w‖) := by ring
      rw [this]
      have : 5 * ‖w‖ < 1 := by linarith
      nlinarith
    linarith
  have hzw : z₀ + w = (n : ℂ)⁻¹ • l := by rw [hw]; abel
  have := left_ne_zero_of_mul hhw
  rwa [hzw] at this

end ReciprocityTheory.MultiplicativeHeights
end


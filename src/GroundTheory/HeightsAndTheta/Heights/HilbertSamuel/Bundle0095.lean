import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0091

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphFibreRatio
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGraphFibreRatio

set_option linter.unusedSectionVars false

section Cone

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_mConeMap {Ω : Type} [Field Ω] (v : (Σ k, ι k) → Ω) (s : K → Ω) (f : MRing ι) :
    eval s (mConeMap v f) = aeval (fun p => s p.1 * v p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, map_mul, hf]
    simp [mConeMap, mul_comm]

theorem aeval_smul_of_isMultiHomog {Ω : Type} [Field Ω] (v : (Σ k, ι k) → Ω) (s : K → Ω) {f : MRing ι}
    {d : K → ℕ} (hf : IsMultiHomog f d) :
    aeval (fun p => s p.1 * v p) f = (∏ k, s k ^ d k) * aeval v f := by
  rw [← eval_mConeMap, ProjLine.mConeMap_eq_of_isMultiHomog v hf, map_mul, eval_C, map_prod]
  simp only [map_pow, eval_X]
  ring

theorem aeval_eq_zero_of_mem {Ω : Type} [Field Ω] {v : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal v) : aeval v f = 0 := by
  have h := eval_mConeMap v (fun _ => 1) f
  rw [show mConeMap v f = 0 from hf] at h
  simpa using h.symm

theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (blockDeg k 1) := by
  classical
  intro m hm k'
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k' = k
  · subst hk
    have hs : ∀ b, (Finsupp.single (⟨k', i⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k', b⟩ = if b = i then 1 else 0 := by
      intro b
      by_cases hb : b = i
      · subst hb
        simp
      · rw [if_neg hb, Finsupp.single_apply, if_neg]
        intro h
        exact hb (eq_of_heq (Sigma.mk.inj h).2).symm
    simp [blockDeg, hs]
  · simp [blockDeg, hk, Sigma.ext_iff]

end Cone

section Graph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem graphMap_rename_inlV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (f : MRing ι) :
    graphMap P g (rename (inlV (ι₂ := ι₂)) f) = C (Ideal.Quotient.mk P f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap]
  | add f f' hf hf' => rw [map_add, map_add, hf, hf', map_add, map_add]
  | mul_X f p hf =>
    rw [map_mul, map_mul, hf, rename_X, map_mul, map_mul]
    congr 1
    rw [graphMap, eval₂Hom_X']
    rfl

theorem mem_iff_aeval_inl {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}
    (G : GenFibre (inrV (ι := ι) (ι₂ := ι₂)) (graphIdeal P g)) (f : MRing ι) :
    f ∈ P ↔ aeval (fun p => G.x' (inlV p)) f = 0 := by
  have h : aeval (fun p => G.x' (inlV p)) f = aeval G.x' (rename inlV f) := by
    rw [aeval_rename]
    rfl
  rw [h, ← RingHom.mem_ker, G.genericFibre_ker_target, graphIdeal, RingHom.mem_ker, graphMap_rename_inlV, C_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem]

end Graph

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]

theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (i : ι k₀) :
    X ⟨k₀, i⟩ - ∑ j, C (N i j) * blockForms k₀ M j ∈ mCoordIdeal y := by
  have hf : ∀ j, mConeMap y (blockForms k₀ M j) = MvPolynomial.C (x j) * MvPolynomial.X k₀ := by
    intro j
    rw [h.1 j, map_sum, Finset.sum_mul]
    simp [blockForms, mConeMap, map_sum, mul_assoc]
  have hX : mConeMap y (X ⟨k₀, i⟩) = MvPolynomial.C (y ⟨k₀, i⟩) * MvPolynomial.X k₀ := by
    simp [mConeMap]
  rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_sum]
  simp only [map_mul, hf]
  rw [hX, h.2 i, map_sum, Finset.sum_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mConeMap, mul_assoc]

def nForm (k₀ : K) (N : Matrix (ι k₀) (Ix κ) ℤ) (l : ι k₀) : MRing (Sum.elim ι (GlobalTheory κ)) :=
  ∑ q : Ix κ, C (N l q) * X (inrV q)

theorem graphMap_nForm {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (l : ι k₀) :
    graphMap (mCoordIdeal y) (blockForms k₀ M) (nForm k₀ N l) =
      C (Ideal.Quotient.mk (mCoordIdeal y) (X ⟨k₀, l⟩)) * X () := by
  rw [Ideal.Quotient.eq.2 (sub_mem_mCoordIdeal h l), nForm, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨⟩, j⟩ := q
  rw [map_mul, graphMap, eval₂Hom_C, eval₂Hom_X']
  change (Int.castRingHom _) (N l ⟨(), j⟩) * (C (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨(), j⟩)) * X ()) = _
  simp [mul_assoc]

end Block

end BlockGraphFibreRatio

open BlockGraphFibreRatio in

theorem BlockGraphFibreRatio.proof : BlockGraphFibreRatio.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hy hB hI G k i j hj
  classical
  set z : (Σ k, ι k) → G.Φ' := fun p => G.x' (inlV p) with hzdef
  have hmem := mem_iff_aeval_inl G
  rw [← hzdef] at hmem
  change z ⟨k, j⟩ ≠ 0 at hj
  change z ⟨k, i⟩ / z ⟨k, j⟩ ∈ _

  have hyj : aeval y (X ⟨k, j⟩ : MRing ι) ≠ 0 := by
    intro h0
    refine hj ?_
    have h1 : (X ⟨k, j⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y _ = 0
      rw [ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_X k j), h0, map_zero, zero_mul]
    simpa using (hmem _).1 h1

  obtain ⟨n, g', h', hg', hh', hh0, hgh⟩ :=
    hB (blockDeg k 1) (X ⟨k, i⟩) (X ⟨k, j⟩) (isMultiHomog_X k i) (isMultiHomog_X k j) hyj
  have hF : (X ⟨k, i⟩ * h' - g' * X ⟨k, j⟩ : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y _ = 0
    rw [map_sub, map_mul, map_mul, ProjLine.mConeMap_eq_of_isMultiHomog y hh',
      ProjLine.mConeMap_eq_of_isMultiHomog y hg', ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_X k i),
      ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_X k j)]
    calc _ = C (aeval y (X ⟨k, i⟩ : MRing ι) * aeval y h' - aeval y g' * aeval y (X ⟨k, j⟩ : MRing ι)) *
          ((∏ k', X k' ^ blockDeg k 1 k') * ∏ k', X k' ^ blockDeg k₀ n k') := by
          rw [map_sub, map_mul, map_mul]
          ring
      _ = 0 := by rw [hgh, sub_self, map_zero, zero_mul]
  have hz := (hmem _).1 hF
  simp only [map_sub, map_mul, aeval_X] at hz
  have hh'z : aeval z h' ≠ 0 := fun h0 => hh0 (aeval_eq_zero_of_mem ((hmem h').2 h0))
  have hratio : z ⟨k, i⟩ / z ⟨k, j⟩ = aeval z g' / aeval z h' := by
    rw [div_eq_div_iff hj hh'z]
    linear_combination hz

  obtain ⟨l, hl⟩ := hy.2.1.2.2 k₀
  have hzl : z ⟨k₀, l⟩ ≠ 0 := fun h0 => hl ((hmem _).2 (by simpa using h0))
  have hw : ∀ a, aeval G.x' (nForm k₀ N a) = algebraMap G.Φ G.Φ' (∑ q, (N a q : G.Φ) * G.x q) := by
    intro a
    simp [nForm, G.compat]
  have hker : ∀ f, aeval G.x' f = 0 ↔ graphMap (mCoordIdeal y) (blockForms k₀ M) f = 0 := by
    intro f
    rw [← RingHom.mem_ker, G.genericFibre_ker_target, graphIdeal, RingHom.mem_ker]
  have hwl : aeval G.x' (nForm k₀ N l) ≠ 0 := by
    intro h0
    rw [hker, graphMap_nForm hI] at h0
    have h1 := congrArg (MvPolynomial.coeff (Finsupp.single () 1)) h0
    rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one, coeff_zero, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hl h1
  have hcross : ∀ a, aeval G.x' (nForm k₀ N a) * z ⟨k₀, l⟩ = z ⟨k₀, a⟩ * aeval G.x' (nForm k₀ N l) := by
    intro a
    have hX : ∀ p : Σ k, ι k, graphMap (mCoordIdeal y) (blockForms k₀ M) (X (inlV p)) =
        C (Ideal.Quotient.mk (mCoordIdeal y) (X p)) := fun p => by
      rw [← rename_X, graphMap_rename_inlV]
    have h0 := (hker (nForm k₀ N a * X (inlV ⟨k₀, l⟩) - X (inlV ⟨k₀, a⟩) * nForm k₀ N l)).2 (by
      rw [map_sub, map_mul, map_mul, graphMap_nForm hI, graphMap_nForm hI, hX, hX]
      ring)
    rw [map_sub, map_mul, map_mul, aeval_X, aeval_X, sub_eq_zero] at h0
    exact h0
  set c := aeval G.x' (nForm k₀ N l) / z ⟨k₀, l⟩ with hcdef
  have hc : c ≠ 0 := div_ne_zero hwl hzl
  have hwc : ∀ a, aeval G.x' (nForm k₀ N a) = c * z ⟨k₀, a⟩ := by
    intro a
    rw [hcdef, div_mul_eq_mul_div, eq_div_iff hzl, hcross a, mul_comm]

  let s : K → G.Φ' := fun k' => if k' = k₀ then c else 0
  have hs : ∀ f : MRing ι, IsMultiHomog f (blockDeg k₀ n) →
      aeval (fun p => s p.1 * z p) f = c ^ n * aeval z f := by
    intro f hf
    rw [aeval_smul_of_isMultiHomog z s hf, Finset.prod_eq_single k₀]
    · simp [s, blockDeg]
    · intro b _ hb
      simp [s, blockDeg, hb]
    · simp
  have hex : ∀ p : Σ k, ι k, ∃ a : G.Φ, algebraMap G.Φ G.Φ' a = s p.1 * z p := by
    rintro ⟨k', a⟩
    by_cases hk : k' = k₀
    · subst hk
      exact ⟨_, ((hw a).symm.trans (hwc a)).trans (by simp [s])⟩
    · exact ⟨0, by simp [s, hk]⟩
  choose u hu using hex
  have hmap : ∀ f : MRing ι, aeval (fun p => s p.1 * z p) f = algebraMap G.Φ G.Φ' (aeval u f) := by
    intro f
    have hfun : (fun p => s p.1 * z p) = algebraMap G.Φ G.Φ' ∘ u := funext fun p => (hu p).symm
    rw [hfun, aeval_algebraMap_apply]
  refine RingHom.mem_range.2 ⟨aeval u g' / aeval u h', ?_⟩
  rw [map_div₀, ← hmap, ← hmap, hs g' hg', hs h' hh', hratio, mul_div_mul_left _ _ (pow_ne_zero n hc)]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockMeasureChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory Matrix
  SupBoundCount

noncomputable section

namespace BlockMeasureChange

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem sup_one_le (hS : SupBoundBlock.Statement) (d : HSMBlockDatum D K ι Ω) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2)) * blockL2Norm d n F := by
  obtain ⟨C, hC⟩ := hS D K ι Ω d
  refine ⟨max C 1, le_max_right _ _, fun n hn F hF z hz => (hC n hn F hF z hz).trans ?_⟩
  have h0 : 0 ≤ blockL2Norm d n F := Real.sqrt_nonneg _
  have h1 : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) h1) h0

theorem integral_le_of_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ}
    {c : ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgc : ∀ x, g x ≤ c) : ∫ x, g x ∂μ ≤ c := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := c)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hg0 x)]; exact hgc x)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

theorem quad_nonneg (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    0 ≤ a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) := by
  rw [gram_quad d n f hf a]
  have hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n) := fun w t =>
    div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)
  have := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n)) fun x => hp _ _
  have := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n))
    fun x => hp _ _
  positivity

theorem quad_le (d d' : HSMBlockDatum D K ι Ω) (hy : d'.y = d.y) (hk : d'.k₀ = d.k₀) (hA : d'.A = d.A) (n : ℕ)
    {r : ℕ} (f : Fin r → MRing ι) (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F) (a : Fin r → ℝ) :
    a ⬝ᵥ (blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) ≤
      c ^ 2 * (a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)) := by
  have hf' : ∀ k, IsMultiHomog (f k) (blockDeg d'.k₀ n) := fun k => by rw [hk]; exact hf k
  have := d'.vol.1
  have hQ := quad_nonneg d n f hf a
  set Q := a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)
  have hpt : ∀ z ∈ mcPts (mCoordIdeal d.y), ‖comb f a z‖ ^ 2 / d.A.h z ^ (2 * n) ≤ c ^ 2 * Q := by
    intro z hz
    have h1 := sup_real d n f hf hc hsup a hz
    have h0 : 0 ≤ ‖comb f a z‖ / d.A.h z ^ n :=
      div_nonneg (norm_nonneg _) (pow_pos (d.A.pos z hz.1) n).le
    have h2 := pow_le_pow_left₀ h0 h1 2
    rwa [div_pow, ← pow_mul', mul_pow, Real.sq_sqrt hQ] at h2
  have hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n) := fun w t =>
    div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)
  have hmem : ∀ x, blockPt d' x ∈ mcPts (mCoordIdeal d.y) := fun x => hy ▸ blockPt_mem d' x
  rw [gram_quad d' n f hf' a, hA]
  have i1 := integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (hmem x)
  have i2 := integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (conjPt_mem_mcPts (hmem x))
  linarith

theorem det_le {r : ℕ} {G G' : Matrix (Fin r) (Fin r) ℝ} (hG : G.IsHermitian) (hG' : G'.PosSemidef) {c : ℝ}
    (h : ∀ a, a ⬝ᵥ (G' *ᵥ a) ≤ c * (a ⬝ᵥ (G *ᵥ a))) : G'.det ≤ c ^ r * G.det := by
  have hH : (c • G - G').IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    have e1 := hG.apply i j
    have e2 := hG'.1.apply i j
    simp only [star_trivial] at e1 e2 ⊢
    simp only [Matrix.sub_apply, Matrix.smul_apply, e1, e2]
  have hpsd : (c • G - G').PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun a => ?_
    rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith [h a]
  have := GroundTheory.Heights₂.Heights.MCDet.re_det_mono hG' (by simpa using hpsd)
  simpa [det_smul] using this

end BlockMeasureChange

open BlockMeasureChange in

theorem BlockMeasureChange.proof (hS : SupBoundBlock.Statement) : BlockMeasureChange.Statement := by
  intro D K _ _ ι _ Ω _ _ d d' hy hk hA
  obtain ⟨C, hC, hsup⟩ := sup_one_le hS d
  obtain ⟨C', hC', hsup'⟩ := sup_one_le hS d'
  set L := max C C' with hL
  have hL1 : 1 ≤ L := hC.trans (le_max_left _ _)

  have key : ∀ n : ℕ, 1 ≤ n → |blockChi d' n - blockChi d n| ≤
      (2 * L ^ 2 * (Real.log L + D)) * ((n : ℝ) ^ D * (1 + Real.log n)) := by
    intro n hn
    have hex := exists_isSecBasisM d.y d.k₀ n
    have hb := hex.choose_spec
    choose f hf hfe using hb.1
    have hbf : hex.choose.2 = fun j => map (Int.castRingHom ℚ) (f j) := funext hfe
    have hf' : ∀ k, IsMultiHomog (f k) (blockDeg d'.k₀ n) := fun k => by rw [hk]; exact hf k
    have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
      have := hb.2.1
      simp only [hbf, aeval_map_int] at this
      exact this
    have hli' : LinearIndependent ℤ fun k => aeval d'.y (f k) := by rw [hy]; exact hli
    have hsame : ∀ (y' : (Σ k, ι k) → Ω) (k' : K), y' = d.y → k' = d.k₀ →
        ∀ h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM y' k' n p.2,
          h.choose = hex.choose := by
      rintro _ _ rfl rfl h; rfl
    have hex' : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d'.y d'.k₀ n p.2 := by
      rw [hy, hk]; exact hex
    have e1 : blockChi d n = -(1 / 2) *
        Real.log (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))).det := by
      rw [blockChi, dif_pos hex, hbf]
    have e2 : blockChi d' n = -(1 / 2) *
        Real.log (blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))).det := by
      rw [blockChi, dif_pos hex', hsame _ _ hy hk hex', hbf]
    set G := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))
    set G' := blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set s := (n : ℝ) ^ ((D : ℝ) / 2) with hs
    have hs1 : 1 ≤ s := Real.one_le_rpow hnR (by positivity)
    have hs2 : s ^ 2 = (n : ℝ) ^ D := by
      rw [hs, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1
      ring
    have hlogs : Real.log s = (D / 2) * Real.log n := by
      rw [hs, Real.log_rpow (by positivity)]
    set c := C * s
    set c' := C' * s
    have hc : 1 ≤ c := one_le_mul_of_one_le_of_one_le hC hs1
    have hc' : 1 ≤ c' := one_le_mul_of_one_le_of_one_le hC' hs1
    have hG : G.PosDef := gram_posDef d n f hf hli (by linarith) (hsup n hn)
    have hG' : G'.PosDef := gram_posDef d' n f hf' hli' (by linarith) (hsup' n hn)
    have q1 := quad_le d d' hy hk hA n f hf (by linarith) (hsup n hn)
    have q2 := quad_le d' d hy.symm hk.symm hA.symm n f hf' (by linarith) (hsup' n hn)
    have d1 := det_le hG.isHermitian hG'.posSemidef q1
    have d2 := det_le hG'.isHermitian hG.posSemidef q2
    have hr := SupBoundCount.rank_le d n f hf hli (by linarith) (hsup n hn)
    have p1 := hG.det_pos
    have p2 := hG'.det_pos
    have l1 : Real.log G'.det ≤ hex.choose.1 * Real.log (c ^ 2) + Real.log G.det := by
      rw [← Real.log_pow, ← Real.log_mul (by positivity) p1.ne']
      exact Real.log_le_log p2 d1
    have l2 : Real.log G.det ≤ hex.choose.1 * Real.log (c' ^ 2) + Real.log G'.det := by
      rw [← Real.log_pow, ← Real.log_mul (by positivity) p2.ne']
      exact Real.log_le_log p1 d2
    have lc : Real.log c ≤ Real.log L + D * Real.log n := by
      have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
      rw [Real.log_mul (by linarith) (by linarith), hlogs]
      have := Real.log_le_log (by linarith) (le_max_left C C')
      nlinarith
    have lc' : Real.log c' ≤ Real.log L + D * Real.log n := by
      have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
      rw [Real.log_mul (by linarith) (by linarith), hlogs]
      have := Real.log_le_log (by linarith) (le_max_right C C')
      nlinarith
    have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
    have hlc' : 0 ≤ Real.log c' := Real.log_nonneg hc'
    have hr0 : (0 : ℝ) ≤ (hex.choose.1 : ℝ) := Nat.cast_nonneg _
    have hrb : (hex.choose.1 : ℝ) ≤ 2 * L ^ 2 * (n : ℝ) ^ D := by
      have : c ^ 2 ≤ L ^ 2 * (n : ℝ) ^ D := by
        rw [mul_pow, hs2]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (le_max_left _ _) 2) (by positivity)
      linarith
    rw [Real.log_pow] at l1 l2
    push_cast at l1 l2
    have hdiff : |blockChi d' n - blockChi d n| ≤ hex.choose.1 * (Real.log L + D * Real.log n) := by
      have m1 := mul_le_mul_of_nonneg_left lc hr0
      have m2 := mul_le_mul_of_nonneg_left lc' hr0
      rw [e1, e2, abs_le]
      constructor <;> linarith
    have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hlL : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hnD : 0 ≤ (n : ℝ) ^ D := by positivity
    refine hdiff.trans ?_
    calc (hex.choose.1 : ℝ) * (Real.log L + D * Real.log n)
        ≤ (2 * L ^ 2 * (n : ℝ) ^ D) * (Real.log L + D * Real.log n) :=
          mul_le_mul_of_nonneg_right hrb (by positivity)
      _ ≤ (2 * L ^ 2 * (Real.log L + D)) * ((n : ℝ) ^ D * (1 + Real.log n)) := by
          have : Real.log L + D * Real.log n ≤ (Real.log L + D) * (1 + Real.log n) := by
            have h3 : 0 ≤ Real.log L * Real.log n := mul_nonneg hlL hln
            have h4 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
            have e : (Real.log L + D) * (1 + Real.log n) =
                Real.log L + D * Real.log n + (D + Real.log L * Real.log n) := by ring
            rw [e]
            linarith
          calc (2 * L ^ 2 * (n : ℝ) ^ D) * (Real.log L + D * Real.log n)
              ≤ (2 * L ^ 2 * (n : ℝ) ^ D) * ((Real.log L + D) * (1 + Real.log n)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring

  have hO : (fun n : ℕ => blockChi d' n - blockChi d n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n) := by
    refine IsBigO.of_bound (2 * L ^ 2 * (Real.log L + D)) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (key n hn).trans (le_of_eq ?_)
    congr 1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (mul_nonneg (by positivity) (by linarith [Real.log_nonneg hnR]))]
  have hlog : (fun n : ℕ => 1 + Real.log n) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have h1 := (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
    have h2 := Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
    exact h1.add h2
  have ho : (fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n)) =o[atTop] pw D := by
    have := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO hlog
    refine this.congr_right fun n => ?_
    simp [pw, pow_succ]
  exact hO.trans_isLittleO ho

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullRatiosAlgebraic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem PullRatiosAlgebraic.proof (h₁ : PullConeNull.Statement) (h₂ : PullConeDegree.Statement)
    (h₃ : PullGradedAlgebraic.Statement) : PullRatiosAlgebraic.Statement := by
  intro K _ ι _ Ω _ _ y D e L hy he hL hz
  obtain ⟨N, hN⟩ := h₁ K ι Ω y D L hz
  exact h₃ K ι Ω y D e L (fun k => e k + N * Fintype.card (ι k)) hy he hL
    (fun d g hg hd => h₂ K ι Ω y D e L N hy hL hN d g hg hd)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionFormsIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockResolutionFormsIndependent.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n r : ℕ) (b : Fin r → MvPolynomial (Σ k, ι k) ℚ),
    IsSecBasisM d.y d.k₀ n b → ∀ a : Fin r → ℂ,
    (∀ y : d.R.X, ∑ k, a k * eval (blockPt d y) (map (algebraMap ℚ ℂ) (b k)) = 0) → a = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatioFieldDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RatioFieldDeg.Statement : Prop :=
  ∀ (ι : Type) (E₁ E₂ : Type) [Field E₁] [CharZero E₁] [Field E₂] [CharZero E₂] (u : ι → E₁) (v : ι → E₂)
    (D : ℕ) (e : Fin (D + 1) → ι), coordIdeal ℤ u = coordIdeal ℤ v → projDeg u e = projDeg v e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end


import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import ReciprocityTheory.SemistableReduction.Bundle0007
import ReciprocityTheory.SemistableReduction.Bundle0008
import Lemmata.GeneralBFactBisAlt.Imports
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0011

-- bundled from ReciprocityTheory.SemistableReduction.CauchyInequalityOnTorus
section
namespace ReciprocityTheory.MultiplicativeHeights

theorem cauchy_inequality_on_torus : CauchyTorusStatement := by
  intro K _ _ _ K₀ hK₀ n c hc hτ χ
  by_contra hχ
  push_neg at hχ
  have hev : ∀ᶠ ψ in Filter.cofinite, ‖c ψ‖ < 1 / 2 := hc.eventually (gt_mem_nhds (by norm_num))
  have hFfin : {ψ | ¬ ‖c ψ‖ < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  set F := hFfin.toFinset with hFdef
  have hχF : χ ∈ F := by
    rw [Set.Finite.mem_toFinset]
    show ¬ ‖c χ‖ < 1 / 2
    linarith
  obtain ⟨χm, hχmF, hmax⟩ := F.exists_max_image (fun ψ => ‖c ψ‖) ⟨χ, hχF⟩
  have hgt : 1 < ‖c χm‖ := lt_of_lt_of_le hχ (hmax χ hχF)
  have hglob : ∀ ψ, ‖c ψ‖ ≤ ‖c χm‖ := by
    intro ψ
    by_cases hψ : ψ ∈ F
    · exact hmax ψ hψ
    · have h2 : ‖c ψ‖ < 1 / 2 := by
        rw [Set.Finite.mem_toFinset] at hψ
        simpa using hψ
      linarith
  set lam := c χm with hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgt
    linarith
  set a : (Fin n → ℤ) → K := fun ψ => c ψ / lam with hadef
  have ha : ∀ ψ, ‖a ψ‖ ≤ 1 := by
    intro ψ
    simp only [hadef, norm_div]
    exact (div_le_one (norm_pos_iff.2 hlam0)).2 (hglob ψ)
  have ha0 : ‖a χm‖ = 1 := by
    simp only [hadef, norm_div]
    exact div_self (norm_ne_zero_iff.2 hlam0)
  obtain ⟨τ, hτu, hτ1⟩ := exists_torus_point_one_le_norm_sum K₀ hK₀ F a ha χm hχmF ha0
  have hprodnorm : ∀ ψ : Fin n → ℤ, ‖∏ i, τ i ^ ψ i‖ = 1 := by
    intro ψ
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [norm_zpow, (hτu i).2, one_zpow]
  have hSF : ∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i = lam * ∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [hadef]
    field_simp
  have hSFn : ‖lam‖ ≤ ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ := by
    rw [hSF, norm_mul]
    calc ‖lam‖ = ‖lam‖ * 1 := (mul_one _).symm
      _ ≤ ‖lam‖ * ‖∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i‖ := mul_le_mul_of_nonneg_left hτ1 (norm_nonneg _)
  have hsum : Summable (fun ψ => c ψ * ∏ i, τ i ^ ψ i) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_mul, hprodnorm] using hc
  have hsplit := hsum.sum_add_tsum_compl (s := F)
  have htail : ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ ≤ 1 / 2 := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun ψ => ?_
    rw [norm_mul, hprodnorm, mul_one]
    have hψ : (ψ : Fin n → ℤ) ∉ F := fun h => ψ.2 (Finset.mem_coe.2 h)
    rw [Set.Finite.mem_toFinset] at hψ
    simp only [Set.mem_setOf_eq, not_not] at hψ
    exact le_of_lt hψ
  have hne : ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ ≠
      ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ := by
    intro h
    linarith
  have htot := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [hsplit] at htot
  have h1 := hτ τ hτu
  unfold torusSum at h1
  rw [htot] at h1
  have h3 := le_max_left ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖
    ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖
  linarith

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.EmbMatMulVecInjective
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DegAdd

open Matrix NumberField
open scoped ComplexOrder

def embMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (v : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a j => σ (v j a)

theorem gramC_eq_mul {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (v : Fin k → Fin r → K) :
    gramC H σ v = (embMat σ v)ᴴ * H * embMat σ v := by
  ext i j
  simp only [gramC, embMat, embVec, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

theorem embMat_mulVec_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    {v : Fin k → Fin r → K} (hv : LinearIndependent K v) :
    Function.Injective (embMat σ v).mulVec := by
  set B : Matrix (Fin r) (Fin k) K := Matrix.of fun a j => v j a
  have hcol : B.col = v := by
    funext j a
    rfl
  have hB : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hv
  have hker : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact hB (by simpa [Matrix.toLin'_apply] using h)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) hker
  have hNB : LinearMap.toMatrix' g * B = 1 := by
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hE : embMat σ v = B.map σ := rfl
  have h1 : (LinearMap.toMatrix' g).map σ * embMat σ v = 1 := by
    rw [hE, ← Matrix.map_mul, hNB, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have h := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, h1] using h

theorem gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) {v : Fin k → Fin r → K} (hH : H.PosDef)
    (hv : LinearIndependent K v) : (gramC H σ v).PosDef := by
  rw [gramC_eq_mul]
  exact hH.conjTranspose_mul_mul_same (embMat_mulVec_injective σ hv)

theorem gramC_append_blocks {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) :
    (gramC H σ (Fin.append b c)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (gramC H σ b) (gramX H σ b c) (gramX H σ c b) (gramC H σ c) := by
  ext (i | i) (j | j) <;> simp [gramC, gramX]

theorem log_det_gram_append {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) (hH : H.PosDef) (hb : LinearIndependent K b)
    (h : LinearIndependent K (Fin.append b c)) :
    Real.log (gramC H σ (Fin.append b c)).det.re =
      Real.log (gramC H σ b).det.re + Real.log (quotGramC H σ b c).det.re := by
  have hG := (gramC_posDef H σ hH h).det_pos
  have hGb := (gramC_posDef H σ hH hb).det_pos
  have : Invertible (gramC H σ b) := (gramC_posDef H σ hH hb).isUnit.invertible
  have hdet : (gramC H σ (Fin.append b c)).det =
      (gramC H σ b).det * (quotGramC H σ b c).det := by
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv (gramC H σ (Fin.append b c)),
      gramC_append_blocks, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    rfl
  rw [hdet] at hG ⊢
  rw [Complex.pos_iff] at hG hGb
  have hre : ((gramC H σ b).det * (quotGramC H σ b c).det).re =
      (gramC H σ b).det.re * (quotGramC H σ b c).det.re := by
    simp [Complex.mul_re, ← hGb.2]
  have hy : 0 < (quotGramC H σ b c).det.re := by
    rw [hre] at hG
    exact (pos_iff_pos_of_mul_pos hG.1).mp hGb.1
  rw [hre, Real.log_mul hGb.1.ne' hy.ne']

end DegAdd

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.ExistsIntSmulMemSpan
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DegAdd

open NumberField

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (a : K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ α : 𝓞 K, (α : K) = d * a := by
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ (L := K) {a}
  exact ⟨d, hd, ⟨d • a, h a (Finset.mem_singleton_self a)⟩, zsmul_eq_mul a d⟩

theorem exists_int_smul_mem_span {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (v : Fin n → Fin r → K) {x : Fin r → K} (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range v) := by
  first | exact Bl.general_b_fact_bis_other.goal1 .. | (apply Bl.general_b_fact_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_other.goal1 <;> assumption)

theorem relIndex_ne_zero_of_fg {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : L.FG) (v : Fin n → Fin r → K)
    (hv : ∀ x ∈ L, x ∈ Submodule.span K (Set.range v)) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
  set N := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.addSubgroupOf L.toAddSubgroup
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  let f : L →+ (L.toAddSubgroup ⧸ N) :=
    { toFun := fun x => QuotientAddGroup.mk (⟨x.1, x.2⟩ : L.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : Module.Finite ℤ (L.toAddSubgroup ⧸ N) := by
    refine Module.Finite.of_surjective f.toIntLinearMap ?_
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨⟨y, hy⟩, rfl⟩
  have : Finite (L.toAddSubgroup ⧸ N) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨d, hd, hdy⟩ := exists_int_smul_mem_span v (hv y hy)
    refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    change (d • (QuotientAddGroup.mk (⟨y, hy⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸ N)) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hdy
  exact AddSubgroup.index_ne_zero_of_finite

theorem range_fin_append {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Set.range (Fin.append b c) = Set.range b ∪ Set.range c := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, (Fin.append_left b c i).symm⟩
    | right j => exact Or.inr ⟨j, (Fin.append_right b c j).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd m i, Fin.append_left b c i⟩
    · exact ⟨Fin.natAdd k j, Fin.append_right b c j⟩

theorem fin_append_comp_equiv {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Fin.append b c ∘ finSumFinEquiv = Sum.elim b c := by
  funext i
  cases i <;> simp

theorem indep_parts {K : Type} [Field K] {r k m : ℕ}
    {b : Fin k → Fin r → K} {c : Fin m → Fin r → K} (h : LinearIndependent K (Fin.append b c)) :
    LinearIndependent K b ∧ LinearIndependent K c ∧
      Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c)) := by
  have h2 := h.comp finSumFinEquiv finSumFinEquiv.injective
  rw [fin_append_comp_equiv] at h2
  have h3 := linearIndependent_sum.mp h2
  simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr] using h3

theorem index_split {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hb : ∀ i, b i ∈ L) (hc : ∀ j, c j ∈ L)
    (hdis : Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c))) :
    (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup.relIndex L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex (satSub L b).toAddSubgroup *
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        L.toAddSubgroup := by
  set Sb := Submodule.span (𝓞 K) (Set.range b)
  set Sc := Submodule.span (𝓞 K) (Set.range c)
  set S := satSub L b
  have hA : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) = Sb ⊔ Sc := by
    rw [range_fin_append, Submodule.span_union]
  have hSbS : Sb ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨hb i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hScL : Sc ≤ L := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hc j
  have hSL : S ≤ L := inf_le_left
  have hmeet : ∀ x, x ∈ Sb ⊔ Sc → x ∈ S → x ∈ Sb := by
    intro x hx1 hx2
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx1
    have hyK : y ∈ Submodule.span K (Set.range b) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hy
    have hzK : z ∈ Submodule.span K (Set.range c) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hz
    have hxK : y + z ∈ Submodule.span K (Set.range b) := hx2.2
    have hz' : z ∈ Submodule.span K (Set.range b) := by
      have h := Submodule.sub_mem _ hxK hyK
      simpa using h
    have hz0 : z = 0 := Submodule.disjoint_def.mp hdis z hz' hzK
    simpa [hz0] using hy
  have hinf : (Sb ⊔ Sc).toAddSubgroup ⊓ S.toAddSubgroup = Sb.toAddSubgroup := by
    ext x
    constructor
    · intro h
      exact hmeet x (AddSubgroup.mem_inf.mp h).1 (AddSubgroup.mem_inf.mp h).2
    · intro h
      exact AddSubgroup.mem_inf.mpr ⟨(le_sup_left : Sb ≤ Sb ⊔ Sc) h, hSbS h⟩
  have key : (Sb ⊔ Sc).toAddSubgroup.relIndex (S ⊔ Sc).toAddSubgroup =
      Sb.toAddSubgroup.relIndex S.toAddSubgroup := by
    have hsup : (S ⊔ Sc).toAddSubgroup = S.toAddSubgroup ⊔ (Sb ⊔ Sc).toAddSubgroup := by
      rw [← Submodule.sup_toAddSubgroup, ← sup_assoc, sup_eq_left.mpr hSbS]
    rw [hsup, AddSubgroup.relIndex_sup_right, ← hinf, AddSubgroup.inf_relIndex_right]
  have le1 : (Sb ⊔ Sc).toAddSubgroup ≤ (S ⊔ Sc).toAddSubgroup :=
    fun x hx => (sup_le_sup_right hSbS Sc) hx
  have le2 : (S ⊔ Sc).toAddSubgroup ≤ L.toAddSubgroup := fun x hx => (sup_le hSL hScL) hx
  rw [hA, ← AddSubgroup.relIndex_mul_relIndex _ _ _ le1 le2, key]

end DegAdd

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.GaussValLeIffDivMem
section
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

theorem gauss_val_le_iff_div_mem {U : Type} [Field U] (V : ValuationSubring U) {x y : U} (hy : y ≠ 0) :
    V.valuation x ≤ V.valuation y ↔ x / y ∈ V := by
  have hy0 : (0 : _) < V.valuation y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy)
  rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hy0]

theorem gauss_exists_div_aeval {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (hgen : IntermediateField.adjoin Ω (Set.range t) = ⊤) (z : U) :
    ∃ p q : MvPolynomial σ Ω, aeval t q ≠ 0 ∧ z = aeval t p / aeval t q := by
  have hz : z ∈ IntermediateField.adjoin Ω (Set.range t) := by rw [hgen]; trivial
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨q, rfl⟩ := hs
  by_cases hq : aeval t q = 0
  · refine ⟨0, 1, by simp, ?_⟩
    simp [hq]
  · exact ⟨p, q, hq, rfl⟩

theorem gauss_nonunits {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] (V : ValuationSubring U)
    (w : Ω) : algebraMap Ω U w ∈ V.nonunits ↔ w ∈ (V.comap (algebraMap Ω U)).nonunits := by
  have key : ∀ (A : ValuationSubring U) (x : U), x ∈ A.nonunits ↔ (x = 0 ∨ x⁻¹ ∉ A) := by
    intro A x
    rw [A.mem_nonunits_iff]
    by_cases hx : x = 0
    · simp [hx]
    · have hv : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      simp only [hx, false_or, ← A.valuation_le_one_iff, map_inv₀, not_le]
      constructor
      · intro h; exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hv, h⟩
      · intro h; exact (one_lt_inv_iff₀.mp h).2
  have key' : ∀ (A : ValuationSubring Ω) (x : Ω), x ∈ A.nonunits ↔ (x = 0 ∨ x⁻¹ ∉ A) := by
    intro A x
    rw [A.mem_nonunits_iff]
    by_cases hx : x = 0
    · simp [hx]
    · have hv : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      simp only [hx, false_or, ← A.valuation_le_one_iff, map_inv₀, not_le]
      constructor
      · intro h; exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hv, h⟩
      · intro h; exact (one_lt_inv_iff₀.mp h).2
  rw [key, key', ValuationSubring.mem_comap, map_inv₀]
  simp

theorem gauss_unif {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (hgen : IntermediateField.adjoin Ω (Set.range t) = ⊤)
    (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (ϖ : Ω) (hdiv : ∀ y ∈ (V.comap (algebraMap Ω U)).nonunits,
      y / ϖ ∈ V.comap (algebraMap Ω U)) (z : U) (hz : z ∈ V.nonunits) :
    z / algebraMap Ω U ϖ ∈ V := by
  classical
  set W := V.comap (algebraMap Ω U) with hWdef
  by_cases hϖ : ϖ = 0
  · simp [hϖ]
  have hϖ' : algebraMap Ω U ϖ ≠ 0 := by simpa using hϖ
  obtain ⟨p, q, hq, rfl⟩ := gauss_exists_div_aeval t hgen z
  have hP := gauss_val t V ht hind p
  have hQ := gauss_val t V ht hind q
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hqs : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hq0
  obtain ⟨β, hβ, hβeq⟩ := Finset.exists_mem_eq_sup q.support hqs
    (fun α => V.valuation (algebraMap Ω U (q.coeff α)))
  have hqβ : q.coeff β ≠ 0 := MvPolynomial.mem_support_iff.mp hβ
  have hqβ' : algebraMap Ω U (q.coeff β) ≠ 0 := by simpa using hqβ
  have hvQ : V.valuation (aeval t q) = V.valuation (algebraMap Ω U (q.coeff β)) := hQ.trans hβeq
  have hvQpos : (0 : _) < V.valuation (aeval t q) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hq)
  have hzlt : V.valuation (aeval t p) < V.valuation (aeval t q) := by
    have := (V.mem_nonunits_iff).mp hz
    rwa [map_div₀, div_lt_one₀ hvQpos] at this
  rw [← gauss_val_le_iff_div_mem V hϖ', map_div₀, div_le_iff₀ hvQpos]
  rw [hP, Finset.sup_le_iff]
  intro α hα
  have hle : V.valuation (algebraMap Ω U (p.coeff α)) ≤ V.valuation (aeval t p) := by
    rw [hP]; exact Finset.le_sup (f := fun α => V.valuation (algebraMap Ω U (p.coeff α))) hα
  have hnu : algebraMap Ω U (p.coeff α / q.coeff β) ∈ V.nonunits := by
    rw [V.mem_nonunits_iff, map_div₀, map_div₀, ← hvQ, div_lt_one₀ hvQpos]
    exact lt_of_le_of_lt hle hzlt
  have hnuW : p.coeff α / q.coeff β ∈ W.nonunits := (gauss_nonunits V _).mp hnu
  have hdivW := hdiv _ hnuW
  have hmem : algebraMap Ω U (p.coeff α / q.coeff β) / algebraMap Ω U ϖ ∈ V := by
    rw [← map_div₀]; exact hdivW
  have := (gauss_val_le_iff_div_mem V hϖ').mpr hmem
  rw [map_div₀, map_div₀, ← hvQ, div_le_iff₀ hvQpos] at this
  rw [hvQ] at this ⊢
  first
  | exact this
  | exact this.trans_eq (mul_comm _ _)

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegSt
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def wittMat {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j =>
    if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
    else if i = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0

def WittBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r), S.G.det ≠ 0 →
    ∃ (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K), P.det ≠ 0 ∧ 2 * m ≤ r ∧
      (P.map S.c)ᵀ * S.G * P = wittMat r m g ∧
      ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
        ∑ i, S.c (t i) * g i * t i = 0 → t = 0

def spanIdx {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℕ :=
  (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup

def hGram {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => S.h (b i) (b j)

def LatDegBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b b' : Fin k → Fin r → K),
    (∀ σ, (H σ).PosDef) → B.FG → IsKBasisIn B b → IsKBasisIn B b' →
    latDeg H B b = latDeg H B b'

def IntegralIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (S : HermForm K r)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K),
    B.FG → IsKBasisIn B b → IsIntegralOn S B → (hGram S b).det ≠ 0 →
    ((spanIdx B b : ℕ) : ℝ) ^ 2 ≤ |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)|

def SelfDualIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin r → Fin r → K),
    IsLattice L → IsSelfDual S L → IsKBasisIn L b →
    |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| ≤ ((spanIdx L b : ℕ) : ℝ) ^ 2

def cutSub (K : Type) [Field K] [NumberField K] (r e : ℕ) : Submodule (𝓞 K) (Fin r → K) := UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub K r e

def projGe (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if e ≤ (i : ℕ) then x i else 0
  map_add' x y := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]

def diagMet {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ) :
    (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ :=
  fun σ => Matrix.diagonal fun i => ((δ σ i : ℝ) : ℂ)

def GradedExtStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r e k k₀ k₁ : ℕ) (δ : (K →+* ℂ) → Fin r → ℝ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (b₀ : Fin k₀ → Fin r → K)
    (b₁ : Fin k₁ → Fin r → K),
    (∀ σ i, 0 < δ σ i) → B.FG → IsKBasisIn B b → IsKBasisIn (B ⊓ cutSub K r e) b₀ →
    IsKBasisIn (B.map (projGe K r e)) b₁ →
    latDeg (diagMet δ) B b ≤
      latDeg (diagMet δ) (B ⊓ cutSub K r e) b₀ + latDeg (diagMet δ) (B.map (projGe K r e)) b₁

def AbsDetStatement : Prop :=
  ∀ (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℂ), A.PosDef → C.IsHermitian →
    (∀ v : Fin n → ℂ, ‖star v ⬝ᵥ (C *ᵥ v)‖ ≤ (star v ⬝ᵥ (A *ᵥ v)).re) → ‖C.det‖ ≤ A.det.re

end ReciprocityTheory.MultiplicativeHeights
end
end


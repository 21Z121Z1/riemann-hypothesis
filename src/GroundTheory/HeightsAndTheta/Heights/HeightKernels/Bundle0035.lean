import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0028
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.CardQuotientEqGenIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder

noncomputable section

theorem S6.MatrixSubDegree.genIndex_trans {G : Type*} [AddCommGroup G] {A B C : AddSubgroup G}
    (hCA : C ≤ A) (hCB : C ≤ B) (hBC : C.relIndex B ≠ 0) :
    genIndex A C = genIndex A B * genIndex B C := by
  unfold genIndex
  rw [AddSubgroup.relIndex_eq_one.mpr hCA, AddSubgroup.relIndex_eq_one.mpr hCB]
  have h1 := AddSubgroup.relIndex_mul_relIndex C (A ⊓ B) A (le_inf hCA hCB) inf_le_left
  have h2 := AddSubgroup.relIndex_mul_relIndex C (A ⊓ B) B (le_inf hCA hCB) inf_le_right
  have h1' : (A ⊓ B).relIndex A = B.relIndex A := by
    rw [inf_comm]; exact AddSubgroup.inf_relIndex_right B A
  have h2' : (A ⊓ B).relIndex B = A.relIndex B := AddSubgroup.inf_relIndex_right A B
  rw [h1'] at h1
  rw [h2'] at h2
  have hb : (A.relIndex B : ℝ) ≠ 0 := by
    intro h0
    apply hBC
    rw [← h2, Nat.cast_eq_zero.mp h0, mul_zero]
  rw [← h1, ← h2]
  push_cast
  field_simp

theorem S6.MatrixSubDegree.genIndex_map {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (f : G →+ G') (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]

theorem S6.MatrixSubDegree.exists_smul_mem {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) (hspan : Submodule.span K (M : Set (Fin N → K)) = ⊤)
    {ι : Type*} [Fintype ι] (v : ι → Fin N → K) :
    ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ i, algebraMap (𝓞 K) K t • v i ∈ M :=
  _root_.GroundTheory.Variant₂.N1.exists_smul_mem_family_of_span_eq_top M hspan v

theorem S6.MatrixSubDegree.finrank_satSub {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] {r : ℕ} (u : Fin r → Fin N → K)
    (hu : LinearIndependent K u) (s : Fin r → satSub M u) (hs : LinearIndependent (𝓞 K) s) :
    Module.finrank (𝓞 K) (satSub M u) = r := by
  set W := Submodule.span K (Set.range u)
  let L : satSub M u →ₗ[𝓞 K] (Fin N → K) := M.subtype ∘ₗ (satSub M u).subtype
  have hLi : Function.Injective L := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply le_antisymm
  · apply Module.finrank_le_of_rank_le
    apply rank_le
    intro T hT
    have h0 := hT.map_injOn L hLi.injOn
    have h1 : LinearIndependent K (L ∘ fun i : T => (i : satSub M u)) :=
      (LinearIndependent.iff_fractionRing (𝓞 K) K).mp h0
    have hmem : ∀ i : T, L i ∈ W := fun i => (i : satSub M u).2
    have h2 : LinearIndependent K (fun i : T => (⟨L i, hmem i⟩ : W)) :=
      LinearIndependent.of_comp W.subtype h1
    have := h2.fintype_card_le_finrank
    rw [finrank_span_eq_card hu, Fintype.card_fin, Fintype.card_coe] at this
    exact this
  · have := hs.fintype_card_le_finrank
    simpa using this

theorem S6.MatrixSubDegree.gramAt_smul {K : Type} [Field K] {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ)
    (σ : K →+* ℂ) {ι : Type*} [Fintype ι] (u : ι → Fin N → K) (c : K) :
    gramAt h σ (fun i => c • u i) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt h σ u := by
  have he : ∀ v : Fin N → K, embVec σ (c • v) = σ c • embVec σ v := fun v => by
    funext k; simp [embVec]
  ext a b
  simp only [gramAt, he, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    Matrix.smul_apply, RCLike.star_def, ← mul_assoc]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem S6.MatrixSubDegree.log_gramDet {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)) {r : ℕ} (u : Fin r → Fin N → K)
    (hu : LinearIndependent K u) (c : K) (hc : c ≠ 0) (v : Fin r → M)
    (hv : ∀ i, (v i : Fin N → K) = c • u i) (σ : K →+* ℂ) :
    Real.log (gramDet (matrixBundle M H hH hconj).metric σ v) =
      r * (2 * Real.log ‖σ c‖) + Real.log (gramAt (H σ) σ u).det.re := by
  have hG : (gram ℂ fun i => fibreVec (matrixBundle M H hH hconj).metric σ (v i)) =
      ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt (H σ) σ u := by
    have e : (fun i => c • u i) = fun i => (v i : Fin N → K) := funext fun i => (hv i).symm
    rw [← S6.MatrixSubDegree.gramAt_smul, e]
    ext i j
    rw [gram_apply]
    exact matrixMetric_inner_one_tmul M H hH hconj σ (v i) (v j)
  have hD : 0 < (gramAt (H σ) σ u).det.re := by
    have := (LinesGramPosDef.full K N (H σ) σ (Fin r) u (hH σ) hu).det_pos
    exact (RCLike.pos_iff.mp this).1
  have hσc : ‖σ c‖ ≠ 0 := by
    rw [norm_ne_zero_iff, map_ne_zero]; exact hc
  simp only [GroundTheory.Heights₂.Heights.gramDet]
  rw [hG, det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Real.log_mul (pow_ne_zero _ (pow_ne_zero _ hσc)) hD.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem S6.MatrixSubDegree.genIndex_span_smul {K : Type} [Field K] [NumberField K] {N r : ℕ}
    (u : Fin r → Fin N → K) (hu : LinearIndependent K u) (c : K) (hc : c ≠ 0) :
    genIndex (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun i => c • u i)).toAddSubgroup =
      |((Algebra.norm ℚ c : ℚ) : ℝ)| ^ r := by
  let φ : (Fin r → K) →ₗ[𝓞 K] (Fin N → K) :=
    (Fintype.linearCombination K u).restrictScalars (𝓞 K)
  have hφx : ∀ x, φ x = ∑ i, x i • u i := fun x => Fintype.linearCombination_apply K u x
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [hφx, hφx] at hxy
    have h0 : ∑ i, (x - y) i • u i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hxy, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hu _ h0 i)
  have hstd := LinesStdIndexDet.full K r (c • (1 : Matrix (Fin r) (Fin r) K))
    (by rw [det_smul, det_one, mul_one]; exact pow_ne_zero _ hc)
  have e1 : (⇑φ ∘ fun j : Fin r => (Pi.single j 1 : Fin r → K)) = u := by
    funext j
    show Fintype.linearCombination K u (Pi.single j 1) = u j
    rw [Fintype.linearCombination_apply_single, one_smul]
  have e2 : (⇑φ ∘ fun j : Fin r => (c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1) =
      fun i => c • u i := by
    funext j
    show Fintype.linearCombination K u ((c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1) =
      c • u j
    rw [Matrix.smul_mulVec, one_mulVec, map_smul, Fintype.linearCombination_apply_single,
      one_smul]
  have hB : Submodule.span (𝓞 K) (Set.range u) = (stdLattice K r).map φ := by
    rw [stdLattice, Submodule.map_span, ← Set.range_comp, e1]
  have hC : Submodule.span (𝓞 K) (Set.range fun i => c • u i) = (Submodule.span (𝓞 K)
      (Set.range fun j => (c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1)).map φ := by
    rw [Submodule.map_span, ← Set.range_comp, e2]
  rw [hB, hC, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    S6.MatrixSubDegree.genIndex_map _ hφ, hstd, det_smul, det_one, mul_one, Fintype.card_fin,
    map_pow, Rat.cast_pow, abs_pow]

theorem S6.MatrixSubDegree.card_quotient_eq_genIndex {R E G : Type*} [Ring R] [AddCommGroup E]
    [Module R E] [AddCommGroup G] [Module R G] (F : Submodule R E) (p : Submodule R F)
    (L : F →ₗ[R] G) (hL : Function.Injective L) :
    (Nat.card (F ⧸ p) : ℝ) = genIndex ((⊤ : Submodule R F).map L).toAddSubgroup (p.map L).toAddSubgroup := by
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    S6.MatrixSubDegree.genIndex_map _ hL, genIndex, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_left, Nat.cast_one, div_one]
  rfl

theorem S6.MatrixSubDegree.card_quotient_pos {K : Type} [Field K] [NumberField K] {E : Type*}
    [AddCommGroup E] [Module (𝓞 K) E] (F : Submodule (𝓞 K) E) [Module.Finite (𝓞 K) F] {r : ℕ}
    (s : Fin r → F) (hs : LinearIndependent (𝓞 K) s) (hr : Module.finrank (𝓞 K) F = r) :
    (0 : ℝ) < Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
  have := finite_quotient_span hs (by rw [Fintype.card_fin, hr])
  exact_mod_cast Nat.card_pos

theorem S6.MatrixSubDegree.proof : S6.MatrixSubDegree.Statement := by
  intro K _ _ N M _ H hH hconj hspan r u hu
  obtain ⟨t, ht, htM⟩ := S6.MatrixSubDegree.exists_smul_mem M hspan u
  have hτ : algebraMap (𝓞 K) K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ht
  have hfW : ∀ i, algebraMap (𝓞 K) K t • u i ∈ Submodule.span K (Set.range u) :=
    fun i => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let s : Fin r → satSub M u := fun i => ⟨⟨algebraMap (𝓞 K) K t • u i, htM i⟩, hfW i⟩
  let L : satSub M u →ₗ[𝓞 K] (Fin N → K) := M.subtype ∘ₗ (satSub M u).subtype
  have hL : Function.Injective L := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  have hLs : ⇑L ∘ s = fun i => algebraMap (𝓞 K) K t • u i := rfl
  have hs : LinearIndependent (𝓞 K) s := by
    refine LinearIndependent.of_comp L ?_
    rw [hLs]
    exact (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr
      (hu.units_smul fun _ => Units.mk0 _ hτ)
  have hrank : (matrixBundle M H hH hconj).rank (satSub M u) = r :=
    S6.MatrixSubDegree.finrank_satSub M u hu s hs
  refine ⟨hrank, ?_⟩
  have hcard : Fintype.card (Fin r) = (matrixBundle M H hH hconj).rank (satSub M u) := by
    rw [Fintype.card_fin, hrank]
  rw [(matrixBundle M H hH hconj).degree_eq_of_linearIndependent (satSub M u) hs hcard]
  have hlog := fun σ => S6.MatrixSubDegree.log_gramDet M H hH hconj u hu _ hτ
    (fun i => (s i : M)) (fun i => rfl) σ
  simp_rw [hlog]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    LinesProductFormula.full K _ hτ]

  have hA : M ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) =
      (⊤ : Submodule (𝓞 K) (satSub M u)).map L := by
    rw [Submodule.map_top, LinearMap.range_comp, Submodule.range_subtype, satSub,
      Submodule.map_comap_subtype]
  have hC : Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i) =
      (Submodule.span (𝓞 K) (Set.range s)).map L := by
    rw [Submodule.map_span, ← Set.range_comp, hLs]
  have hpos := S6.MatrixSubDegree.card_quotient_pos (satSub M u) s hs hrank
  rw [S6.MatrixSubDegree.card_quotient_eq_genIndex (satSub M u) _ L hL, ← hA, ← hC] at hpos
  erw [S6.MatrixSubDegree.card_quotient_eq_genIndex (satSub M u) _ L hL]
  rw [← hA]
  erw [← hC]
  have hBC := S6.MatrixSubDegree.genIndex_span_smul u hu _ hτ
  have hN : |((Algebra.norm ℚ (algebraMap (𝓞 K) K t) : ℚ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]; exact hτ
  have hCA : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup ≤
      (M ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨htM i, hfW i⟩
  have hCB : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show algebraMap (𝓞 K) K t • u i ∈ Submodule.span (𝓞 K) (Set.range u)
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ t (Submodule.subset_span ⟨i, rfl⟩)
  have hrel : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup ≠ 0 := by
    intro h0
    apply pow_ne_zero r hN
    rw [← hBC, genIndex, h0, Nat.cast_zero, zero_div]
  have htrans := S6.MatrixSubDegree.genIndex_trans hCA hCB hrel
  rw [htrans, hBC] at hpos ⊢
  have hAB := left_ne_zero_of_mul hpos.ne'
  rw [Real.log_mul hAB (pow_ne_zero _ hN), Real.log_pow, subDegree]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ExistsSmulMemIdealLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder

noncomputable section

namespace S6.QuotExtension

theorem schur_inner {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (G : Matrix (m ⊕ k) (m ⊕ k) ℂ) (hA : IsUnit G.toBlocks₁₁.det) (β β' : m → ℂ) (γ γ' : k → ℂ)
    (h : ∀ i, (G *ᵥ Sum.elim β' γ') (Sum.inl i) = 0) :
    star (Sum.elim β γ) ⬝ᵥ (G *ᵥ Sum.elim β' γ') =
      star γ ⬝ᵥ ((G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂) *ᵥ γ') := by
  set A := G.toBlocks₁₁
  set B := G.toBlocks₁₂
  set C := G.toBlocks₂₁
  set D := G.toBlocks₂₂
  have hG : G = fromBlocks A B C D := (fromBlocks_toBlocks G).symm
  have hv : G *ᵥ Sum.elim β' γ' = Sum.elim (A *ᵥ β' + B *ᵥ γ') (C *ᵥ β' + D *ᵥ γ') := by
    rw [hG, fromBlocks_mulVec]
    rfl
  have h0 : A *ᵥ β' + B *ᵥ γ' = 0 := funext fun i => by simpa [hv] using h i
  have hβ : β' = -((A⁻¹ * B) *ᵥ γ') := by
    have hinv : A⁻¹ *ᵥ (A *ᵥ β') = β' := by rw [mulVec_mulVec, nonsing_inv_mul A hA, one_mulVec]
    rw [← hinv, eq_neg_iff_add_eq_zero, ← mulVec_mulVec, ← mulVec_add, h0, mulVec_zero]
  have hw : C *ᵥ β' + D *ᵥ γ' = (D - C * A⁻¹ * B) *ᵥ γ' := by
    rw [hβ, mulVec_neg, mulVec_mulVec, sub_mulVec, Matrix.mul_assoc]
    abel
  rw [hv, h0, hw]
  simp [dotProduct, Fintype.sum_sum_type]

variable {K : Type} [Field K] [NumberField K]

def embMat (σ : K →+* ℂ) {n : ℕ} {ι : Type*} (u : ι → Fin n → K) : Matrix (Fin n) ι ℂ :=
  Matrix.of fun r s => σ (u s r)

omit [NumberField K] in

theorem gramAt_eq {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) : gramAt h σ u = (embMat σ u)ᴴ * h * embMat σ u := by
  ext s t
  simp only [gramAt, embVec, embMat, dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply,
    of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  ring

omit [NumberField K] in

theorem inner_embMat {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) (w w' : ι → ℂ) :
    star (embMat σ u *ᵥ w) ⬝ᵥ (h *ᵥ (embMat σ u *ᵥ w')) = star w ⬝ᵥ (gramAt h σ u *ᵥ w') := by
  rw [star_mulVec, ← dotProduct_mulVec, gramAt_eq, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

omit [NumberField K] in

theorem gramAt_mulVec_apply {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*}
    [Fintype ι] (u : ι → Fin n → K) (w : ι → ℂ) (s : ι) :
    (gramAt h σ u *ᵥ w) s = star (embVec σ (u s)) ⬝ᵥ (h *ᵥ (embMat σ u *ᵥ w)) := by
  rw [gramAt_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [mulVec, dotProduct, conjTranspose_apply, embMat, embVec, of_apply, Pi.star_apply]

theorem exists_smul_mem_idealLattice {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K}
    (ha : ∀ x, a x ≠ 0) (v : Fin n → K) : ∃ t : 𝓞 K, t ≠ 0 ∧ t • v ∈ idealLattice a := by
  classical
  choose e he0 hea using fun x => FractionalIdeal.exists_ne_zero_mem_isInteger (ha x)
  obtain ⟨c, hc0, hc⟩ := exists_common_denominator (M := Submodule.span (𝓞 K) {v})
    (Submodule.fg_span_singleton v)
  refine ⟨c * ∏ x, e x, mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun x _ => he0 x), ?_⟩
  rw [idealLattice, Submodule.mem_pi]
  intro x _
  obtain ⟨w, hw⟩ := hc v (Submodule.mem_span_singleton_self v) x
  rw [← Finset.mul_prod_erase Finset.univ e (Finset.mem_univ x)]
  have hx : ((c * (e x * ∏ y ∈ Finset.univ.erase x, e y)) • v) x =
      (w * ∏ y ∈ Finset.univ.erase x, e y) • algebraMap (𝓞 K) K (e x) := by
    rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_mul, hw]
    ring
  rw [hx]
  exact Submodule.smul_mem _ _ (hea x)

theorem coord_decomp {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n)
    (σ : K →+* ℂ) (x : Fibre σ (idealLattice a)) :
    ∃ β : Fin m → ℂ, latticeCoord σ (idealLattice a) x =
      embMat σ (Sum.elim b c) *ᵥ Sum.elim β (latticeCoord σ (quotLattice a b c hli hmk)
        ((quotProj a b c hli hmk).lTensor (ComplexAt σ) x)) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul z v =>
    refine ⟨fun i => σ ((sumBasis b c hli hmk).repr v (Sum.inl i)) * (ofComplex σ).symm z, ?_⟩
    have hu : Sum.elim (fun i => σ ((sumBasis b c hli hmk).repr v (Sum.inl i)) *
        (ofComplex σ).symm z) (latticeCoord σ (quotLattice a b c hli hmk)
          ((quotProj a b c hli hmk).lTensor (ComplexAt σ) (z ⊗ₜ v))) =
        fun s => σ ((sumBasis b c hli hmk).repr v s) * (ofComplex σ).symm z := by
      funext s
      rcases s with i | j
      · rfl
      · rw [Sum.elim_inr, LinearMap.lTensor_tmul, latticeCoord_tmul]
        rfl
    rw [hu]
    funext r
    rw [latticeCoord_tmul]
    have hv := congrFun ((sumBasis b c hli hmk).sum_repr (v : Fin n → K)) r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sumBasis_apply] at hv
    simp only [mulVec, dotProduct, embMat, of_apply]
    rw [← hv, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_mul]
    ring
  | add x y hx hy =>
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', hβ'⟩ := hy
    refine ⟨β + β', ?_⟩
    rw [map_add, map_add, map_add, hβ, hβ', ← mulVec_add, Sum.elim_add_add]

theorem orth_sub {n m : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (ha : ∀ x, a x ≠ 0)
    {d : (K →+* ℂ) → Fin n → ℝ} (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x)
    (b : Fin m → Fin n → K) (σ : K →+* ℂ) (y : Fibre σ (idealLattice a))
    (hy : ∀ w : Fibre σ (subLattice a b), ((latticeBundle a d hd hc).metric.form σ).inner
      ((subLattice a b).subtype.lTensor (ComplexAt σ) w) y = 0) (i : Fin m) :
    star (embVec σ (b i)) ⬝ᵥ (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y) = 0 := by
  obtain ⟨t, ht, htv⟩ := exists_smul_mem_idealLattice ha (b i)
  have hW : (⟨t • b i, htv⟩ : idealLattice a) ∈ subLattice a b :=
    Submodule.smul_of_tower_mem (Submodule.span K (Set.range b)) t
      (Submodule.subset_span ⟨i, rfl⟩)
  have h := hy ((1 : ComplexAt σ) ⊗ₜ ⟨_, hW⟩)
  rw [LinearMap.lTensor_tmul] at h
  have h' : star (latticeCoord σ (idealLattice a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K]
      (⟨t • b i, htv⟩ : idealLattice a))) ⬝ᵥ
      (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y) = 0 := h
  have hl : latticeCoord σ (idealLattice a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K]
      (⟨t • b i, htv⟩ : idealLattice a)) = σ (t : K) • embVec σ (b i) := by
    funext r
    rw [latticeCoord_tmul]
    simp [embVec, Algebra.smul_def]
  have hσt : σ (t : K) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast ht
  rw [hl, star_smul, smul_dotProduct, smul_eq_mul] at h'
  exact (mul_eq_zero.mp h').resolve_left (by simpa using hσt)

end S6.QuotExtension

open S6.QuotExtension in

theorem S6.QuotExtension.proof : S6.QuotExtension.Statement := by
  intro K _ _ n a d hd hc ha m k b c hli hmk
  refine ⟨{ incl := (subLattice a b).subtype
            proj := quotProj a b c hli hmk
            incl_injective := (subLattice a b).injective_subtype
            proj_surjective := LinearMap.submoduleMap_surjective _ _
            exact := ?_
            incl_isometric := fun σ x y => rfl
            proj_coisometric := ?_ }, rfl, rfl⟩
  · show ∀ y : idealLattice a, quotProj a b c hli hmk y = 0 ↔ y ∈ Set.range (subLattice a b).subtype
    intro y
    have hker := KLinesQuotIndex.ker_coordProj (sumBasis b c hli hmk)
    have hr : (fun i => sumBasis b c hli hmk (Sum.inl i)) = b :=
      funext fun i => by rw [sumBasis_apply]; rfl
    rw [hr] at hker
    have h1 : quotProj a b c hli hmk y = 0 ↔
        coordProj (sumBasis b c hli hmk) (y : Fin n → K) = 0 := by
      rw [← Submodule.coe_eq_zero]
      exact Iff.rfl
    rw [h1, ← LinearMap.mem_ker, hker]
    constructor
    · intro h
      exact ⟨⟨y, h⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact w.2
  · intro σ x y _ hy
    obtain ⟨β, hx⟩ := coord_decomp a b c hli hmk σ x
    obtain ⟨β', hy'⟩ := coord_decomp a b c hli hmk σ y
    have hG := LinesGramPosDef.full K n _ σ _ _ (diagMetric_posDef hd σ) hli
    have hA : IsUnit (gramAt (diagMetric d σ) σ (Sum.elim b c)).toBlocks₁₁.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (hG.submatrix Sum.inl_injective).isUnit
    change star (latticeCoord σ (quotLattice a b c hli hmk) _) ⬝ᵥ
        (schurMetric d b c σ *ᵥ latticeCoord σ (quotLattice a b c hli hmk) _) =
      star (latticeCoord σ (idealLattice a) x) ⬝ᵥ
        (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y)
    rw [hx, hy', inner_embMat]
    refine (schur_inner _ hA _ _ _ _ fun i => ?_).symm
    rw [gramAt_mulVec_apply]
    exact (congrArg (fun v => star (embVec σ (b i)) ⬝ᵥ (diagMetric d σ *ᵥ v)) hy').symm.trans
      (orth_sub ha hd hc b σ y hy i)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegStandard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

theorem DualGeomDegStandard.proof (hD : DualGeomDegCharts.Statement)
    (hG : GrassGeomDegChart.Statement) (hM : ChartMassInvariant.Statement) :
    DualGeomDegStandard.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨A, hA, hE⟩ := hD K i F T b hb hi
  obtain ⟨B, hB, hG'⟩ := hG (i - 1)
  have e1 : 1 * 1 * (i - 1) = i - 1 := by simp
  have hterm : ∀ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ) =
      chartMass (1 : Matrix (Fin (i - 1 + 1)) (Fin (i - 1 + 1)) ℂ) := fun σ =>
    hM _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hA σ).1)
  rw [e1, hE, hG', hM _ _ (Matrix.PosDef.conjTranspose_mul_self B hB.1),
    Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, Finset.card_univ,
    Embeddings.card K ℂ, nsmul_eq_mul]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopStandard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem DualTopStandard.proof (hBC : DualStdBaseChange.Statement) (hGL : GrassLinesProj.Statement) :
    DualTopStandard.Statement := by
  intro K _ _ i T _ _ b hb II hi hII
  rw [hBC K i T b hb II hi hII]
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, hGL m II hII]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsClosedPointChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ClosedPointChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧
        ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a

end

end GroundTheory.Heights₂.Heights
end


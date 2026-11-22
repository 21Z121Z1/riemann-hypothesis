import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.BaseChangeIndex
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField TensorProduct ComplexAt GroundTheory.Heights₂.Heights

noncomputable section

section GramDet

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

omit [NumberField K] [NumberField L] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in

theorem baseChangeCoord_one_tmul (τ : L →+* ℂ) (e : E) :
    baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] e)) =
      (1 : ComplexAt (τ.comp (algebraMap K L))) ⊗ₜ e := by
  rw [baseChangeCoord_tmul]
  congr 1
  simp

theorem gramDet_baseChange (h : HermitianMetric K E) (τ : L →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → E) :
    gramDet (h.baseChange L) τ (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) =
      gramDet h (τ.comp (algebraMap K L)) s := by
  have hv : ∀ i j, inner ℂ (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s i))
      (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s j)) =
      inner ℂ (fibreVec h (τ.comp (algebraMap K L)) (s i))
        (fibreVec h (τ.comp (algebraMap K L)) (s j)) := by
    intro i j
    rw [fibreVec, fibreVec, FibreSpace.inner_equiv]
    change inner ℂ (FibreSpace.equiv h _ (baseChangeCoord τ _))
      (FibreSpace.equiv h _ (baseChangeCoord τ _)) = _
    rw [baseChangeCoord_one_tmul, baseChangeCoord_one_tmul]
    rfl
  simp only [gramDet]
  congr 2
  ext i j
  simp only [Matrix.gram_apply, hv]

end GramDet

theorem BaseChange.proof : BaseChange.Statement := by
  intro K _ _ L _ _ _ M
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  set N := Submodule.span (𝓞 K) (Set.range s)
  have hrank : Module.finrank (𝓞 L) (𝓞 L ⊗[𝓞 K] M.carrier) = Module.finrank (𝓞 K) M.carrier :=
    (TensorProduct.isBaseChange (𝓞 K) M.carrier (𝓞 L)).finrank_eq

  let b : Module.Basis (Fin (Module.finrank (𝓞 K) M.carrier)) (𝓞 K) N := Module.Basis.span hs
  let bL := Algebra.TensorProduct.basis (𝓞 L) b
  let f : 𝓞 L ⊗[𝓞 K] N →ₗ[𝓞 L] 𝓞 L ⊗[𝓞 K] M.carrier :=
    AlgebraTensorModule.lTensor (𝓞 L) (𝓞 L) N.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
  have hfb : (f ∘ bL) = fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i := by
    funext i
    simp only [Function.comp_apply, bL, f, b, Algebra.TensorProduct.basis_apply,
      AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  have ht : LinearIndependent (𝓞 L) (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) := by
    rw [← hfb]
    exact bL.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hspan : Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) =
      LinearMap.range f := by
    rw [LinearMap.range_eq_map, ← bL.span_eq, Submodule.map_span, ← Set.range_comp, hfb]

  have hfin : Finite (M.carrier ⧸ N) := finite_quotient_span hs (Fintype.card_fin _)
  have hidx : Nat.card ((𝓞 L ⊗[𝓞 K] M.carrier) ⧸
      Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i)) =
      Nat.card (M.carrier ⧸ N) ^ Module.finrank K L := by
    rw [hspan, ← card_tensor_integers L]
    exact Nat.card_congr (AlgebraTensorModule.tensorQuotientEquiv (𝓞 L) (𝓞 K) (𝓞 L) N).toEquiv.symm

  have hn : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  show arithDegree (M.metric.baseChange L) / Module.finrank ℚ L =
    arithDegree M.metric / Module.finrank ℚ K
  rw [arithDegree_eq (M.metric.baseChange L) ht (by rw [Fintype.card_fin]; exact hrank.symm),
    arithDegree_eq M.metric hs (Fintype.card_fin _), ← Module.finrank_mul_finrank ℚ K L]
  simp only [degreeWith, gramDet_baseChange]
  rw [hidx, sum_comp_algebraMap L (fun σ ↦ Real.log (gramDet M.metric σ s)), Nat.cast_pow,
    Real.log_pow, Nat.cast_mul]
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PChainSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

namespace ChainSum

theorem deg_eq_of_linearEquiv {K : Type u} [Field K] [NumberField K] (A B : HermitianBundle.{v} K)
    (φ : A.carrier ≃ₗ[𝓞 K] B.carrier)
    (hg : ∀ (σ : K →+* ℂ) (n : ℕ) (s : Fin n → A.carrier),
      GroundTheory.Heights₂.Heights.gramDet A.metric σ s =
        GroundTheory.Heights₂.Heights.gramDet B.metric σ (fun i ↦ φ (s i))) :
    A.deg = B.deg := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := A.carrier)
  have ht : LinearIndependent (𝓞 K) (fun i ↦ φ (s i)) := hs.map' φ.toLinearMap φ.ker
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) A.carrier)) =
      Module.finrank (𝓞 K) B.carrier := by
    rw [Fintype.card_fin]
    exact φ.finrank_eq
  simp only [HermitianBundle.deg, HermitianBundle.arithDegree]
  rw [arithDegree_eq A.metric hs (Fintype.card_fin _), arithDegree_eq B.metric ht hcard]
  simp only [GroundTheory.Heights₂.Heights.degreeWith, hg]
  have hmap : (Submodule.span (𝓞 K) (Set.range s)).map φ.toLinearMap =
      Submodule.span (𝓞 K) (Set.range fun i ↦ φ (s i)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ φ hmap).toEquiv]

theorem deg_sub_top {K : Type u} [Field K] [NumberField K] (M : HermitianBundle.{v} K) :
    (M.sub ⊤).deg = M.deg :=
  deg_eq_of_linearEquiv (M.sub ⊤) M Submodule.topEquiv fun σ _ s ↦
    gramDet_comap M.metric (⊤ : Submodule (𝓞 K) M.carrier).subtype (Submodule.injective_subtype _) σ s

theorem deg_sub_comap {K : Type u} [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    {F G : Submodule (𝓞 K) M.carrier} (hGF : G ≤ F) :
    ((M.sub F).sub (G.comap F.subtype)).deg = (M.sub G).deg :=
  deg_eq_of_linearEquiv _ _ (Submodule.comapSubtypeEquivOfLe hGF) fun σ _ s ↦ by
    have e1 := gramDet_comap (M.sub F).metric (G.comap F.subtype).subtype
      (Submodule.injective_subtype _) σ s
    have e2 := gramDet_comap M.metric F.subtype (Submodule.injective_subtype _) σ
      fun i ↦ (G.comap F.subtype).subtype (s i)
    have e3 := gramDet_comap M.metric G.subtype (Submodule.injective_subtype _) σ
      fun i ↦ Submodule.comapSubtypeEquivOfLe hGF (s i)
    exact e1.trans (e2.trans e3.symm)

end ChainSum

theorem ChainSum.proof (h1 : ExactSequence.Statement.{u, v}) : ChainSum.Statement.{u, v} := by
  intro K _ _ M k
  induction k with
  | zero =>
    intro c h0 _ _
    have hl : c (Fin.last 0) = ⊤ := h0
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero, hl, ChainSum.deg_sub_top]
  | succ k ih =>
    intro c h0 hmono hc
    have hmono' : Antitone fun a : Fin (k + 1) ↦ c a.castSucc :=
      fun a b hab ↦ hmono (Fin.castSucc_le_castSucc_iff.mpr hab)
    have hIH := ih (fun a ↦ c a.castSucc) h0 hmono' fun a ↦ hc _
    have hle : c (Fin.last (k + 1)) ≤ c (Fin.last k).castSucc :=
      hmono (Fin.castSucc_lt_last _).le
    have hE := h1 K (M.sub (c (Fin.last k).castSucc))
      ((c (Fin.last (k + 1))).comap (c (Fin.last k).castSucc).subtype)
      ((hc (Fin.last (k + 1))).comap_subtype _)
    rw [ChainSum.deg_sub_comap M hle] at hE
    rw [Fin.sum_univ_castSucc, hIH, hE, add_assoc]
    congr 1
    rw [add_comm]
    rfl

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PDiagonalChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem span_fibreVec_eq_top (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i)) = ⊤ := by
  set N := Submodule.span (𝓞 K) (Set.range s)
  have := finite_quotient_span hs hcard
  set m := Nat.card (E ⧸ N)
  have hm : 0 < m := Nat.card_pos
  have hmem : ∀ e : E, m • e ∈ N := fun e ↦
    (Submodule.Quotient.mk_eq_zero N).mp (by rw [Submodule.Quotient.mk_smul]; exact card_nsmul_eq_zero')
  set W := Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i))
  have h1 : ∀ e ∈ N, fibreVec h σ e ∈ W := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp [fibreVec]
    | add x y _ _ hx hy => rw [fibreVec_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [fibreVec_smul]; exact W.smul_mem _ hx
  have h2 : ∀ e : E, fibreVec h σ e ∈ W := by
    intro e
    have := h1 _ (hmem e)
    rw [← Nat.cast_smul_eq_nsmul (𝓞 K) m e, fibreVec_smul] at this
    have hc : (σ ((m : 𝓞 K) : K)) = (m : ℂ) := by simp
    rw [hc] at this
    exact (W.smul_mem_iff (Nat.cast_ne_zero.mpr hm.ne')).mp this
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := (FibreSpace.equiv h σ).surjective x
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact W.zero_mem
  | add y z hy hz => rw [map_add]; exact W.add_mem hy hz
  | tmul z e =>
    have hz : (z ⊗ₜ[𝓞 K] e : Fibre σ E) = ((ofComplex σ).symm z) • ((1 : ComplexAt σ) ⊗ₜ e) := by
      rw [← fibre_smul_eq, smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul]
    exact W.smul_mem _ (h2 e)

theorem gramDet_eq_of_norm_eq (h h' : HermitianMetric K E) (σ : K →+* ℂ)
    (T : Fibre σ E →ₗ[ℂ] Fibre σ E)
    (hT : ∀ x, ‖FibreSpace.equiv h' σ x‖ = ‖FibreSpace.equiv h σ (T x)‖) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    gramDet h' σ s = ‖LinearMap.det T‖ ^ 2 * gramDet h σ s := by
  have kadd : ∀ (c : ℂ) (x y : Fibre σ E), ‖FibreSpace.equiv h' σ x + c • FibreSpace.equiv h' σ y‖ =
      ‖FibreSpace.equiv h σ (T x) + c • FibreSpace.equiv h σ (T y)‖ := by
    intro c x y
    rw [← map_smul, ← map_add, hT, map_add, map_add, map_smul, map_smul]
  have ksub : ∀ (c : ℂ) (x y : Fibre σ E), ‖FibreSpace.equiv h' σ x - c • FibreSpace.equiv h' σ y‖ =
      ‖FibreSpace.equiv h σ (T x) - c • FibreSpace.equiv h σ (T y)‖ := by
    intro c x y
    rw [← map_smul, ← map_sub, hT, map_sub, map_sub, map_smul, map_smul]
  have hinner : ∀ x y : Fibre σ E, inner ℂ (FibreSpace.equiv h' σ x) (FibreSpace.equiv h' σ y) =
      inner ℂ (FibreSpace.equiv h σ (T x)) (FibreSpace.equiv h σ (T y)) := by
    intro x y
    have e1 := kadd 1 x y
    have e2 := ksub 1 x y
    simp only [one_smul] at e1 e2
    rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (FibreSpace.equiv h' σ x),
      inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (FibreSpace.equiv h σ (T x)), e1, e2, kadd, ksub]
  let bv : Module.Basis ι ℂ (FibreSpace h σ) :=
    Module.Basis.mk (linearIndependent_fibreVec h σ hs) (span_fibreVec_eq_top h σ hs hcard).ge
  let S : FibreSpace h σ →ₗ[ℂ] FibreSpace h σ := (FibreSpace.equiv h σ).conj T
  let B := LinearMap.toMatrix bv bv S
  have hS : ∀ e : E, S (fibreVec h σ e) = FibreSpace.equiv h σ (T ((1 : ComplexAt σ) ⊗ₜ e)) := by
    intro e
    simp only [S, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, fibreVec,
      LinearEquiv.symm_apply_apply]
  have hgram : (gram ℂ fun i ↦ fibreVec h' σ (s i)) = gram ℂ fun j ↦ ∑ i, B i j • bv i := by
    ext i j
    simp only [gram_apply]
    have hj : ∀ j, ∑ i, B i j • bv i = S (fibreVec h σ (s j)) := by
      intro j
      have := bv.sum_repr (S (bv j))
      simp only [B, LinearMap.toMatrix_apply]
      rw [this, Module.Basis.mk_apply]
    rw [hj, hj, hS, hS]
    exact hinner _ _
  have hbv : (⇑bv : ι → FibreSpace h σ) = fun i ↦ fibreVec h σ (s i) := funext fun i ↦ Module.Basis.mk_apply _ _ _
  have hdet : B.det = LinearMap.det T := by
    rw [LinearMap.det_toMatrix]
    exact LinearMap.det_conj T (FibreSpace.equiv h σ)
  simp only [gramDet]
  rw [hgram, gram_comb, hbv, det_mul, det_mul, det_conjTranspose, mul_comm _ B.det, ← mul_assoc,
    RCLike.star_def, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, hdet]

theorem DiagonalChange.proof : DiagonalChange.Statement := by
  intro K _ _ M h' T hT _
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) M.carrier)) =
      Module.finrank (𝓞 K) M.carrier := Fintype.card_fin _
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet h' σ s) =
      2 * Real.log ‖LinearMap.det (T σ)‖ + Real.log (gramDet M.metric σ s) := by
    intro σ
    have hp := gramDet_pos h' σ hs
    have hp0 := gramDet_pos M.metric σ hs
    rw [gramDet_eq_of_norm_eq M.metric h' σ (T σ) (hT σ) hs hcard] at hp ⊢
    have hd : ‖LinearMap.det (T σ)‖ ≠ 0 := by
      intro h0
      rw [h0] at hp
      simp at hp
    rw [Real.log_mul (pow_ne_zero 2 hd) hp0.ne', Real.log_pow]
    push_cast
    ring
  simp only [HermitianBundle.deg, HermitianBundle.arithDegree]
  rw [arithDegree_eq h' hs hcard, arithDegree_eq M.metric hs hcard]
  simp only [degreeWith, hlog, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PExactSequence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace HermitianBundle

variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)

theorem quotFibreMap_mkQ_of_orthogonal (σ : K →+* ℂ) (x : Fibre σ M.carrier)
    (hx : FibreSpace.equiv M.metric σ x ∈ (subFibre M.metric σ F)ᗮ) :
    quotFibreMap M F hF σ (fibreMap σ F.mkQ x) = FibreSpace.equiv M.metric σ x := by
  have := quot_projective hF
  set V := subFibre M.metric σ F
  set z := fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x) - x with hzdef
  have hex := lTensor_exact (ComplexAt σ) (LinearMap.exact_subtype_mkQ F) F.mkQ_surjective
  have h0 : F.mkQ.lTensor (ComplexAt σ) z = 0 := by
    change fibreMap σ F.mkQ z = 0
    rw [hzdef, map_sub, fibreMap_fibreMap, fibreMap_fibreMap,
      mkQ_comp_quotSection, LinearMap.id_comp, sub_self]
  obtain ⟨y, hy⟩ := (hex z).mp h0
  have hz : FibreSpace.equiv M.metric σ z ∈ V := ⟨y, congrArg (FibreSpace.equiv M.metric σ) hy⟩
  have hsplit : FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x)) =
      FibreSpace.equiv M.metric σ x + FibreSpace.equiv M.metric σ z := by
    rw [hzdef, map_sub]
    abel
  change Vᗮ.starProjection
      (FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x))) = _
  rw [hsplit, map_add, Submodule.starProjection_orthogonal_apply_eq_zero hz, add_zero,
    Submodule.starProjection_eq_self_iff.mpr hx]

def subQuotExtension : HermitianExtension (M.sub F) M (M.quot F hF) where
  incl := F.subtype
  proj := F.mkQ
  incl_injective := F.injective_subtype
  proj_surjective := F.mkQ_surjective
  exact := LinearMap.exact_subtype_mkQ F
  incl_isometric _ _ _ := rfl
  proj_coisometric σ x y hx hy := by
    have hmem : ∀ z : Fibre σ M.carrier,
        (∀ w, (M.metric.form σ).inner (F.subtype.lTensor (ComplexAt σ) w) z = 0) →
          FibreSpace.equiv M.metric σ z ∈ (subFibre M.metric σ F)ᗮ := by
      intro z hz
      rw [Submodule.mem_orthogonal]
      rintro u ⟨w, rfl⟩
      exact hz w
    change inner ℂ (quotFibreMap M F hF σ (fibreMap σ F.mkQ x))
      (quotFibreMap M F hF σ (fibreMap σ F.mkQ y)) = _
    rw [quotFibreMap_mkQ_of_orthogonal M F hF σ x (hmem x hx),
      quotFibreMap_mkQ_of_orthogonal M F hF σ y (hmem y hy)]
    rfl

end HermitianBundle

namespace LatticeLemmas

theorem ExactSequence.proof : ExactSequence.Statement := by
  intro K _ _ M F hF
  simp only [HermitianBundle.deg]
  rw [(HermitianBundle.subQuotExtension M F hF).arithDegree_eq_add, add_div]

end LatticeLemmas

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PHadamard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights InnerProductSpace

universe u v w

noncomputable section

theorem det_gram_re_le_prod_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) :
    (det (gram ℂ v)).re ≤ ∏ i, ‖v i‖ ^ 2 := by
  set W := Submodule.span ℂ (Set.range v)
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  let w : Fin n → W := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hgw : gram ℂ v = gram ℂ w := by
    ext i j
    simp only [gram_apply, w, Submodule.coe_inner]
  have hfin : Module.finrank ℂ W = Fintype.card (Fin n) := finrank_span_eq_card hv
  let b : OrthonormalBasis (Fin n) ℂ W := gramSchmidtOrthonormalBasis hfin w
  have hb : b.toBasis.det w = ∏ i, inner ℂ (b i) (w i) := gramSchmidtOrthonormalBasis_det hfin w
  set A := b.toBasis.toMatrix w
  have hA : gram ℂ w = Aᴴ * A := by
    ext j k
    rw [gram_apply, mul_apply, ← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [A, conjTranspose_apply, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, RCLike.star_def,
      inner_conj_symm]
  have hdet : (det (gram ℂ w)).re = ‖b.toBasis.det w‖ ^ 2 := by
    rw [hA, det_mul, det_conjTranspose, Module.Basis.det_apply, RCLike.star_def, Complex.conj_mul']
    norm_cast
  rw [hgw, hdet, hb, norm_prod, ← Finset.prod_pow]
  gcongr with i
  calc ‖inner ℂ (b i) (w i)‖ ≤ ‖b i‖ * ‖w i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]; rfl

section Gram

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem log_gramDet_le (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s) :
    Real.log (gramDet h σ s) ≤ 2 * ∑ i, Real.log ‖fibreVec h σ (s i)‖ := by
  let e := Fintype.equivFin ι
  have hs' : LinearIndependent (𝓞 K) (s ∘ e.symm) := hs.comp _ e.symm.injective
  have hne : ∀ i, fibreVec h σ (s i) ≠ 0 := (linearIndependent_fibreVec h σ hs).ne_zero
  have hH := det_gram_re_le_prod_norm_sq (fun i ↦ fibreVec h σ ((s ∘ e.symm) i))
    (linearIndependent_fibreVec h σ hs')
  rw [← gramDet_reindex h σ e.symm s]
  calc Real.log (gramDet h σ (s ∘ e.symm))
      ≤ Real.log (∏ i, ‖fibreVec h σ ((s ∘ e.symm) i)‖ ^ 2) :=
        Real.log_le_log (gramDet_pos h σ hs') hH
    _ = 2 * ∑ i, Real.log ‖fibreVec h σ ((s ∘ e.symm) i)‖ := by
        rw [Real.log_prod (s := Finset.univ) (f := fun i ↦ ‖fibreVec h σ ((s ∘ e.symm) i)‖ ^ 2)
          (fun i _ ↦ pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne (e.symm i)))), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Real.log_pow]
        push_cast
        ring
    _ = 2 * ∑ i, Real.log ‖fibreVec h σ (s i)‖ := by
        congr 1
        exact e.symm.sum_comp (fun i ↦ Real.log ‖fibreVec h σ (s i)‖)

end Gram

theorem Hadamard.intersectionNumber_baseChange : Hadamard.Statement.{u, v, w} := by
  intro K _ _ M ι _ x La hli hcard hnorm
  classical
  set r := Module.finrank (𝓞 K) M.carrier
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hN : 0 ≤ Real.log (Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range x))) :=
    Real.log_natCast_nonneg _
  have hσ : ∀ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤ 2 * (r * Real.log La) := by
    intro σ
    refine (log_gramDet_le M.metric σ hli).trans ?_
    have hle : ∑ i, Real.log ‖fibreVec M.metric σ (x i)‖ ≤ ∑ _i : ι, Real.log La :=
      Finset.sum_le_sum fun i _ ↦ Real.log_le_log
        (norm_pos_iff.mpr ((linearIndependent_fibreVec M.metric σ hli).ne_zero i)) (hnorm i σ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hle
    linarith
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ x) ≤
      Module.finrank ℚ K * (2 * (r * Real.log La)) := by
    calc _ ≤ ∑ _σ : K →+* ℂ, 2 * (r * Real.log La) := Finset.sum_le_sum fun σ _ ↦ hσ σ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  rw [HermitianBundle.deg, HermitianBundle.arithDegree, arithDegree_eq M.metric hli hcard, degreeWith,
    le_div_iff₀ hd]
  nlinarith

theorem Hadamard.proof (_h1 : Sublattice.Statement.{u, v}) : Hadamard.Statement.{u, v, w} :=
  Hadamard.intersectionNumber_baseChange

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end


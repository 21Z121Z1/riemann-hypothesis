import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0021

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotDegreeBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem LinesQuotDegreeBound.proof (h1 : LinesExtendBasis.Statement)
    (h2 : LinesQuotIndexLog.Statement) (h3 : LinesQuotGramLog.Statement) :
    LinesQuotDegreeBound.Statement := by
  intro K _ _ n a d ha hd m k b c hbc hmk
  have hb : LinearIndependent K b := hbc.comp Sum.inl Sum.inl_injective
  obtain ⟨τ, hτ, hbs⟩ := h1 K n m k b hb hmk
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) := by
    simp [hmk]
  let B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hbs hcard
  have hBl : ∀ i, B (Sum.inl i) = b i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank']
  have hBr : ∀ j, B (Sum.inr j) = Pi.single (τ j) 1 := fun j => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank']
  refine ⟨τ, hτ, ?_⟩
  set D := (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det with hD
  have hI := h2 K n m k a B b c τ ha hBl hBr hτ hbc
  have hG : ∀ σ : K →+* ℂ,
      Real.log (gramAt (diagMetric d σ) σ (Sum.elim b c)).det.re -
          Real.log (gramAt (diagMetric d σ) σ b).det.re ≤
        ∑ j, Real.log (d σ (τ j)) + 2 * Real.log ‖σ D‖ := fun σ =>
    h3 K n m k (d σ) σ B b c τ (hd σ) hBl hBr hτ hbc
  have hGs := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hG σ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm] at hGs
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold quotDegree
  linarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotGramLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

namespace KLinesQuotGramLog

theorem basis_eq_elim {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (b : Fin m → Fin n → K) (τ : Fin k → Fin n)
    (hBl : ∀ i, B (Sum.inl i) = b i) (hBr : ∀ j, B (Sum.inr j) = Pi.single (τ j) 1) :
    (⇑B : Fin m ⊕ Fin k → Fin n → K) = Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K) := by
  funext x
  cases x with
  | inl i => exact hBl i
  | inr j => exact hBr j

theorem diag_posDef {n : ℕ} (d : Fin n → ℝ) (hd : ∀ x, 0 < d x) :
    (Matrix.diagonal fun x => (d x : ℂ)).PosDef :=
  PosDef.diagonal fun x => Complex.zero_lt_real.mpr (hd x)

end KLinesQuotGramLog

open KLinesQuotGramLog in

theorem LinesQuotGramLog.proof (h1 : LinesGramDetChange.Statement) (h2 : LinesCoordDet.Statement)
    (h3 : LinesGramFischerBound.Statement) (h4 : LinesGramPosDef.Statement) :
    LinesQuotGramLog.Statement := by
  intro K _ n m k d σ B b c τ hd hBl hBr hτ hli
  classical
  set H : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun x => (d x : ℂ) with hH
  have hHpd : H.PosDef := diag_posDef d hd
  have hBe := basis_eq_elim B b τ hBl hBr

  have hchg := h1 K n H σ (Fin m ⊕ Fin k) B (Sum.elim b c)
  obtain ⟨hdetP, hV⟩ := h2 K n m k B b c hBl hli
  set z : ℂ := σ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det with hz
  rw [hdetP] at hchg
  have hzc : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  rw [hzc] at hchg
  have hGu : (gramAt H σ (Sum.elim b c)).det.re = ‖z‖ ^ 2 * (gramAt H σ (⇑B)).det.re := by
    rw [hchg, Complex.re_ofReal_mul]

  have hliB : LinearIndependent K (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K)) := by
    rw [← hBe]; exact B.linearIndependent
  have hFis := h3 K n m k d σ b τ hd hτ hliB
  rw [← hBe] at hFis

  have hlib : LinearIndependent K b := hli.comp Sum.inl Sum.inl_injective
  have hGb : 0 < (gramAt H σ b).det.re :=
    MCDet.re_det_pos (h4 K n H σ (Fin m) b hHpd hlib)
  have hGB : 0 < (gramAt H σ (⇑B)).det.re :=
    MCDet.re_det_pos (h4 K n H σ (Fin m ⊕ Fin k) (⇑B) hHpd B.linearIndependent)
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hV)
  have hprod : 0 < ∏ j, d (τ j) := Finset.prod_pos fun j _ => hd (τ j)

  rw [hGu, Real.log_mul (pow_pos hz0 2).ne' hGB.ne', Real.log_pow]
  have hlog := Real.log_le_log hGB hFis
  rw [Real.log_mul hGb.ne' hprod.ne', Real.log_prod fun j _ => (hd (τ j)).ne'] at hlog
  push_cast
  linarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesQuotIndex

theorem genIndex_comap_of_surjective {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (f : G →+ G') (hf : Function.Surjective f) (H H' : AddSubgroup G') :
    genIndex (H.comap f) (H'.comap f) = genIndex H H' := by
  unfold genIndex
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf,
    AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf]

theorem coordProj_surjective {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) : Function.Surjective (coordProj B) :=
  (LinearMap.funLeft_surjective_of_injective K K Sum.inr Sum.inr_injective).comp
    B.equivFun.surjective

theorem ker_coordProj {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) :
    LinearMap.ker (coordProj B) = Submodule.span K (Set.range fun i => B (Sum.inl i)) := by
  ext v
  have hr : (Set.range fun i => B (Sum.inl i)) = B '' Set.range Sum.inl := by
    rw [← Set.range_comp]; rfl
  rw [hr, Module.Basis.mem_span_image, LinearMap.mem_ker]
  constructor
  · intro h x hx
    rcases x with i | j
    · exact ⟨i, rfl⟩
    · exact absurd (congr_fun h j) (by simpa [coordProj] using hx)
  · intro h
    funext j
    have : Sum.inr j ∉ (B.repr v).support := fun hj => by
      obtain ⟨i, hi⟩ := h hj
      exact Sum.inl_ne_inr hi
    simpa [coordProj] using this

end KLinesQuotIndex

open KLinesQuotIndex in
theorem LinesQuotIndex.proof : LinesQuotIndex.Statement := by
  intro K _ n m k B L c
  set π' := (coordProj B).restrictScalars (𝓞 K) with hπ'
  set W := (Submodule.span K (Set.range fun i => B (Sum.inl i))).restrictScalars (𝓞 K) with hW
  have hker : LinearMap.ker π' = W := by
    rw [hπ', LinearMap.ker_restrictScalars, ker_coordProj]
  have hsurj : Function.Surjective π'.toAddMonoidHom := coordProj_surjective B
  have hcomap : ∀ N : Submodule (𝓞 K) (Fin n → K),
      (N ⊔ W).toAddSubgroup = (N.map π').toAddSubgroup.comap π'.toAddMonoidHom := by
    intro N
    rw [← hker, ← Submodule.comap_map_eq]
    rfl
  have hspan : (Submodule.span (𝓞 K) (Set.range c)).map π' =
      Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hcomap, hcomap, genIndex_comap_of_surjective _ hsurj, hspan]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndexLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

theorem LinesQuotIndexLog.proof (h1 : LinesQuotIndexSplit.Statement)
    (h2 : LinesProjIndexLower.Statement) (h3 : LinesIdealIndexPos.Statement)
    (h4 : LinesProductFormula.Statement) (h5 : LinesCoordDet.Statement) :
    LinesQuotIndexLog.Statement := by
  intro K _ _ n m k a B b c τ ha hBl hBr hτ hli
  have hsplit := h1 K n m k a B b c τ ha hBl hBr hτ hli
  have hlow := h2 K n m k a B τ ha hBr hτ
  have hpos : 0 < ∏ j, idealIndex (a (τ j)) :=
    Finset.prod_pos fun j _ => h3 K (a (τ j)) (ha (τ j))
  have hdet := (h5 K n m k B b c hBl hli).2
  have hN : Algebra.norm ℚ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hdet
  have hpf := h4 K _ hdet
  have hGpos := lt_of_lt_of_le hpos hlow
  have hNabs : |((Algebra.norm ℚ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det : ℚ) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hN)
  rw [hsplit, Real.log_mul hGpos.ne' hNabs, hpf,
    ← Real.log_prod fun j _ => (h3 K (a (τ j)) (ha (τ j))).ne']
  exact add_le_add (Real.log_le_log hpos hlow) le_rfl

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndexSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace KLinesQuotIndexSplit

theorem colSpan_fg_span (K : Type) [Field K] [NumberField K] (k : ℕ)
    (V : Matrix (Fin k) (Fin k) K) (hV : V.det ≠ 0) :
    ((Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).restrictScalars
        ℤ).FG ∧
      Submodule.span K ((Submodule.span (𝓞 K)
          (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K)) : Submodule (𝓞 K) (Fin k → K)) :
            Set (Fin k → K)) = ⊤ := by
  refine ⟨(Submodule.fg_span (Set.finite_range _)).restrictScalars, ?_⟩
  rw [Submodule.span_span_of_tower]
  have hr : (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K)) =
      (Matrix.mulVecLin V) '' Set.range (Pi.basisFun K (Fin k)) := by
    rw [← Set.range_comp]
    congr 1
    funext j
    simp [Pi.basisFun_apply]
  have hs : Function.Surjective (Matrix.mulVecLin V) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det V).mpr hV.isUnit)
  rw [hr, Submodule.span_image, (Pi.basisFun K (Fin k)).span_eq, Submodule.map_top,
    LinearMap.range_eq_top.mpr hs]

end KLinesQuotIndexSplit

open KLinesQuotIndexSplit in

theorem LinesQuotIndexSplit.proof (h1 : LinesQuotIndex.Statement) (h2 : LinesCoordImage.Statement)
    (h3 : LinesCoordDet.Statement) (h4 : LinesIsLattice.Statement)
    (h5 : LinesGenIndexTrans.Statement) (h6 : LinesStdIndexDet.Statement)
    (h7 : LinesProjLattice.Statement) : LinesQuotIndexSplit.Statement := by
  intro K _ _ n m k a B b c τ ha hb hτ hinj hli
  set V := (B.toMatrix (Sum.elim b c)).toBlocks₂₂ with hVdef
  have hdet : V.det ≠ 0 := (h3 K n m k B b c hb hli).2
  have hbB : (fun i => B (Sum.inl i)) = b := funext hb
  have hc : coordProj B ∘ c = fun j => V *ᵥ (Pi.single j 1 : Fin k → K) :=
    funext fun j => h2 K n m k B b c j
  rw [← hbB, h1 K n m k B (idealLattice a) c, hc]
  obtain ⟨hPfg, hPspan, -⟩ := h7 K n m k a B τ ha hτ hinj
  have hP := h4 K (Fin k) _ hPfg hPspan
  have hSfg : ((stdLattice K k).restrictScalars ℤ).FG :=
    (Submodule.fg_span (Set.finite_range _)).restrictScalars
  have hSspan : Submodule.span K ((stdLattice K k : Submodule (𝓞 K) (Fin k → K)) :
      Set (Fin k → K)) = ⊤ := by
    rw [stdLattice, Submodule.span_span_of_tower]
    have : (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
        Set.range (Pi.basisFun K (Fin k)) := by
      ext v; simp [Pi.basisFun_apply]
    rw [this, (Pi.basisFun K (Fin k)).span_eq]
  have hS := h4 K (Fin k) _ hSfg hSspan
  obtain ⟨hCfg, hCspan⟩ := colSpan_fg_span K k V hdet
  have hC := h4 K (Fin k) _ hCfg hCspan
  have e : genIndex ((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))).toAddSubgroup
        (stdLattice K k).toAddSubgroup *
      genIndex (stdLattice K k).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup =
      genIndex ((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup :=
    (h5 (Fin k → K) _ _ _ hP hS hC).2
  rw [← e, h6 K k V hdet]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesStdIndexDet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped Pointwise

noncomputable section

namespace KLinesStdIndexDet

theorem span_toAddSubgroup_eq_closure (K : Type) [Field K] [NumberField K] (k : ℕ)
    (f : (Fin k → K) →ₗ[K] (Fin k → K)) :
    (Submodule.span (𝓞 K) (Set.range fun j : Fin k => f (Pi.single j 1))).toAddSubgroup =
      AddSubgroup.closure (Set.range fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k =>
        integralBasis K p.1 • f (Pi.single p.2 1)) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  have hs : Submodule.span ℤ (Set.range (RingOfIntegers.basis K)) = ⊤ :=
    (RingOfIntegers.basis K).span_eq
  have h := Submodule.span_smul_of_span_eq_top hs
    (Set.range fun j : Fin k => f (Pi.single j 1))
  have hr : (Set.range (RingOfIntegers.basis K) • Set.range fun j : Fin k => f (Pi.single j 1)) =
      Set.range fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k =>
        integralBasis K p.1 • f (Pi.single p.2 1) := by
    rw [Set.range_smul_range]
    congr 1
    funext p
    rw [integralBasis_apply, algebraMap_smul]
  rw [hr] at h
  rw [h]
  rfl

end KLinesStdIndexDet

open KLinesStdIndexDet in

theorem LinesStdIndexDet.proof (h1 : LinesGenIndexDet.Statement) : LinesStdIndexDet.Statement := by
  classical
  intro K _ _ k V hV
  let B0 : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k) ℚ (Fin k → K) :=
    (integralBasis K).smulTower (Pi.basisFun K (Fin k))
  have hB0 : ∀ p, B0 p = integralBasis K p.1 • (Pi.single p.2 1 : Fin k → K) := by
    intro p
    simp only [B0, Module.Basis.smulTower_apply, Pi.basisFun_apply]
  let Ve : (Fin k → K) ≃ₗ[K] (Fin k → K) :=
    Matrix.toLinearEquiv' V (Matrix.invertibleOfIsUnitDet V (Ne.isUnit hV))
  have hVe : ∀ v, Ve v = V *ᵥ v := fun v => rfl
  let Vq : (Fin k → K) ≃ₗ[ℚ] (Fin k → K) := Ve.restrictScalars ℚ
  have hA : (stdLattice K k).toAddSubgroup = AddSubgroup.closure (Set.range B0) := by
    have := span_toAddSubgroup_eq_closure K k LinearMap.id
    simp only [LinearMap.id_apply] at this
    rw [stdLattice, this]
    exact congrArg (fun s => AddSubgroup.closure s)
      (congrArg Set.range (funext fun p => (hB0 p).symm))
  have hB : (Submodule.span (𝓞 K)
        (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup =
      AddSubgroup.closure (Set.range (B0.map Vq)) := by
    have := span_toAddSubgroup_eq_closure K k (Matrix.toLin' V)
    simp only [Matrix.toLin'_apply] at this
    rw [this]
    refine congrArg (fun s => AddSubgroup.closure s)
      (congrArg Set.range (funext fun p => ?_))
    rw [Module.Basis.map_apply, hB0]
    change _ = Ve _
    rw [map_smul, hVe]
  rw [h1 (Fin k → K) _ B0 (B0.map Vq) _ _ hA hB]
  have hdet : B0.det (B0.map Vq) = Algebra.norm ℚ V.det := by
    have hc : (⇑(B0.map Vq) : _ → Fin k → K) = (Vq : (Fin k → K) →ₗ[ℚ] (Fin k → K)) ∘ B0 := by
      funext p
      rfl
    rw [hc, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
    have hq : (Vq : (Fin k → K) →ₗ[ℚ] (Fin k → K)) = (Matrix.toLin' V).restrictScalars ℚ := by
      ext v
      rfl
    rw [hq, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  rw [hdet]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesStdPi
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesStdPi

theorem eq_sum_smul_single {K : Type*} [Field K] {k : ℕ} (y : Fin k → 𝓞 K) :
    (fun i => algebraMap (𝓞 K) K (y i)) = ∑ j, y j • (Pi.single j 1 : Fin k → K) := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, Algebra.smul_def, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end KLinesStdPi

theorem LinesStdPi.proof : LinesStdPi.Statement := by
  intro K _ k
  ext v
  simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      dsimp only
      rw [Pi.single_apply]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => intro i; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro i; exact Submodule.add_mem _ (hx i) (hy i)
    | smul a x _ hx => intro i; exact Submodule.smul_mem _ a (hx i)
  · intro hv
    choose y hy using fun i => Submodule.mem_one.mp (hv i)
    have hv' : v = fun i => algebraMap (𝓞 K) K (y i) := funext fun i => (hy i).symm
    rw [hv', KLinesStdPi.eq_sum_smul_single]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem OrthogonalLines.proof (hQ : LinesQuotDegreeBound.Statement)
    (hL : LinesLineDegree.Statement) : OrthogonalLines.Statement := by
  intro K _ _ n a d ha hd _ μ hμ m k b c hbc hmk
  obtain ⟨τ, -, hτ⟩ := hQ K n a d ha hd m k b c hbc hmk
  have hf : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have key : ∀ j, (Module.finrank ℚ K : ℝ) * μ ≤
      Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j)) := by
    intro j
    have h := hμ (τ j)
    rw [hL K n a d (τ j), normalise, le_div_iff₀ hf] at h
    linarith
  have hsum : ∑ _j : Fin k, (Module.finrank ℚ K : ℝ) * μ ≤
      ∑ j, (Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j))) :=
    Finset.sum_le_sum fun j _ => key j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [normalise, le_div_iff₀ hf]
  have e : (k : ℝ) * μ * (Module.finrank ℚ K : ℝ) = (k : ℝ) * ((Module.finrank ℚ K : ℝ) * μ) := by
    ring
  linarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootArithVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootArithmeticVariety

theorem isIntegral_of_pow_eq_one {x : ℂ} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by
    simp [Polynomial.eval₂_sub, h]⟩

theorem isIntegral_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem (integralClosure ℤ ℂ) fun σ _ => ?_
  rw [Units.smul_def]
  refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ => hM (σ i) i) _

theorem isIntegral_onePipe {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, IsIntegral ℤ (Z a b))
    (a : Fin j) (b : Fin (j + m)) : IsIntegral ℤ (onePipe Z a b) := by
  simp only [onePipe, Matrix.of_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) b
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    exact hZ a i

theorem isIntegral_rootCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine isIntegral_det _ fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id]
  refine isIntegral_onePipe _ (fun a b => ?_) _ _
  obtain ⟨k, hk, h⟩ := hζ p.1 a b
  exact isIntegral_of_pow_eq_one hk h

end RootArithmeticVariety

open RootArithmeticVariety in

theorem RootArithVar.proof (h : CoordConeArithVar.Statement) : RootArithVar.Statement := by
  intro f j m ζ hf hζ
  have hK : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have := h (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) (fun _ => plAnchor j m) 0 Fin.elim0 hK
    (fun k => by simp [rootCoord, anchor_minor]) (algebraicIndependent_empty_type)
    (fun i => Fin.elim0 i) ?_
  · simpa [rootPointIdeal] using this
  · rintro r ⟨p, rfl⟩
    have h1 : IsIntegral ℚ (rootCoord ζ p / rootCoord ζ ⟨p.1, plAnchor j m⟩) := by
      simp only [rootCoord, anchor_minor, div_one]
      exact (isIntegral_rootCoord ζ hζ p).tower_top
    exact (h1.tower_top (A := IntermediateField.adjoin ℚ (Set.range (Fin.elim0 : Fin 0 → ℂ)))).isAlgebraic

end

end GroundTheory.Heights₂.Heights
end


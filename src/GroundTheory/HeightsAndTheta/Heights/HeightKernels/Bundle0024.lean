import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramPosDef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGramPosDef

open Matrix

variable {K : Type*} [Field K] {n : ℕ} {ι : Type*}

theorem gramAt_eq (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (u : ι → Fin n → K) :
    gramAt h σ u = (((Matrix.of fun j a => u a j).map σ)ᴴ * h *
      (Matrix.of fun j a => u a j).map σ) := by
  ext a b
  simp [gramAt, embVec, Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem mulVec_injective [Fintype ι] (σ : K →+* ℂ) (u : ι → Fin n → K) (hu : LinearIndependent K u) :
    Function.Injective ((Matrix.of fun j a => u a j).map σ).mulVec := by
  classical
  set Uk : Matrix (Fin n) ι K := Matrix.of fun j a => u a j with hUk
  have hinj : LinearMap.ker Uk.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Fintype.linearIndependent_iff] at hu
    funext a
    refine hu c ?_ a
    funext j
    have := congrFun hc j
    simpa [Uk, Matrix.mulVec, dotProduct, mul_comm] using this
  obtain ⟨g, hg⟩ := Uk.mulVecLin.exists_leftInverse_of_injective hinj
  set Lk : Matrix ι (Fin n) K := LinearMap.toMatrix' g
  have hL : Lk * Uk = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin'] at this
  have hLσ : Lk.map σ * Uk.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have := congrArg (fun v => (Lk.map σ) *ᵥ v) hxy
  simpa [Matrix.mulVec_mulVec, hLσ] using this

end KLinesGramPosDef

open KLinesGramPosDef Matrix ComplexOrder in

theorem LinesGramPosDef.proof : LinesGramPosDef.Statement := by
  intro K _ n h σ ι _ u hh hu
  rw [gramAt_eq]
  exact hh.conjTranspose_mul_mul_same (mulVec_injective σ u hu)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealIndexPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesIdealIndexPos

variable {K : Type} [Field K] [NumberField K]

noncomputable def toOne (K : Type) [Field K] : K →ₗ[𝓞 K] (Unit → K) :=
  LinearMap.pi fun _ => LinearMap.id

omit [NumberField K] in
theorem toOne_injective : Function.Injective (toOne K) := fun _ _ h =>
  congrFun h ()

theorem fg_and_span (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) :
    (((J : Submodule (𝓞 K) K).map (toOne K)).restrictScalars ℤ).FG ∧
      Submodule.span K (((J : Submodule (𝓞 K) K).map (toOne K) : Submodule (𝓞 K) (Unit → K)) :
        Set (Unit → K)) = ⊤ := by
  refine ⟨((FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map _).restrictScalars, ?_⟩
  obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hJ)
  refine eq_top_iff.mpr fun v _ => ?_
  have hmem : toOne K x ∈ Submodule.span K (((J : Submodule (𝓞 K) K).map (toOne K) :
      Submodule (𝓞 K) (Unit → K)) : Set (Unit → K)) :=
    Submodule.subset_span (Submodule.mem_map_of_mem hxJ)
  have hv : v = (v () / x) • toOne K x := by
    funext u
    simp [toOne, div_mul_cancel₀ _ hx0]
  rw [hv]
  exact Submodule.smul_mem _ _ hmem

end KLinesIdealIndexPos

open KLinesIdealIndexPos in

theorem LinesIdealIndexPos.proof (h1 : LinesIsLattice.Statement) (h2 : LinesGenIndexTrans.Statement) :
    LinesIdealIndexPos.Statement := by
  intro K _ _ I hI
  have hL : ∀ J : FractionalIdeal (𝓞 K)⁰ K, J ≠ 0 →
      Submodule.IsLattice ℚ (((J : Submodule (𝓞 K) K).map (toOne K)).restrictScalars ℤ) :=
    fun J hJ => h1 K Unit _ (fg_and_span J hJ).1 (fg_and_span J hJ).2
  have hpos := (h2 (Unit → K) _ _ _ (hL I hI) (hL 1 one_ne_zero) (hL 1 one_ne_zero)).1
  have hmap : ∀ A B : AddSubgroup K, genIndex (A.map ((toOne K : K →+ (Unit → K))))
      (B.map (toOne K : K →+ (Unit → K))) = genIndex A B := by
    intro A B
    have hinj : Function.Injective (toOne K : K →+ (Unit → K)) := toOne_injective
    simp only [genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  rw [FractionalIdeal.coe_one] at hpos
  unfold idealIndex
  rw [← hmap]
  exact hpos

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesIdealLatticeFG

theorem idealLattice_eq_iSup (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice a = ⨆ x, Submodule.map (LinearMap.single (𝓞 K) (fun _ : Fin n => K) x)
      (a x : Submodule (𝓞 K) K) :=
  (Submodule.iSup_map_single).symm

theorem fg (K : Type) [Field K] [NumberField K] {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).FG := by
  rw [idealLattice_eq_iSup]
  exact Submodule.fg_iSup _ fun x =>
    ((a x).fg_of_isNoetherianRing le_rfl).map _

theorem single_mem_span (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) (hx : a x ≠ 0) :
    (Pi.single x 1 : Fin n → K) ∈ Submodule.span K (idealLattice a : Set (Fin n → K)) := by
  have hbot : (a x : Submodule (𝓞 K) K) ≠ ⊥ := by
    rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hmem : (Pi.single x y : Fin n → K) ∈ idealLattice a := by
    rw [idealLattice, Submodule.mem_pi]
    intro i _
    by_cases h : i = x
    · subst h; simpa using hy
    · simp [h]
  have heq : (Pi.single x 1 : Fin n → K) = y⁻¹ • (Pi.single x y : Fin n → K) := by
    ext i
    by_cases h : i = x
    · subst h; simp [hy0]
    · simp [h]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end KLinesIdealLatticeFG

open KLinesIdealLatticeFG in

theorem LinesIdealLatticeFG.proof : LinesIdealLatticeFG.Statement := by
  intro K _ _ n a ha
  refine ⟨fg K a, ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [Pi.basisFun_apply]
  exact single_mem_span K a x (ha x)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealStdIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesIdealStdIndex

theorem idealLattice_toAddSubgroup {K : Type} [Field K] {k : ℕ}
    (a : Fin k → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).toAddSubgroup =
      AddSubgroup.pi Set.univ fun j => (a j : Submodule (𝓞 K) K).toAddSubgroup := by
  ext x
  simp [idealLattice, Submodule.mem_pi, AddSubgroup.mem_pi]

end KLinesIdealStdIndex

open KLinesIdealStdIndex in

theorem LinesIdealStdIndex.proof (h1 : LinesGenIndexPi.Statement) (h2 : LinesStdPi.Statement) :
    LinesIdealStdIndex.Statement := by
  intro K _ _ k a
  rw [idealLattice_toAddSubgroup, h2 K k, h1 (Fin k) K]
  rfl

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesIsLattice

theorem smul_mem_span_of_mem {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K} (hv : v ∈ M) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  rw [← (integralBasis K).sum_repr t, Finset.sum_smul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_assoc, integralBasis_apply, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (M.smul_mem _ hv))

theorem smul_mem_span {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K}
    (hv : v ∈ Submodule.span ℚ (M : Set (ι → K))) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact smul_mem_span_of_mem M t hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ q hx

def qSpan {K : Type} [Field K] [NumberField K] {ι : Type} (M : Submodule (𝓞 K) (ι → K)) :
    Submodule K (ι → K) where
  carrier := Submodule.span ℚ (M : Set (ι → K))
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' t _ hv := smul_mem_span M t hv

end KLinesIsLattice

theorem LinesIsLattice.proof : LinesIsLattice.Statement := by
  intro K _ _ ι _ M hfg hspan
  refine ⟨hfg, ?_⟩
  have hMN : Submodule.span K (M : Set (ι → K)) ≤ KLinesIsLattice.qSpan M :=
    Submodule.span_le.mpr fun v hv => Submodule.subset_span hv
  rw [hspan, top_le_iff] at hMN
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ KLinesIsLattice.qSpan M := hMN ▸ Submodule.mem_top
  exact hv

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LinesLatticeBasis.proof : LinesLatticeBasis.Statement := by
  intro V _ _ _ ι _ hcard M hM
  let b0 := Module.Free.chooseBasis ℤ M
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M) ℚ V := b0.extendOfIsLattice ℚ
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = Fintype.card ι := by
    rw [hcard, Module.finrank_eq_card_basis B]
  let e := Fintype.equivOfCardEq hc
  refine ⟨B.reindex e, ?_⟩
  rw [Module.Basis.range_reindex]
  have hB : Set.range B = M.subtype '' Set.range b0 := by
    rw [← Set.range_comp]
    ext x
    simp [B, Module.Basis.extendOfIsLattice_apply]
  rw [hB, ← Submodule.map_span, b0.span_eq, Submodule.map_top, Submodule.range_subtype]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped nonZeroDivisors

noncomputable section

namespace KLinesLineDegree

variable {K : Type} [Field K] {n : ℕ}

theorem genIndex_map_of_injective {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]

theorem single_injective (x : Fin n) :
    Function.Injective (AddMonoidHom.single (fun _ : Fin n => K) x) := by
  intro s t h
  simpa using congrFun h x

theorem inter_line (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) :
    (idealLattice a ⊓ (Submodule.span K
        (Set.range fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).restrictScalars (𝓞 K)).toAddSubgroup =
      ((a x : Submodule (𝓞 K) K).toAddSubgroup).map (AddMonoidHom.single (fun _ : Fin n => K) x) := by
  ext v
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Set.range_const, Submodule.mem_span_singleton, AddSubgroup.mem_map, AddMonoidHom.single_apply]
  constructor
  · rintro ⟨hv, t, rfl⟩
    refine ⟨t, ?_, ?_⟩
    · have h := (Submodule.mem_pi.mp hv) x (Set.mem_univ _)
      simpa using h
    · rw [← Pi.single_smul', smul_eq_mul, mul_one]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, t, ?_⟩
    · rw [idealLattice, Submodule.mem_pi]
      intro y _
      by_cases hy : y = x
      · subst hy
        simpa using ht
      · simp only [Pi.single_apply, hy, if_false]
        exact zero_mem _
    · rw [← Pi.single_smul', smul_eq_mul, mul_one]

theorem span_line (x : Fin n) :
    (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).toAddSubgroup =
      ((1 : Submodule (𝓞 K) K).toAddSubgroup).map (AddMonoidHom.single (fun _ : Fin n => K) x) := by
  ext v
  simp only [Submodule.mem_toAddSubgroup, Set.range_const, Submodule.mem_span_singleton,
    AddSubgroup.mem_map, Submodule.mem_one, AddMonoidHom.single_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨algebraMap (𝓞 K) K y, ⟨y, rfl⟩, by rw [← Pi.single_smul', Algebra.smul_def, mul_one]⟩
  · rintro ⟨t, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, by rw [← Pi.single_smul', Algebra.smul_def, mul_one]⟩

theorem gram_line (d : (K →+* ℂ) → Fin n → ℝ) (σ : K →+* ℂ) (x : Fin n) :
    (gramAt (diagMetric d σ) σ (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).det.re = d σ x := by
  rw [Matrix.det_unique]
  simp [gramAt, diagMetric, embVec, dotProduct, Matrix.mulVec_diagonal, Pi.single_apply]

end KLinesLineDegree

open KLinesLineDegree in

theorem LinesLineDegree.proof : LinesLineDegree.Statement := by
  intro K _ _ n a d x
  unfold subDegree idealIndex
  rw [inter_line, span_line, genIndex_map_of_injective _ (single_injective x)]
  simp only [gram_line]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProductFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesProductFormula

theorem prod_norm_embeddings (K : Type) [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  classical
  have h := congr_arg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖)
    (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]] at h
  rw [← h, eq_ratCast, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_ratCast]

end KLinesProductFormula

theorem LinesProductFormula.proof : LinesProductFormula.Statement := by
  intro K _ _ x hx
  rw [← KLinesProductFormula.prod_norm_embeddings K x, Real.log_prod]
  intro σ _
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProjIndexLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace KLinesProjIndexLower

theorem stdLattice_fg (K : Type) [Field K] [NumberField K] (k : ℕ) :
    ((stdLattice K k).restrictScalars ℤ).FG :=
  (Submodule.fg_span (Set.finite_range _)).restrictScalars

theorem stdLattice_span (K : Type) [Field K] [NumberField K] (k : ℕ) :
    Submodule.span K ((stdLattice K k : Submodule (𝓞 K) (Fin k → K)) : Set (Fin k → K)) = ⊤ :=
  (HermLattice.standard K k).span_eq

end KLinesProjIndexLower

open KLinesProjIndexLower in

theorem LinesProjIndexLower.proof (h1 : LinesProjLattice.Statement)
    (h2 : LinesIdealLatticeFG.Statement) (h3 : LinesIsLattice.Statement)
    (h4 : LinesGenIndexMono.Statement) (h5 : LinesIdealStdIndex.Statement) :
    LinesProjIndexLower.Statement := by
  intro K _ _ n m k a B τ ha hB hτ
  obtain ⟨hPfg, hPspan, hle⟩ := h1 K n m k a B τ ha hB hτ
  obtain ⟨hAfg, hAspan⟩ := h2 K k (fun j => a (τ j)) (fun j => ha (τ j))
  have hA := h3 K (Fin k) _ hAfg.restrictScalars hAspan
  have hP := h3 K (Fin k) _ hPfg hPspan
  have hS := h3 K (Fin k) _ (stdLattice_fg K k) (stdLattice_span K k)
  have key := h4 (Fin k → K) _ _ _ hA hP hS (Submodule.restrictScalars_mono ℤ hle)
  rw [← h5 K k (fun j => a (τ j))]
  exact key

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProjLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesProjLattice

theorem coordProj_surjective {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) : Function.Surjective (coordProj B) := by
  unfold coordProj
  rw [LinearMap.coe_comp]
  exact (LinearMap.funLeft_surjective_of_injective K K Sum.inr Sum.inr_injective).comp
    B.equivFun.surjective

theorem coordProj_basis_inr {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (j : Fin k) :
    coordProj B (B (Sum.inr j)) = Pi.single j 1 := by
  ext i
  simp only [coordProj, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.funLeft_apply, Module.Basis.equivFun_self]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end KLinesProjLattice

open KLinesProjLattice in

theorem LinesProjLattice.proof (h1 : LinesIdealLatticeFG.Statement) : LinesProjLattice.Statement := by
  intro K _ _ n m k a B τ ha hB hτ
  obtain ⟨hfg, hspan⟩ := h1 K n a ha
  refine ⟨?_, ?_, ?_⟩
  · exact (hfg.map ((coordProj B).restrictScalars (𝓞 K))).restrictScalars
  · rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan,
      Submodule.map_top, LinearMap.range_eq_top]
    exact coordProj_surjective B
  · intro v hv
    have hv' : ∀ j, v j ∈ (a (τ j) : Submodule (𝓞 K) K) := fun j =>
      (Submodule.mem_pi (I := Set.univ)).1 hv j (Set.mem_univ j)
    refine ⟨∑ j, v j • (Pi.single (τ j) 1 : Fin n → K), ?_, ?_⟩
    · refine (Submodule.mem_pi (I := Set.univ)).2 fun x _ => ?_
      rw [Finset.sum_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases h : τ j = x
      · subst h; simpa using hv' j
      · simp [Pi.single_eq_of_ne' h]
    · simp only [LinearMap.restrictScalars_apply, map_sum, map_smul, ← hB, coordProj_basis_inr]
      ext i
      simp [Pi.single_apply]

end GroundTheory.Heights₂.Heights
end


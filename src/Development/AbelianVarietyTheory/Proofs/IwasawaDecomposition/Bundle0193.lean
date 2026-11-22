import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0182
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0186
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeProdFormula

theorem card_residue (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  obtain ⟨a, ha⟩ := GlobalTheory.HaarLatticeScale.exists_valued_eq_exp F v (-1)
  have ha1 : a ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp _).2 ha.le).le
  have h := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 ⟨a, ha1⟩ 1
    (by simpa using ha)
  have e : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {⟨a, ha1⟩} := by
    ext y
    rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v
      (by change Valued.v a ≠ 0; rw [ha]; exact WithZero.exp_ne_zero)]
    change _ ↔ _ ≤ Valued.v a
    rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  rw [pow_one, ← e] at h
  exact h

theorem modu_finite (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v)
    (hx : x ≠ 0) : (modu (Fv F v) x : ℝ) = ‖x‖ := by
  have hu : IsUnit x := hx.isUnit
  have hv : Valued.v x ≠ 0 := by simpa using hx
  let μ : Measure (Fv F v) := Measure.addHaar
  have h := GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp F v (Fv F v) μ Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm (WithZero.log (Valued.v x))
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have e0 : (v.adicCompletionIntegers F : Set (Fv F v)) = Metric.closedBall 0 1 := by
    ext y
    rw [mem_closedBall_zero_iff, Valued.toNormedField.norm_le_one_iff]
    rfl
  have h0 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
  have h1 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ ∞ := by
    rw [e0]; exact (isCompact_closedBall _ _).measure_lt_top.ne
  have e1 : {y : Fv F v | ∀ i, Valued.v ((ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i) ≤
      WithZero.exp (WithZero.log (Valued.v x))} = hu.unit • (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, WithZero.exp_log hv, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
      Units.val_inv_eq_inv_val, map_inv₀, IsUnit.unit_spec, inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
    simp
  have e2 : {y : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp
  rw [e1, e2, Measure.real, ← distribHaarChar_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, card_residue,
    Fintype.card_unit, pow_one] at h
  have h2 := mul_right_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h
  rw [modu, dif_pos hu, h2, FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  push_cast
  congr 1
  conv_lhs => rw [← WithZero.coe_unzero hv]
  rfl

theorem distribHaarChar_pi_real (ι : Type) [Fintype ι] (u : (ι → ℝ)ˣ) :
    (distribHaarChar (ι → ℝ) u : ℝ) = ∏ i, |(u : ι → ℝ) i| := by
  have hu : ∀ i, (u : ι → ℝ) i ≠ 0 := fun i => ((Pi.isUnit_iff.1 u.isUnit) i).ne_zero
  have hp : (volume : Measure (ι → ℝ)) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]; simp
  have e : u • (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) =
      Set.univ.pi fun i => (u : ι → ℝ) i • Set.Icc (0 : ℝ) 1 := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hu i), Units.smul_def, smul_eq_mul, smul_eq_mul, Pi.mul_apply]
    have : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i = ((u : ι → ℝ) i)⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrFun u.inv_mul i)
    rw [this]
  rw [distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume)
    (s := Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) (r := ∏ i, ‖(u : ι → ℝ) i‖₊) (by rw [hp]; simp) (by rw [hp]; simp)]
  · simp
  · rw [hp, e, volume_pi_pi, mul_one, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.addHaar_smul]
    rw [Module.finrank_self, pow_one, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one,
      ← Real.enorm_eq_ofReal_abs]
    rfl

theorem modu_infinite (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ainf F) (hx : IsUnit x) :
    (modu (Ainf F) x : ℝ) = ∏ w : InfinitePlace F, ‖x w‖ := by
  let r : Ainf F ≃+* (InfinitePlace F → ℝ) := RingEquiv.piCongrRight fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  let e : Ainf F ≃ₜ+ (InfinitePlace F → ℝ) :=
    { r.toAddEquiv with
      continuous_toFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
          (continuous_apply w)
      continuous_invFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous.comp
          (continuous_apply w) }
  have h := GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e hx.unit
    (Units.map (r : Ainf F →* (InfinitePlace F → ℝ)) hx.unit) (fun y => map_mul r x y)
  rw [modu, dif_pos hx, ← h, distribHaarChar_pi_real]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal w)).norm_map_of_map_zero (map_zero _) (x w)

theorem prod_modu_eq_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : F), e ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v) (algebraMap F (Fv F v) e)).Finite ∧ modu (Ainf F) (algebraMap F (Ainf F) e) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) = 1 := by
  intro F _ _ _ e he
  have hf : ∀ v : HeightOneSpectrum (𝓞 F), (modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ) =
      FinitePlace.equivHeightOneSpectrum.symm v e := fun v => by
    rw [modu_finite F v _ ((map_ne_zero _).2 he)]
    rfl
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      modu (Fv F v) (algebraMap F (Fv F v) e)).Finite := by
    refine ((FinitePlace.hasFiniteMulSupport he).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn).subset fun v hv h => hv ?_
    apply NNReal.coe_injective
    rw [hf]
    exact h
  refine ⟨hfin, NNReal.coe_injective ?_⟩
  have h1 : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ≥0) : ℝ) =
      ∏ᶠ w : FinitePlace F, w e := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [← hf]
    exact (NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.map_finprod hfin
  rw [NNReal.coe_mul, h1, modu_infinite F _ (he.isUnit.map _), NNReal.coe_one, ← prod_abs_eq_one he]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  exact InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 e)

end GlobalTheory.GaugeProdFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtGaussianParametersAtIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss.ParDer

variable {l m n : Type} [Fintype m]

theorem der_mul {M : ℝ → Matrix l m ℂ} {N : ℝ → Matrix m n ℂ} {M' : Matrix l m ℂ} {N' : Matrix m n ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hN : ∀ i j, HasDerivAt (fun t => N t i j) (N' i j) s)
    (i : l) (j : n) : HasDerivAt (fun t => (M t * N t) i j) ((M' * N s + M s * N') i j) s := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hM i k).fun_mul (hN k j)

theorem der_dot {u v : ℝ → m → ℂ} {u' v' : m → ℂ} {s : ℝ}
    (hu : ∀ i, HasDerivAt (fun t => u t i) (u' i) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) :
    HasDerivAt (fun t => u t ⬝ᵥ v t) (u' ⬝ᵥ v s + u s ⬝ᵥ v') s := by
  simp only [dotProduct, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hu k).fun_mul (hv k)

theorem der_mulVec {M : ℝ → Matrix l m ℂ} {v : ℝ → m → ℂ} {M' : Matrix l m ℂ} {v' : m → ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s)
    (i : l) : HasDerivAt (fun t => (M t *ᵥ v t) i) ((M' *ᵥ v s + M s *ᵥ v') i) s :=
  der_dot (u := fun t => M t i) (u' := M' i) (hM i) hv

theorem der_vecMul {M : ℝ → Matrix m n ℂ} {v : ℝ → m → ℂ} {M' : Matrix m n ℂ} {v' : m → ℂ} {s : ℝ}
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (j : n) : HasDerivAt (fun t => (v t ᵥ* M t) j) ((v' ᵥ* M s + v s ᵥ* M') j) s :=
  der_dot (v := fun t i => M t i j) (v' := fun i => M' i j) hv fun i => hM i j

theorem par_deriv : ∀ (P Q : ℕ) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (Z : Mat P Q) (g g' : ℝ → Mat P Q), g 0 = 1 → g' 0 = 1 → (∀ a b, HasDerivAt (fun t => g t a b) (Z a b) 0) → (∀ a b, HasDerivAt (fun t => g' t a b) (-Z a b) 0) → (∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0) ∧ (∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0) ∧ HasDerivAt (fun t => scal (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t)) (dS Z A x) 0 := by
  intro P Q A x Z g g' h0 h0' hg hg'
  have hY : ∀ i j, HasDerivAt (fun t => (g t * baseY A) i j) ((Z * baseY A) i j) 0 := fun i j => by
    simpa using der_mul (N := fun _ => baseY A) (N' := 0) hg (fun _ _ => hasDerivAt_const _ _) i j
  have hZ : Z * baseY A = Matrix.fromRows (Z.toBlocks₁₁ * A + Z.toBlocks₁₂) (Z.toBlocks₂₁ * A + Z.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Z, baseY, Matrix.fromBlocks_mul_fromRows]
    simp
  have hY1 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₁ i j) ((Z.toBlocks₁₁ * A + Z.toBlocks₁₂) i j) 0 :=
    fun i j => by have := hY (.inl i) j; rw [hZ] at this; exact this
  have hY2 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₂ i j) ((Z.toBlocks₂₁ * A + Z.toBlocks₂₂) i j) 0 :=
    fun i j => by have := hY (.inr i) j; rw [hZ] at this; exact this
  have e2 : (g 0 * baseY A).toRows₂ = 1 := by rw [h0, Matrix.one_mul]; rfl
  have e1 : (g 0 * baseY A).toRows₁ = A := by rw [h0, Matrix.one_mul]; rfl
  obtain ⟨hdet, hinv⟩ := GlobalTheory.T.hasDerivAt_inv_det_and_inv_at_identity Q (fun t => (g t * baseY A).toRows₂) _ e2 hY2
  have hA : ∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0 := fun i j => by
    have := der_mul (N' := -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂)) hY1 hinv i j
    rw [e1, e2, inv_one, Matrix.mul_one, Matrix.mul_neg, ← sub_eq_add_neg] at this
    exact this
  have eA : matA (g 0 * baseY A) = A := by rw [h0, Matrix.one_mul, matA_baseY]
  have hv : ∀ i, HasDerivAt (fun t => (g t *ᵥ baseV x) i) ((Z *ᵥ baseV x) i) 0 := fun i => by
    simpa using der_mulVec (v := fun _ => baseV x) (v' := 0) hg (fun _ => hasDerivAt_const _ _) i
  have hf : ∀ i, HasDerivAt (fun t => (baseF x ᵥ* g' t) i) ((baseF x ᵥ* (-Z)) i) 0 := fun i => by
    simpa using der_vecMul (v := fun _ => baseF x) (v' := 0) (M' := -Z) (fun _ => hasDerivAt_const _ _) hg' i
  have hv1 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inl) i) ((Z.toBlocks₁₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inl i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₁₁])
  have hv2 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inr) i) ((Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inr i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf1 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inl) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₁)) i) 0 :=
    fun i => (hf (.inl i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf2 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inr) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₂)) i) 0 :=
    fun i => (hf (.inr i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₂])
  have ev : (g 0 *ᵥ baseV x) ∘ Sum.inr = 0 := by rw [h0, Matrix.one_mulVec]; rfl
  have ef : (baseF x ᵥ* g' 0) ∘ Sum.inl = 0 := by rw [h0', Matrix.vecMul_one]; rfl
  have hX : ∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0 := by
    rintro (i | j)
    · refine ((hv1 i).fun_sub (der_mulVec hA hv2 i)).congr_deriv ?_
      rw [ev, eA]
      simp [dX, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    · refine ((der_vecMul hf1 hA j).fun_add (hf2 j)).congr_deriv ?_
      rw [ef, eA]
      simp [dX, Matrix.vecMul_add, Matrix.neg_vecMul, Matrix.vecMul_vecMul, add_comm]
  refine ⟨hA, hX, ?_⟩
  have hd := der_dot (u := fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) ∘ Sum.inr)
    (u' := dX Z A x ∘ Sum.inr) (fun j => hX (.inr j)) hv2
  refine (hdet.fun_mul hd.fun_neg.cexp).congr_deriv ?_
  simp only [ev, e2]
  rw [h0, h0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, linX_base]
  simp [dS, sub_eq_add_neg]

end GlobalTheory.OscGauss.ParDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticFormOrbitRationalVectorEq
section
noncomputable section

namespace GlobalTheory.GaugeEx.OrbitQuadric

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem hform_eq_dot {A : Type} [CommRing A] (s : A →+* A) (G : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  unfold Formalism.UG.hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_mulVec_of_cT_mul_mul_eq {A : Type} [CommRing A] (s : A →+* A)
    (G g : Matrix (Fin M) (Fin M) A) (hg : Formalism.UG.cT s g * G * g = G) (x y : Fin M → A) :
    Formalism.UG.hform s G (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform s G x y := by
  have hc : Formalism.UG.cT s g = (g.map s)ᵀ := by
    unfold Formalism.UG.cT
    first
      | rfl
      | (ext i j; simp)
  rw [hc] at hg
  have hs : (fun i => s ((g *ᵥ x) i)) = (g.map s) *ᵥ (fun i => s (x i)) := by
    funext i
    exact RingHom.map_mulVec s g x i
  rw [hform_eq_dot, hform_eq_dot, hs, Matrix.mulVec_mulVec,
    ← Matrix.vecMul_transpose (g.map s) (fun i => s (x i)),
    ← Matrix.dotProduct_mulVec (fun i => s (x i)) (g.map s)ᵀ ((G * g) *ᵥ y),
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem hR_act (k : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J k).1 *ᵥ x) ((HA.mat R σ J k).1 *ᵥ y) = hR R σ J x y := by
  have hk : HA.mat R σ J k ∈ HR R σ J := (k : HR R σ J).2
  unfold HR Formalism.UG.UJ at hk
  have hk' : Formalism.UG.cT (sigR R σ) (HA.mat R σ J k).1 * JR R J * (HA.mat R σ J k).1 = JR R J := hk
  unfold hR
  exact hform_mulVec_mulVec_of_cT_mul_mul_eq (sigR R σ) (JR R J) _ hk' x y

theorem hR_rat (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (z i)) = (1 : R) ⊗ₜ[F] hE σ J x z := by
  unfold hR hE JR
  rw [hform_eq_dot, hform_eq_dot]
  show _ = inclR R _
  rw [RingHom.map_dotProduct]
  congr 1
  all_goals funext i
  all_goals first
    | exact (RingHom.map_mulVec (inclR R) J z i).symm
    | simp [sigR, inclR]

end Form

theorem qR_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (a : F), hE σ J (x 0) (x 0) = algebraMap F E a → ∀ g : HA R σ J, qR R σ J ((g • ratTup (F := F) R x) 0) = algebraMap F R a := by
  intro F E _ _ _ _ _ σ hcm R _ _ M J x a hx g
  have hfin : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  have hact : (g • ratTup (F := F) R x) 0 = (HA.mat R σ J g).1 *ᵥ (fun i => inclR R (x 0 i)) := rfl
  rw [hact]
  unfold qR
  rw [hR_act R σ J g, hR_rat R σ J (x 0) (x 0), hx]
  have h2 : (1 : R) ⊗ₜ[F] algebraMap F E a = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [← IsScalarTower.algebraMap_apply F R (R ⊗[F] E)]
    exact (Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)).commutes a
  rw [h2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasis F E)) (algebraMap F R a),
    Fintype.card_fin, hcm.2.2.1, nsmul_eq_mul, ← mul_assoc]
  have h3 : algebraMap F R (1 / 2) * ((2 : ℕ) : R) = 1 := by
    rw [← map_natCast (algebraMap F R) 2, ← map_mul]
    norm_num
  rw [h3, one_mul]

end GlobalTheory.GaugeEx.OrbitQuadric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponents
section
noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

section BaseMap

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem qloc_trace_tmul [FiniteDimensional F E] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (r ⊗ₜ[F] e : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

variable (φ : R →ₐ[F] R') (π : R ⊗[F] E →+* R' ⊗[F] E)
  (hπ : ∀ r e, π (r ⊗ₜ[F] e) = φ r ⊗ₜ[F] e)
include hπ

theorem qloc_trace [FiniteDimensional F E] (z : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (π z) = φ (Algebra.trace R (R ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [hπ, qloc_trace_tmul, qloc_trace_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem qloc_sig (σ : E →ₐ[F] E) (z : R ⊗[F] E) : sigR R' σ (π z) = π (sigR R σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hπ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem qloc_incl (e : E) : π (inclR R e) = inclR R' e := by
  simp [inclR, hπ]

theorem qloc_q [FiniteDimensional F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (z : Fin M → R ⊗[F] E) : qR R' σ J (fun i => π (z i)) = φ (qR R σ J z) := by
  have h : hR R' σ J (fun i => π (z i)) (fun i => π (z i)) = π (hR R σ J z z) := by
    simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, qloc_sig φ π hπ,
      qloc_incl φ π hπ]
  rw [qR, qR, h, qloc_trace φ π hπ, map_mul, AlgHom.commutes]

theorem qloc_group (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    ∃ g' : HA R' σ J, (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  have hJ : (JR R J).map π = JR R' J := by
    ext i j
    exact qloc_incl φ π hπ _
  have hc : Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) =
      (Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val).map π := by
    ext i j
    exact qloc_sig φ π hπ σ _
  have hm : Formalism.UG.bc π (HA.mat R σ J g) ∈ HR R' σ J := by
    change Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) * JR R' J *
      ((HA.mat R σ J g).val.map π) = JR R' J
    rw [hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  exact ⟨(⟨_, hm⟩ : HR R' σ J), rfl⟩

end BaseMap

theorem qloc_adele_ext {F : Type} [Field F] [NumberField F] (a b : AF F)
    (h1 : fstA F a = fstA F b) (h2 : ∀ v, evalV F v (sndA F a) = evalV F v (sndA F b)) : a = b := by
  refine Prod.ext h1 ?_
  exact FiniteAdeleRing.ext F fun v => h2 v

theorem q_and_unitary_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), (∀ (z : Fin M → AF F ⊗[F] E) (β : F), qR (AF F) σ J z = algebraMap F (AF F) β ↔ qR (Ainf F) σ J (fun i => prInf (z i)) = algebraMap F (Ainf F) β ∧ ∀ v : HeightOneSpectrum (𝓞 F), qR (Fv F v) σ J (fun i => prV v (z i)) = algebraMap F (Fv F v) β) ∧ ∀ g : HA (AF F) σ J, (∃ gi : HA (Ainf F) σ J, (HA.mat (Ainf F) σ J gi).val = (HA.mat (AF F) σ J g).val.map prInf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∃ gv : HA (Fv F v) σ J, (HA.mat (Fv F v) σ J gv).val = (HA.mat (AF F) σ J g).val.map (prV v) := by
  intro F E _ _ _ _ _ σ M J
  have hI : ∀ (r : AF F) (e : E), prInf (r ⊗ₜ[F] e) = fstA F r ⊗ₜ[F] e := fun r e => rfl
  have hV : ∀ v (r : AF F) (e : E),
      prV v (r ⊗ₜ[F] e) = ((evalV F v).comp (sndA F)) r ⊗ₜ[F] e := fun v r e => rfl
  refine ⟨fun z β => ?_, fun g => ⟨qloc_group _ _ hI σ J g, fun v => qloc_group _ _ (hV v) σ J g⟩⟩
  simp only [qloc_q _ _ hI, qloc_q _ _ (hV _)]
  constructor
  · intro h
    rw [h]
    exact ⟨AlgHom.commutes _ _, fun v => AlgHom.commutes _ _⟩
  · rintro ⟨h1, h2⟩
    refine qloc_adele_ext _ _ (by rw [h1, AlgHom.commutes]) fun v => ?_
    rw [AlgHom.commutes, AlgHom.commutes]
    exact h2 v

end GlobalTheory.GaugeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_local_sqrt_nontrivial (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  have hd : HasStrictDerivAt (fun x : K => x * x) 2 1 := by
    have := (hasStrictDerivAt_id (1 : K)).mul (hasStrictDerivAt_id (1 : K))
    have h11 : (1 : K) * id 1 + id 1 * 1 = 2 := by simp; norm_num
    rw [h11] at this
    exact this
  have hF := hd.hasStrictFDerivAt_equiv h2
  let e := hF.toOpenPartialHomeomorph
  have he : ∀ x, e x = x * x := fun x => rfl
  have h1 : (1 : K) ∈ e.source := hF.mem_toOpenPartialHomeomorph_source
  have h1' : e 1 = 1 := by rw [he, mul_one]
  refine ⟨e.target, e.open_target, h1' ▸ e.map_source h1, e.symm, e.continuousOn_symm, ?_, ?_⟩
  · have := e.left_inv h1
    rwa [h1'] at this
  · intro u hu
    rw [← he]; exact e.right_inv hu

theorem exists_local_sqrt (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  by_cases h : ∃ x : K, 1 < ‖x‖
  · let : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := h }
    exact exists_local_sqrt_nontrivial K h2
  · push Not at h
    refine ⟨Metric.ball 1 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun _ => 1,
      continuousOn_const, rfl, fun u hu => ?_⟩
    rw [mem_ball_iff_norm] at hu
    by_contra hne
    have h0 : u - 1 ≠ 0 := fun h0 => hne (by rw [sub_eq_zero.1 h0, mul_one])
    have h3 := h (u - 1)⁻¹
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)] at h3
    exact absurd hu (not_lt.2 h3)

theorem nice_field (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) : Nice K :=
  ⟨inferInstance, inferInstance, inferInstance, exists_local_sqrt K h2⟩

theorem nice_pi {ι : Type} [Fintype ι] (K : ι → Type) [∀ i, NormedField (K i)]
    [∀ i, CompleteSpace (K i)] (h2 : ∀ i, (2 : K i) ≠ 0) : Nice (∀ i, K i) := by
  refine ⟨inferInstance, inferInstance, ⟨Units.isOpenEmbedding_val⟩, ?_⟩
  choose U hU h1 s hs hs1 hss using fun i => exists_local_sqrt (K i) (h2 i)
  refine ⟨Set.univ.pi U, isOpen_set_pi Set.finite_univ fun i _ => hU i, fun i _ => h1 i,
    fun x i => s i (x i), ?_, funext fun i => hs1 i, fun u hu => funext fun i => hss i _ (hu i trivial)⟩
  exact continuousOn_pi.2 fun i => (hs i).comp (continuous_apply i).continuousOn
    fun x hx => hx i trivial

theorem nice_ainf_fv : ∀ (F : Type) [Field F] [NumberField F],
    Nice (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Nice (Fv F v) := by
  intro F _ _
  refine ⟨nice_pi (fun w : InfinitePlace F => w.Completion) fun w => ?_, fun v => nice_field _ ?_⟩
  · have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero
  · have : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizerStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_unramifiedUniformizer : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (v : (D.mem u).A.vT), Unram (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  first | exact @GlobalTheory.LevelUnram.unram | exact GlobalTheory.LevelUnram.unram | (intros; apply GlobalTheory.LevelUnram.unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDualStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_O1_iso_blowup_twist_dual : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (J : X.IdealSheafData) (L₀ : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L₀.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (D : GlobalTheory.EffCartierData W), L₀.IsLB →
    GlobalTheory.ProjBlowup.Generates J σ → GlobalTheory.ProjBlowup.Proportional σ g ψ → D.idealSheaf = J.comap g →
    LBIso ((GlobalTheory.ProjSpace.O1 R m).pull ψ) (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := by
  first | exact @GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional | exact GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional | (intros; apply GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLatticesStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_completion_maps_dualLattices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (L Lb : Submodule (𝓞 E) (Fin n → E)) (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)), IsUnit J.det → Submodule.IsLattice E L → Submodule.IsLattice E Lb → y ∈ UPts σ J (v.adicCompletion F) → (∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb) → ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) := by
  first | exact @GlobalTheory.DualCompletion.dual_move | exact GlobalTheory.DualCompletion.dual_move | (intros; apply GlobalTheory.DualCompletion.dual_move <;> assumption)
end


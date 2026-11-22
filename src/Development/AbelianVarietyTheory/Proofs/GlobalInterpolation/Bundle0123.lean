import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0036
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0119
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0121
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex GlobalTheory.Idele WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.StdDual

variable (F : Type) [Field F] [NumberField F]

theorem traceInf_algebraMap (x : F) :
    traceInf F (algebraMap F (Ainf F) x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  first
  | exact @_root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap
  | exact _root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap
  | (apply _root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceSumRealEmbeddings.traceInf_algebraMap ..)

variable {F}

theorem char_fin_algebraMap {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (((Algebra.trace ℚ F x : ℚ) : ℂ) * (2 * Real.pi * Complex.I)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have h2 := h.2 (algebraMap F (Ainf F) (-x))
  rw [psiInf] at h2
  rw [e, AddChar.map_add_eq_mul, h.1.2.2.1, one_mul, h2, stdInf, traceInf_algebraMap, map_neg]
  congr 1
  push_cast
  ring

theorem char_fin_algebraMap_eq_one_iff {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 ↔
      Algebra.trace ℚ F x ∈ (algebraMap ℤ ℚ).range := by
  rw [char_fin_algebraMap h, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have := mul_right_cancel₀ Complex.two_pi_I_ne_zero hn
    rw [eq_intCast]
    exact_mod_cast this.symm
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn, eq_intCast, Rat.cast_intCast]⟩

variable (F) in

abbrev codiff : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)

theorem codiff_ne_zero : codiff F ≠ 0 :=
  FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))

theorem one_le_codiff : 1 ≤ codiff F := FractionalIdeal.one_le_dual_one ℤ ℚ

theorem mem_codiff_iff {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ) (x : F) :
    x ∈ codiff F ↔ ∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1 := by
  rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
  simp_rw [char_fin_algebraMap_eq_one_iff h, Algebra.traceForm_apply]
  constructor
  · intro H a
    rw [mul_comm]
    exact H _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
  · intro H a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [mul_comm]
    exact H a

theorem char_fin_add (ψ : AddChar (AF F) ℂ) (y z : Af F) :
    ψ (pairA F 0 (y + z)) = ψ (pairA F 0 y) * ψ (pairA F 0 z) := by
  rw [← AddChar.map_add_eq_mul]
  exact congrArg ψ (Prod.ext (add_zero (0 : Ainf F)).symm rfl)

theorem mem_adelicIdeal_codiff_iff {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ) (y : Af F) :
    y ∈ adelicIdeal (codiff F) ↔
      ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 (α * y)) = 1 := by
  have key : ∀ x : F, x ∈ codiff F ↔ ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) →
      ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := fun x => by
    rw [mem_codiff_iff h]
    refine ⟨fun H α hα => GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ h.1.1 x H α hα,
      fun H a => ?_⟩
    rw [map_mul]
    refine H _ fun v => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, adele_algebraMap_apply, valued_algebraMap]
    exact v.valuation_le_one a
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = 1 :=
    fun α hα => by
      have := (key 1).1 (one_le_codiff (FractionalIdeal.one_mem_one _)) α hα
      rwa [map_one, mul_one] at this
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F)) y
  have hx1 := mem_adelicIdeal_one_iff.1 hx
  have hx2 : y - algebraMap F (Af F) x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun v => (hx1 v).trans ?_
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    rw [← exp_zero, exp_le_exp]
    omega
  have e : y = algebraMap F (Af F) x + (y - algebraMap F (Af F) x) := by ring
  rw [e, (adelicIdeal (codiff F)).add_mem_iff_left hx2, algebraMap_mem_adelicIdeal codiff_ne_zero, key]
  refine forall_congr' fun α => forall_congr' fun hα => ?_
  rw [mul_add, char_fin_add, hint (α * (y - algebraMap F (Af F) x))
    fun v => mul_mem (hα v) (hx1 v), mul_one]

theorem singleV_self (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) : singleV F v t v = t := by
  classical
  exact RestrictedProduct.single_eq_same _ v t

theorem singleV_of_ne {v w : HeightOneSpectrum (𝓞 F)} (t : Fv F v) (h : w ≠ v) :
    singleV F v t w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne _ t h

theorem mul_singleV (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) (α : Af F) :
    α * singleV F v t = singleV F v (t * α v) := by
  ext1 w
  rw [adele_mul_apply]
  by_cases h : w = v
  · subst h
    rw [singleV_self, singleV_self, mul_comm]
  · rw [singleV_of_ne _ h, singleV_of_ne _ h, mul_zero]

theorem mem_dualV_iff_valued {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ)
    (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    t ∈ dualV F ψ v ↔ Valued.v t ≤ exp (-FractionalIdeal.count F v (codiff F)) := by
  have h1 : t ∈ dualV F ψ v ↔ singleV F v t ∈ adelicIdeal (codiff F) := by
    rw [mem_adelicIdeal_codiff_iff h]
    constructor
    · intro H α hα
      rw [mul_singleV]
      exact H _ (hα v)
    · intro H s hs
      have := H (singleV F v s) fun w => by
        by_cases hw : w = v
        · subst hw; rwa [singleV_self]
        · rw [singleV_of_ne _ hw]; exact zero_mem _
      rwa [mul_singleV, singleV_self] at this
  rw [h1, mem_adelicIdeal_iff codiff_ne_zero]
  refine ⟨fun H => by simpa only [singleV_self] using H v, fun H w => ?_⟩
  by_cases hw : w = v
  · subst hw; rwa [singleV_self]
  · rw [singleV_of_ne _ hw, map_zero]; exact zero_le'

theorem exists_generator_differentV (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y : v.adicCompletionIntegers F,
      Valued.v (y : Fv F v) = exp (FractionalIdeal.count F v (codiff F)) ∧
        differentV F v = Ideal.span {y} := by
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hne : (codiff F)⁻¹ ≠ 0 := inv_ne_zero codiff_ne_zero
  obtain ⟨y, hy, hv⟩ := exists_mem_valuation_eq hne v
  rw [← hD] at hy
  obtain ⟨y, hyD, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have hc : ∀ r : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r :
      v.adicCompletionIntegers F) : Fv F v) = v.valuation F (algebraMap (𝓞 F) F r) :=
    fun r => valued_algebraMap v _
  refine ⟨algebraMap (𝓞 F) _ y, by rw [hc, hv, FractionalIdeal.count_inv, neg_neg], ?_⟩
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun r hr => ?_)
    ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ hyD))
  have hr' : algebraMap (𝓞 F) F r ∈ (codiff F)⁻¹ := by
    rw [← hD]; exact (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩
  have h2 := (mem_iff_valuation_le hne _).1 hr' v
  rw [← hv, ← hc, ← hc] at h2
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  exact (Valuation.Integers.le_iff_dvd (Valuation.valuationSubring.integers _)).1 h2

theorem dualV_eq_inv_different {ψ : AddChar (AF F) ℂ} (h : IsStdChar F ψ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (∀ t : Fv F v, t ∈ dualV F ψ v ↔
      ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) ∧
    dualIndex F ψ v = normDifferentV F v := by
  obtain ⟨y, hy, hD⟩ := exists_generator_differentV v
  have hy0 : (y : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact exp_ne_zero hy.symm
  have h1 : ∀ t : Fv F v, t ∈ dualV F ψ v ↔ t * y ∈ v.adicCompletionIntegers F := fun t => by
    rw [mem_dualV_iff_valued h, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hy, exp_neg,
      ← one_div, le_div_iff₀ (zero_lt_iff.2 exp_ne_zero)]
  refine ⟨fun t => ?_, ?_⟩
  · rw [h1, hD]
    refine ⟨fun H d hd => ?_, fun H => H y (Ideal.mem_span_singleton_self y)⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hd
    rw [MulMemClass.coe_mul, ← mul_assoc]
    exact mul_mem H c.2
  · have hle : intV F v ≤ dualV F ψ v := fun t ht => (h1 t).2 (mul_mem ht y.2)
    have hinj : Function.Injective (AddMonoidHom.mulRight (y : Fv F v)) :=
      mul_left_injective₀ hy0
    let j : v.adicCompletionIntegers F →+ Fv F v :=
      (v.adicCompletionIntegers F).subtype.toAddMonoidHom
    have hj : Function.Injective j := Subtype.val_injective
    have e1 : (dualV F ψ v).map (AddMonoidHom.mulRight (y : Fv F v)) = (⊤ : AddSubgroup _).map j := by
      ext z
      simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, AddMonoidHom.mulRight_apply]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨_, (h1 t).1 ht⟩, rfl⟩
      · rintro ⟨c, rfl⟩
        have : (c : Fv F v) / y * y = c := div_mul_cancel₀ _ hy0
        exact ⟨c / y, (h1 _).2 (this.symm ▸ c.2), this⟩
    have e2 : (intV F v).map (AddMonoidHom.mulRight (y : Fv F v)) =
        (differentV F v).toAddSubgroup.map j := by
      ext z
      simp only [AddSubgroup.mem_map, AddMonoidHom.mulRight_apply, hD,
        Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        exact ⟨c, c.2, rfl⟩
    rw [dualIndex, AddSubgroup.relIndex_eq_one.2 hle, Nat.cast_one, div_one,
      ← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, e1, e2,
      AddSubgroup.relIndex_map_map_of_injective _ _ hj, AddSubgroup.relIndex_top_right]
    rfl

theorem dualV_eq_inv_different_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ₀, IsStdChar F ψ₀ → ∀ v : HeightOneSpectrum (𝓞 F), (∀ t : Fv F v, t ∈ dualV F ψ₀ v ↔ ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) ∧ dualIndex F ψ₀ v = normDifferentV F v :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h v => dualV_eq_inv_different h v

end GlobalTheory.StdDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRealAdelicHermitianSignatureCoordinates
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealSpaceCoord

theorem herm_eq_dot {P Q : ℕ} (x y : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm y x = star x ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ y) := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, Fintype.sum_sum_type, dotProduct, fromBlocks_mulVec, neg_mulVec,
    mul_comm]

theorem form_eq {M P Q : ℕ} (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (x y : Fin M → ℂ) :
    ∑ i, ∑ j, star (x i) * (Aᴴ * Formalism.UG.Jpq P Q * A) i j * y j = ActionCoordinates.herm (A *ᵥ y) (A *ᵥ x) := by
  rw [herm_eq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), P + Q = M → ∀ J : Matrix (Fin M) (Fin M) E, IsHermND σ J → ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ, (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∃ e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (T → ActionCoordinates.Wsp P Q), (∀ X ρ, e X ρ = A ρ *ᵥ fun i => θ ρ (X 0 i)) ∧ ∀ X Y ρ, θ ρ (hR (Ainf F) σ J (X 0) (Y 0)) = ActionCoordinates.herm (e Y ρ) (e X ρ) := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ M P Q hM J hJ A hA
  obtain ⟨e0, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ T τ θ h hτ hθ
  let B : T → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => by
    have hd : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    simp only [B]
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul]
    rw [hd]
    exact ((map_ne_zero (τ ρ)).2 hJ.2).isUnit
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ =>
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hM])).2 (hBA ρ)
  have he' : ∀ z ρ, θ ρ (e0.symm z) = z ρ := fun z ρ => by rw [← he, e0.apply_symm_apply]
  refine ⟨{ toFun := fun X ρ => A ρ *ᵥ fun i => θ ρ (X 0 i)
            invFun := fun z _ i => e0.symm fun ρ => (B ρ *ᵥ z ρ) i
            left_inv := fun X => ?_
            right_inv := fun z => ?_
            map_add' := fun X Y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ _ => rfl, fun X Y ρ => ?_⟩
  · funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [mulVec_mulVec, hBA, one_mulVec]
    rw [RingEquiv.symm_apply_eq]
    funext ρ
    rw [he]
  · funext ρ
    simp only [he']
    rw [mulVec_mulVec, hAB, one_mulVec]
  · funext ρ
    refine Eq.trans ?_ (mulVec_add (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    congr 1
    funext i
    simp
  · refine continuous_pi fun ρ => continuous_const.matrix_mulVec (continuous_pi fun i => ?_)
    simp only [← he]
    exact (continuous_apply ρ).comp (hc.comp ((continuous_apply i).comp (continuous_apply 0)))
  · exact continuous_pi fun _ => continuous_pi fun i => hc'.comp (continuous_pi fun ρ =>
      (continuous_apply i).comp (continuous_const.matrix_mulVec (continuous_apply ρ)))
  · refine Eq.trans ?_ (form_eq (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    rw [hA]
    simp only [hR, Formalism.UG.hform, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Mem.VolInfIso.infEmb_sigR σ (τ ρ) (θ ρ) h (hθ ρ)]
    congr 2
    exact (hθ ρ).1 _

end GlobalTheory.RealSpaceCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GLevHChiPowEqOneAndMemRange
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem gLevH_chi_pow_eq_one_and_mem_range : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))) (lam : ∀ a v h, H a v h →* ℂˣ) (_ : GLevH S G H lam) (K : Type) [Field K] (s : K →+* ℂ) (N : ℕ), (∀ i, (gp i).Prime) → (∀ a v h M, ((lam a v h M : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((lam a v h M : ℂˣ) : ℂ)) → ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ n J T f bad S gp G H lam L K _ s N _ hl x
  have hmul : ∀ a b : ℂ, (a ^ N = 1 ∧ ∃ r : K, s r = a) → (b ^ N = 1 ∧ ∃ r : K, s r = b) →
      ((a * b) ^ N = 1 ∧ ∃ r : K, s r = a * b) := by
    rintro a b ⟨ha, r, hr⟩ ⟨hb, r', hr'⟩
    exact ⟨by rw [mul_pow, ha, hb, one_mul], r * r', by rw [map_mul, hr, hr']⟩
  have hone : (1 : ℂ) ^ N = 1 ∧ ∃ r : K, s r = 1 := ⟨one_pow N, 1, map_one s⟩
  rw [L.chi_eq x]
  refine Finset.prod_induction _ (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hmul hone ?_
  intro a _
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro v
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro h
  obtain ⟨h1, r, hr⟩ := hl a v h (L.red a v h x)
  exact ⟨by rw [inv_pow, h1, inv_one], r⁻¹, by rw [map_inv₀, hr]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodWeierstrassValueMemConjStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPeriod_weierstrassValue_mem_conj : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  first | exact @GlobalTheory.HalfPeriodValue.halfPeriod_value | exact GlobalTheory.HalfPeriodValue.halfPeriod_value | (intros; apply GlobalTheory.HalfPeriodValue.halfPeriod_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralClosureCompletedCMAlgebraCompactOpenStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_completedCMAlgebra_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : HeightOneSpectrum (𝓞 F), IsCompact (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) ∧ IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure | exact GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure | (intros; apply GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsOrthogonalComplementUnitaryFrameOfMatrixStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrthogonalComplementUnitaryFrame_of_matrix : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ x : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x ≠ 0 → ∀ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ, Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' → (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0 → ∀ ι : UpqT P' Q' → UpqT P Q, (∀ b, UpqT.mat (ι b) * C = C * UpqT.mat b ∧ UpqT.mat (ι b) *ᵥ x = x) → ActionCoordinates.IsPerpFrame x (Matrix.toLin' C) ι := by
  first | exact @GlobalTheory.PerpFrameOfMatrix.isPerpFrame_of_matrix | exact GlobalTheory.PerpFrameOfMatrix.isPerpFrame_of_matrix | (intros; apply GlobalTheory.PerpFrameOfMatrix.isPerpFrame_of_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LamJMemRangeAndPowEqOne
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → Nat.card k = p →
      (∃ ζ : K, IsPrimitiveRoot ζ p) → (∃ ζ : K, IsPrimitiveRoot ζ (p - 1)) →
      ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t nb skip : ℕ)
        (M : Matrix (Fin n) (Fin n) k),
        (∃ r : K, s r = lamJ ψ χ a t nb skip M) ∧
          (lamJ ψ χ a t nb skip M ≠ 0 → lamJ ψ χ a t nb skip M ^ (p * (p - 1)) = 1) := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ ⟨ξ, hξ⟩ n ψ χ a t nb skip M
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact hp.ne_zero)
  letI : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = p := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hψ : ∀ x : k, ψ x ^ p = 1 := by
    intro x
    rw [← AddChar.map_nsmul_eq_pow, ← hk, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  have hχ : ∀ (i : ℕ) (x : k), χ i x ≠ 0 → χ i x ^ (p - 1) = 1 := by
    intro i x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (MulChar.map_zero _)
    rw [← map_pow, ← hk', FiniteField.pow_card_sub_one_eq_one x hx0, map_one]
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hψr : ∀ x : k, ψ x ∈ s.range := fun x =>
    complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ (hψ x)
  have hχr : ∀ (i : ℕ) (x : k), χ i x ∈ s.range := by
    intro i x
    by_cases hx : χ i x = 0
    · rw [hx]; exact zero_mem _
    · exact complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s (p - 1) ξ hp1 hξ _ (hχ i x hx)
  unfold lamJ
  refine ⟨?_, ?_⟩
  · exact mul_mem (hψr _) (prod_mem fun i _ => hχr i _)
  · intro h
    have h2 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)
    rw [mul_pow, pow_mul, hψ, one_pow, one_mul, mul_comm p, pow_mul, ← Finset.prod_pow,
      Finset.prod_eq_one (fun i hi => hχ i _ (h2 i hi)), one_pow]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelCharacterNoBlocksPthRootOfUnity
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_zero_blocks_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → (p : k) = 0 → (∃ ζ : K, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t skip : ℕ) (M : Matrix (Fin n) (Fin n) k), (∃ r : K, s r = lamJ ψ χ a t 0 skip M) ∧ lamJ ψ χ a t 0 skip M ^ p = 1 := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ n ψ χ a t skip M
  have hψ : ∀ x : k, ψ x ^ p = 1 := fun x => by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hk, zero_mul, AddChar.map_zero_eq_one]
  have h : lamJ ψ χ a t 0 skip M ^ p = 1 := by
    unfold Formalism.L2.Forms.lamJ
    simp [hψ]
  exact ⟨complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ h, h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegDefiniteSelfDualStabilizerVolumeOneStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negDefinite_selfDualStabilizer_volume_one : ∀ (D : D7) (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) → ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram), IsVolMeas D W 0 n μ → μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) = 1 := by
  first | exact @GlobalTheory.NegDefStab.measure_SFin_negDef | exact GlobalTheory.NegDefStab.measure_SFin_negDef | (intros; apply GlobalTheory.NegDefStab.measure_SFin_negDef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmoothStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_latticeHyp_and_smooth : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.VecP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b := by
  first | exact @GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth | exact GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth | (intros; apply GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PageDutiesOfClassSeven
section
namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

theorem tameList_eq {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : DC.tameList χ = Formalism.MainNotions.tameList χ := by
  funext o
  rcases o with _ | ⟨j, _ | _⟩ <;> rfl

theorem tameDistinct_iff (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) :
    DC.TameDistinct r g χ ↔ Formalism.MainNotions.TameDistinct r g χ := by
  unfold DC.TameDistinct Formalism.MainNotions.TameDistinct
  rw [tameList_eq]

end GlobalTheory.EX.DQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLattice_halfLattice_inclusions_splitPrime : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Ctx A a b S SG ϖ p g cA → IsSdLat N → IsSdLat N' → A.AA ≠ ⊥ ∧ (∀ y ∈ per A N N', ((g : X.E) * ((ϖ : X.E) / star (ϖ : X.E))) • y ∈ halfBO S (per A N N') (p * g)) ∧ (∀ y ∈ halfBO S (per A N N') (p * g), ((g : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • y ∈ per A N N') ∧ (∀ x ∈ divLat cA (homAt S N N'), x ∈ homAt (divs ϖ) N N' → ∀ t ∈ halfAO S (per A N N') (cA * (p * g)), t - x ∈ mulLat (p * g) (homAt S N N') → ((cA * g : ℕ) : X.E) • t ∈ per A N N') ∧ (∀ y ∈ per A N N', y ∈ homAt S N N' ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ halfAO S (per A N N') (cA * (p * g)) ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt SG N N') ∧ ((((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt S N N') ↔ y ∈ smulLat (ϖ : X.E) (per A N N'))) ∧ (∀ (y : HomE X.E a b) (n : ℕ), Nat.Coprime n p → (n : X.E) • y ∈ smulLat ((ϖ : X.E) / star (ϖ : X.E)) (per A N N') → y ∈ mulLat p (homAt (divs ϖ) N N')) ∧ (∀ x ∈ halfBO S (per A N N') (p * g), ∀ y ∈ halfBO S (per A N N') (p * g), ∃ n : ℤ, coc A x y = n) ∧ ∀ x ∈ halfAO S (per A N N') (cA * (p * g)), ∀ y ∈ halfAO S (per A N N') (cA * (p * g)), ∃ n : ℤ, coc A x y = n := by
  first | exact @GlobalTheory.MomT.HalfIncl.half_inclusions | exact GlobalTheory.MomT.HalfIncl.half_inclusions | (intros; apply GlobalTheory.MomT.HalfIncl.half_inclusions <;> assumption)
end


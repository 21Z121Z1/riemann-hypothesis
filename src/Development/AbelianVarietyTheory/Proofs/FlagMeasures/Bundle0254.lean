import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmStarOfIsCMUnram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeMiddleLatticeHomLatticeIdeal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBounds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryOfSelfDualAtPlace
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeOfDiag
section
open NumberField Formalism.BasicNotions

namespace GlobalTheory.SA.AmbSig

open Matrix Module

theorem card_le_of_diag {p q d : ℕ} (N : Matrix (Fin p ⊕ Fin q) (Fin d) ℂ) (δ : Fin d → ℂ)
    (hδ : ∀ j, (δ j).re ≤ 0) (hN : Nᴴ * Formalism.UG.Jpq p q * N = diagonal δ)
    (hinj : ∀ c, N *ᵥ c = 0 → c = 0) : d ≤ q := by
  classical

  let f : (Fin d → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
    LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q) ∘ₗ Matrix.mulVecLin N
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun c hc => ?_
    set w := N *ᵥ c with hw
    have hr : ∀ i, w (Sum.inr i) = 0 := fun i => congrFun hc i

    have hform : star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w) = star c ⬝ᵥ (diagonal δ *ᵥ c) := by
      rw [← hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      conv_rhs => rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hleft : (star w ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ w)).re = ∑ i, Complex.normSq (w (Sum.inl i)) := by
      unfold Formalism.UG.Jpq
      rw [Matrix.fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type, hr, Complex.mul_re, Complex.normSq_apply]
    have hright : (star c ⬝ᵥ (diagonal δ *ᵥ c)).re = ∑ j, (δ j).re * Complex.normSq (c j) := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.normSq_apply]
      ring
    have hnn : ∀ i, 0 ≤ Complex.normSq (w (Sum.inl i)) := fun i => Complex.normSq_nonneg _
    have hsum : ∑ i, Complex.normSq (w (Sum.inl i)) ≤ 0 := by
      rw [← hleft, hform, hright]
      exact Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonpos_of_nonneg (hδ j) (Complex.normSq_nonneg _)
    have hl : ∀ i, w (Sum.inl i) = 0 := fun i =>
      Complex.normSq_eq_zero.1 (le_antisymm
        ((Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans hsum) (hnn i))
    apply hinj
    funext x
    cases x with
    | inl i => exact hl i
    | inr i => exact hr i
  simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem hT_eq_sum {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ b, (∑ a, star (S.frame.repr x a) * S.gram a b) * S.frame.repr y b := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  simp only [HSpace.gram]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem amb_of_sig : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (k r : ℕ),
    GlobalTheory.SA.CMStar E → S.SigOK → (∀ τ : E →+* ℂ, S.sig τ = (k + r, r + 1)) → GlobalTheory.SA.Amb S k r := by
  intro E _ _ _ S k r hcm hok hsig

  have hfac : ∀ τ : E →+* ℂ, S.rank = k + r + (r + 1) ∧
      ∃ A : Matrix (Fin (k + r) ⊕ Fin (r + 1)) (Fin S.rank) ℂ,
        Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A = S.gram.map τ ∧
        ∃ B : Matrix (Fin S.rank) (Fin (k + r) ⊕ Fin (r + 1)) ℂ, B * A = 1 := by
    intro τ
    have h := hok τ
    rw [hsig τ] at h
    obtain ⟨h1, ⟨A, hA⟩, h3⟩ :=
      GlobalTheory.Mem.SignatureFactor.exists_factor S.rank (k + r) (r + 1) _ h
    obtain ⟨B, -, hBA⟩ := h3 A hA
    exact ⟨h1.symm, A, hA, B, hBA⟩
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine ⟨hcm, ?_, ?_⟩
  · rw [S.rank_eq, (hfac τ₀).1]
    ring
  · intro τ U hU
    classical
    obtain ⟨-, A, hA, B, hBA⟩ := hfac τ

    let F : U →ₗ[E] U →ₛₗ[starRingEnd E] E := S.hT.flip.domRestrict₁₂ U U
    have hF : ∀ x y, starRingEnd E (F x y) = F y x := fun x y => S.herm.eq (y : S.V) (x : S.V)
    obtain ⟨u, hu⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (E := E) (c := starRingEnd E)
      two_ne_zero (Module.finrank E U) F hF rfl

    let v : Fin (Module.finrank E U) → Fin S.rank → E := fun j => S.frame.repr (u j : S.V)
    have hv : LinearIndependent E v := by
      have hker : LinearMap.ker (S.frame.equivFun.toLinearMap ∘ₗ U.subtype) = ⊥ :=
        LinearMap.ker_eq_bot.2 (S.frame.equivFun.injective.comp Subtype.val_injective)
      exact u.linearIndependent.map' _ hker
    letI : Algebra E ℂ := τ.toAlgebra
    haveI : FaithfulSMul E ℂ := (faithfulSMul_iff_algebraMap_injective E ℂ).2 τ.injective
    have hvC : LinearIndependent ℂ (fun j => algebraMap E ℂ ∘ v j) :=
      linearIndependent_algebraMap_comp_iff.2 hv
    let C : Matrix (Fin S.rank) (Fin (Module.finrank E U)) ℂ := Matrix.of fun a j => τ (v j a)
    refine card_le_of_diag (A * C) (fun j => τ (S.hT (u j : S.V) (u j : S.V)))
      (fun j => hU _ (u j).2) ?_ ?_
    · have hsplit : (A * C)ᴴ * Formalism.UG.Jpq (k + r) (r + 1) * (A * C) =
          Cᴴ * (Aᴴ * Formalism.UG.Jpq (k + r) (r + 1) * A) * C := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hsplit, hA]
      ext i j
      have hij : τ (S.hT (u i : S.V) (u j : S.V)) = (Cᴴ * S.gram.map τ * C) i j := by
        rw [hT_eq_sum, map_sum, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, map_sum, Matrix.mul_apply]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [C, v, hcm τ]
      rw [← hij, Matrix.diagonal_apply]
      split_ifs with h
      · rw [h]
      · have h0 : F (u j) (u i) = 0 := hu j i (Ne.symm h)
        simp only [F, LinearMap.domRestrict₁₂_apply, LinearMap.flip_apply] at h0
        rw [h0, map_zero]
    · intro c hc
      have hCc : C *ᵥ c = 0 := by
        rw [← Matrix.mulVec_mulVec] at hc
        rw [← Matrix.one_mulVec (C *ᵥ c), ← hBA, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
      have hlin := Fintype.linearIndependent_iff.1 hvC c (by
        rw [← hCc]
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, C, mul_comm, RingHom.algebraMap_toAlgebra])
      funext j
      exact hlin j

end GlobalTheory.SA.AmbSig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreserving
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.ReImVolume

noncomputable def reImLinear (ι : Type) (n : ℕ) :
    (ι → Fin n → ℂ) ≃ₗ[ℝ] (ι × Fin n × Bool → ℝ) where
  toFun y p := if p.2.2 then (y p.1 p.2.1).re else (y p.1 p.2.1).im
  invFun x v i := ⟨x (v, i, true), x (v, i, false)⟩
  map_add' y z := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  map_smul' c y := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp
  left_inv y := by
    funext v i
    simp
  right_inv x := by
    funext p
    rcases p with ⟨v, i, _ | _⟩ <;> simp

theorem volume_re_im (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume {z : ℂ | z.re ∈ A ∧ z.im ∈ B} = volume A * volume B := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (hA.prod hB).nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_prod] at h
  rw [← h]
  rfl

theorem measurePreserving_reImLinear (ι : Type) [Fintype ι] (n : ℕ) :
    MeasurePreserving (reImLinear ι n) volume volume := by
  have hm : Measurable (reImLinear ι n) :=
    (reImLinear ι n).toLinearMap.continuous_of_finiteDimensional.measurable
  refine ⟨hm, ?_⟩
  rw [volume_pi (α := fun _ : ι × Fin n × Bool => ℝ)]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (reImLinear ι n) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun v => Set.univ.pi fun i =>
        {z : ℂ | z.re ∈ s (v, i, true) ∧ z.im ∈ s (v, i, false)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_setOf_eq]
    constructor
    · intro h v i
      exact ⟨h (v, i, true), h (v, i, false)⟩
    · rintro h ⟨v, i, _ | _⟩
      · exact (h v i).2
      · exact (h v i).1
  rw [hpre, volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool, volume_re_im _ _ (hs _) (hs _)]

theorem exists_reIm_measurePreserving :
    ∀ (ι : Type) [Fintype ι] (n : ℕ), ∃ T : (ι → Fin n → ℂ) ≃ₜ+ (ι × Fin n × Bool → ℝ),
      MeasurePreserving T volume volume ∧
        ∀ y v i, T y (v, i, true) = (y v i).re ∧ T y (v, i, false) = (y v i).im := by
  intro ι _ n
  let L := (reImLinear ι n).toContinuousLinearEquiv
  refine ⟨{ toAddEquiv := (reImLinear ι n).toAddEquiv
            continuous_toFun := L.continuous
            continuous_invFun := L.symm.continuous }, ?_, fun y v i => ⟨rfl, rfl⟩⟩
  exact measurePreserving_reImLinear ι n

end GlobalTheory.ReImVolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
section
noncomputable section

namespace GlobalTheory.GaugeQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal

variable {P Q P' Q' : ℕ}

def hsDist (g : UpqT P Q) : ℝ := ∑ i, ∑ j, ‖(UpqT.mat g - 1) i j‖ ^ 2

def ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ ^ 2 + 2 * ∑ i, ‖y (e (some i))‖ ^ 2

def tanSq (t : ℝ × Sp P' Q') : ℝ := t.1 ^ 2 + 2 * ∑ i, ‖t.2 i‖ ^ 2

def gaussSp (y : Sp P Q) : ℝ := Real.exp (-∑ i, ‖y i‖ ^ 2)

def ballVol (d : ℕ) (r : ℝ) : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)

def HasEuclDensity (μ : Measure (UpqT P Q)) : Prop :=
  Tendsto (fun r : ℝ => μ {g | hsDist g < r ^ 2} / ballVol ((P + Q) ^ 2) r) (𝓝[>] 0) (𝓝 1)

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.hsDist_nonneg (g : _root_.Formalism.BasicNotions.UpqT P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.hsDist g := by
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_hsDist : Continuous (_root_.GlobalTheory.GaugeQuot.hsDist : _root_.Formalism.BasicNotions.UpqT P Q → ℝ) := by
  have hmat : Continuous (_root_.Formalism.BasicNotions.UpqT.mat : _root_.Formalism.BasicNotions.UpqT P Q → _) := _root_.GlobalTheory.UpqTopology.continuous_mat
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_apply j).comp ((continuous_apply i).comp
    (hmat.sub continuous_const))).norm).pow 2

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ptSq_nonneg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.ptSq e y := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (_root_.GlobalTheory.GaugeQuot.ptSq e) := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.tanSq_nonneg (t : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q') :
    0 ≤ _root_.GlobalTheory.GaugeQuot.tanSq t := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_tanSq :
    Continuous (_root_.GlobalTheory.GaugeQuot.tanSq : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q' → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_gaussSp :
    Continuous (_root_.GlobalTheory.GaugeQuot.gaussSp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.gaussSp
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_mul (d : ℕ) (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d (t * r) = ENNReal.ofReal (t ^ d) * _root_.GlobalTheory.GaugeQuot.ballVol d r := by
  unfold _root_.GlobalTheory.GaugeQuot.ballVol
  rw [Measure.addHaar_ball_mul_of_pos _ _ ht, finrank_euclideanSpace_fin]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_zero (d : ℕ) {r : ℝ} (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ 0 :=
  (Metric.measure_ball_pos volume _ hr).ne'

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_top (d : ℕ) (r : ℝ) : _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ ⊤ :=
  measure_ball_lt_top.ne

end GlobalTheory.GaugeQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeMiddleLatticeHomLatticeIdealStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_middleLattice_homLattice_ideal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ a : Fin r, HasDom volume (homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a)) (ENNReal.ofReal (((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * Fintype.card (InfinitePlace E))) ^ (k + 1))) := by
  first | exact @GlobalTheory.SnMass.VolN.CovH.covolume_homLat | exact GlobalTheory.SnMass.VolN.CovH.covolume_homLat | (intros; apply GlobalTheory.SnMass.VolN.CovH.covolume_homLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeQuotientOfRealIdentityStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolumeQuotient_ofReal_identity : ∀ (d c : ℝ) (f t : ℕ) (m : ℝ≥0∞), 1 ≤ d → 0 < c → ENNReal.ofReal (((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2)) = ENNReal.ofReal ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) * m → ENNReal.ofReal ((2 * c) ^ f) * m = ENNReal.ofReal (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by
  first | exact @GlobalTheory.covolQuotient_arith | exact GlobalTheory.covolQuotient_arith | (intros; apply GlobalTheory.covolQuotient_arith <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBoundsStatement
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_referenceLattice_stabiliser_bounds : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ L : Submodule (𝓞 K) V, IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → N.F.z ∈ L → ∃ Ω : Set (ι → Mt k r), IsFund (realPts Φ (N.Gam (N.Ref L) : Set (V ≃ₗ[K] V))) (RP k r g) Ω ∧ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) / (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) ≤ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ∧ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) := by
  first | exact @GlobalTheory.DegVol.RefCov.covol_ref | exact GlobalTheory.DegVol.RefCov.covol_ref | (intros; apply GlobalTheory.DegVol.RefCov.covol_ref <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesLowestKTypeUnitUnitaryFormalDegreeStatement
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  first | exact @GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | exact GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | (intros; apply GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCmExtensionMixedSpaceRealCoordsStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmExtension_mixedSpace_realCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : mixedEmbedding.mixedSpace F ≃L[ℝ] (InfinitePlace E → ℝ), MeasurePreserving e volume volume ∧ ∀ y : F, e (mixedEmbedding F y) = reV (algebraMap F E y) := by
  first | exact @GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords | exact GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords | (intros; apply GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainSndOfTwoSmulMemStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_snd_of_two_smul_mem' : ∀ {ι : Type} [Fintype ι] (Λ : Submodule ℤ ((ι → ℝ) × (ι → ℝ))) [DiscreteTopology Λ], Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) = ⊤ → (∀ a b, (a, b) ∈ Λ → ((0 : ι → ℝ), (2 : ℝ) • b) ∈ Λ) → ∃ D : Set (ι → ℝ), MeasurableSet D ∧ ∀ y, ∃! l, l ∈ {b : ι → ℝ | ∃ a, (a, b) ∈ Λ} ∧ y + l ∈ D := by
  first | exact @GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem | exact GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem | (intros; apply GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftAntidiagonal
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem exists_lift_antidiag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a l hl
  obtain ⟨c, hc, hσ, hlw⟩ := hl
  have hσ' : σ c = -c := hσ
  refine ⟨rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c, ?_, ?_⟩
  · refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV a 0 c ?_ ?_ ?_ hc
    · intro b _
      simp [form]
    · simp [form, hσ']
    · intro b _
      simp
  have hE : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c) w i j =
      (if i = j then 1 else 0) +
        (if j = esI k r a then (if i = eI k r a then (s a : ℂ) * ((s a : ℂ) * w.embedding c) else 0) else 0) := by
    intro w i j
    have h0 : (A w *ᵥ fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
      have h1 : (fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
        funext l
        simp
      rw [h1, mulVec_zero]
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV a 0 c w i j, h0]
    simp [herm]
  have hne : ∀ b b' : Fin r, eI k r b ≠ esI k r b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [eI, esI] at this
    omega
  have hnw : ∀ (j : Fin (k + 1)) (b : Fin r), wI k r j ≠ esI k r b := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, esI] at this
    omega
  have hnw' : ∀ (j : Fin (k + 1)) (b : Fin r), eI k r b ≠ wI k r j := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, eI] at this
    omega
  have hee : ∀ b b' : Fin r, b ≠ b' → eI k r b ≠ eI k r b' := by
    intro b b' hb h
    apply hb
    have := congrArg Fin.val h
    simp only [eI] at this
    exact Fin.ext this
  have hss : ∀ b b' : Fin r, esI k r b = esI k r b' → b = b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [esI] at this
    exact Fin.ext (by omega)
  constructor
  · intro w
    show ((gM A _ w) (eI k r a) (esI k r a)).im = l w
    rw [hE, hlw w]
    simp [hne a a, pow_two, mul_assoc, Complex.mul_im]
  · rintro (p | b | p | b) hβ _ w
    · show (gM A _ w) (eI k r p.1.1) (eI k r p.1.2) = 0
      rw [hE]
      have h1 : eI k r p.1.1 ≠ eI k r p.1.2 := hee _ _ (ne_of_lt p.2)
      simp [h1, (hne p.1.2 a)]
    · funext j
      show (gM A _ w) (eI k r b) (wI k r j) = 0
      rw [hE]
      simp [hnw' j b, hnw j a]
    · show (gM A _ w) (eI k r p.1.1) (esI k r p.1.2) = 0
      rw [hE]
      have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2
      by_cases h2 : p.1.2 = a
      · have h3 : eI k r p.1.1 ≠ eI k r a := hee _ _ (h2 ▸ h1)
        simp [hne p.1.1 p.1.2, h3]
      · have h3 : esI k r p.1.2 ≠ esI k r a := fun h => h2 (hss _ _ h)
        simp [hne p.1.1 p.1.2, h3]
    · show ((gM A _ w) (eI k r b) (esI k r b)).im = 0
      rw [hE]
      have hb : b ≠ a := fun h => hβ (by rw [h])
      have h3 : esI k r b ≠ esI k r a := fun h => hb (hss _ _ h)
      simp [hne b b, h3]

end GlobalTheory.SnMass.VolN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsListProdStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irr_pairs_char_prod_eq_sum : ∀ (G₁ G₂ : Type) [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ), IsChar Φ → ∃ L : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧ ∀ x y, Φ (x, y) = (L.map fun p => p.1 x * p.2 y).sum := by
  first | exact @GlobalTheory.GLm.ProdChar.exists_list_prod | exact GlobalTheory.GLm.ProdChar.exists_list_prod | (intros; apply GlobalTheory.GLm.ProdChar.exists_list_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryOfSelfDualAtPlaceStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localUnitary_of_selfDual_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ (v : HeightOneSpectrum (𝓞 F)), SelfDualAt cm.sig J v L → SelfDualAt cm.sig J v M → ∃ h ∈ UPts cm.sig J (v.adicCompletion F), ∀ x, x ∈ loc v L ↔ h.1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt | exact GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt | (intros; apply GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt <;> assumption)
end


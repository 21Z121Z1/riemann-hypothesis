import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IndexAtLevelIffOuterClausesAnd

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyStandardLocalHaarMeasures
section
noncomputable section

namespace GlobalTheory.GaugeEx.StdExist

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

def coordHomeo {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (R ⊗[F] E) ≃ₜ (Fin d → R) where
  toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
  continuous_toFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  continuous_invFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  exact isCompact_iff_compactSpace.2 this

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

theorem intV_eq {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    intV b v = coordHomeo b (Fv F v) ⁻¹'
      (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
  ext y
  simp only [intV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rfl

theorem isCompact_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (intV b v) := by
  rw [intV_eq, Homeomorph.isCompact_preimage]
  exact isCompact_univ_pi fun _ => isCompact_integers v

theorem isOpen_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (intV b v) := by
  rw [intV_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integers v).preimage
    (coordHomeo b (Fv F v)).continuous

def intK (v : HeightOneSpectrum (𝓞 F)) : TopologicalSpace.PositiveCompacts (Fv F v) where
  carrier := v.adicCompletionIntegers F
  isCompact' := isCompact_integers v
  interior_nonempty' := by
    rw [(isOpen_integers v).interior_eq]
    exact ⟨0, zero_mem _⟩

def intVK {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    TopologicalSpace.PositiveCompacts (Fv F v ⊗[F] E) where
  carrier := intV b v
  isCompact' := isCompact_intV b v
  interior_nonempty' := by
    rw [(isOpen_intV b v).interior_eq]
    exact ⟨0, fun k => by simp⟩

theorem nonempty_stdMeas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) : Nonempty (StdMeas b) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  exact ⟨{
    lamI := Measure.addHaar
    lamV := fun v => Measure.addHaarMeasure (intVK b v)
    nuI := Measure.addHaar
    nuV := fun v => Measure.addHaarMeasure (intK v)
    haar_lamI := inferInstance
    haar_lamV := fun v => inferInstance
    haar_nuI := inferInstance
    haar_nuV := fun v => inferInstance
    lamV_int := fun v => Measure.addHaarMeasure_self (K₀ := intVK b v)
    nuV_int := fun v => Measure.addHaarMeasure_self (K₀ := intK v) }⟩

end GlobalTheory.GaugeEx.StdExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtStandardFrameEqNormComplexForm
section
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbNormTie

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_eq_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = ∑ i, ∑ j, star (x i) * H i j * y j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem j_eq_sum {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (x i) : Fin n → K) = x i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, LinearMap.map_smulₛₗ]

theorem j_ne_zero {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    {x : Fin n → K} (hx : x ≠ 0) : j x ≠ 0 := by
  intro h0
  apply hx
  funext i
  rw [j_eq_sum] at h0
  have := Fintype.linearIndependent_iff.mp hli (fun i => σ (x i)) h0 i
  simpa using this

theorem normAt_sq {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K V) (Xf : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b Xf v x ^ 2 = (Formalism.HermitianLatticesTheory.majAt b Xf v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem hAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H : Matrix (Fin n) (Fin n) K)
    (hin : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y)) :
    (∀ x y, hAt H (InfinitePlace.mk σ) x y = inner ℂ (j x) (j y)) ∨
      (∀ x y, hAt H (InfinitePlace.mk σ) x y = star (inner ℂ (j x) (j y))) := by
  rcases InfinitePlace.embedding_mk_eq σ with he | he
  · left
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    simp only [map_sum, map_mul, hσ]
    rfl
  · right
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    simp only [map_sum, map_mul, hσ, star_sum, star_mul', ComplexEmbedding.conjugate_coe_eq, Complex.star_def]

theorem posAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K)
    (op : W →ₗ[ℂ] W) (hT : FormsTie σ j H E op) :
    PosAt H (InfinitePlace.mk σ) ∧ ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; simp [Complex.star_def]
  refine ⟨⟨fun x y => ?_, fun x hx => ?_⟩, hd⟩
  · rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, h]; exact (inner_conj_symm (j y) (j x)).symm
    · rw [h, h, star_star]; exact inner_conj_symm (j x) (j y)
  · rw [hd, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.mpr (j_ne_zero j hT.li hx)) 2

end GlobalTheory.AmbNormTie

open GlobalTheory.AmbNormTie in

theorem GlobalTheory.AmbNormTie.normAt_frm_mk : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  intro K _ _ _ _ σ hσ W _ _ n j H E op hT x
  obtain ⟨hP, hd⟩ := posAt_mk hσ j H E op hT
  have hPD := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H (InfinitePlace.mk σ) hP
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x x =
      hAt H (InfinitePlace.mk σ) x x := by
    rw [Formalism.L2.DIV.majAt_eq, GlobalTheory.AmbCrd.frm_of_posDef H _ hPD, (Formalism.L2.DIV.frameOfSpec _ _ hPD).2,
      GlobalTheory.Core.AmbTieStep.hAt_eq_dot]
  have h2 := normAt_sq (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x
  rw [hmaj, hd, Complex.ofReal_re] at h2
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x :=
    Real.sqrt_nonneg _
  exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).mp h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefinite
section
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.DefiniteUnitaryCasimir

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.UnitaryLieComplexification

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

theorem exists_linear_extension (hJ : Jᴴ = J) (hu : IsUnit J.det) {A : Type} [Ring A] [Algebra ℂ A] (ρ : lieU J → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsm : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A,
      (∀ Z, R Z = ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)) ∧ (∀ X : lieU J, R X.1 = ρ X) := by
  have hsub : ∀ X Y, ρ (X - Y) = ρ X - ρ Y := by
    intro X Y
    have := hadd (X - Y) Y
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have h0 : ρ 0 = 0 := by
    have := hsub 0 0
    rwa [sub_self, sub_self] at this
  let r : Matrix (Fin n) (Fin n) ℂ → A := fun Z => ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)
  have key : ∀ X Y : lieU J, r (X.1 + Complex.I • Y.1) = ρ X + Complex.I • ρ Y := by
    intro X Y
    simp only [r, rePart_mk, imPart_mk]
  have hII : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (m : M), Complex.I • Complex.I • m = -m := by
    intro M _ _ m
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  refine ⟨{ toFun := r, map_add' := ?_, map_smul' := ?_ }, fun Z => rfl, ?_⟩
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : X.1 + Complex.I • Y.1 + (X'.1 + Complex.I • Y'.1) = (X + X').1 + Complex.I • (Y + Y').1 := by
      change _ = (X.1 + X'.1) + Complex.I • (Y.1 + Y'.1)
      module
    rw [this, key, key, key, hadd, hadd]
    module
  · intro c Z
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    generalize c.re = a at hc
    generalize c.im = b at hc
    subst hc
    have : ((a : ℂ) + (b : ℂ) * Complex.I) • (X.1 + Complex.I • Y.1) =
        (a • X - b • Y).1 + Complex.I • (b • X + a • Y).1 := by
      change _ = ((a : ℂ) • X.1 - (b : ℂ) • Y.1) + Complex.I • ((b : ℂ) • X.1 + (a : ℂ) • Y.1)
      simp only [add_smul, smul_add, mul_smul, hII]
      module
    rw [this, key, key, hsub, hadd, hsm, hsm, hsm, hsm]
    simp only [RingHom.id_apply, add_smul, smul_add, mul_smul, hII]
    module
  · intro X
    have := key X 0
    simpa [h0] using this

theorem mul_single_mul (U V : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    U * single a b (1 : ℂ) * V = ∑ c, ∑ d, (U c a * V b d) • single c d (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single (U * single a b (1 : ℂ) * V)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem casimir_move {A : Type} [Ring A] [Algebra ℂ A] (R R' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (U V : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, R (U * single a b 1 * V) * R' (single b a 1) =
      ∑ c, ∑ d, R (single c d 1) * R' (V * single d c 1 * U) := by
  simp only [mul_single_mul, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type' (f := fun c d => ∑ b, ∑ a, (V b d * U c a) • (R (single c d 1) * R' (single b a 1)))]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))) _ _
    fun q => ?_
  simp [mul_comm]

theorem casimir_conj {A : Type} [Ring A] [Algebra ℂ A] (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    ∑ a, ∑ b, R (single a b 1) * R (single b a 1) =
      ∑ a, ∑ b, R (B⁻¹ * single a b 1 * B) * R (B⁻¹ * single b a 1 * B) := by
  have := casimir_move R (R ∘ₗ (LinearMap.mulRight ℂ B) ∘ₗ (LinearMap.mulLeft ℂ B⁻¹)) B⁻¹ B
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul B hB, Matrix.mul_one]

theorem cj_conj_single (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) (h : J = Bᴴ * B ∨ J = -(Bᴴ * B))
    (a b : Fin n) : cj J (B⁻¹ * single a b 1 * B) = -(B⁻¹ * single b a 1 * B) := by
  have hBH : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact hB.star
  have key : (Bᴴ * B)⁻¹ * (B⁻¹ * single a b (1 : ℂ) * B)ᴴ * (Bᴴ * B) = B⁻¹ * single b a 1 * B := by
    rw [Matrix.mul_inv_rev, conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_single,
      star_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᴴ⁻¹ Bᴴ B, ← Matrix.mul_assoc Bᴴ⁻¹ Bᴴ, Matrix.nonsing_inv_mul _ hBH, Matrix.one_mul,
      Matrix.one_mul]
  rcases h with rfl | rfl
  · rw [cj, key]
  · have hu : IsUnit (Bᴴ * B).det := by rw [det_mul]; exact hBH.mul hB
    have : (-(Bᴴ * B))⁻¹ = -(Bᴴ * B)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [neg_mul_neg, Matrix.nonsing_inv_mul _ hu]
    rw [cj, this, neg_mul, neg_mul_neg, key]

theorem sum_squares {A : Type} [Ring A] [Algebra ℂ A] (F : Fin n → Fin n → A) :
    ∑ a, ∑ b, F a b * F b a =
      -∑ a, ∑ b, (((1 / 2 : ℂ) • (F a b - F b a)) * ((1 / 2 : ℂ) • (F a b - F b a)) +
        ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) * ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a))) := by
  have h : (1 / (2 * Complex.I) : ℂ) * (1 / (2 * Complex.I)) = -(1 / 4) := by
    field_simp
    simp
    norm_num
  have h1 : ∀ a b, ((1 / 2 : ℂ) • (F a b - F b a)) * ((1 / 2 : ℂ) • (F a b - F b a)) +
        ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) * ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) =
        -((1 / 2 : ℂ) • (F a b * F b a) + (1 / 2 : ℂ) • (F b a * F a b)) := by
    intro a b
    simp only [smul_mul_smul_comm, h, mul_add, add_mul, mul_sub, sub_mul]
    module
  simp only [h1, Finset.sum_neg_distrib, neg_neg, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => F b a * F a b)]
  module

theorem casimir_eq_neg_sum_sq : ∀ (n : ℕ) (J B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det → (J = Bᴴ * B ∨ J = -(Bᴴ * B)) → ∃ X : Fin n × Fin n × Bool → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Submodule.span ℝ (Set.range X) = ⊤ ∧ ∀ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ Y Z, ρ (Y + Z) = ρ Y + ρ Z) → (∀ (c : ℝ) Y, ρ (c • Y) = (c : ℂ) • ρ Y) → ∑ a, ∑ b, (ρ (P a b) + Complex.I • ρ (Q a b)) * (ρ (P b a) + Complex.I • ρ (Q b a)) = -∑ i, ρ (X i) * ρ (X i) := by
  intro n J B hB h
  have hBH : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact hB.star
  have hJ : Jᴴ = J := by
    rcases h with rfl | rfl <;> simp
  have hu : IsUnit J.det := by
    rcases h with rfl | rfl
    · rw [det_mul]; exact hBH.mul hB
    · rw [det_neg, det_mul]; exact (isUnit_one.neg.pow _).mul (hBH.mul hB)
  let F : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b => B⁻¹ * single a b 1 * B
  let X : Fin n × Fin n × Bool → lieU J := fun p =>
    if p.2.2 then rePart hJ hu (F p.1 p.2.1) else imPart hJ hu (F p.1 p.2.1)
  refine ⟨X, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro Y -
    let S : Submodule ℝ (lieU J) := Submodule.span ℝ (Set.range X)
    have hS : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => F p.1 p.2) →
        ∃ U ∈ S, ∃ V ∈ S, Z = U.1 + Complex.I • V.1 := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem Z hZ =>
        obtain ⟨⟨a, b⟩, rfl⟩ := hZ
        exact ⟨_, Submodule.subset_span ⟨(a, b, true), rfl⟩, _, Submodule.subset_span ⟨(a, b, false), rfl⟩,
          (re_add_im hJ hu _).symm⟩
      | zero => exact ⟨0, S.zero_mem, 0, S.zero_mem, by simp⟩
      | add Z W _ _ hZ hW =>
        obtain ⟨U, hU, V, hV, rfl⟩ := hZ
        obtain ⟨U', hU', V', hV', rfl⟩ := hW
        refine ⟨U + U', S.add_mem hU hU', V + V', S.add_mem hV hV', ?_⟩
        change _ = (U.1 + U'.1) + Complex.I • (V.1 + V'.1)
        module
      | smul c Z _ hZ =>
        obtain ⟨U, hU, V, hV, rfl⟩ := hZ
        have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
        generalize c.re = a at hc
        generalize c.im = b at hc
        subst hc
        refine ⟨a • U - b • V, S.sub_mem (S.smul_mem _ hU) (S.smul_mem _ hV), b • U + a • V,
          S.add_mem (S.smul_mem _ hU) (S.smul_mem _ hV), ?_⟩
        have hII : ∀ (m : Matrix (Fin n) (Fin n) ℂ), Complex.I • Complex.I • m = -m := by
          intro m
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        change _ = ((a : ℂ) • U.1 - (b : ℂ) • V.1) + Complex.I • ((b : ℂ) • U.1 + (a : ℂ) • V.1)
        simp only [add_smul, smul_add, mul_smul, hII]
        module
    have hY : Y.1 ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => F p.1 p.2) := by
      have : Y.1 = B⁻¹ * (B * Y.1 * B⁻¹) * B := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.one_mul, Matrix.mul_assoc,
          Matrix.nonsing_inv_mul B hB, Matrix.mul_one]
      rw [this, Matrix.matrix_eq_sum_single (B * Y.1 * B⁻¹)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      have : Matrix.single a b ((B * Y.1 * B⁻¹) a b) = (B * Y.1 * B⁻¹) a b • Matrix.single a b (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [this, mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)
    obtain ⟨U, hU, V, -, hUV⟩ := hS _ hY
    have h1 := rePart_mk hJ hu U V
    have h2 := rePart_mk hJ hu Y 0
    have h3 : Y.1 + Complex.I • (0 : lieU J).1 = Y.1 := by simp
    rw [h3, hUV, h1] at h2
    rw [← h2]
    exact hU
  · intro P Q hPQ A _ _ ρ hadd hsm
    obtain ⟨R, hR, hX⟩ := exists_linear_extension hJ hu ρ hadd hsm
    have hP : ∀ a b, P a b = rePart hJ hu (single a b 1) := fun a b => Subtype.ext (hPQ a b).1
    have hQ : ∀ a b, Q a b = imPart hJ hu (single a b 1) := fun a b => Subtype.ext (hPQ a b).2
    simp only [hP, hQ, ← hR]
    rw [casimir_conj R B hB, sum_squares (fun a b => R (F a b))]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e1 : ρ (X (a, b, true)) = (1 / 2 : ℂ) • (R (F a b) - R (F b a)) := by
      rw [← hX]
      change R ((1 / 2 : ℂ) • (F a b + cj J (F a b))) = _
      rw [cj_conj_single B hB h, map_smul, map_add, map_neg, ← sub_eq_add_neg]
    have e2 : ρ (X (a, b, false)) = (1 / (2 * Complex.I) : ℂ) • (R (F a b) + R (F b a)) := by
      rw [← hX]
      change R ((1 / (2 * Complex.I) : ℂ) • (F a b - cj J (F a b))) = _
      rw [cj_conj_single B hB h, map_smul, map_sub, map_neg, sub_neg_eq_add]
    rw [Fintype.sum_bool, e1, e2]

end GlobalTheory.DefiniteUnitaryCasimir
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureSmulFactorsEqSmul
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdScale

theorem finite_mulSupport_sub {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (p : ι → Prop) : (Function.mulSupport fun v : {v // p v} => (r v.1 : ℝ)).Finite := by
  refine (hr.preimage (f := (Subtype.val : {v // p v} → ι)) Subtype.val_injective.injOn).subset ?_
  intro v hv h
  exact hv (by simp [h])

theorem summable_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) : Summable fun v => |r v * f v - 1| := by
  refine hf.congr_cofinite ?_
  filter_upwards [hr.compl_mem_cofinite] with v hv
  have : r v = 1 := by simpa using hv
  simp [this]

theorem finprod_eq {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ((∏ᶠ v, r v : ℝ≥0) : ℝ) = (∏ v ∈ S, (r v : ℝ)) * ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : (Function.mulSupport fun v => (r v : ℝ)).Finite :=
    hr.subset fun v hv h => hv (by simp [h])
  have h1 : ((∏ᶠ v, r v : ℝ≥0) : ℝ) = ∏ᶠ v, (r v : ℝ) :=
    NNReal.toRealHom.toMonoidHom.map_finprod hr
  rw [h1, ← tprod_eq_finprod (L := SummationFilter.unconditional ι) h0, ← Finset.tprod_subtype' S (fun v => (r v : ℝ))]
  exact (Multipliable.tprod_mul_tprod_compl (f := fun v => (r v : ℝ)) (s := (S : Set ι))
    (multipliable_of_finite_mulSupport (finite_mulSupport_sub r hr _))
    (multipliable_of_finite_mulSupport (finite_mulSupport_sub r hr _))).symm

theorem tprod_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ∏' v : {v // v ∉ S}, ((r v.1 : ℝ) * f v.1) =
      (∏' v : {v // v ∉ S}, (r v.1 : ℝ)) * ∏' v : {v // v ∉ S}, f v.1 := by
  refine Multipliable.tprod_mul
    (multipliable_of_finite_mulSupport (finite_mulSupport_sub r hr _)) ?_
  have h := multipliable_one_add_of_summable (f := fun v : {v // v ∉ S} => f v.1 - 1)
    (hf.subtype {v | v ∉ S})
  simpa using h

theorem finprod_ennreal {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (S : Finset ι) :
    ∃ c : ℝ≥0, (∏ᶠ v, r v) = (∏ v ∈ S, r v) * c ∧ (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
    rw [tprod_eq_finprod (finite_mulSupport_sub r hr _)]
    exact finprod_nonneg fun v => (r v.1).2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := ⟨⟨_, h0⟩, rfl⟩
  refine ⟨c, ?_, hc⟩
  apply NNReal.coe_injective
  rw [finprod_eq r hr S, ← hc]
  simp

theorem isProd_smul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ri : ℝ≥0)
    (r : HeightOneSpectrum (𝓞 F) → ℝ≥0) (h : IsProd b ν mi mv)
    (hr : (Function.mulSupport r).Finite) :
    IsProd b ((ri * ∏ᶠ v, r v) • ν) (ri • mi) (fun v => r v • mv v) := by
  obtain ⟨⟨hi, hv, hs⟩, hf⟩ := h
  have key : ∀ v, ((r v • mv v) (latV b v)).toReal = r v * (mv v (latV b v)).toReal := by
    intro v
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  refine ⟨⟨inferInstance, fun v => inferInstance, ?_⟩, ?_⟩
  · simp only [key]
    exact summable_scale _ r hs hr
  · intro S fi fv hfi hfv
    obtain ⟨c, hc, hc'⟩ := finprod_ennreal r hr S
    have ht : tailProd b (fun v => r v • mv v) S = c * tailProd b mv S := by
      unfold tailProd
      simp only [key]
      rw [tprod_scale (fun v => (mv v (latV b v)).toReal) r hs hr S, ← hc',
        ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    rw [Measure.restrict_smul, lintegral_smul_measure, hf S fi fv hfi hfv, ht, hc]
    simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
    push_cast
    ring

end GlobalTheory.GaugeEx.ProdScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationalityStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardOperator_preserves_rationality : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), (∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x) → ∀ (v : (D.mem u).A.vT) (x : ((D.fm u).lat 0).V), LT.Uop D u 0 v ((D.fm u).emb 0 x) ∈ (D.fm u).Fi 0 → ∃ y, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x) := by
  first | exact @GlobalTheory.LevelHecke.uop_rat | exact GlobalTheory.LevelHecke.uop_rat | (intros; apply GlobalTheory.LevelHecke.uop_rat <;> assumption)
end


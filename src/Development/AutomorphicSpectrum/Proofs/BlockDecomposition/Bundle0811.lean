import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0804
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsExponentPolynomialDiscrete
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0800
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0799
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0805
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0806
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf

namespace GlobalTheory.CompanionTheory.SwUnf

open PositivityTheory.GramSchwartzFunctions.EC

section Blocks

variable {K : Type} [Field K] {n : ℕ}

theorem lowerC_apply' (M : Matrix (Fin (n + n)) (Fin (n + n)) K) (i j : Fin n) :
    lowerC M i j = M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) := rfl

theorem lowerC_siegel_mul {y : Matrix (Fin (n + n)) (Fin (n + n)) K} (hy : IsSiegelP y)
    (W : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    lowerC (y * W) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD y * lowerC W := by
  have hy' : ∀ i j : Fin n, y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := hy
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hy', zero_mul, Finset.sum_const_zero, zero_add, GlobalTheory.CompanionTheory.RatPtsUnn.blkD]

theorem lowerC_mul_unip (X : Matrix (Fin (n + n)) (Fin (n + n)) K) (b : Matrix (Fin n) (Fin n) K) :
    lowerC (X * blk4 1 b 0 1) = lowerC X := by
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₁, Matrix.one_apply, Matrix.zero_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero]

end Blocks

variable {D : D7} {n : ℕ}

private theorem incA_injective' (D : D7) : Function.Injective (incA D) := by
  haveI : Nontrivial (AF D.host.F) :=
    inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing D.host.F ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F))
  haveI : Nontrivial (AF D.host.F ⊗[D.host.F] D.host.E) :=
    Function.Injective.nontrivial
      (Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective)
  exact (incA D).injective

theorem isUnit_det_of_mat (x : GF D n) {g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
    (h : mat (x : G D n) = g.map (incA D)) : IsUnit g.det := by
  obtain ⟨g', hg', -, hg'm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause1 (x : G D n) x.2
  have hgg : g = g' := Matrix.map_injective (incA_injective' D) (h.symm.trans hg'm)
  rw [hgg]
  exact hg'

private theorem mat_mul_eq_ite_of_hasMult {D : D7} {n : ℕ} (a b : G D n) : mat (a * b) = mat a * mat b := by
  simp only [mat, map_mul, Units.val_mul]

theorem cosetCell_rmulEquiv : ∀ {D : D7} {n : ℕ} (q : Cosets (P D n) (GF D n)) (γ : GF D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat (γ : G D n) = blk4 1 (b.map (incA D)) 0 1 → cosetCell (rmulEquiv (P D n) (GF D n) γ q) = cosetCell q := by
  intro D n q γ b h
  set q' := rmulEquiv (P D n) (GF D n) γ q with hq'
  have e3 : GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) :=
    calc GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = q' := Quotient.out_eq q'
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ q := rfl
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ (GlobalTheory.AutomorphicL2Unitary.mk _ q.out) :=
        congrArg (GlobalTheory.AutomorphicL2Unitary.rmul _ γ) (Quotient.out_eq q).symm
      _ = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) := GlobalTheory.AutomorphicL2Unitary.rmul_mk _ _
  obtain ⟨p, hp⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.mp e3
  have hp' : ((p : GF D n) : G D n) * (q'.out : G D n) = (q.out : G D n) * (γ : G D n) :=
    congrArg Subtype.val hp
  have hb : blk4 1 (b.map (incA D)) 0 1 = (blk4 1 b 0 1).map (incA D) := by
    have h1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := (incA D).mapMatrix.map_one
    have h0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := (incA D).mapMatrix.map_zero
    unfold blk4
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, h1, h0]
  have hm := congrArg mat hp'
  rw [mat_mul_eq_ite_of_hasMult, mat_mul_eq_ite_of_hasMult, h, mat_ratOf, mat_ratOf, mat_ratOf, hb, ← Matrix.map_mul,
    ← Matrix.map_mul] at hm
  have hm2 : ratOf (p : GF D n) * ratOf q'.out = ratOf q.out * blk4 1 b 0 1 :=
    Matrix.map_injective (incA_injective' D) hm
  have hpP : ((p : GF D n) : G D n) ∈ P D n := Subgroup.mem_subgroupOf.mp p.2
  have hS : IsSiegelP (ratOf (p : GF D n)) :=
    (GlobalTheory.CompanionTheory.RatPtsUnn.clause3 _ (p : GF D n).2 _ (mat_ratOf (p : GF D n))).mp hpP
  have hC : lowerC (ratOf q.out) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) * lowerC (ratOf q'.out) := by
    rw [← lowerC_mul_unip (ratOf q.out) b, ← hm2, lowerC_siegel_mul hS]
  have hU : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n))).det := by
    have hd := isUnit_det_of_mat (p : GF D n) (mat_ratOf (p : GF D n))
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero _ hS] at hd
    exact isUnit_of_mul_isUnit_right hd
  have hinj : ∀ w, GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) *ᵥ w = 0 → w = 0 := by
    intro w hw
    rw [← Matrix.one_mulVec w, ← Matrix.nonsing_inv_mul _ hU, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero]
  simp only [cosetCell, cellKer]
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [hC, ← Matrix.mulVec_mulVec]
  constructor
  · intro h0
    rw [h0, Matrix.mulVec_zero]
  · intro h0
    exact hinj _ h0

end GlobalTheory.CompanionTheory.SwUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeightsStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_holomorphy_of_heights : HtExist → EisHol := by
  first | exact @GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist | exact GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist | (intros; apply GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsExponentPolynomialDiscreteStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponent_polynomial_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N r : ℕ), 0 < r → r < N → ∃ D : ℕ, ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
  (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL V τ m) → ∀ φ ∈ V, ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ D ∧ An.Kill r φ.1 p ∧
    ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
  first | exact @GlobalTheory.CompanionTheory.KillU.killU | exact GlobalTheory.CompanionTheory.KillU.killU | (intros; apply GlobalTheory.CompanionTheory.KillU.killU <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionByOneFormulaStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_extension_by_one_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibSF σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ UsetF σ J t B₀)ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.fibSF_support | exact GlobalTheory.CompanionTheory.SW.StageF.fibSF_support | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.fibSF_support <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionByOneIntegralStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_extension_by_one_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem | exact GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionCompatibleStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_extension_compatible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free | exact GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionHaarStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_extension_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} → ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibSF σ J t m₁ m' s B₀ a κ₁ cm S) ∧ ∫ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = ((κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) * cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n : ℝ≥0) : ℝ) * Preal σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.integrable_fibSF_and_integral | exact GlobalTheory.CompanionTheory.SW.StageF.integrable_fibSF_and_integral | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.integrable_fibSF_and_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionMeasurableStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_lintegral_blockOne_eq_iterated : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF | exact GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSigmaFiniteStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_extension_sigma_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Set.univ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.ContTwoF.cont_double_free | exact GlobalTheory.CompanionTheory.SW.StageF.ContTwoF.cont_double_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.ContTwoF.cont_double_free <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSymmetricStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_extension_symmetric : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | exact GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalPairTypedStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_pair_typed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ (typed U₁ K₁ W₁) → FiniteDimensional ℂ (typed U₂ K₂ W₂) → FiniteDimensional ℂ ((pairSpace U₁ U₂ ⊓ typeHF K₁ K₂ W₁ W₂ : Submodule ℂ (H E a b → ℂ))) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF | exact GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF | (intros; apply GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedExtensionStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_typed_extension : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z : ℂ), (∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U K W)) → ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (tw U z) K W) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.typed_tw_finite | exact GlobalTheory.CompanionTheory.LimV.typed_tw_finite | (intros; apply GlobalTheory.CompanionTheory.LimV.typed_tw_finite <;> assumption)
end


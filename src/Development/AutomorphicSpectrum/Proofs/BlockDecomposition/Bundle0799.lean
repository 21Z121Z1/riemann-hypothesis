import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0794
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0791
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0002
import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.EcHeisSch
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0795
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0005
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoCoinvariantsOfBernstein
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitTop

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistAbsoluteCharacterStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_twist_absolute_character : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z z' : ℂ), Carries (absFn N (z' - z)) (tw U z) (tw U z') := by
  first | exact @GlobalTheory.CompanionTheory.LimV.carries_absFn_tw | exact GlobalTheory.CompanionTheory.LimV.carries_absFn_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.carries_absFn_tw <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_twist : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (e : GA E N → ℂ) (U U' : Submodule ℂ (Sm E N)) (z : ℂ), Carries e U U' → Carries e (tw U z) (tw U' z) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.carries_tw | exact GlobalTheory.CompanionTheory.LimV.carries_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.carries_tw <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHeckeCapelliOperatorsStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_hecke_capelli_operators : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s →
  ∃ (S : Subalgebra ℂ (Module.End ℂ (Sm E (r + s)))) (a b : (E →+* ℂ) → ℕ → Module.End ℂ (Sm E (r + s))) (t : (E →+* ℂ) → ℂ),
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
    (∀ x ∈ S, ∀ (τ : E →+* ℂ) (u : ℂ), Commute (cap (a := r + s) τ u) x) ∧
    (∀ x ∈ S, ∀ F : Sm E (r + s), (∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g) →
      ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (x F).1 (unip v * g) = (x F).1 g) ∧
    (∀ τ k, a τ k ∈ S) ∧ (∀ τ k, b τ k ∈ S) ∧ (∀ τ, a τ r = 1) ∧ (∀ τ, b τ s = 1) ∧
    (∀ τ, a τ (r - 1) = ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) + t τ • 1) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capR r s τ (u - (s : ℂ) / 2) = ∑ k ∈ Finset.range (r + 1), u ^ k • a τ k) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capS r s τ (u + (r : ℂ) / 2) = ∑ k ∈ Finset.range (s + 1), u ^ k • b τ k) := by
  first | exact @GlobalTheory.CompanionTheory.CapCoeff.exists_coeffs | exact GlobalTheory.CompanionTheory.CapCoeff.exists_coeffs | (intros; apply GlobalTheory.CompanionTheory.CapCoeff.exists_coeffs <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompactStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_free_set_projects_compact : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [T2Space K] (M n : ℕ) (Q : Set (Fin (n + 1) → Fin (M + 1) → K)), IsCompact Q → (∀ Y ∈ Q, LinearIndependent K Y) → ∃ C : Set (Fin n → Fin M → K), IsCompact C ∧ (∀ X ∈ C, LinearIndependent K X) ∧ ∀ (A : K) (c : Fin n → K) (X : Fin n → Fin M → K), vec A c X ∈ Q → X ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | exact GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSymmUnitaryChart
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.ChartSymm

theorem continuous_mat {D : D7} {n : ℕ} : Continuous (mat : G D n → Mx D (n + n) (n + n)) := by
  unfold GlobalTheory.StdUnn.mat
  exact Continuous.comp' Units.continuous_val continuous_induced_dom

private theorem gram_conjTranspose_eq_self {D : D7} (S : HSp D) :
    (Formalism.BasicNotions.HSpace.gram S).conjTranspose = Formalism.BasicNotions.HSpace.gram S := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Formalism.BasicNotions.HSpace.gram]
  exact S.herm.eq (S.frame j) (S.frame i)

private theorem fromRows_gram_mul_fromCols_eq_one_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : D.host.E)
    (hμ : μ ≠ 0) :
    Matrix.fromRows (d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S)
        (μ⁻¹ • (d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S)) *
      Matrix.fromCols d.e (μ • d.e') = 1 := by
  have h1 : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 1 := d.e'e
  have h0 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 0 := d.ee
  have h0' : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 0 := d.e'e'
  have h2 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 1 := by
    have h := congrArg Matrix.conjTranspose h1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose_eq_self,
      Matrix.conjTranspose_one] at h
    rw [Matrix.mul_assoc]
    exact h
  rw [Matrix.fromRows_mul_fromCols]
  simp only [Matrix.mul_smul, Matrix.smul_mul, h1, h0, h0', h2, smul_zero, smul_smul,
    inv_mul_cancel₀ hμ, mul_inv_cancel₀ hμ, one_smul, Matrix.fromBlocks_one]

theorem continuous_symm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ (κ : GA D (dblSp A) ≃* G D A.rank), IsChart A μ κ →
    Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hL : ((Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id) * Tm A μ = 1 := by
    show _ * (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e')).submatrix id finSumFinEquiv.symm = 1
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, fromRows_gram_mul_fromCols_eq_one_of_hypDec _ μ hμ.1,
      Matrix.submatrix_one_equiv]
  have hR := mul_eq_one_comm.mp hL
  set L := (Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id with hLdef
  have hTP : rat (Tm A μ) * rat L = (1 : Mx D (A.rank + A.rank) (A.rank + A.rank)) := by
    show (incA D).mapMatrix (Tm A μ) * (incA D).mapMatrix L = 1
    rw [← map_mul, hR, map_one]
  have key : ∀ h : G D A.rank, mt (dblSp A) (κ.symm h) = rat (Tm A μ) * mat h * rat L := by
    intro h
    have e := hκ (κ.symm h)
    rw [MulEquiv.apply_symm_apply] at e
    calc mt (dblSp A) (κ.symm h) = mt (dblSp A) (κ.symm h) * (rat (Tm A μ) * rat L) := by
          rw [hTP, Matrix.mul_one]
      _ = (mt (dblSp A) (κ.symm h) * rat (Tm A μ)) * rat L := by rw [Matrix.mul_assoc]
      _ = rat (Tm A μ) * mat h * rat L := by rw [← e]
  have hind : Topology.IsInducing (fun g : GA D (dblSp A) => matHom (dblSp A) g) := ⟨rfl⟩
  have hmi : Continuous (fun h : G D A.rank => mat h⁻¹) := by
    unfold GlobalTheory.StdUnn.mat
    simp only [map_inv]
    exact Units.continuous_coe_inv.comp continuous_induced_dom
  rw [hind.continuous_iff, Units.continuous_iff]
  constructor
  · have hf : (Units.val ∘ (fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) =
        fun h => rat (Tm A μ) * mat h * rat L := by
      funext h
      exact key h
    rw [hf]
    exact (continuous_const.matrix_mul continuous_mat).matrix_mul continuous_const
  · have hf : (fun h : G D A.rank => (((fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) h)⁻¹.val) =
        fun h => rat (Tm A μ) * mat h⁻¹ * rat L := by
      funext h
      simp only [Function.comp_apply]
      rw [← map_inv (matHom (dblSp A)), ← map_inv κ.symm]
      exact key h⁻¹
    rw [hf]
    exact (continuous_const.matrix_mul hmi).matrix_mul continuous_const

end GlobalTheory.CompanionTheory.ChartSymm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeisenbergSchwartz
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HeisSchwartz

theorem heisSch_holds : PositivityTheory.GramSchwartzFunctions.EC.HeisSch := PositivityTheory.RdEc.heisSch

end GlobalTheory.CompanionTheory.HeisSchwartz
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDeterminingSetStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_determining_set : ∀ {A : Type} (W : Submodule ℂ (A → ℂ)), FiniteDimensional ℂ W → ∃ S : Finset A, ∀ w ∈ W, (∀ a ∈ S, w a = 0) → w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points | exact GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points | (intros; apply GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRescaledConvergentSubsequenceStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescaled_convergent_subsequence : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (g : ℕ → M), (∀ k, g k ≠ 0) → ∃ (c : ℕ → ℂ) (φ : ℕ → ℕ) (G : M), StrictMono φ ∧ G ≠ 0 ∧ ∀ ℓ : Module.Dual ℂ M, Tendsto (fun k => c k * ℓ (g (φ k))) atTop (𝓝 (ℓ G)) := by
  first | exact @GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit | exact GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit | (intros; apply GlobalTheory.CompanionTheory.LimVec.normalised_subseq_limit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralContinuousInParameterStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integral_continuous_in_parameter : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V), IsOpen U → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → C ⊆ U → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset | exact GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset | (intros; apply GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow
section
open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BernBridge.Split

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr

def NarrowBernstein : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible

def IndIrredLt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ), (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
    IsSmoothChar α → IsSmoothChar β → a' < a →
    ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β

theorem indIrredLt_of (NB : NarrowBernstein) : IndIrredLt := by
  intro k _ _ _ _ a a' α β hα hβ sα sβ hlt N hN hr
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  refine Or.inr (le_antisymm hN ?_)
  obtain ⟨F, hFN, hF0⟩ := (Submodule.ne_bot_iff N).1 h0
  have hI : (parInd (two (stdE a a')) (rhoD a a' α β)).IsIrreducible :=
    NB k a a' α β sα sβ hα hβ (Or.inl hlt.ne')
  let S : Subrepresentation (parInd (two (stdE a a')) (rhoD a a' α β)) :=
    ⟨N.comap (toFn a a' α β), fun g f hf => hr g _ hf⟩
  rcases hI.eq_bot_or_eq_top S with e | e
  · obtain ⟨f, rfl⟩ := exists_toFn (hN hFN)
    have hf : f ∈ S.toSubmodule := hFN
    rw [e] at hf
    have hf0 : f = 0 := hf
    exact absurd (by rw [hf0, map_zero]) hF0
  · intro G hG
    obtain ⟨f, rfl⟩ := exists_toFn hG
    have hf : f ∈ S.toSubmodule := by rw [e]; trivial
    exact hf

section Onto
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem onto_of_irredLt (hI : IndIrredLt) {a a' : ℕ} {α β : kˣ →* ℂˣ} (hα : ∀ x, ‖(α x : ℂ)‖ = 1)
    (hβ : ∀ x, ‖(β x : ℂ)‖ = 1) (sα : IsSmoothChar α) (sβ : IsSmoothChar β) (hlt : a' < a)
    {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hlin : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁)
    (hin : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ))
    (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) : ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hlin 0 (SB X).zero_mem 0 (SB X).zero_mem 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + (1 : ℂ) • Φ₁, (SB X).add_mem hΦ ((SB X).smul_mem _ hΦ₁), by rw [hlin _ hΦ _ hΦ₁, one_smul]⟩
      zero_mem' := ⟨0, (SB X).zero_mem, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨0 + c • Φ, (SB X).add_mem (SB X).zero_mem ((SB X).smul_mem _ hΦ), by
          rw [hlin _ (SB X).zero_mem _ hΦ, h0, zero_add]⟩ }
  have hle : N ≤ indSp a a' α β := by
    rintro _ ⟨Φ, hΦ, rfl⟩
    exact hin Φ hΦ
  have hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N := by
    rintro h₁ _ ⟨Φ, hΦ, rfl⟩
    exact heq Φ hΦ h₁
  rcases hI k a a' α β hα hβ sα sβ hlt N hle hst with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    have hm : p Φ ∈ N := ⟨Φ, hΦ, rfl⟩
    rw [h] at hm
    exact absurd ((Submodule.mem_bot ℂ).1 hm) hne
  · intro F hF
    rw [← h] at hF
    exact hF

end Onto

theorem unrMaps_of_lt (hI : IndIrredLt) : UnrMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν hS hα hβ
  have hν := isUnram_nu hS hα hβ
  have hp1 := p_lin hS hν
  have hp2 := p'_lin hS hν
  have hp3 := p_mem hS hν hβ
  have hp4 := p'_mem hS hν hα
  have hu := p_unit hS hν hβ
  have hu' := p'_unit hS hν hα
  have sα : IsSmoothChar α := isSmoothChar_of_isUnram hα
  have sβ : IsSmoothChar β := isSmoothChar_of_isUnram hβ
  refine ⟨hp1, hp2, hp3, hp4, p_inv hS hν, p'_inv hS hν, fun Φ _ h₁ => p_equiv Φ h₁, fun Ψ _ h₁ => p'_equiv Ψ h₁,
    ?_, ?_, hu, hu'⟩
  · refine onto_of_irredLt hI hS.unitα hS.unitβ sα sβ hS.lt _ hp1 hp3
      (fun Φ hΦ h₁ => ⟨_, omA_mem_SB ν β 1 h₁ hΦ, p_equiv Φ h₁⟩) ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu 1 (one_mem _)] using congrFun h0 1
  · refine onto_of_irredLt hI hS.unitα hS.unitβ sα sβ hS.lt _ hp2 hp4
      (fun Ψ hΨ h₁ => ⟨_, omB_mem_SB ν α 1 h₁ hΨ, p'_equiv Ψ h₁⟩) ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu' 1 (one_mem _)] using congrFun h0 1

section Global

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThK PositivityTheory.ThK.SplitAsm

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance measFv {F : Type} [Field F] [NumberField F] (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFv {F : Type} [Field F] [NumberField F] (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

theorem finSplit_of_lt (hU : UnrMaps) (hI : IndIrredLt) (hIw : IndIwasawa) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts)
    (hZ : IntEq) : FinSplit := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨hv, ⟨τ⟩⟩
  obtain ⟨hα, hβ, hν, hcond, -, hunr⟩ := hC F E B X a a' v τ hT.chars
  obtain ⟨hαu, hβu⟩ := hunr hv
  have hS : HidaSetting a a' (unifAt v) (chrW X.α τ) (chrW X.β τ) (chrW X.ν τ) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon', hsph, hsph'⟩ :=
    hU (Fv F v) a a' _ _ _ _ hS hαu hβu
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, -, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v τ
  have hind : ∀ m n : ℕ, (intInd v : Matrix (Fin m) (Fin n) (Fv F v) → ℂ) =
      Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[Fv F v]} 1 := by
    intro m n
    unfold intInd
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq, hZ F v]
  have h1 : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph h hh
  have h1' : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph' h hh
  have hiSB : intInd v ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := by
    rw [← hvac]; exact hW.bij.mapsTo (hT.geo.hM.vac v).1
  have hnz : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) ≠ 0 := fun h0 => by
    have := h1 1 (one_mem _)
    rw [h0] at this
    exact zero_ne_one this
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ)) (pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨_, hiSB, hnz⟩
    (fun N hN hst => hI (Fv F v) a a' _ _ hα hβ (isSmoothChar_of_isUnram hαu) (isSmoothChar_of_isUnram hβu)
      hT.geo.lt N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro _
    rw [oneMaps_p, oneMaps_p']
    have e1 := hp _ (hT.geo.hM.vac v).1
    have e2 := hp' _ (hT.geo.hM'.vac v).1
    rw [hvac] at e1
    rw [hvac'] at e2
    have hm1 := hmem _ hiSB
    have hm2 : pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) ∈ indSp a a' (chrW X.α τ) (chrW X.β τ) := by
      rw [← e2]; exact (p' (G.M'.vac v)).2
    have hd : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) -
        pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) = 0 :=
      hIw (Fv F v) a a' _ _ _ (Submodule.sub_mem _ hm1 hm2) fun h hh => by
        simp only [Pi.sub_apply, h1 h hh, h1' h hh, sub_self]
    refine ⟨Subtype.ext ?_, fun h0 => hnz ?_⟩
    · erw [e1, e2]; exact sub_eq_zero.1 hd
    · have := congrArg Subtype.val h0
      erw [e1] at this
      exact this
  · intro _ hvT; exact absurd hvT hv

theorem finSplit_of_narrow : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) → PositivityTheory.ThK.FinSplit :=
  fun NB => finSplit_of_lt (unrMaps_of_lt (indIrredLt_of NB)) (indIrredLt_of NB) induced_vanish_of_vanish_on_integral split_place_dictionary
    PositivityTheory.KCo.action_uniqueness split_character_facts valuation_integers_eq_completion

end Global

end GlobalTheory.CompanionTheory.BernBridge.Split
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableInducedSpanStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finStable_induced_span : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), FinStable (indSpan U₁ U₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.indSpan_finStable | exact GlobalTheory.CompanionTheory.LimV.indSpan_finStable | (intros; apply GlobalTheory.CompanionTheory.LimV.indSpan_finStable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableTwistStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finStable_twist : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z : ℂ), FinStable U → FinStable (tw U z) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.finStable_tw | exact GlobalTheory.CompanionTheory.LimV.finStable_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.finStable_tw <;> assumption)
end


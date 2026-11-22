import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0780
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0819
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0826
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0828
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0821
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivity
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScalingStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_GL_right_scaling : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (g : GL (Fin t) (AE D)), (nuT hn I μ x₀).map (fun z => (z.1, mm z.2 g.1)) = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (W.rank + t) : ℝ≥0) • nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov | exact GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFactorizationRows
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.ClassRep

variable {K : Type} [Field K]

theorem blkMul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blkInj {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h' := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  exact Matrix.fromBlocks_inj.mp h'

theorem blMul {n ρ p : ℕ} (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K)
    (b b' : Matrix (Fin ρ) (Fin p) K) (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem cTMul (σ : K →+* K) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) K) (y : Matrix (Fin b) (Fin c) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (x * y) = PositivityTheory.GramSchwartzFunctions.EC.cT σ y * PositivityTheory.GramSchwartzFunctions.EC.cT σ x := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cTAdd (σ : K →+* K) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (x + y) = PositivityTheory.GramSchwartzFunctions.EC.cT σ x + PositivityTheory.GramSchwartzFunctions.EC.cT σ y := by
  ext i j
  simp [PositivityTheory.GramSchwartzFunctions.EC.cT]

theorem cTZero (σ : K →+* K) {a b : ℕ} : PositivityTheory.GramSchwartzFunctions.EC.cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  ext i j
  simp [PositivityTheory.GramSchwartzFunctions.EC.cT]

theorem cTInvol (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (PositivityTheory.GramSchwartzFunctions.EC.cT σ x) = x := by
  ext i j
  simp [PositivityTheory.GramSchwartzFunctions.EC.cT, hσ]

theorem cTBlk (σ : K →+* K) {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    PositivityTheory.GramSchwartzFunctions.EC.cT σ (blk4 a b c d) =
      blk4 (PositivityTheory.GramSchwartzFunctions.EC.cT σ a) (PositivityTheory.GramSchwartzFunctions.EC.cT σ c) (PositivityTheory.GramSchwartzFunctions.EC.cT σ b) (PositivityTheory.GramSchwartzFunctions.EC.cT σ d) := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.cT, blk4]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem siegel_relations (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {p : ℕ}
    {A B Dd : Matrix (Fin p) (Fin p) K}
    (hU : PositivityTheory.GramSchwartzFunctions.EC.IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd)) :
    Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A = 1 ∧
      A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B = B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by
  unfold PositivityTheory.GramSchwartzFunctions.EC.IsUnitary at hU
  rw [cTBlk, blkMul, blkMul] at hU
  obtain ⟨-, h12, h21, h22⟩ := blkInj hU
  simp only [cTZero, neg_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, Matrix.mul_neg,
    Matrix.neg_mul, mul_neg, neg_mul] at h12 h21 h22
  have e2 : PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd * A = 1 := neg_injective h21
  have e3 : PositivityTheory.GramSchwartzFunctions.EC.cT σ B * Dd = PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd * B := by
    exact (neg_add_eq_zero.mp h22).symm
  have e4 : Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A = 1 := mul_eq_one_comm.mp h12
  have e5 : A * PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd = 1 := mul_eq_one_comm.mp e2
  refine ⟨e4, ?_⟩
  calc A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B
      = A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B * (Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ A) := by rw [e4, mul_one]
    _ = A * (PositivityTheory.GramSchwartzFunctions.EC.cT σ B * Dd) * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by
        simp only [Matrix.mul_assoc]
    _ = (A * PositivityTheory.GramSchwartzFunctions.EC.cT σ Dd) * B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by
        rw [e3]; simp only [Matrix.mul_assoc]
    _ = B * PositivityTheory.GramSchwartzFunctions.EC.cT σ A := by rw [e5, one_mul]

theorem exists_change_rep : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ A B Dd : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd) → blk4 a b c d = blk4 A B 0 Dd * blk4 a₂ b₂ c₂ d₂ →
    ∀ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K), cT σ ζ = ζ →
    ∃ (ζ₂ : Matrix (Fin ρ) (Fin ρ) K) (η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      cT σ ζ₂ = ζ₂ ∧ rowC hn η a c = T * rowC hn η₂ a₂ c₂ ∧ rowD hn σ ζ η b d = T * rowD hn σ ζ₂ η₂ b₂ d₂ := by
  intro K _ σ hσ n ρ p hn a b c d a₂ b₂ c₂ d₂ A B Dd hU hs ζ η hζ
  obtain ⟨e4, e6⟩ := siegel_relations σ hσ hU
  rw [blkMul] at hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := blkInj hs
  refine ⟨ζ + η * B * PositivityTheory.GramSchwartzFunctions.EC.cT σ (η * A), η * A, bl hn 1 (-(η * B)) 0 Dd, ?_, ?_, ?_⟩
  · rw [cTAdd, hζ, cTMul, cTInvol σ hσ, cTMul σ η B]
    congr 1
    rw [cTMul σ η A]
    calc η * A * (PositivityTheory.GramSchwartzFunctions.EC.cT σ B * PositivityTheory.GramSchwartzFunctions.EC.cT σ η)
        = η * (A * PositivityTheory.GramSchwartzFunctions.EC.cT σ B) * PositivityTheory.GramSchwartzFunctions.EC.cT σ η := by simp only [Matrix.mul_assoc]
      _ = η * B * (PositivityTheory.GramSchwartzFunctions.EC.cT σ A * PositivityTheory.GramSchwartzFunctions.EC.cT σ η) := by
          rw [e6]; simp only [Matrix.mul_assoc]
  · simp only [rowC, blMul]
    congr 1
    · simp
    · simp [Matrix.mul_add, Matrix.mul_assoc, add_comm]
    · simp
    · simp
  · simp only [rowD, blMul]
    have e7 : Dd * PositivityTheory.GramSchwartzFunctions.EC.cT σ (η * A) = PositivityTheory.GramSchwartzFunctions.EC.cT σ η := by
      rw [cTMul, ← Matrix.mul_assoc, e4, Matrix.one_mul]
    congr 1
    · simp [Matrix.mul_assoc]
    · simp [Matrix.mul_add, Matrix.mul_assoc, add_comm]
    · simp [e7]
    · simp

end GlobalTheory.CompanionTheory.ZUnf.ClassRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonHermMain
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

theorem poissonHerm_main : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm := by
  intro D r V ψ θ μ lam ν φ hH hJ
  obtain ⟨hm, hψ, hθ, hμ, ⟨𝓖, hlam⟩, -, hφ, -⟩ := hH
  have hc := GlobalTheory.T.theta_integral_continuous D r V ψ θ μ φ hψ hθ hμ hφ
  have hu := GlobalTheory.T.theta_integral_locally_summable_bound D r V ψ θ μ φ hm hψ hθ hμ hφ
  have hW := GlobalTheory.T.siegel_eisenstein_coefficients_summable D r V ψ θ μ lam 𝓖 φ hm hψ hθ hμ hlam hφ
  obtain ⟨-, hP⟩ := GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam 𝓖 hlam _ hc hu
  have hgW : ∀ β : HermE D r, (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) ((hermEquiv (D := D) (r := r)) β) = W ψ V μ lam φ β :=
    fun β => (W_eq ψ V μ lam φ β).symm
  have hS : Summable (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
    refine (hermEquiv (D := D) (r := r)).summable_iff.1 ?_
    exact hW.congr fun β => (hgW β).symm
  have e := hP hS
  have hsumJ : ∑' b : HermE D r, J ψ V μ φ b = ∑' c : ratHerm D r, Jt ψ V μ φ c.1 :=
    (hermEquiv (D := D) (r := r)).tsum_eq (fun c => Jt ψ V μ φ c.1)
  have hsumW : ∑' β : HermE D r, W ψ V μ lam φ β = ∑' t : ratHerm D r, ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam := by
    rw [← (hermEquiv (D := D) (r := r)).tsum_eq]
    exact tsum_congr fun β => (hgW β).symm
  rw [hsumJ, e, ← hsumW]
  exact hW.hasSum

end GlobalTheory.CompanionTheory.HermPoisson
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsOfWeylHeisenbergProduct
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.LowerRows

variable {K : Type} [Field K] {n ρ p : ℕ}

theorem block_matrix_mul {m : ℕ} (a b c d a' b' c' d' : Matrix (Fin m) (Fin m) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockMatrix_mul_blockMatrix (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K) (b b' : Matrix (Fin ρ) (Fin p) K)
    (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockMatrix_add (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K) (b b' : Matrix (Fin ρ) (Fin p) K)
    (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  simp only [bl]
  rw [← Matrix.fromBlocks_add]
  rfl

theorem lowerRight_block_matrix {m : ℕ} (a b c d : Matrix (Fin m) (Fin m) K) :
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (blk4 a b c d) = d := by
  ext i j
  simp only [GlobalTheory.CompanionTheory.RatPtsUnn.blkD, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₂]

theorem lower_rows_word (σ : K →+* K) (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K)
    (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K) :
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  simp only [wM, nM, sM, eM, rowC, rowD, block_matrix_mul, BigCell.lowerLeft_block, lowerRight_block_matrix, blockMatrix_mul_blockMatrix,
    blockMatrix_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero, and_self]

theorem lower_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K),
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  intro K _ σ _ n ρ p hn a b c d ζ η
  exact lower_rows_word σ hn a b c d ζ η

end GlobalTheory.CompanionTheory.ZUnf.LowerRows
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsProportionalOfTransform
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.LowerRows

variable {R : Type} [CommRing R] {n ρ p : ℕ}

theorem lr_bl_mul (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem lr_bl_inj (hn : ρ + p = n) {a a' : Matrix (Fin ρ) (Fin ρ) R} {b b' : Matrix (Fin ρ) (Fin p) R}
    {c c' : Matrix (Fin p) (Fin ρ) R} {d d' : Matrix (Fin p) (Fin p) R}
    (h : bl hn a b c d = bl hn a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix (finSumFinEquiv.trans (finCongr hn))
    (finSumFinEquiv.trans (finCongr hn))) h
  simp only [bl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

theorem lr_exists_bl (hn : ρ + p = n) (T : Matrix (Fin n) (Fin n) R) :
    ∃ (T₁₁ : Matrix (Fin ρ) (Fin ρ) R) (T₁₂ : Matrix (Fin ρ) (Fin p) R)
      (T₂₁ : Matrix (Fin p) (Fin ρ) R) (T₂₂ : Matrix (Fin p) (Fin p) R),
      T = bl hn T₁₁ T₁₂ T₂₁ T₂₂ := by
  let M := T.submatrix (finSumFinEquiv.trans (finCongr hn)) (finSumFinEquiv.trans (finCongr hn))
  refine ⟨M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₁, M.toBlocks₂₂, ?_⟩
  simp only [bl, Matrix.fromBlocks_toBlocks, M, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id]

theorem lr_eq_zero {m : ℕ} (a b c d : Matrix (Fin p) (Fin p) R) (hy : IsUnit (blk4 a b c d).det)
    (X : Matrix (Fin m) (Fin p) R) (hc : X * c = 0) (hd : X * d = 0) : X = 0 := by
  have hF : IsUnit (Matrix.fromBlocks a b c d).det := by
    have h := hy
    simp only [blk4] at h
    rwa [Matrix.det_submatrix_equiv_self] at h
  have hRF : Matrix.fromCols (0 : Matrix (Fin m) (Fin p) R) X * Matrix.fromBlocks a b c d = 0 := by
    ext i (j | j)
    · simpa [Matrix.mul_apply, Fintype.sum_sum_type] using congrFun (congrFun hc i) j
    · simpa [Matrix.mul_apply, Fintype.sum_sum_type] using congrFun (congrFun hd i) j
  have hR : Matrix.fromCols (0 : Matrix (Fin m) (Fin p) R) X = 0 := by
    have h := congrArg (· * (Matrix.fromBlocks a b c d)⁻¹) hRF
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF] using h
  ext i j
  simpa using congrFun (congrFun hR i) (Sum.inr j)

end GlobalTheory.CompanionTheory.ZUnf.LowerRows

namespace GlobalTheory.CompanionTheory.ZUnf

open GlobalTheory.CompanionTheory.ZUnf.LowerRows in

theorem lowerRows_determine : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ : Matrix (Fin p) (Fin p) K) (ζ ζ₂ : Matrix (Fin ρ) (Fin ρ) K)
      (η η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
    rowC hn η₂ a₂ c₂ = T * rowC hn η a c → rowD hn σ ζ₂ η₂ b₂ d₂ = T * rowD hn σ ζ η b d →
    (∃ T' : Matrix (Fin p) (Fin p) K, c₂ = T' * c ∧ d₂ = T' * d) ∧
    (IsUnit (blk4 a b c d).det → a₂ = a → b₂ = b → c₂ = c → d₂ = d → ζ₂ = ζ ∧ η₂ = η) := by
  intro K _ σ _ n ρ p hn a b c d a₂ b₂ c₂ d₂ ζ ζ₂ η η₂ T h₁ h₂
  obtain ⟨T₁₁, T₁₂, T₂₁, T₂₂, rfl⟩ := lr_exists_bl hn T
  simp only [rowC, rowD, lr_bl_mul] at h₁ h₂
  obtain ⟨e₁, e₂, e₃, e₄⟩ := lr_bl_inj hn h₁
  obtain ⟨f₁, f₂, f₃, f₄⟩ := lr_bl_inj hn h₂
  have hT₁₁ : T₁₁ = 1 := by
    simpa using e₁.symm
  have hT₂₁ : T₂₁ = 0 := by
    simpa using e₃.symm
  subst hT₁₁ hT₂₁
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_neg, zero_add, add_zero,
    neg_zero] at e₂ e₄ f₁ f₂ f₃ f₄
  refine ⟨⟨T₂₂, e₄, f₄⟩, ?_⟩
  intro hy ha hb hc hd
  subst ha hb hc hd
  have hT₂₂ : T₂₂ = 1 := by
    have h0 : T₂₂ - 1 = 0 := by
      refine lr_eq_zero a₂ b₂ c₂ d₂ hy (T₂₂ - 1) ?_ ?_
      · rw [Matrix.sub_mul, Matrix.one_mul, ← e₄, sub_self]
      · rw [Matrix.sub_mul, Matrix.one_mul, ← f₄, sub_self]
    exact sub_eq_zero.1 h0
  subst hT₂₂
  have hη : η₂ = η := by
    have h := neg_injective (by simpa using f₃ : -cT σ η₂ = -cT σ η)
    ext i j
    have := congrFun (congrFun h j) i
    exact σ.injective (by simpa [cT] using this)
  subst hη
  have hT₁₂ : T₁₂ = 0 := by
    refine lr_eq_zero a₂ b₂ c₂ d₂ hy T₁₂ ?_ ?_
    · simpa using e₂
    · simpa using f₂
  subst hT₁₂
  refine ⟨?_, rfl⟩
  simpa using f₁

end GlobalTheory.CompanionTheory.ZUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreFormulaStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_extension_fibre_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J), Measurable s → (∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y) → (∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C') → ∃ B : Set (HermR R σ (n + 1)), IsOpen B ∧ hermOf R σ _ hT' ∈ B ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1)) (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B) ∩ {X | LinearIndependent (R ⊗[F] E) X}) (coordHerm R σ b lam (n + 1)) B fib ∧ fib (hermOf R σ _ hT') = c ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.fibre_family_free_near_block | exact GlobalTheory.CompanionTheory.SW.StageF.fibre_family_free_near_block | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.fibre_family_free_near_block <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelParabolicQuotientIffRows
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.SRows

theorem blkD_siegel_mul {K : Type} [Field K] {n : ℕ} {y : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hy : IsSiegelP y) (W : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (y * W) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD y * GlobalTheory.CompanionTheory.RatPtsUnn.blkD W := by
  ext i j
  change (y * W) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = _
  rw [Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type, Matrix.mul_apply]
  have h0 : ∑ k : Fin n, y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl k)) *
      W (finSumFinEquiv (Sum.inl k)) (finSumFinEquiv (Sum.inr j)) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hy i k, zero_mul]
  rw [h0, zero_add]
  rfl

theorem inverse_unitary_block_form {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {a b c d : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 a b c d)) :
    (blk4 a b c d)⁻¹ = blk4 (cT σ d) (-cT σ b) (-cT σ c) (cT σ a) := by
  have hJJ' : (blk4 0 (-1) 1 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 1 (-1) 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [GlobalTheory.CompanionTheory.SwUnf.BigCell.block_identity_eq_one]
  have h0 : cT σ (blk4 a b c d) * blk4 0 1 (-1) 0 * blk4 a b c d = blk4 0 1 (-1) 0 := h
  have h1 : (blk4 0 (-1) 1 0 * cT σ (blk4 a b c d) * blk4 0 1 (-1) 0) * blk4 a b c d = 1 := by
    rw [mul_assoc (blk4 0 (-1) 1 0), mul_assoc (blk4 0 (-1) 1 0), h0, hJJ']
  rw [Matrix.inv_eq_left_inv h1, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

end GlobalTheory.CompanionTheory.ZUnf.SRows

theorem GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (x r : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit r.det → IsUnitary σ (blk4 0 1 (-1) 0) x → IsUnitary σ (blk4 0 1 (-1) 0) r →
    (IsSiegelP (x * r⁻¹) ↔ ∃ T : Matrix (Fin n) (Fin n) K, lowerC x = T * lowerC r ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD r) := by
  intro K _ σ _ n x r hr hx hrU
  obtain ⟨a, b, hr4⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq r
  constructor
  · intro h
    have e : x = (x * r⁻¹) * r := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hr, Matrix.mul_one]
    refine ⟨GlobalTheory.CompanionTheory.RatPtsUnn.blkD (x * r⁻¹), ?_, ?_⟩
    · conv_lhs => rw [e]
      exact GlobalTheory.CompanionTheory.SwUnf.lowerC_siegel_mul h r
    · conv_lhs => rw [e]
      exact GlobalTheory.CompanionTheory.ZUnf.SRows.blkD_siegel_mul h r
  · rintro ⟨T, h1, h2⟩
    rw [GlobalTheory.CompanionTheory.SwUnf.BigCell.isSiegelParabolic_iff]
    obtain ⟨a', b', hx4⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq x
    have hU' : IsUnitary σ (blk4 0 1 (-1) 0)
        (blk4 a b (lowerC r) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD r)) := by
      rw [← hr4]; exact hrU
    have hinv := GlobalTheory.CompanionTheory.ZUnf.SRows.inverse_unitary_block_form σ hU'
    rw [← hr4] at hinv
    have hrel := GlobalTheory.CompanionTheory.SwUnf.BigCell.lower_rel σ hU'
    have e : lowerC (x * r⁻¹) = lowerC x * cT σ (GlobalTheory.CompanionTheory.RatPtsUnn.blkD r)
        - GlobalTheory.CompanionTheory.RatPtsUnn.blkD x * cT σ (lowerC r) := by
      rw [hinv]
      conv_lhs => rw [hx4]
      rw [submatrix_fromBlocks_mul, GlobalTheory.CompanionTheory.SwUnf.BigCell.lowerLeft_block]
      simp [sub_eq_add_neg]
    rw [e, h1, h2, mul_assoc, mul_assoc, hrel, sub_self]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothFibreActionStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_fibre_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z), IsSmooth ρ₀ → IsSmooth (fibAct t ρ₀) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivityStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_additivity : PositivityTheory.PfSWUS.WhitTAdd := by
  first | exact @GlobalTheory.CompanionTheory.WhitAdd.whitTAdd | exact GlobalTheory.CompanionTheory.WhitAdd.whitTAdd | (intros; apply GlobalTheory.CompanionTheory.WhitAdd.whitTAdd <;> assumption)
end
end


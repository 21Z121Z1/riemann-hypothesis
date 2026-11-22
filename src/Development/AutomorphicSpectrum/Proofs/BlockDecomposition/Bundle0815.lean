import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0812
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0800
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0799
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0041
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0036
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParamStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_cell_cosets_hermitian_param : ∀ {D : D7} {n : ℕ} {w : G D n}, mat w = blk4 0 1 (-1) 0 → ∀ {nb : hermA D n → G D n}, IsNMap nb → ∃ e : ratHerm D n → Cosets (P D n) (GF D n), Function.Injective e ∧ (∀ q, cosetCell q = ⊥ ↔ q ∈ Set.range e) ∧ ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D n) (y : G D n), term (P D n) (GF D n) f y (e l) = f (w * nb l.1 * y) := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell | exact GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell | (intros; apply GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExists
section
open ResidueKilled.Tr
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.TChartProof

open Matrix

theorem mat_mul' {D : D7} {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one' {D : D7} {n : ℕ} : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem blkA_mul_of_lowerLeft {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (hY : ∀ i j : Fin n, Y (Fin.natAdd n i) (Fin.castAdd n j) = 0) : blkA (X * Y) = blkA X * blkA Y := by
  ext i j
  simp only [blkA, Matrix.mul_apply, Fin.sum_univ_add, hY, mul_zero, Finset.sum_const_zero, add_zero,
    toBlocks₁₁, Matrix.of_apply, submatrix_apply, finSumFinEquiv_apply_left]

theorem blkA_one' {R : Type} [CommRing R] {n : ℕ} : blkA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkA, toBlocks₁₁, Matrix.one_apply]

theorem exists_gl_blkA {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) :
    ∃ a : GL (Fin n) (AE D), blkA (mat g) = a.1 := by
  have hg' : g⁻¹ ∈ P D n := inv_mem hg
  have e₁ : blkA (mat g) * blkA (mat g⁻¹) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg'), ← mat_mul', mul_inv_cancel, mat_one', blkA_one']
  have e₂ : blkA (mat g⁻¹) * blkA (mat g) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg), ← mat_mul', inv_mul_cancel, mat_one', blkA_one']
  exact ⟨⟨_, _, e₁, e₂⟩, rfl⟩

theorem tChart : TChart := by
  intro hDict hDI hStd D χ V a hMaj
  obtain ⟨m0, hm0, hp0⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_standardUnitaryChart_doubledSpace D V m0 hm0
  obtain ⟨p, hp⟩ := hp0 V a hMaj κ hκ
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D V m0 hm0 κ hκ
  obtain ⟨Ψ, h1, h2, h3, h4⟩ := hStd hDict hDI D χ V.rank
  have hG := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D V m0 hm0 κ hκ
  have hP := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D V m0 hm0 κ hκ
  let κt : GA D (dblSp V) ≃ₜ* G D V.rank :=
    { κ with continuous_toFun := hc, continuous_invFun := hc' }
  have hκt : ∀ g, κt g = κ g := fun _ => rfl
  refine ⟨κt.trans Ψ, p, fun g => ?_, fun g => ?_, fun k => ?_, fun q => ?_, fun x => ?_⟩
  · exact (hG g).trans (h1 (κ g))
  · exact (hP g).trans (h2 (κ g))
  · exact (hp k).trans (h3 _)
  · obtain ⟨b, hb⟩ := exists_gl_blkA ((hP q).1 q.2)
    have e₁ := GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D V m0 hm0 κ hκ q b hb
    have e₂ := h4 (κ q) b hb
    rw [e₁]
    exact e₂
  · have e := (hDict D.host.F D.host.E).2.2.2.2 x
    show Real.log _ = _
    rw [e]

end GlobalTheory.CompanionTheory.TChartProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientLeviEquivariance
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzLevi

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul block_matrix_one)
open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply blockMatrix_add' blockMatrix_one mat_mul')
open GlobalTheory.CompanionTheory.IwaAd (levi_mem_P adj_mul_adj_inv adj_inv_mul_adj)

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem adj_zero' {k l : ℕ} : adj (0 : Mx D k l) = 0 := by
  have h := adj_add (0 : Mx D k l) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem blkA_blk4 {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) : blkA (blk4 a b c d) = a := by
  simp only [blkA, blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id,
    Matrix.toBlocks_fromBlocks₁₁]

theorem blockMatrix_zero' {R : Type} [CommRing R] (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem emb_comm (M : Maps D hn) (ζ : hermA D ρ) (g₀ : G D p) (a : GL (Fin p) (AE D))
    (hg : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    M.w * M.nzx ζ 0 * M.emb g₀ = M.emb g₀ * (M.w * M.nzx ζ 0) := by
  have hE := M.emb_mat g₀ _ _ _ _ hg
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  simp only [mat_mul']
  rw [hE, M.w_mat, M.nzx_mat, adj_zero']
  simp only [submatrix_fromBlocks_mul]
  simp only [blockMatrix_zero' hn, blockMatrix_add', blockMatrix_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_zero]

theorem mat_inv_levi (g₀ : G D p) (a : GL (Fin p) (AE D)) (hg : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    mat g₀⁻¹ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 : HMul.hMul (mat g₀) (blk4 (a⁻¹).1 0 0 (adj a.1)) = (1 : Mx D (p + p) (p + p)) := by
    rw [hg, submatrix_fromBlocks_mul]
    have e1 : a.1 * (a⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e2 : HMul.hMul (adj (a⁻¹).1) (adj a.1) = (1 : Mx D p p) := adj_inv_mul_adj a
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e2]
    exact block_matrix_one
  calc mat g₀⁻¹ = HMul.hMul (mat g₀⁻¹) (HMul.hMul (mat g₀) (blk4 (a⁻¹).1 0 0 (adj a.1))) := by
        rw [h1]; exact (Matrix.mul_one _).symm
    _ = HMul.hMul (mat (g₀⁻¹ * g₀)) (blk4 (a⁻¹).1 0 0 (adj a.1)) := by
        rw [mat_mul']; exact (Matrix.mul_assoc _ _ _).symm
    _ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
        rw [inv_mul_cancel]; exact Matrix.one_mul _

theorem exists_lv (hn : ρ + p = n) (a : GL (Fin p) (AE D)) :
    ∃ b : GL (Fin n) (AE D), b.1 = bl hn 1 0 0 a.1 := by
  have e : a.1 * (a⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e' : (a⁻¹).1 * a.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨bl hn 1 0 0 a.1, bl hn 1 0 0 (a⁻¹).1, ?_, ?_⟩, rfl⟩
  · rw [blockMatrix_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, e]
    exact blockMatrix_one hn
  · rw [blockMatrix_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, e']
    exact blockMatrix_one hn

theorem det_lv (hn : ρ + p = n) (a : GL (Fin p) (AE D)) (b : GL (Fin n) (AE D)) (hb : b.1 = bl hn 1 0 0 a.1) :
    Matrix.GeneralLinearGroup.det b = Matrix.GeneralLinearGroup.det a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hb]
  simp only [bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

theorem wz_emb : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
  (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ x : G D n, Wz M m ψ b₀ f (M.emb g₀ * x) =
    (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) * Wz M m ψ b₀ f x := by
  intro D n ρ p hn M m ψ b₀ χ z f hf g₀ a hg x
  have hE := M.emb_mat g₀ _ _ _ _ hg
  have hE' := M.emb_mat g₀⁻¹ _ _ _ _ (mat_inv_levi g₀ a hg)
  rw [blockMatrix_zero' hn] at hE hE'
  have hP : M.emb g₀ ∈ P D n :=
    levi_mem_P hE hE' (by rw [← map_mul, inv_mul_cancel, map_one])
  obtain ⟨b, hb⟩ := exists_lv hn a
  have hA : blkA (mat (M.emb g₀)) = b.1 := by
    rw [hE, blkA_blk4, hb]
  have e : ∀ ζ : hermA D ρ, f (M.w * M.nzx ζ 0 * (M.emb g₀ * x)) =
      (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) *
        f (M.w * M.nzx ζ 0 * x) := by
    intro ζ
    rw [← mul_assoc, emb_comm M ζ g₀ a hg, mul_assoc, hf _ hP b hA, det_lv hn a b hb]
  simp only [Wz]
  simp only [e]
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul]

end GlobalTheory.CompanionTheory.WzLevi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientUnipotentLeviInvariance
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzHeis

section Blocks
variable {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n)

theorem block_mul₂ (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 1 = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem bl_add (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  unfold bl
  rw [← Matrix.fromBlocks_add]
  rfl

theorem block_sub (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d - bl hn a' b' c' d' = bl hn (a - a') (b - b') (c - c') (d - d') := by
  ext i j
  simp only [bl, Matrix.sub_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem blockMatrix_zero : bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  ext i j
  simp only [bl, Matrix.zero_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem det_bl_lower (c : Matrix (Fin p) (Fin ρ) R) : (bl hn 1 0 c 1).det = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
  simp

end Blocks

variable {D : D7} {n ρ p : ℕ}

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem chz_add (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    chz ψ b₀ (a + b) = chz ψ b₀ a * chz ψ b₀ b := by
  have e : chz ψ b₀ (a + b) = ψ (GlobalTheory.CompanionTheory.FourierN.pr b₀.1 (a.1 + b.1)) := rfl
  rw [e, GlobalTheory.CompanionTheory.FourierN.pr_add_right, AddChar.map_add_eq_mul]
  rfl

theorem conj_chz (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    conj (chz ψ b₀ a) = conj (chz ψ b₀ (a + b)) * chz ψ b₀ b := by
  have hb : ‖chz ψ b₀ b‖ = 1 := hψ.2.1 _
  rw [chz_add, map_mul, mul_assoc, Complex.conj_mul', hb]
  simp

variable {hn : ρ + p = n} (M : Maps D hn)

theorem mat_u (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) :
    mat (M.nzx 0 x₀ * M.emb g₁) = blk4 1 (bl hn 0 x₀ (adj x₀) b) 0 1 := by
  have h1 := M.emb_mat g₁ 1 b 0 1 hg
  rw [blockRowSubstitution_one, blockMatrix_zero] at h1
  rw [LeftInvSect.mat_mul, M.nzx_mat, h1, submatrix_fromBlocks_mul]
  simp [bl_add]

theorem nzx_comm (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) (ζ z₀ : hermA D ρ) :
    M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁) = (M.nzx 0 x₀ * M.emb g₁) * M.nzx (ζ + z₀) 0 := by
  have h1 := M.emb_mat g₁ 1 b 0 1 hg
  rw [blockRowSubstitution_one, blockMatrix_zero] at h1
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [LeftInvSect.mat_mul, LeftInvSect.mat_mul, LeftInvSect.mat_mul, mat_u M g₁ b hg, M.nzx_mat, M.nzx_mat, M.nzx_mat, h1]
  simp only [submatrix_fromBlocks_mul, bl_add, adj_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [show (ζ + z₀).1 = z₀.1 + ζ.1 from add_comm _ _]

theorem q_mat (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) :
    ∃ (β δ : Mx D n n), mat (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹) = blk4 (bl hn 1 0 (adj x₀) 1) β 0 δ := by
  have h := GlobalTheory.CompanionTheory.SwUnf.SmallCell.conj_block M.w (M.nzx 0 x₀ * M.emb g₁) M.w_mat (mat_u M g₁ b hg x₀)
  have hC : adj (bl hn (-1 : Mx D ρ ρ) 0 0 0) = bl hn (-1) 0 0 0 := by
    simp [adj_bl, adj_zero, adj_neg, adj_one]
  rw [hC] at h
  have e1 : (1 : Mx D n n) - bl hn 0 0 0 1 * bl hn 0 x₀ (adj x₀) b * bl hn (-1) 0 0 0 = bl hn 1 0 (adj x₀) 1 := by
    rw [← blockRowSubstitution_one hn]
    simp [block_mul₂, block_sub]
  have e2 : -(bl hn (-1 : Mx D ρ ρ) 0 0 0 * bl hn 0 x₀ (adj x₀) b * bl hn (-1) 0 0 0) = (0 : Mx D n n) := by
    simp [block_mul₂, blockMatrix_zero]
  rw [e1, e2] at h
  exact ⟨_, _, h⟩

theorem law_q (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ) (hf : IsLaw χ z f) (g₁ : G D p) (b : Mx D p p)
    (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) (v : G D n) :
    f (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹ * v) = f v := by
  obtain ⟨β, δ, hq⟩ := q_mat M g₁ b hg x₀
  let a : GL (Fin n) (AE D) := ⟨bl hn 1 0 (adj x₀) 1, bl hn 1 0 (-adj x₀) 1,
    by simp [block_mul₂, blockRowSubstitution_one], by simp [block_mul₂, blockRowSubstitution_one]⟩
  have hdet : Matrix.GeneralLinearGroup.det a = 1 := Units.ext (det_bl_lower hn _)
  have hA : blkA (mat (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹)) = a.1 := by
    rw [hq]
    simp [blkA, blk4, a]
  rw [hf _ (GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hq) a hA v, hdet, map_one, map_one]
  simp [npow]

theorem wz_heis : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₁ : G D p) (b : Mx D p p),
  mat g₁ = blk4 1 b 0 1 → ∀ (z₀ : hermA D ρ) (x₀ : Mx D ρ p) (x : G D n),
    Wz M m ψ b₀ f (M.nzx z₀ x₀ * M.emb g₁ * x) = chz ψ b₀ z₀ * Wz M m ψ b₀ f x := by
  intro D n ρ p hn M m ψ hψ b₀ χ z f hf g₁ b hg z₀ x₀ x
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨hlam, -, -⟩ := m.hz
  have step : ∀ ζ : hermA D ρ, f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) =
      f (M.w * M.nzx (ζ + z₀) 0 * x) := by
    intro ζ
    have e : M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x) =
        M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹ * (M.w * M.nzx (ζ + z₀) 0 * x) := by
      have h := nzx_comm M g₁ b hg x₀ ζ z₀
      calc M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)
          = M.w * (M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁)) * x := by group
        _ = M.w * ((M.nzx 0 x₀ * M.emb g₁) * M.nzx (ζ + z₀) 0) * x := by rw [h]
        _ = _ := by group
    rw [e, law_q M χ z f hf g₁ b hg x₀]
  unfold Wz
  calc ∫ ζ, f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) * conj (chz ψ b₀ ζ) ∂m.lz
      = ∫ ζ, (fun y => chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y))) (ζ + z₀) ∂m.lz := by
        refine integral_congr_ae (.of_forall fun ζ => ?_)
        show f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) * conj (chz ψ b₀ ζ) =
          chz ψ b₀ z₀ * (f (M.w * M.nzx (ζ + z₀) 0 * x) * conj (chz ψ b₀ (ζ + z₀)))
        rw [step, conj_chz ψ hψ b₀ ζ z₀]
        ring
    _ = ∫ y, chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y)) ∂m.lz :=
        integral_add_right_eq_self (μ := m.lz) (fun y => chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y))) z₀
    _ = _ := integral_const_mul _ _

end GlobalTheory.CompanionTheory.WzHeis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotentStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_cell_invariant_unipotent : ∀ {D : D7} {n : ℕ} (q : Cosets (P D n) (GF D n)) (γ : GF D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat (γ : G D n) = blk4 1 (b.map (incA D)) 0 1 → cosetCell (rmulEquiv (P D n) (GF D n) γ q) = cosetCell q := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv | exact GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv | (intros; apply GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIsoStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_of_product_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | exact GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem lintegral_UsetF_eq_MidF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = MidF σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hCM := D.hCM
  have hlam := D.hlam
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id D.hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, hlf1, -, -, -, hae1⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hCM (M + 1) 1 _ hJ' R D.hR d b lam hlam m₁ D.hm₁
  obtain ⟨hm, -, -, -⟩ := GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ hCM M n J D.hJ R D.hR d b lam hlam m' D.hm'
  obtain ⟨-, -, h₃, -, h₅, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hJ' R
  have hc := (hact (n + 1)).1
  haveI := hBorel n M
  haveI := hBorel (n + 1) (M + 1)
  haveI := hBorel 1 (M + 1)
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordW R b lam n M) := inferInstance
  haveI : SigmaFinite (m₁ (hermScal R σ (algebraMap F R t))) := inferInstance
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : SFinite (Measure.pi fun _ : Fin n => coordK R b lam) := inferInstance
  have hB : MeasurableSet B₀ := D.hB₀.measurableSet
  rw [GlobalTheory.T.fibre_measure_extension_compatible F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ]
  unfold MidF
  refine setLIntegral_congr_fun hB fun x hx => ?_
  refine congrArg _ ?_
  set f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → (Fin n → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ :=
    fun y₀ c X => φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) with hfdef
  have hf : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      f p.1 p.2.1 p.2.2 := by
    have hcm : Measurable (fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) p.1 p.2) := by
      haveI : SecondCountableTopology (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J)) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
        Prod.opensMeasurableSpace
      exact hc.measurable
    have hg : Measurable (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        ((s p.1, vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) p.2.1 p.2.2) :
          HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E))) :=
      (D.hs.comp measurable_fst).prodMk
        ((Unfold.measurable_vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))).comp measurable_snd)
    exact hφ.comp (hcm.comp hg)
  have hae : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ)
          (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) =
        ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, f y₀ c X ∂(m' S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
    filter_upwards [hae1 (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    exact GlobalTheory.T.fibre_measure_lintegral_blockOne_eq_iterated F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  rw [lintegral_congr_ae hae]
  have key := Unfold.swap_through_fibres (m₁ (hermScal R σ (algebraMap F R t)))
    (Measure.pi fun _ => coordK R b lam) (coordW R b lam n M) (coordHerm R σ b lam n)
    {X | LinearIndependent (R ⊗[F] E) X} Set.univ MeasurableSet.univ m' hm (fun S hS => absurd (Set.mem_univ S) hS)
    D.hm'.2.1 f hf
  simp only [Measure.restrict_univ] at key
  exact key

end GlobalTheory.CompanionTheory.SW.StageF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneIsotropicStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_volume_rank_one_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ I : Measure (Fin 1 → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ℝ≥0, ∀ (φinf : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → ∫⁻ X, pureL b S φinf φ X ∂I = (c : ℝ≥0∞) * ((∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeFact.fact_free | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeFact.fact_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeFact.fact_free <;> assumption)
end


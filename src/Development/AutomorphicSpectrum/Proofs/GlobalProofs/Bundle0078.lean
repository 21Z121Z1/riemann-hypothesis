import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviPartsCommute
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0066
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0504
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0803
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0802
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0799

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviPartsCommuteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_frame_K_type_decomposition : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∃ B : Finset (GA D V), ∀ φ ∈ formsOn θ V X Y T U ε fr ρ c, (∀ b ∈ B, ∀ g ∈ levi D.sp.cm.sig V.gram X Y T, φ (g * b) = 0) → φ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep.exists_finset_sep_levi | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep.exists_finset_sep_levi | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep.exists_finset_sep_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
section
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

variable {D : D7}

theorem blk4_map_alt {n : ℕ} (f : D.host.E →+* AE D) (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem adj_map_herm {n : ℕ} (b : HermQ D n) : adj (b.1.map (incA D) : Mx D n n) = b.1.map (incA D) := by
  ext i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [← b.2 i j]
  rfl

theorem cell_value {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) {b : Mx D n n} (hu : mat u = blk4 1 b 0 1) (Φ : schwartzA θ V.rank n) :
    (ω (w * u) Φ).1 0 = ∫ y, Φ.1 y * ψ (halfTr (Matrix.trace (HMul.hMul b (StdUnn.inner V y y) : Mx D n n))) ∂μ := by
  rw [map_mul, Module.End.mul_apply, hω.weyl w hw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have z : StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
  simp only [z, Matrix.trace_zero, map_zero, AddChar.map_zero_eq_one, mul_one]
  rw [hω.unip u b hu, mul_comm]

theorem mat_cell {n : ℕ} {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) {b : Mx D n n} (hu : mat u = blk4 1 b 0 1) :
    mat (w * u) = blk4 0 1 (-1) (-b) := by
  rw [mat_mul, hw, hu, submatrix_fromBlocks_mul]
  simp

theorem cell_mem_GF {n : ℕ} {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : HermQ D n)
    (hu : mat u = blk4 1 (b.1.map (incA D)) 0 1) : w * u ∈ GF D n := by
  rw [ChartRat.mem_GF_iff, mat_cell hw hu]
  refine ⟨blk4 0 1 (-1) (-b.1), ?_⟩
  change (blk4 0 1 (-1) (-b.1)).map (incA D) = _
  rw [blk4_map_alt]
  have e0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := map_zero (incA D).mapMatrix
  have e1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := map_one (incA D).mapMatrix
  have e2 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = -1 := by
    have := map_neg (incA D).mapMatrix (1 : Matrix (Fin n) (Fin n) D.host.E)
    rwa [map_one] at this
  have e3 : (-b.1).map (incA D) = -(b.1.map (incA D)) := map_neg (incA D).mapMatrix b.1
  rw [e0, e1, e2, e3]

theorem cell_inj {n : ℕ} {w u u' : G D n} (hw : mat w = blk4 0 1 (-1) 0) {b b' : Mx D n n} (hu : mat u = blk4 1 b 0 1)
    (hu' : mat u' = blk4 1 b' 0 1) (h : (w * u') * (w * u)⁻¹ ∈ P D n) : b = b' := by
  obtain ⟨β, d, hp⟩ := siegelParabolicUnn_matrix_blockUpperTriangular h
  have e : mat ((w * u') * (w * u)⁻¹) * mat (w * u) = mat (w * u') := by
    rw [← mat_mul, inv_mul_cancel_right]
  rw [hp, mat_cell hw hu, mat_cell hw hu', submatrix_fromBlocks_mul] at e
  obtain ⟨-, -, h3, h4⟩ := blockMatrixTwoByTwoFin_injective e
  simp only [mul_zero, mul_neg, mul_one, zero_mul, add_zero, zero_add, neg_inj] at h3 h4
  rw [h3] at h4
  simpa using h4

end GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
end


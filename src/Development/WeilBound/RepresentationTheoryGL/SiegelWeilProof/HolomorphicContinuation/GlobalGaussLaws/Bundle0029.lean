import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0028
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0005
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0008
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AdelicConjTransposeBlockMatrixTwoByTwoFin
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LeviH

variable {D : D7}

def bA {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁

def bB {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

def bC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

def bD {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem block_matrix_of_blocks {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    M = blk4 (bA M) (bB M) (bC M) (bD M) := by
  unfold blk4 bA bB bC bD
  rw [Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix]
  simp

theorem upper_left_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bA (blk4 a b c d) = a := by
  unfold bA blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem upper_right_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bB (blk4 a b c d) = b := by
  unfold bB blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bA_reidx {n : ℕ} (y : M2 n) : bA (reidx y) = y.toBlocks₁₁ := by
  unfold bA reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bB_reidx {n : ℕ} (y : M2 n) : bB (reidx y) = y.toBlocks₁₂ := by
  unfold bB reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bC_reidx {n : ℕ} (y : M2 n) : bC (reidx y) = y.toBlocks₂₁ := by
  unfold bC reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bB_one {R : Type} [CommRing R] {n : ℕ} : bB (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, upper_right_of_block_matrix]

theorem bA_one {R : Type} [CommRing R] {n : ℕ} : bA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, upper_left_of_block_matrix]

theorem lower_left_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bC (blk4 a b c d) = c := by
  unfold bC blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bC_one {R : Type} [CommRing R] {n : ℕ} : bC (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, lower_left_of_block_matrix]

theorem bA_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bA M).map f = bA (M.map f) := rfl

theorem bB_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bB M).map f = bB (M.map f) := rfl

theorem bC_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bC M).map f = bC (M.map f) := rfl

theorem compAt_bA (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bA M) = bA (compAt θ τ M) := rfl

theorem compAt_bB (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bB M) = bB (compAt θ τ M) := rfl

theorem compAt_bC (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bC M) = bC (compAt θ τ M) := rfl

theorem adj_mul {m n k : ℕ} (x : Mx D m n) (z : Mx D n k) :
    adj (HMul.hMul x z : Mx D m k) = HMul.hMul (adj z) (adj x) := by
  unfold adj
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one {n : ℕ} : adj (1 : Mx D n n) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero (cA D)) (map_one (cA D)), Matrix.transpose_one]

theorem adelicConjTranspose_blockMatrixTwoByTwoFin {n : ℕ} (a d : Mx D n n) : adj (blk4 a 0 0 d) = blk4 (adj a) 0 0 (adj d) := by
  unfold adj
  rw [GlobalTheory.StdUnn.Frame.block_matrix_map, GlobalTheory.StdUnn.Frame.blockMatrixTwoByTwoFin_transpose, Matrix.map_zero _ (map_zero (cA D)),
    Matrix.transpose_zero]

theorem unitary_mat {n : ℕ} (g : G D n) :
    adj (mat g) * (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * mat g = blk4 0 1 (-1) 0 := by
  have h : adj (mat g) * rat (Jst D n) * mat g = rat (Jst D n) := g.2
  rwa [GlobalTheory.StdUnn.Frame.rat_Jst] at h

end PositivityTheory.Rg.Sw.Glob.LeviH

namespace PositivityTheory.Rg.Sw.Glob

open LeviH in
set_option maxHeartbeats 800000 in
theorem leviTau : LeviTau := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
  have hθ := hC.hθ
  obtain ⟨hτ, hτ', hfin⟩ := hC.hι.2 y
  have h1 : mat (ι y) * mat (ι y)⁻¹ = 1 := by
    show mat (ι y * (ι y)⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have h2 : mat (ι y)⁻¹ * mat (ι y) = 1 := by
    show mat ((ι y)⁻¹ * ι y) = 1
    rw [inv_mul_cancel]
    rfl
  have hU := unitary_mat (ι y)
  have hlevi := hC.hω.levi (ι y)
  generalize mat (ι y) = M at hτ hτ' hfin h1 h2 hU hlevi
  generalize mat (ι y)⁻¹ = M' at h1 h2
  have hB : bB M = 0 := by
    apply GlobalTheory.StabAtPlace.mx_ext hθ
    · rw [Matrix.map_zero _ (map_zero (finPart D)), bB_map, hfin, bB_one]
    · intro τ'
      rw [OG.compAt_zero', compAt_bB]
      by_cases h : τ' = τ
      · subst h
        rw [hτ, bB_reidx, hya]
        simp only [mM, Matrix.toBlocks_fromBlocks₁₂]
      · rw [hτ' τ' h, bB_one]
  have hC0 : bC M = 0 := by
    apply GlobalTheory.StabAtPlace.mx_ext hθ
    · rw [Matrix.map_zero _ (map_zero (finPart D)), bC_map, hfin, bC_one]
    · intro τ'
      rw [OG.compAt_zero', compAt_bC]
      by_cases h : τ' = τ
      · subst h
        rw [hτ, bC_reidx, hya]
        simp only [mM, Matrix.toBlocks_fromBlocks₂₁]
      · rw [hτ' τ' h, bC_one]
  have hM : M = blk4 (bA M) 0 0 (bD M) := by
    conv_lhs => rw [block_matrix_of_blocks M]
    rw [hB, hC0]
  have hAA' : bA M * bA M' = 1 := by
    have e := congrArg bA h1
    rw [hM, block_matrix_of_blocks M', GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, upper_left_of_block_matrix, bA_one, zero_mul, add_zero] at e
    exact e
  have hA'A : bA M' * bA M = 1 := by
    have e := congrArg bA h2
    rw [hM, block_matrix_of_blocks M', GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, upper_left_of_block_matrix, bA_one, mul_zero, add_zero] at e
    exact e
  have hAD : adj (bA M) * bD M = 1 := by
    rw [hM, adelicConjTranspose_blockMatrixTwoByTwoFin, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul] at hU
    have e := congrArg bB hU
    rw [upper_right_of_block_matrix, upper_right_of_block_matrix] at e
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at e
    exact e
  have hD : bD M = adj (bA M') := by
    have e : adj (bA M') * adj (bA M) = 1 := by rw [← LeviH.adj_mul, hAA', LeviH.adj_one]
    calc bD M = 1 * bD M := (one_mul _).symm
      _ = adj (bA M') * (adj (bA M) * bD M) := by rw [← mul_assoc, e]
      _ = adj (bA M') := by rw [hAD, mul_one]
  have hmat : M = blk4 (bA M) 0 0 (adj (bA M')) := by
    calc M = blk4 (bA M) 0 0 (bD M) := hM
      _ = blk4 (bA M) 0 0 (adj (bA M')) := by rw [hD]
  refine ⟨_, bA M, ?_, ?_, ?_, fun Φ x => hlevi ⟨bA M, bA M', hAA', hA'A⟩ hmat Φ x⟩
  · rw [compAt_bA, hτ, bA_reidx, hya]
    simp only [mM, Matrix.toBlocks_fromBlocks₁₁]
  · intro τ' h
    rw [compAt_bA, hτ' τ' h, bA_one]
  · rw [bA_map, hfin, bA_one]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DerOneBH

variable {D : D7} {n : ℕ}

theorem mt_mul' (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem shiftPt (V : HSp D) (x k : GA D V) (y : Mx D V.rank n) :
    HMul.hMul (mt V (x * k⁻¹)⁻¹) y = HMul.hMul (mt V k) (HMul.hMul (mt V x⁻¹) y) := by
  rw [mul_inv_rev, inv_inv, mt_mul', Matrix.mul_assoc]

theorem leftInv_absTheta (V : HSp D) (φ : Mx D V.rank n → ℂ) : LeftInv (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc],
      fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : mt V (γ * h)⁻¹ = mt V h⁻¹ * mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  show ‖φ (HMul.hMul (mt V (γ * h)⁻¹) (rat ξ))‖ₑ = ‖φ (HMul.hMul (mt V h⁻¹) (rat (u.1 * ξ)))‖ₑ
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]

section Quot

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure]

theorem absTheta_eq (φ : Mx D V.rank n → ℂ) (y : GA D V) :
    GlobalTheory.SiegelFormula.absTheta V φ y =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖φ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) (rat ξ : Mx D V.rank n))‖ₑ := rfl

theorem absThetaInt_eq (φ : Mx D V.rank n → ℂ) :
    GlobalTheory.SiegelFormula.absThetaInt V ν φ = ∫⁻ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q ∂autMeasure V ν := rfl

theorem int_q (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) :
    ∫ q, descend (GQ V) f q ∂autMeasure V ν = ∫ x in stdDom (GQ V), f x ∂ν := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [autMeasure, integral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]
  exact integral_congr_ae (.of_forall fun x => hf.descend_mk x)

theorem lint_q (f : GA D V → ℝ≥0∞) (hf : LeftInv (GQ V) f) :
    ∫⁻ q, descend (GQ V) f q ∂autMeasure V ν = ∫⁻ x in stdDom (GQ V), f x ∂ν := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [autMeasure, lintegral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]
  exact lintegral_congr fun x => hf.descend_mk x

theorem intg_q (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (hi : Integrable (descend (GQ V) f) (autMeasure V ν)) :
    Integrable f (ν.restrict (stdDom (GQ V))) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [← memLp_one_iff_integrable] at hi ⊢
  have := (memLp_quotMeasure_iff (isFundamentalDomain_stdDom (GQ V) ν)).1 hi
  rwa [hf.lift_descend] at this

theorem desc_r {X' : Type} (f : GA D V → X') (hf : LeftInv (GQ V) f) (k : GA D V) (q : GlobalTheory.AutomorphicL2Unitary.Quot (GQ V)) :
    descend (GQ V) (fun x => f (x * k)) q = descend (GQ V) f (GlobalTheory.ThetaInv.rmulEquiv (GQ V) k q) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  induction q using Quotient.inductionOn with
  | h x => exact ((hf.mul_right k).descend_mk x).trans (hf.descend_mk (x * k)).symm

theorem mp_r (k : GA D V) :
    MeasurePreserving (GlobalTheory.ThetaInv.rmulEquiv (GQ V) k) (autMeasure V ν) (autMeasure V ν) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : ν.IsMulRightInvariant := GlobalTheory.RegSch.Ibp.isMulRightInvariant ν
  exact measurePreserving_rmul k

theorem int_r (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (k : GA D V) :
    ∫ x in stdDom (GQ V), f (x * k) ∂ν = ∫ x in stdDom (GQ V), f x ∂ν := by
  rw [← int_q V ν _ (hf.mul_right k), ← int_q V ν f hf]
  simp only [desc_r V f hf k]
  exact (mp_r V ν k).integral_comp' (descend (GQ V) f)

theorem lint_r (f : GA D V → ℝ≥0∞) (hf : LeftInv (GQ V) f) (k : GA D V) :
    ∫⁻ x in stdDom (GQ V), f (x * k) ∂ν = ∫⁻ x in stdDom (GQ V), f x ∂ν := by
  rw [← lint_q V ν _ (hf.mul_right k), ← lint_q V ν f hf]
  simp only [desc_r V f hf k]
  exact (mp_r V ν k).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (descend (GQ V) f)

theorem intg_r (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (hi : Integrable (descend (GQ V) f) (autMeasure V ν))
    (k : GA D V) : Integrable (fun x => f (x * k)) (ν.restrict (stdDom (GQ V))) := by
  refine intg_q V ν _ (hf.mul_right k) ?_
  have e : descend (GQ V) (fun x => f (x * k)) = descend (GQ V) f ∘ GlobalTheory.ThetaInv.rmulEquiv (GQ V) k :=
    funext fun q => desc_r V f hf k q
  rw [e]
  exact ((mp_r V ν k).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi

end Quot

section Kernel

variable (V : HSp D)

def tK (φ : Mx D V.rank n → ℂ) (x : GA D V) : ℂ :=
  ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, φ (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n))

def FF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) : ℂ :=
  φ (HMul.hMul (Formalism.L2.Theta.mt V (hh t)) (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n)))

theorem leftInv_tK (φ : Mx D V.rank n → ℂ) : LeftInv (GQ V) (tK V φ) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc],
      fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  show φ (HMul.hMul (Formalism.L2.Theta.mt V (γ * h)⁻¹) (rat ξ)) = φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (rat (u.1 * ξ)))
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]

theorem tsum_FF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) :
    ∑' ξ, FF V φ hh x t ξ = tK V φ (x * (hh t)⁻¹) :=
  tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]

theorem tsum_nFF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) :
    ∑' ξ, ‖FF V φ hh x t ξ‖ₑ = GlobalTheory.SiegelFormula.absTheta V φ (x * (hh t)⁻¹) := by
  rw [absTheta_eq]
  exact tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]

end Kernel

end PositivityTheory.Rg.Sw.Glob.DerOneBH

namespace PositivityTheory.Rg.Sw.Glob

open DerOneBH

set_option maxHeartbeats 1000000 in
theorem derivOne_of (hW : GlobalTheory.Published.WeilThetaConvergence) (hC : DerOneH.CurveSt) : DerivOne := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX Θ Θ' hΘ'
  obtain ⟨h0, -, hΦ⟩ := hC D n V θ τ s ε fr X hx.hθ hx.hs hx.hfr hX
  haveI : ν.IsHaarMeasure := hx.hν
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : IsFiniteMeasure (autMeasure V ν) := GlobalTheory.RegSch.Ibp.isFiniteMeasure_autMeasure ν
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
  letI : MeasurableSpace (Matrix (Fin V.rank) (Fin n) D.host.E) := ⊤
  haveI : MeasurableSingletonClass (Matrix (Fin V.rank) (Fin n) D.host.E) := ⟨fun _ => trivial⟩
  haveI : IsFiniteMeasure (ν.restrict (stdDom (GQ V))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ (isFundamentalDomain_stdDom (GQ V) ν)]
        exact measure_lt_top _ _⟩
  have hT : ∀ Φ : schwartzA θ V.rank n, theta ω Φ 1 = tK V Φ.1 := fun Φ => by
    funext x
    simp only [theta, map_one, Module.End.one_apply, tK]
  have hfinA : ∀ Φ : schwartzA θ V.rank n, GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 < ⊤ :=
    fun Φ => hW D n V hx.hn (Or.inr hx.hr.2.2) θ hx.hθ ν hx.hν Φ
  have hfinA' : ∀ (Φ : schwartzA θ V.rank n) (k : GA D V),
      ∫⁻ x in stdDom (GQ V), GlobalTheory.SiegelFormula.absTheta V Φ.1 (x * k) ∂ν = GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 :=
    fun Φ k => by
      rw [lint_r V ν _ (leftInv_absTheta V Φ.1) k, ← lint_q V ν _ (leftInv_absTheta V Φ.1), absThetaInt_eq]
  have hintT : ∀ Φ : schwartzA θ V.rank n, Integrable (descend (GQ V) (tK V Φ.1)) (autMeasure V ν) := fun Φ => by
    rw [← hT]; exact GlobalTheory.T.integrable_standardPair_theta_weilRange hW D n V hx.hn hx.hr.2.2 θ hx.hθ ω ν hx.hν Φ 1
  have hhinv0 : (DerOneH.hhT θ V τ fr X 0)⁻¹ = 1 := by rw [h0, inv_one]
  have hmeasA : ∀ (Φ : schwartzA θ V.rank n) (t : ℝ), Measurable fun x : GA D V =>
      ∑' ξ, ‖FF V Φ.1 (DerOneH.hhT θ V τ fr X) x t ξ‖ₑ :=
    fun Φ t => Measurable.ennreal_tsum fun ξ =>
      (((hΦ Φ).1 (rat ξ : Mx D V.rank n)).comp (Continuous.prodMk continuous_id continuous_const)).enorm.measurable
  have key := DerOneAbsH.integral_deriv_zero (ν.restrict (stdDom (GQ V)))
    (FF V Θ.1 (DerOneH.hhT θ V τ fr X)) (FF V Θ'.1 (DerOneH.hhT θ V τ fr X))
    (fun x ξ t _ => by
      have := (hΦ Θ).2 (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n)) t
      rw [← hΘ'] at this
      exact this)
    (fun x ξ => by
      have h := ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).comp
        (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (x, t))
      exact h)
    (fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).aestronglyMeasurable)
    (by
      have hm : Measurable fun p : GA D V × ℝ => ∑' ξ, ‖FF V Θ'.1 (DerOneH.hhT θ V τ fr X) p.1 p.2 ξ‖ₑ :=
        Measurable.ennreal_tsum fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).enorm.measurable
      rw [lintegral_prod_symm _ hm.aemeasurable]
      simp only [tsum_nFF, hfinA']
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      simp only [sub_zero, ENNReal.ofReal_one, mul_one]
      exact (hfinA Θ').ne)
    (by
      have h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖ₑ ∂ν ≠ ⊤ := by
        simp only [tsum_nFF, hfinA']
        exact (hfinA Θ).ne
      filter_upwards [ae_lt_top' (hmeasA Θ 0).aemeasurable h1] with x hx'
      have hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖₊ :=
        ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne
      exact NNReal.summable_coe.2 hs)
    (by
      have h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖ₑ ∂ν ≠ ⊤ := by
        simp only [tsum_nFF, hfinA']
        exact (hfinA Θ).ne
      filter_upwards [ae_lt_top' (hmeasA Θ 1).aemeasurable h1] with x hx'
      have hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖₊ :=
        ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne
      exact NNReal.summable_coe.2 hs)
    (by
      simp only [tsum_FF, hhinv0, mul_one]
      exact intg_q V ν _ (leftInv_tK V Θ.1) (hintT Θ))
    (by
      simp only [tsum_FF]
      exact intg_r V ν _ (leftInv_tK V Θ.1) (hintT Θ) _)
    (by
      simp only [tsum_FF, hhinv0, mul_one]
      exact int_r V ν _ (leftInv_tK V Θ.1) _)
    (fun t _ => by
      simp only [tsum_FF, hhinv0, mul_one]
      exact int_r V ν _ (leftInv_tK V Θ'.1) _)
  simp only [tsum_FF, hhinv0, mul_one] at key
  rw [thetaInt, hT, average_eq, int_q V ν _ (leftInv_tK V Θ'.1), key, smul_zero]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlanchLoc
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def PlanchLoc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t : ℝ), t ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ f : (Fin m → Fin n → ℂ) → ℂ, IsSch f →
    ∫ u, ‖ftLoc ε t f u‖ ^ 2 = c * ∫ u, ‖f u‖ ^ 2

def AwayNZ : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∃ (Ψ : Mx D V.rank n → ℂ) (x₀ : Mx D V.rank n), AwayCls θ τ fr Ψ ∧ Ψ x₀ ≠ 0

end PositivityTheory.Rg.Sw.Glob
end
end


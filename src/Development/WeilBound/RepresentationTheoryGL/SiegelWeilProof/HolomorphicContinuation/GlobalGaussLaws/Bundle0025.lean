import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0023
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenInf
section
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenInfH

open PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Formalism.IndefR.Eqv (psiT glueA splitInv psiT_glueA finPart_glueA ae_ext' mat_ext)

variable {D : D7} {n : ℕ}

theorem isUnit_of_comps (x : AE D) (h1 : ∀ τ, psiT D τ x ≠ 0) (h2 : IsUnit (finPart D x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h2
  set y : AE D := glueA D (splitInv D fun τ => (psiT D τ x)⁻¹) ((u⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _)
  have hxy : x * y = 1 := by
    apply ae_ext' D
    · intro τ
      rw [map_mul, psiT_glueA, map_one, mul_inv_cancel₀ (h1 τ)]
    · rw [map_mul, finPart_glueA, map_one, ← hu, Units.mul_inv]
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

theorem cT_blk4 {R : Type} [CommRing R] (σ : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (blk4 a b c d) = blk4 (Formalism.UG.cT σ a) (Formalism.UG.cT σ c) (Formalism.UG.cT σ b) (Formalism.UG.cT σ d) := by
  ext i j
  simp only [Formalism.UG.cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem cT_zero' {R : Type} [CommRing R] (σ : R →+* R) : Formalism.UG.cT σ (0 : Matrix (Fin n) (Fin n) R) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_neg' {R : Type} [CommRing R] (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (-M) = -Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT]

theorem blk4_neg {R : Type} [CommRing R] (a b c d : Matrix (Fin n) (Fin n) R) :
    blk4 (-a) (-b) (-c) (-d) = -blk4 a b c d := by
  ext i j
  simp only [blk4, Matrix.neg_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem blkDm_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    blkDm (M.map f) = (blkDm M).map f := by
  ext i j; rfl

theorem blkDm_one {R : Type} [CommRing R] : blkDm (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkDm, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem eI_mul_self {R : Type} [CommRing R] (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R) * eI I = eI I := by
  simp only [eI, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i ∈ I <;> simp [h]

theorem eI_conjTranspose (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) ℂ)ᴴ = eI I := by
  simp only [eI, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i ∈ I <;> simp [h]

theorem weyl_idem {R : Type} [CommRing R] (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) :
    blk4 1 e 0 1 * blk4 1 0 (-e) 1 * blk4 1 e 0 1 = blk4 (1 - e) e (-e) (1 - e) := by
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.add_mul, he]
  congr 1 <;> abel

theorem unip_unitary {R : Type} [CommRing R] (σ : R →+* R) (b : Matrix (Fin n) (Fin n) R) (hb : Formalism.UG.cT σ b = b) :
    Formalism.UG.cT σ (blk4 1 b 0 1) * blk4 0 1 (-1) 0 * blk4 1 b 0 1 = blk4 0 1 (-1) 0 := by
  rw [cT_blk4, Formalism.UG.cT_one, cT_zero', hb, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> simp

theorem unipBar_unitary {R : Type} [CommRing R] (σ : R →+* R) (c : Matrix (Fin n) (Fin n) R) (hc : Formalism.UG.cT σ c = c) :
    Formalism.UG.cT σ (blk4 1 0 c 1) * blk4 0 1 (-1) 0 * blk4 1 0 c 1 = blk4 0 1 (-1) 0 := by
  rw [cT_blk4, Formalism.UG.cT_one, cT_zero', hc, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> simp

theorem JR_Jst (D : D7) (n : ℕ) : JR (F := D.host.F) (AF D.host.F) (Jst D n) = blk4 0 1 (-1) 0 := by
  rw [JR, Jst, block_matrix_map, Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _)]

def nEl (b : Matrix (Fin n) (Fin n) (AE D)) (hb : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) b = b) : G D n :=
  (⟨⟨blk4 1 b 0 1, blk4 1 (-b) 0 1,
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one],
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]⟩,
    by
      show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (blk4 1 b 0 1) * JR (AF D.host.F) (Jst D n) * blk4 1 b 0 1 =
        JR (AF D.host.F) (Jst D n)
      rw [JR_Jst]; exact unip_unitary _ b hb⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

def nBarEl (c : Matrix (Fin n) (Fin n) (AE D)) (hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) c = c) : G D n :=
  (⟨⟨blk4 1 0 c 1, blk4 1 0 (-c) 1,
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one],
      by rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]⟩,
    by
      show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (blk4 1 0 c 1) * JR (AF D.host.F) (Jst D n) * blk4 1 0 c 1 =
        JR (AF D.host.F) (Jst D n)
      rw [JR_Jst]; exact unipBar_unitary _ c hc⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

theorem mat_nEl (b : Matrix (Fin n) (Fin n) (AE D)) (hb) : mat (nEl b hb) = blk4 1 b 0 1 := rfl

theorem mat_nBarEl (c : Matrix (Fin n) (Fin n) (AE D)) (hc) : mat (nBarEl c hc) = blk4 1 0 c 1 := rfl

theorem cT_starRingEnd (M : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

set_option maxHeartbeats 1000000 in

theorem exists_I (hL : LocRedField) (k : G D n) (τ : D.what₂.Tau) :
    ∃ I : Finset (Fin n), IsUnit (blkDm ((mat k).map (psiT D τ) * wIm I)).det := by
  set M := (mat k).map (psiT D τ) with hM
  have hgU : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat k) * JR (AF D.host.F) (Jst D n) * mat k =
      JR (AF D.host.F) (Jst D n) := k.2
  have hu : Mᴴ * blk4 0 1 (-1) 0 * M = blk4 0 1 (-1) 0 := by
    have := congrArg (fun X => X.map (psiT D τ)) hgU
    simp only [Matrix.map_mul, cT_map_psiT', Jst_map_psiT] at this
    exact this
  have hJJ : (blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
    rw [submatrix_fromBlocks_mul]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg]
    rw [← block_matrix_one, ← blk4_neg, neg_zero]
  have hinv : ((-(blk4 0 1 (-1) 0)) * Mᴴ * blk4 0 1 (-1) 0) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hu, Matrix.neg_mul, hJJ, neg_neg]
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hinv
  have hg : Matrix.nonsingInvUnit M hdet ∈ Formalism.UG.UJ (starRingEnd ℂ) (J2 ℂ n) := by
    show Formalism.UG.cT (starRingEnd ℂ) M * J2 ℂ n * M = J2 ℂ n
    rw [cT_starRingEnd]
    exact hu
  obtain ⟨I, hI⟩ := hL ℂ (starRingEnd ℂ) (fun a => star_star a) n _ hg
  exact ⟨I, hI⟩

end PositivityTheory.Rg.Sw.Glob.GenInfH

namespace PositivityTheory.Rg.Sw.Glob

open GenInfH PlaceFactsH
open Formalism.IndefR.Eqv (psiT glueA splitInv psiT_glueA finPart_glueA ae_ext' mat_ext)

set_option maxHeartbeats 1000000 in
theorem kInInf_of (hU : UnitD) (hL : LocRedField) : KInInf := by
  intro D n k hk hfin
  classical
  choose I hI using exists_I hL k
  set B : Matrix (Fin n) (Fin n) (AE D) :=
    Matrix.of fun i j => glueA D (splitInv D fun τ => (eI (I τ) : Matrix (Fin n) (Fin n) ℂ) i j) 0 with hBdef
  have hBτ : ∀ τ, B.map (psiT D τ) = eI (I τ) := by
    intro τ; ext i j; simp only [hBdef, Matrix.map_apply, Matrix.of_apply, psiT_glueA]
  have hBf : B.map (finPart D) = 0 := by
    ext i j; simp only [hBdef, Matrix.map_apply, Matrix.of_apply, finPart_glueA, Matrix.zero_apply]
  have hBB : B * B = B := by
    apply mat_ext D
    · intro τ; rw [Matrix.map_mul, hBτ, eI_mul_self]
    · rw [Matrix.map_mul, hBf, Matrix.zero_mul]
  have hBc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) B = B := by
    apply mat_ext D
    · intro τ; rw [cT_map_psiT', hBτ, eI_conjTranspose]
    · rw [PositivityTheory.Rg.Sw.Glob.EmbP.cT_map_fin, hBf]
      ext i j; simp [Formalism.UG.cT]
  have hBc' : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (-B) = -B := by rw [cT_neg', hBc]
  set W : G D n := nEl B hBc * nBarEl (-B) hBc' * nEl B hBc with hW
  have hWmat : mat W = blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1 := rfl
  have hWτ : ∀ τ, (mat W).map (psiT D τ) = wIm (I τ) := by
    intro τ
    rw [hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBτ, weyl_idem _ (eI_mul_self _)]
    rfl
  have hWf : (mat W).map (finPart D) = 1 := by
    rw [hWmat, Matrix.map_mul, Matrix.map_mul, block_matrix_map, block_matrix_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hBf, neg_zero, block_matrix_one, Matrix.one_mul, Matrix.one_mul]
  have hunit : IsUnit (blkDm (mat (k * W))).det := by
    apply GenInfH.isUnit_of_comps
    · intro τ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hWτ]
      exact (hI τ).ne_zero
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ← blkDm_map, mat_mul', Matrix.map_mul, hfin, hWf, Matrix.one_mul,
        blkDm_one, Matrix.det_one]
      exact isUnit_one
  have h1 := hU D n (k * W) hunit
  have h2 : W ∈ Subgroup.closure (genSet D n) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr (Or.inr ⟨-B, rfl⟩))
    · exact Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)
  have : k = (k * W) * W⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SiegelParabolicUnnMatrixBlockUpperTriangular
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GlobalGaussBlockRelations

variable {D : D7} {n : ℕ}

def bA (M : Mx D (n + n) (n + n)) : Mx D n n := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁

def bB (M : Mx D (n + n) (n + n)) : Mx D n n := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

def bC (M : Mx D (n + n) (n + n)) : Mx D n n := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

theorem siegelParabolicUnn_matrix_blockUpperTriangular (M : Mx D (n + n) (n + n)) : M = blk4 (bA M) (bB M) (bC M) (blkDm M) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem rel1 (g : G D n) : adj (mat g) * blk4 0 1 (-1) 0 * mat g = blk4 0 1 (-1) 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rwa [JR_Jst] at h

theorem JJ_sq : (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * blk4 0 1 (-1) 0 = -1 := by
  rw [submatrix_fromBlocks_mul]
  simp only [mul_one, zero_add, add_zero, mul_neg, mul_zero, neg_zero]
  rw [← block_matrix_one (R := AE D) (n := n)]
  unfold blk4
  rw [show Matrix.fromBlocks (-1 : Mx D n n) 0 0 (-1) = -Matrix.fromBlocks 1 0 0 1 by
    rw [Matrix.fromBlocks_neg]; simp, Matrix.submatrix_neg]
  rfl

set_option maxHeartbeats 1000000 in
theorem rel2 (g : G D n) : mat g * blk4 0 1 (-1) 0 * adj (mat g) = blk4 0 1 (-1) 0 := by
  have hMN : mat g * mat g⁻¹ = 1 := by
    rw [show mat g * mat g⁻¹ = mat (g * g⁻¹) from rfl, mul_inv_cancel]; rfl
  have h1 := rel1 g
  have hJ : (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * blk4 0 1 (-1) 0 = -1 := JJ_sq
  generalize (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) = J at h1 hJ ⊢
  generalize mat g⁻¹ = N at hMN
  generalize mat g = M at hMN h1 ⊢
  have h2 : adj M * J = J * N := by
    calc adj M * J = adj M * J * (M * N) := by rw [hMN, mul_one]
      _ = (adj M * J * M) * N := by simp only [mul_assoc]
      _ = J * N := by rw [h1]
  have h3 : N = -(J * adj M * J) := by
    have : J * (adj M * J) = J * (J * N) := by rw [h2]
    rw [← mul_assoc, ← mul_assoc, hJ] at this
    rw [this, neg_mul, one_mul, neg_neg]
  have h4 : M * (J * adj M * J) = -1 := by
    have : M * N = 1 := hMN
    rw [h3, mul_neg] at this
    rw [← neg_neg (M * (J * adj M * J)), this]
  have h5 : M * J * adj M * J = -1 := by rw [← h4]; simp only [mul_assoc]
  calc M * J * adj M = -(M * J * adj M * (J * J)) := by rw [hJ, mul_neg, mul_one, neg_neg]
    _ = -((M * J * adj M * J) * J) := by rw [mul_assoc (M * J * adj M) J J]
    _ = J := by rw [h5, neg_mul, one_mul, neg_neg]

set_option maxHeartbeats 1000000 in
theorem blockRels (g : G D n) :
    adj (bB (mat g)) * blkDm (mat g) = adj (blkDm (mat g)) * bB (mat g) ∧
    adj (bA (mat g)) * blkDm (mat g) - adj (bC (mat g)) * bB (mat g) = 1 ∧
    blkDm (mat g) * adj (bC (mat g)) = bC (mat g) * adj (blkDm (mat g)) ∧
    bA (mat g) * adj (blkDm (mat g)) - bB (mat g) * adj (bC (mat g)) = 1 := by
  have h1 := rel1 g
  have h2 := rel2 g
  rw [siegelParabolicUnn_matrix_blockUpperTriangular (mat g)] at h1 h2
  generalize bA (mat g) = A at h1 h2 ⊢
  generalize bB (mat g) = B at h1 h2 ⊢
  generalize bC (mat g) = C at h1 h2 ⊢
  generalize blkDm (mat g) = Dd at h1 h2 ⊢
  rw [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h1 h2
  simp only [mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h1 h2
  obtain ⟨-, e12, -, e22⟩ := blockMatrixTwoByTwoFin_injective h1
  obtain ⟨-, f12, -, f22⟩ := blockMatrixTwoByTwoFin_injective h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (neg_add_eq_zero.1 e22).symm
  · rw [← e12]; abel
  · exact neg_add_eq_zero.1 f22
  · rw [← f12]; abel

end PositivityTheory.Rg.Sw.Glob.GlobalGaussBlockRelations

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.MixModel

set_option maxHeartbeats 2000000 in
theorem unitD : UnitD := by
  intro D n g hD
  obtain ⟨r1, r2, r3, r4⟩ := GlobalGaussBlockRelations.blockRels g
  have hM := GlobalGaussBlockRelations.siegelParabolicUnn_matrix_blockUpperTriangular (mat g)
  generalize GlobalGaussBlockRelations.bA (mat g) = A at r1 r2 r3 r4 hM
  generalize GlobalGaussBlockRelations.bB (mat g) = B at r1 r2 r3 r4 hM
  generalize GlobalGaussBlockRelations.bC (mat g) = C at r1 r2 r3 r4 hM
  generalize blkDm (mat g) = Dd at r1 r2 r3 r4 hM hD
  obtain ⟨Di, hDi1, hDi2⟩ : ∃ Di : Mx D n n, Dd * Di = 1 ∧ Di * Dd = 1 :=
    ⟨Dd⁻¹, Matrix.mul_nonsing_inv Dd hD, Matrix.nonsing_inv_mul Dd hD⟩
  have hA1 : adj Di * adj Dd = 1 := by rw [← adj_mul, hDi1, adj_one]
  have hA2 : adj Dd * adj Di = 1 := by rw [← adj_mul, hDi2, adj_one]
  have hb : adj (B * Di) = B * Di := by
    rw [adj_mul]
    calc adj Di * adj B = adj Di * (adj B * Dd) * Di := by simp only [mul_assoc, hDi1, mul_one]
      _ = adj Di * (adj Dd * B) * Di := by rw [r1]
      _ = B * Di := by rw [← mul_assoc (adj Di), hA1, one_mul]
  have hc : adj (Di * C) = Di * C := by
    rw [adj_mul]
    calc adj C * adj Di = Di * (Dd * adj C) * adj Di := by simp only [← mul_assoc, hDi2, one_mul]
      _ = Di * (C * adj Dd) * adj Di := by rw [r3]
      _ = Di * C := by simp only [mul_assoc, hA2, mul_one]
  have ha1 : (A - B * Di * C) * adj Dd = 1 := by
    rw [sub_mul, mul_assoc (B * Di) C (adj Dd), ← r3, ← mul_assoc (B * Di) Dd (adj C), mul_assoc B Di Dd, hDi2,
      mul_one, r4]
  have ha2 : adj Dd * (A - B * Di * C) = 1 := mul_eq_one_comm.mp ha1
  let aG : GL (Fin n) (AE D) := ⟨A - B * Di * C, adj Dd, ha1, ha2⟩
  obtain ⟨m, hm⟩ := exists_levi aG
  have hm' : mat m = blk4 (A - B * Di * C) 0 0 Dd := by
    rw [hm]
    show blk4 (A - B * Di * C) 0 0 (adj (adj Dd)) = _
    rw [adj_adj]
  obtain ⟨u, hu⟩ := (exists_unip (B * Di)).2 hb
  obtain ⟨v, hv⟩ : ∃ v : G D n, mat v = blk4 1 0 (Di * C) 1 := by
    refine exists_mat _ (blk4 1 0 (-(Di * C)) 1) ?_ ?_ ?_
    · rw [submatrix_fromBlocks_mul]
      simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, add_neg_cancel]
      exact block_matrix_one
    · rw [submatrix_fromBlocks_mul]
      simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, neg_add_cancel]
      exact block_matrix_one
    · rw [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, hc]
      simp only [adj_one, adj_zero, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add,
        Matrix.mul_neg, neg_add_cancel]
  have hg : g = u * m * v := by
    apply Subtype.ext
    apply Units.ext
    show mat g = mat u * mat m * mat v
    rw [hM, hu, hm', hv, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    have e1 : B * Di * Dd = B := by rw [mul_assoc, hDi2, mul_one]
    have e2 : Dd * (Di * C) = C := by rw [← mul_assoc, hDi1, one_mul]
    rw [e1, e2, mul_assoc B Di C, sub_add_cancel]
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, hu⟩))
    (Subgroup.subset_closure (Or.inr (Or.inl ⟨_, _, hm'⟩)))) (Subgroup.subset_closure (Or.inr (Or.inr ⟨_, hv⟩)))

end PositivityTheory.Rg.Sw.Glob
end
end


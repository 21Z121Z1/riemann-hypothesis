import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiagonalDoubleCosets
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0491
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalSectionsCompatibleSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
section
noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {n : ℕ} : blk4 (1 : Matrix (Fin n) (Fin n) K) 0 0 1 = 1 := by
  simp [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_injective {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h' := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  exact Matrix.fromBlocks_inj.mp h'

theorem neg_block_matrix {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_neg]
  rfl

theorem exists_blockMatrixTwoByTwoFin_eq {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    ∃ A B C D : Matrix (Fin n) (Fin n) K, g = blk4 A B C D := by
  refine ⟨(g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  simp only [blk4, Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id]

theorem is_siegel_parabolic_block_iff {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    IsSiegelP (blk4 a b c d) ↔ c = 0 := by
  constructor
  · intro h
    ext i j
    have h' := h i j
    simpa only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply] using h'
  · rintro rfl i j
    simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]

theorem det_block_lower_zero {n : ℕ} (a b d : Matrix (Fin n) (Fin n) K) :
    (blk4 a b 0 d).det = a.det * d.det := by
  simp only [blk4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

section cT
variable (σ : K →+* K)

theorem cT_mul {a b c : ℕ} (x : Matrix (Fin a) (Fin b) K) (y : Matrix (Fin b) (Fin c) K) :
    cT σ (x * y) = cT σ y * cT σ x := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {a : ℕ} : cT σ (1 : Matrix (Fin a) (Fin a) K) = 1 := by
  unfold cT; simp

theorem cT_zero {a b : ℕ} : cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  unfold cT; simp

theorem cT_neg {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

theorem cT_sub {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) : cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  simp [cT]

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (cT σ x) = x := by
  ext i j
  simp [cT, hσ]

theorem det_cT {a : ℕ} (x : Matrix (Fin a) (Fin a) K) : (cT σ x).det = σ x.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem isUnit_det_cT {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : IsUnit (cT σ x).det := by
  rw [det_cT]; exact hx.map σ

theorem cT_inv {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : cT σ x⁻¹ = (cT σ x)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← cT_mul, Matrix.mul_nonsing_inv _ hx, cT_one]

theorem cT_blk4 {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 a b c d) = blk4 (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  rcases finSumFinEquiv.surjective i with ⟨i, rfl⟩
  rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

end cT

theorem Jm_mul_Jm (n : ℕ) : Jm K n * Jm K n = -1 := by
  rw [Jm, submatrix_fromBlocks_mul, ← block_matrix_one (K := K), neg_block_matrix]
  congr 1 <;> simp

theorem unitary_left_inv (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : (-(Jm K n * cT σ g * Jm K n)) * g = 1 := by
  unfold IsUnitary at hg
  rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g), hg, Jm_mul_Jm, neg_neg]

theorem isUnit_det_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (unitary_left_inv σ hg)

theorem inv_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : g⁻¹ = -(Jm K n * cT σ g * Jm K n) :=
  Matrix.inv_eq_left_inv (unitary_left_inv σ hg)

theorem unitary_mul (σ : K →+* K) {N : ℕ} {J g h : Matrix (Fin N) (Fin N) K}
    (hg : IsUnitary σ J g) (hh : IsUnitary σ J h) : IsUnitary σ J (g * h) := by
  unfold IsUnitary at *
  rw [cT_mul, show cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h by
    simp only [Matrix.mul_assoc], hg, hh]

section eId

theorem eId_mul_eId (n r : ℕ) : eId K n r * eId K n r = eId K n r := by
  rw [eId, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> simp

theorem cT_eId (σ : K →+* K) (n r : ℕ) : cT σ (eId K n r) = eId K n r := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cT, eId, Matrix.diagonal_apply, apply_ite σ]
  · simp [cT, eId, Matrix.diagonal_apply, h, Ne.symm h]

theorem eId_mul_extB {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : eId K n r * extB b = extB b := by
  ext i j
  simp only [eId, Matrix.diagonal_mul, extB]
  split_ifs <;> simp_all

theorem extB_mul_eId {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : extB b * eId K n r = extB b := by
  ext i j
  simp only [eId, Matrix.mul_diagonal, extB]
  split_ifs <;> simp_all

theorem cT_extB (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) :
    cT σ (extB (n := n) b) = extB (cT σ b) := by
  ext i j
  simp only [cT, extB, Matrix.transpose_apply, Matrix.map_apply]
  split_ifs <;> simp_all

theorem extB_injective {n r : ℕ} (hr : r ≤ n) {b b' : Matrix (Fin r) (Fin r) K}
    (h : extB (n := n) b = extB b') : b = b' := by
  ext i j
  have h' := congrFun (congrFun h ⟨i, by omega⟩) ⟨j, by omega⟩
  simpa [extB] using h'

end eId

theorem repMat_eq (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) (a : Matrix (Fin n) (Fin n) K) :
    repMat σ b a = blk4 ((1 - eId K n r) * a) (eId K n r * (cT σ a)⁻¹) (-(eId K n r * a))
      ((1 - eId K n r - extB b) * (cT σ a)⁻¹) := by
  rw [repMat, wr, nB, mA, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  congr 1 <;> simp [sub_mul, mul_sub, add_mul, eId_mul_extB] <;> abel

end GlobalTheory.CompanionTheory.BruhatCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntertwinerOfEquiv
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirSeq

section Alg

variable {k : Type} [Field k]

theorem mul_colMat_of_mem {n : ℕ} (h : GL (Fin (n + 1)) k) (hh : h ∈ Mir k n) (v : Fin n → k) :
    (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * colMat k n v =
      colMat k n ((blockMat k n (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).mulVec v) := by
  have hl := (mem_Mir_iff k h).1 hh
  ext i j
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last =>
      have e : ∀ l : Fin n, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc l) = 0 := by
        intro l
        rw [hl]
        simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
      simp [colMat, mul_apply, Fin.sum_univ_castSucc, e]
    | cast i =>
      simp [colMat, mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct, blockMat]
  · simp [colMat, mul_apply, hj]

theorem colMat_mul_of_mem {n : ℕ} (h : GL (Fin (n + 1)) k) (hh : h ∈ Mir k n) (w : Fin n → k) :
    colMat k n w * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = colMat k n w := by
  have hl := (mem_Mir_iff k h).1 hh
  ext i j
  have e : (colMat k n w * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) i j =
      colMat k n w i (Fin.last n) * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j := by
    rw [mul_apply, Finset.sum_eq_single (Fin.last n)]
    · intro l _ hlne
      simp [colMat, hlne]
    · simp
  rw [e, hl]
  by_cases hj : j = Fin.last n
  · subst hj
    simp [colMat, eLast]
  · simp [colMat, eLast, hj]

theorem conj_mem_MirUin {n : ℕ} (h : Mir k n) (u : MirUin k n) : h * (u : Mir k n) * h⁻¹ ∈ MirUin k n := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  show (h : GL (Fin (n + 1)) k) * ((u : Mir k n) : GL (Fin (n + 1)) k) * (h : GL (Fin (n + 1)) k)⁻¹ ∈ MirU k n
  rw [hv']
  refine ⟨Multiplicative.ofAdd ((blockMat k n ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).mulVec
    v.toAdd), ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext1
  rw [Units.val_mul, Units.val_mul]
  show (1 + colMat k n _) * _ = _ * (1 + colMat k n v.toAdd)
  rw [add_mul, mul_add, one_mul, mul_one, colMat_mul_of_mem _ h.2, mul_colMat_of_mem _ h.2]
  simp

end Alg

section Seq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cInd_ext {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    {H : Subgroup G} {σ : Representation ℂ H W} {F F' : cIndSpace H σ} (h : ∀ g, F.1.1.1 g = F'.1.1.1 g) : F = F' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

section Beta

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle) {n : ℕ}
  (τ : Representation ℂ (Mir k (n + 1)) V)

theorem betaFun_add (a b : V) (g : Mir k (n + 1)) :
    betaFun ψ τ (a + b) g = betaFun ψ τ a g + betaFun ψ τ b g := by
  simp only [betaFun, map_add, Submodule.Quotient.mk_add]

theorem betaFun_smul (c : ℂ) (a : V) (g : Mir k (n + 1)) :
    betaFun ψ τ (c • a) g = c • betaFun ψ τ a g := by
  simp only [betaFun, map_smul, Submodule.Quotient.mk_smul]

end Beta

variable (hI : BetaInd k) (hS : BetaSmooth k) (hC : BetaCompact k)

include hI hS in
theorem betaFun_mem_smooth (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V) (hτ : IsSmooth τ) (v : V) :
    (⟨betaFun ψ τ v, hI ψ n V τ v⟩ : indSpace (Q k n) (qRep k ψ (phiMinus k ψ τ))) ∈
      smoothPart (ind (Q k n) (qRep k ψ (phiMinus k ψ τ))) := by
  have e : {g : Mir k (n + 1) | ind (Q k n) (qRep k ψ (phiMinus k ψ τ)) g ⟨betaFun ψ τ v, hI ψ n V τ v⟩ =
      ⟨betaFun ψ τ v, hI ψ n V τ v⟩} = {g | ∀ x, betaFun ψ τ v (x * g) = betaFun ψ τ v x} := by
    ext g
    exact Subtype.ext_iff.trans funext_iff
  show IsOpen {g : Mir k (n + 1) | ind (Q k n) (qRep k ψ (phiMinus k ψ τ)) g ⟨betaFun ψ τ v, hI ψ n V τ v⟩ =
      ⟨betaFun ψ τ v, hI ψ n V τ v⟩}
  rw [e]
  exact hS ψ n V τ hτ v

def betaMap (ψ : AddChar k Circle) (hc : Continuous ψ) (hne : ψ ≠ 1) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V) (hτ : IsSmooth τ) :
    twKer τ (MirUin k (n + 1)) 1 →ₗ[ℂ] cIndSpace (Q k n) (qRep k ψ (phiMinus k ψ τ)) where
  toFun v := ⟨⟨⟨betaFun ψ τ v, hI ψ n V τ v⟩, betaFun_mem_smooth hI hS ψ τ hτ v⟩, hC ψ hc hne n V τ hτ v v.2⟩
  map_add' a b := cInd_ext fun g => betaFun_add ψ τ (a : V) (b : V) g
  map_smul' c a := cInd_ext fun g => betaFun_smul ψ τ c (a : V) g

end Seq

end GlobalTheory.CompanionTheory.BZMirSeq

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiagonalDoubleCosetsStatement
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_diagonal_double_cosets : ∀ (H : Type) [Group H] (Z L C : Subgroup H) (F : H × H → ℂ),
  (∀ x : H, Z ⊓ L.map (MulAut.conj x).toMonoidHom ≤ C ∧ (Z ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) →
  (∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C) →
  (∀ t ∈ Z, ∀ x h, F (t * x, t * h) = F (x, h)) →
  (∀ l ∈ L, ∀ l' ∈ L, ∀ x h, F (x * l, h * l') = F (x, h)) →
  {Q : DoubleCoset.Quotient ((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) : Subgroup (H × H)) : Set (H × H)) ((L.prod L : Subgroup (H × H)) : Set (H × H)) | F (Quotient.out Q) ≠ 0}.Finite →
  ∑ᶠ Q : DoubleCoset.Quotient ((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) : Subgroup (H × H)) : Set (H × H)) ((L.prod L : Subgroup (H × H)) : Set (H × H)),
      (((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) ⊓ (L.prod L).map (MulAut.conj (Quotient.out Q)).toMonoidHom).relIndex (C.map ((MonoidHom.id H).prod (MonoidHom.id H))) : ℕ) : ℂ) * F (Quotient.out Q) =
    ∑ᶠ q : DoubleCoset.Quotient (Z : Set H) (L : Set H),
      (((Z ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * ∑ᶠ p : H ⧸ L, F (Quotient.out q, p.out) := by
  first | exact @GlobalTheory.CompanionTheory.OrbitCount.orbit_count | exact GlobalTheory.CompanionTheory.OrbitCount.orbit_count | (intros; apply GlobalTheory.CompanionTheory.OrbitCount.orbit_count <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspacesStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_of_annihilating_poly_eigenspaces : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (V : Submodule ℂ M), (∀ v ∈ V, T v ∈ V) → ∀ p : Polynomial ℂ, p ≠ 0 → (∀ v ∈ V, Polynomial.aeval T p v = 0) → (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) → FiniteDimensional ℂ V := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces | exact GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces | (intros; apply GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFieldEmbeddingsDifferFrobeniusStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_field_embeddings_differ_frobenius : ∀ {l : ℕ} [Fact l.Prime] {k D : Type} [Field k] [Finite k] [CommRing D] [IsDomain D] [CharP D l]
    (α β : k →+* D), ∃ i : ℕ, ∀ x, β x = α x ^ l ^ i := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecompositionStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_char_twist_cuspidal_lie_eigenvalue_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ c : ℂ, ∃ (χ : Formalism.L2.Host.HChar E) (L' : Subgroup (GL (Fin a) (Af E))) (J' : Set (Module.End ℂ (Sm E a))), IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ Cofin J' ∧ ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → lie E a (oneL E a) φ = c • φ → mulChi a χ φ ∈ genSpace L' ρ J' ∧ IsCuspidal (mulChi a χ φ).1 ∧ lie E a (oneL E a) (mulChi a χ φ) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspTwist.twist_central | exact GlobalTheory.CompanionTheory.CuspTwist.twist_central | (intros; apply GlobalTheory.CompanionTheory.CuspTwist.twist_central <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteHalfOfTwistStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_half_of_twist : PositivityTheory.Rg.BcB.G8.Fin.FinHalfOf := by
  first | exact @GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf | exact GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf | (intros; apply GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMassProductFormulaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_mass_product_formula : PositivityTheory.Rg.BcB.G8.Fin.MassProd := by
  first | exact @GlobalTheory.CompanionTheory.MassProd.massProd | exact GlobalTheory.CompanionTheory.MassProd.massProd | (intros; apply GlobalTheory.CompanionTheory.MassProd.massProd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_minor_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl F) (X : GL ι (AE F E)) (κ : Matrix ι ι (AE F E)),
    (∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) → ∀ f e : Fin n → ι,
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | exact GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionCentralizerStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_torsion_centralizer_alt : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (N : GL (Fin n) E), N.val.charpoly.Separable →
  {g : GL (Fin n) E | g * N = N * g ∧ IsOfFinOrder g}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer | exact GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer | (intros; apply GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionLatticeCompactStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_torsion_lattice_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K T Γ : Subgroup G) (C : Set G),
  IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (T : Set G) → (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → Γ ≤ T →
  IsCompact C → (∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) →
  (∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) → {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ}.Finite →
  (∀ x : G, T ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
    (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0) ∧
  (∀ x : G, Finite (Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)) ∧
  Finite (Γ ⊓ cptPart T : Subgroup G) ∧
  Finite (DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T) (((cptPart T).subgroupOf T : Subgroup T) : Set T)) := by
  first | exact @GlobalTheory.CompanionTheory.CountClosedComm.main | exact GlobalTheory.CompanionTheory.CountClosedComm.main | (intros; apply GlobalTheory.CompanionTheory.CountClosedComm.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalSectionsCompatibleSystemStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_sections_compatible_system : GEClosedProj → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (E : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (E e) ((E (e + 1)).pull (β e))), (∀ e, (E e).IsLB ∧ (w e).IsGen) → ∀ (m : ℕ) (z : ∀ e, Fin (m + 1) → LB.Sec (E e)), (∀ e j, SecMaps (w e) (z e j) (secPull (z (e + 1) j) (β e))) → VeryAmpleBy (Y 0).hom (E 0) (z 0) → ∃ (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (ζ : Fin (m + 1) → LB.Sec Q) (b : ∀ e, (Y e).left ⟶ X.left) (ω : ∀ e, LB.Iso (Q.pull (b e)) (E e)), Q.IsLB ∧ IsProper X.hom ∧ VeryAmpleBy X.hom Q ζ ∧ (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (ω e).IsGen) ∧ (∀ e j, SecMaps (ω e) (secPull (ζ j) (b e)) (z e j)) ∧ (∀ i₁ i₂ i₃ i₄, (∀ e (c : (E e).ι), (z e i₁).f c * (z e i₂).f c = (z e i₃).f c * (z e i₄).f c) → ∀ c : Q.ι, (ζ i₁).f c * (ζ i₂).f c = (ζ i₃).f c * (ζ i₄).f c) ∧ (∀ S : Set (Fin (m + 1)), (⨆ i ∈ S, nonzeroLocus (z 0 i) = ⊤) → ⨆ i ∈ S, nonzeroLocus (ζ i) = ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.exists_tower_algebraisation | exact GlobalTheory.CompanionTheory.FormalAlg.exists_tower_algebraisation | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.exists_tower_algebraisation <;> assumption)
end


import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0392
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0474
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0489
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0491
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationRelIndexEqResidueCardPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZDeriv

theorem isSmooth_resM {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (N + 1)) k) V)
    (hπ : IsSmooth π) : IsSmooth (resM k π).ρ := by
  intro v
  exact (hπ v).preimage continuous_subtype_val

theorem isGenericFor_of_isCuspidal_of
    (hNZ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (τ : Representation ℂ (Mir k m) V), IsSmooth τ → Nontrivial V →
      ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)))
    (hRes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (m + 1)) k) V),
      twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n))
    (hVan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N →
      twKer π (derUnip k N n) (derChar k ψ N n) = ⊤)
    (hW0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin N) k) V),
      twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N)) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := by
  intro k _ _ _ _ ψ hψc hψ1 N V _ _ π hπ hV
  have hV' : Nontrivial (resM k π).V := hV
  obtain ⟨n, hn, hnt⟩ := hNZ k ψ hψc hψ1 N (resM k π).V (resM k π).ρ (isSmooth_resM π hπ.1) hV'
  rw [Submodule.Quotient.nontrivial_iff, hRes k ψ N n V π] at hnt
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [hW0 k ψ (N + 1) V π] at hnt
    exact Submodule.Quotient.nontrivial_iff.2 hnt
  · exact absurd (hVan k ψ (N + 1) n V π hπ hpos (Nat.lt_succ_of_le hn)) hnt

theorem isGenericFor_of_isCuspidal :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π :=
  isGenericFor_of_isCuspidal_of GlobalTheory.T.exists_nontrivial_derivative (fun k _ _ _ _ ψ m n V _ _ π =>
    GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM (k := k) ψ m n V π) GlobalTheory.T.cuspidal_twisted_kernel_top
    (fun k _ _ _ _ ψ N V _ _ π => GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ N V π)

end GlobalTheory.CompanionTheory.BZDeriv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorBoundByHeightStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_bound_by_height : ∀ (F : Type) [Field F] [NumberField F] (y : F), ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ ∏ᶠ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ∧
    IsIntegral ℤ ((m : F) * y) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.Den.denominator_le | exact GlobalTheory.CompanionTheory.GodementH.Den.denominator_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.Den.denominator_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatPtsUnn

def blkD {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  fun i k => M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr k))

def blkA' {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  fun i k => M (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl k))

theorem det_eq_of_lowerLeft_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (h : ∀ i j : Fin n, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) :
    M.det = (blkA' M).det * (blkD M).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j; exact h i j
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  rfl

theorem mem_upperHalf {D : D7} {n : ℕ} (x : Fin (n + n) → AE D) :
    x ∈ upperHalf D n ↔ ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i)) = 0 := by
  unfold upperHalf
  rw [LinearMap.mem_ker]
  exact funext_iff

end GlobalTheory.CompanionTheory.RatPtsUnn

namespace GlobalTheory.CompanionTheory.RatPtsUnn

theorem mulVec_inr {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (x : Fin (n + n) → R) (i : Fin n) :
    (M *ᵥ x) (finSumFinEquiv (Sum.inr i)) =
      (∑ j, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j))) +
        (blkD M *ᵥ fun k => x (finSumFinEquiv (Sum.inr k))) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  rfl

variable {D : D7} {n : ℕ}

theorem exists_ratEmb_of_mem {γ : G D n} (hγ : γ ∈ GF D n) :
    ∃ g0 : GRat D.sp.cm.sig (Jst D n), ratEmb _ _ g0 = γ := by
  have h : γ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range := by rw [range_ratEmb]; exact hγ
  exact h

theorem mat_ratEmb (g0 : GRat D.sp.cm.sig (Jst D n)) :
    mat (ratEmb _ _ g0) = (g0.1 : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E).map (incA D) := rfl

theorem clause1 : ∀ γ ∈ GF D n, ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det ∧
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g ∧ mat γ = g.map (incA D) := by
  intro γ hγ
  obtain ⟨g0, rfl⟩ := exists_ratEmb_of_mem hγ
  exact ⟨g0.1.1, (Matrix.isUnit_iff_isUnit_det _).1 g0.1.isUnit, g0.2, mat_ratEmb g0⟩

theorem clause2 : ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det →
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g → ∃ γ ∈ GF D n, mat γ = g.map (incA D) := by
  intro g hg hu
  let u : GL (Fin (n + n)) D.host.E := ((Matrix.isUnit_iff_isUnit_det g).2 hg).unit
  have hu' : u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := hu
  refine ⟨ratEmb _ _ ⟨u, hu'⟩, ?_, rfl⟩
  have h : ratEmb D.sp.cm.sig (Jst D n) ⟨u, hu'⟩ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range := ⟨_, rfl⟩
  rw [range_ratEmb] at h
  exact h

theorem mem_P_iff (γ : G D n) :
    γ ∈ P D n ↔ ∀ x : Fin (n + n) → AE D, x ∈ upperHalf D n ↔ mat γ *ᵥ x ∈ upperHalf D n := by
  unfold P
  rw [Subgroup.mem_comap]
  exact Iff.rfl

theorem clause3 : ∀ γ ∈ GF D n, ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = g.map (incA D) →
      (γ ∈ P D n ↔ IsSiegelP g) := by
  intro γ _ g hg
  rw [mem_P_iff, hg]
  constructor
  · intro h i j
    have hx : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈ upperHalf D n := by
      rw [mem_upperHalf]
      intro k
      exact Pi.single_eq_of_ne (fun e => Sum.inr_ne_inl (finSumFinEquiv.injective e)) _
    have h2 := (mem_upperHalf _).1 ((h _).1 hx) i
    rw [Matrix.mulVec_single_one] at h2
    change incA D (g _ _) = 0 at h2
    exact incA_injective (h2.trans (map_zero _).symm)
  · intro hS
    have hM : ∀ i j : Fin n, g.map (incA D) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
      intro i j; rw [Matrix.map_apply, hS i j, map_zero]
    have hdet : IsUnit (blkD (g.map (incA D))).det := by
      have h1 : IsUnit (mat γ).det := by
        unfold mat
        exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
      rw [hg] at h1
      rw [det_eq_of_lowerLeft_zero _ hM] at h1
      exact isUnit_of_mul_isUnit_right h1
    have hinj : ∀ y : Fin n → AE D, blkD (g.map (incA D)) *ᵥ y = 0 → y = 0 := by
      intro y hy
      rw [← Matrix.one_mulVec y, ← Matrix.nonsing_inv_mul _ hdet, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
    have hsum : ∀ (x : Fin (n + n) → AE D) (i : Fin n), (∑ j, g.map (incA D) (finSumFinEquiv (Sum.inr i))
        (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j))) = 0 := fun x i =>
      Finset.sum_eq_zero fun j _ => by rw [hM i j, zero_mul]
    intro x
    rw [mem_upperHalf, mem_upperHalf]
    constructor
    · intro hx i
      rw [mulVec_inr]
      have h0 : (fun k => x (finSumFinEquiv (Sum.inr k))) = 0 := funext hx
      rw [hsum, h0, Matrix.mulVec_zero, zero_add]
      rfl
    · intro hx
      have h0 : (blkD (g.map (incA D)) *ᵥ fun k => x (finSumFinEquiv (Sum.inr k))) = 0 := by
        funext i
        have := hx i
        rw [mulVec_inr, hsum, zero_add] at this
        exact this
      have h1 := hinj _ h0
      exact fun i => congrFun h1 i

theorem ratPtsUnn : RatPts := fun _ _ => ⟨clause1, clause2, clause3⟩

end GlobalTheory.CompanionTheory.RatPtsUnn
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSiegelParabolicInvariance
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

section Blocks

variable {R : Type} [CommRing R] {n : ℕ}

theorem block_matrix_mul_comm_ring (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blk4_map_alt {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem block_matrix_diagonal_one_eq_one : (blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1) = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_injective {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M : Matrix (Fin (n + n)) (Fin (n + n)) R =>
    M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.mp h2

theorem block_matrix_eta (g : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    g = blk4 (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
      (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
      (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
      (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ := by
  unfold blk4
  rw [Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

end Blocks

theorem block_matrix_conj_transpose {K : Type} [Field K] [StarRing K] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    (blk4 a b c d)ᴴ = blk4 aᴴ cᴴ bᴴ dᴴ := by
  unfold blk4
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

variable {D : D7}

theorem jst_eq (n : ℕ) : Jst D n = blk4 0 1 (-1) 0 := rfl

theorem rat_form {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E)
    (hu : gᴴ * Jst D n * g = Jst D n)
    (hP : ∀ i j : Fin n, g (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) :
    ∃ a b d : Matrix (Fin n) (Fin n) D.host.E, g = blk4 a b 0 d ∧ aᴴ * d = 1 ∧ dᴴ * a = 1 := by
  have hg := block_matrix_eta g
  set M := g.submatrix finSumFinEquiv finSumFinEquiv
  have hc : M.toBlocks₂₁ = 0 := by
    exact Matrix.ext fun i j => hP i j
  rw [hc] at hg
  refine ⟨M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₂, hg, ?_⟩
  rw [hg, jst_eq, block_matrix_conj_transpose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring] at hu
  have h := block_matrix_injective hu
  simp at h
  exact ⟨h.1, h.2.1⟩

theorem sigR_incA (x : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (incA D x) = incA D (D.sp.cm.sig x) := by
  simp [sigR, incA, inclR]

theorem lift_mem {n : ℕ} (g0 : GL (Fin (n + n)) D.host.E)
    (h : g0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n)) :
    Formalism.UG.bc (incA D) g0 ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
  have h' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g0.1 * Jst D n * g0.1 = Jst D n := h
  show Formalism.UG.cT _ _ * _ * _ = _
  have e1 : Units.val (Formalism.UG.bc (incA D) g0) = g0.1.map (incA D) := rfl
  have e2 : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g0.1.map (incA D)) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g0.1).map (incA D) := by
    ext i j
    simp [Formalism.UG.cT, sigR_incA]
  rw [e1, e2, show JR (AF D.host.F) (Jst D n) = (Jst D n).map (incA D) from rfl, ← Matrix.map_mul,
    ← Matrix.map_mul, h']

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

variable {D : D7}

theorem mat_mul' {n : ℕ} (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

theorem rat_of_mem {n : ℕ} (p : G D n) (hp : p ∈ P D n ⊓ GF D n) :
    ∃ g0 : GL (Fin (n + n)) D.host.E, g0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) ∧
      mat p = g0.1.map (incA D) ∧
      ∀ i j : Fin n, g0.1 (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
  obtain ⟨hpP, hpF⟩ := Subgroup.mem_inf.mp hp
  have hF : p.1 ∈ HFin (AF D.host.F) D.sp.cm.sig (Jst D n) := hpF
  obtain ⟨g0, hg0, hg0p⟩ := Subgroup.mem_map.mp hF
  have hmat : mat p = g0.1.map (incA D) := by
    show p.1.1 = _
    rw [← hg0p]
    rfl
  refine ⟨g0, hg0, hmat, fun i j => ?_⟩
  apply incA_injective (D := D)
  rw [map_zero]
  have hst := (Subgroup.mem_comap.mp hpP)
  have key := (hst (Pi.single (finSumFinEquiv (Sum.inl j)) 1)).mp ?_
  · rw [upperHalf, LinearMap.mem_ker] at key
    have := congrFun key i
    simp only [LinearMap.funLeft_apply, Pi.zero_apply, Matrix.mulVec_single_one] at this
    change (mat p)ᵀ _ _ = 0 at this
    rw [hmat] at this
    exact this
  · rw [upperHalf, LinearMap.mem_ker]
    funext k
    simp only [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    exact Pi.single_eq_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega) _

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

variable {D : D7}

theorem adj_incA {n : ℕ} (d : Matrix (Fin n) (Fin n) D.host.E) :
    adj ((dᴴ).map (incA D)) = d.map (incA D) := by
  ext i j
  show cA D (incA D (star (d i j))) = incA D (d i j)
  rw [show cA D (incA D (star (d i j))) = incA D (star (star (d i j))) from rfl, star_star]

theorem ratLevi {n : ℕ} (a d : Matrix (Fin n) (Fin n) D.host.E) (had : aᴴ * d = 1) (hda : dᴴ * a = 1) :
    blk4 a 0 0 d * blk4 dᴴ 0 0 aᴴ = 1 ∧ blk4 dᴴ 0 0 aᴴ * blk4 a 0 0 d = 1 ∧
      (blk4 a 0 0 d)ᴴ * Jst D n * blk4 a 0 0 d = Jst D n := by
  have h1 : a * dᴴ = 1 := mul_eq_one_comm.mp hda
  have h2 : d * aᴴ = 1 := mul_eq_one_comm.mp had
  refine ⟨?_, ?_, ?_⟩
  · rw [block_matrix_mul_comm_ring]; simp [h1, h2, block_matrix_diagonal_one_eq_one]
  · rw [block_matrix_mul_comm_ring]; simp [had, hda, block_matrix_diagonal_one_eq_one]
  · rw [jst_eq, block_matrix_conj_transpose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring]; simp [had, hda]

theorem core {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hχ : IsHeckeChar D χ) (hω : IsWeilSch ψ χ θ V μ ω) (p : G D n) (hp : p ∈ P D n ⊓ GF D n)
    (Ψ : schwartzA θ V.rank n) : (ω p Ψ).1 0 = Ψ.1 0 := by
  obtain ⟨g0, hg0, hmat, hlow⟩ := rat_of_mem p hp
  obtain ⟨a, b, d, hg, had, hda⟩ := rat_form g0.1 hg0 hlow
  obtain ⟨hm1, hm2, hmU⟩ := ratLevi (D := D) (n := n) a d had hda
  let a0 : GL (Fin n) D.host.E := ⟨a, dᴴ, mul_eq_one_comm.mp hda, hda⟩
  let m0 : GL (Fin (n + n)) D.host.E := ⟨blk4 a 0 0 d, blk4 dᴴ 0 0 aᴴ, hm1, hm2⟩
  let mEl : G D n := ⟨Formalism.UG.bc (incA D) m0, lift_mem m0 hmU⟩
  let A : GL (Fin n) (AE D) := Formalism.UG.bc (incA D) a0
  have hmEl : mat mEl = blk4 A.1 0 0 (adj (A⁻¹).1) := by
    show (blk4 a 0 0 d).map (incA D) = blk4 (a.map (incA D)) 0 0 (adj ((dᴴ).map (incA D)))
    rw [blk4_map_alt, adj_incA, Matrix.map_zero _ (map_zero _)]
  let nEl : G D n := p * mEl⁻¹
  have hpe : p = nEl * mEl := by simp [nEl]
  have hinv : mat mEl⁻¹ = (blk4 dᴴ 0 0 aᴴ).map (incA D) := by
    simp only [mat, map_inv]
    rfl
  have hnEl : mat nEl = blk4 1 ((b * aᴴ).map (incA D)) 0 1 := by
    rw [mat_mul', hinv, hmat, hg, ← Matrix.map_mul, block_matrix_mul_comm_ring]
    have h1 : a * dᴴ = 1 := mul_eq_one_comm.mp hda
    have h2 : d * aᴴ = 1 := mul_eq_one_comm.mp had
    simp [h1, h2, blk4_map_alt]
  have hdet : Matrix.GeneralLinearGroup.det A = Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a0) := by
    ext
    simp [A, Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [hpe, map_mul, Module.End.mul_apply, hω.unip nEl _ hnEl, hω.levi mEl A hmEl, hdet, hχ.2]
  have hab : absA D (Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a0)) = 1 :=
    absE_inclR _
  simp [npow, GlobalTheory.StdUnn.inner, halfTr]
  erw [hab]
  simp

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open PositivityTheory.GramSchwartzFunctions.EC

theorem pInv : PositivityTheory.GramSchwartzFunctions.EC.PInv := by
  intro D n V ψ χ θ μ ω hS Φ γ hγ g
  have hχ : IsHeckeChar D χ := hS.2.2.2.1
  have hω : IsWeilSch ψ χ θ V μ ω := hS.2.2.2.2.2.2.2
  show (ω (γ * g) Φ).1 0 = (ω g Φ).1 0
  rw [map_mul, Module.End.mul_apply]
  exact core hχ hω γ hγ _

end GlobalTheory.CompanionTheory.EisCellsPInv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationMapsLinearStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_maps_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f g : XS τ σ) (c : ℂ),
  eC ψ (f + g) = eC ψ f + eC ψ g ∧ eC ψ (c • f) = c • eC ψ f ∧ eO ψ (f + g) = eO ψ f + eO ψ g ∧ eO ψ (c • f) = c • eO ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear | exact GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversalStatement
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_conjugacy_transversal : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H), IsCompact (K : Set H) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  first | exact @GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets | exact GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets | (intros; apply GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGaloisExtensionOfEmbeddingStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_extension_of_embedding : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l),
    ∃ g : GQ l, ∀ x : ↥K.1, g (x : Om l) = μ x := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_gal_extending_embedding <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenIntegralSubgroup
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.LevelU

theorem exists_level : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) →
  ∃ U : Subgroup (AdelicGLn.integralFiniteGL E N), IsOpen (U : Set (AdelicGLn.integralFiniteGL E N)) ∧ ∀ u : U, ∃ k ∈ L,
    finEmb E N ((u : AdelicGLn.integralFiniteGL E N) : AdelicGLn.FiniteAdelicGL E N) = finGL E N k := by
  intro E _ _ _ N L hL
  refine ⟨L.subgroupOf (AdelicGLn.integralFiniteGL E N), hL.preimage continuous_subtype_val, ?_⟩
  intro u
  exact ⟨_, Subgroup.mem_subgroupOf.1 u.2, GlobalTheory.CompanionTheory.AutLevel.finEmb_eq_finGL E N _⟩

end GlobalTheory.CompanionTheory.Conc.LevelU
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPositiveHermitianFormStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positive_hermitian_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (N : GL (Fin n) E),
  N.val.charpoly.Separable → (∀ τ : E →+* ℂ, ∀ z ∈ (N.val.charpoly.map τ).roots, ‖z‖ = 1) →
  ∃ H : Matrix (Fin n) (Fin n) E, IsUnit H.det ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
    N ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ ∀ τ : E →+* ℂ, (H.map τ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.TraceHerm.exists_posDef_herm | exact GlobalTheory.CompanionTheory.TraceHerm.exists_posDef_herm | (intros; apply GlobalTheory.CompanionTheory.TraceHerm.exists_posDef_herm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationRelIndexEqResidueCardPowStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_relIndex_eq_residue_card_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → ∀ d : ℕ, (filt ϖ x (d + 1)).relIndex (filt ϖ x d) = Nat.card 𝓀[k] ^ ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.relIndex_filt_succ | exact GlobalTheory.CompanionTheory.IwJac.relIndex_filt_succ | (intros; apply GlobalTheory.CompanionTheory.IwJac.relIndex_filt_succ <;> assumption)
end


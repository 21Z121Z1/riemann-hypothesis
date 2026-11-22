import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0774
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0669
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0667
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0647
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0804
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0767
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0783

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

namespace GlobalTheory.CompanionTheory.SwUnf.BigCell

section Field

variable {K : Type} [Field K] {n : ℕ}

theorem cT_mul_sq (σ : K →+* K) (x y : Matrix (Fin n) (Fin n) K) : cT σ (x * y) = cT σ y * cT σ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq (σ : K →+* K) : cT σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem cT_blk4 (σ : K →+* K) (a b c d : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 a b c d) = blk4 (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  simp only [cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem block_identity_eq_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem lowerLeft_block {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) : lowerC (blk4 a b c d) = c := by
  ext i j
  simp [lowerC, blk4]

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ a b, M = blk4 a b (lowerC M) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD M) := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂, ?_⟩
  have h : Matrix.fromBlocks (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ (lowerC M) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD M) =
      M.submatrix finSumFinEquiv finSumFinEquiv :=
    Matrix.fromBlocks_toBlocks _
  unfold blk4
  rw [h]
  ext i j
  simp

theorem isSiegelParabolic_iff (M : Matrix (Fin (n + n)) (Fin (n + n)) K) : IsSiegelP M ↔ lowerC M = 0 := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

theorem cellKer_eq_bot_iff' {E : Type} [Field E] (C : Matrix (Fin n) (Fin n) E) :
    LinearMap.ker C.mulVecLin = ⊥ ↔ IsUnit C.det := by
  rw [LinearMap.ker_eq_bot, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  rfl

abbrev cellM (b : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 0 1 (-1) (-b)

theorem cellM_mul (b : Matrix (Fin n) (Fin n) K) : cellM b * blk4 (-b) (-1) 1 0 = 1 := by
  rw [cellM, submatrix_fromBlocks_mul]
  simp [block_identity_eq_one]

theorem mul_cellM (b : Matrix (Fin n) (Fin n) K) : blk4 (-b) (-1) 1 0 * cellM b = 1 := by
  rw [cellM, submatrix_fromBlocks_mul]
  simp [block_identity_eq_one]

theorem cellM_det (b : Matrix (Fin n) (Fin n) K) : IsUnit (cellM b).det :=
  Matrix.isUnit_det_of_left_inverse (mul_cellM b)

theorem cellM_inv (b : Matrix (Fin n) (Fin n) K) : (cellM b)⁻¹ = blk4 (-b) (-1) 1 0 :=
  Matrix.inv_eq_right_inv (cellM_mul b)

theorem lower_rel (σ : K →+* K) {A B C Dd : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B C Dd)) : Dd * cT σ C = C * cT σ Dd := by
  have hJJ : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 (-1) 1 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [block_identity_eq_one]
  have hJJ' : (blk4 0 (-1) 1 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 1 (-1) 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [block_identity_eq_one]
  have h0 : cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0 * blk4 A B C Dd = blk4 0 1 (-1) 0 := h
  have h1 : (blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0) * blk4 A B C Dd = 1 := by
    rw [mul_assoc (blk4 0 (-1) 1 0), mul_assoc (blk4 0 (-1) 1 0), h0, hJJ']
  have h2 := mul_eq_one_comm.1 h1
  have h3 : blk4 A B C Dd * blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) = blk4 0 (-1) 1 0 := by
    calc _ = blk4 A B C Dd * (blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0) * blk4 0 (-1) 1 0 := by
          simp only [mul_assoc, hJJ, mul_one]
      _ = _ := by rw [h2, one_mul]
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h3
  obtain ⟨-, -, -, h4⟩ := blockMatrixTwoByTwoFin_injective h3
  simp only [mul_zero, mul_neg, mul_one, zero_add, add_zero] at h4
  exact sub_eq_zero.1 (by simpa [sub_eq_add_neg, add_comm] using h4)

theorem herm_of_rel (σ : K →+* K) {C Dd : Matrix (Fin n) (Fin n) K} (hC : IsUnit C.det)
    (h : Dd * cT σ C = C * cT σ Dd) : cT σ (C⁻¹ * Dd) = C⁻¹ * Dd := by
  have a1 : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ hC
  have b1 : cT σ C * cT σ C⁻¹ = 1 := by rw [← cT_mul_sq, a1, cT_one_sq]
  have b2 : C⁻¹ * Dd * cT σ C = cT σ Dd := by rw [mul_assoc, h, ← mul_assoc, a1, one_mul]
  rw [cT_mul_sq, ← b2, mul_assoc, b1, mul_one]

theorem lower_unit {x : Matrix (Fin (n + n)) (Fin (n + n)) K} (hx : IsUnit x.det) (b : Matrix (Fin n) (Fin n) K)
    (hS : IsSiegelP (x * (cellM b)⁻¹)) : IsUnit (lowerC x).det := by
  rw [cellM_inv] at hS
  set S := x * blk4 (-b) (-1) 1 0 with hSd
  have hSx : S * cellM b = x := by rw [hSd, mul_assoc, mul_cellM, mul_one]
  have hdet : IsUnit S.det := by
    rw [hSd, Matrix.det_mul]
    exact hx.mul (Matrix.isUnit_det_of_left_inverse (cellM_mul b))
  have hd : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD S).det := by
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero S hS] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  obtain ⟨a, c, hb⟩ := exists_blockMatrixTwoByTwoFin_eq S
  have h0 : lowerC S = 0 := (isSiegelParabolic_iff S).1 hS
  rw [h0] at hb
  have e : lowerC x = -GlobalTheory.CompanionTheory.RatPtsUnn.blkD S := by
    rw [← hSx, hb, cellM, submatrix_fromBlocks_mul, lowerLeft_block, ← hb]
    simp
  rw [e, ← Matrix.isUnit_iff_isUnit_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).2 hd).neg

theorem of_lower_unit (σ : K →+* K) {x : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hu : IsUnitary σ (blk4 0 1 (-1) 0) x) (hC : IsUnit (lowerC x).det) :
    cT σ ((lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x) = (lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x ∧
      IsSiegelP (x * (cellM ((lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x))⁻¹) := by
  obtain ⟨a, b, hb⟩ := exists_blockMatrixTwoByTwoFin_eq x
  have hu' : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 a b (lowerC x) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD x)) := by
    rw [← hb]
    exact hu
  refine ⟨herm_of_rel σ hC (lower_rel σ hu'), ?_⟩
  rw [cellM_inv, isSiegelParabolic_iff]
  have a2 : lowerC x * (lowerC x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hC
  generalize hl : (lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = l
  have e : lowerC x * l = GlobalTheory.CompanionTheory.RatPtsUnn.blkD x := by
    rw [← hl, ← mul_assoc, a2, one_mul]
  conv_lhs => rw [hb]
  rw [submatrix_fromBlocks_mul, lowerLeft_block, mul_neg, e]
  simp

end Field

variable {D : D7} {n : ℕ}

theorem ratOf_spec (γ : GF D n) : IsUnit (ratOf γ).det ∧
    IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (blk4 0 1 (-1) 0) (ratOf γ) := by
  obtain ⟨g, hd, hu, hm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause1 γ.1 γ.2
  have e : ratOf γ = g := Matrix.map_injective incA_injective ((mat_ratOf γ).symm.trans hm)
  rw [e]
  exact ⟨hd, hu⟩

theorem mat_cell_rat {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : Matrix (Fin n) (Fin n) D.host.E)
    (hu : mat u = blk4 1 (b.map (incA D)) 0 1) : mat (w * u) = (cellM b).map (incA D) := by
  rw [mat_cell hw hu, cellM, blk4_map_alt]
  have e0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := map_zero (incA D).mapMatrix
  have e1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := map_one (incA D).mapMatrix
  have e2 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = -1 := by
    have := map_neg (incA D).mapMatrix (1 : Matrix (Fin n) (Fin n) D.host.E)
    rwa [map_one] at this
  have e3 : (-b).map (incA D) = -(b.map (incA D)) := map_neg (incA D).mapMatrix b
  rw [e0, e1, e2, e3]

theorem exists_hermQ (l : ratHerm D n) : ∃ b : HermQ D n, b.1.map (incA D) = l.1.1 := by
  have hm : l.1.1 ∈ ratMx D n n := l.2
  obtain ⟨b, hb⟩ := hm
  have hb' : b.map (incA D) = l.1.1 := hb
  have hadj : adj (b.map (incA D) : Mx D n n) = b.map (incA D) := by
    rw [hb']
    exact l.1.2
  refine ⟨⟨b, fun i j => incA_injective ?_⟩, hb'⟩
  exact congrFun (congrFun hadj i) j

theorem bigCell : ∀ {D : D7} {n : ℕ} {w : G D n}, mat w = blk4 0 1 (-1) 0 → ∀ {nb : hermA D n → G D n}, IsNMap nb → ∃ e : ratHerm D n → Cosets (P D n) (GF D n), Function.Injective e ∧ (∀ q, cosetCell q = ⊥ ↔ q ∈ Set.range e) ∧ ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D n) (y : G D n), term (P D n) (GF D n) f y (e l) = f (w * nb l.1 * y) := by
  intro D n w hw nb hnb
  choose β hβ using exists_hermQ (D := D) (n := n)
  have hu : ∀ l, mat (nb l.1) = blk4 1 ((β l).1.map (incA D)) 0 1 := fun l => by
    rw [hβ]
    exact hnb l.1
  let c : ratHerm D n → GF D n := fun l => ⟨w * nb l.1, cell_mem_GF hw (β l) (hu l)⟩
  have hc : ∀ l, mat (c l).1 = (cellM (β l).1).map (incA D) := fun l => mat_cell_rat hw _ (hu l)
  refine ⟨fun l => mk ((P D n).subgroupOf (GF D n)) (c l), ?_, ?_, ?_⟩
  · intro l l' h
    obtain ⟨δ, hδ⟩ := mk_eq_iff.1 h
    have hP : (w * nb l'.1) * (w * nb l.1)⁻¹ ∈ P D n := by
      have e : (w * nb l'.1) * (w * nb l.1)⁻¹ = δ.1.1 := by
        have := congrArg Subtype.val hδ
        change δ.1.1 * (w * nb l.1) = w * nb l'.1 at this
        rw [← this]
        exact mul_inv_cancel_right _ _
      rw [e]
      exact Subgroup.mem_subgroupOf.1 δ.2
    have hbb := cell_inj hw (hu l) (hu l') hP
    apply Subtype.ext
    apply Subtype.ext
    rw [← hβ l, ← hβ l', hbb]
  · intro q
    have hspec := ratOf_spec (Quotient.out q)
    have hker : cosetCell q = ⊥ ↔ IsUnit (lowerC (ratOf (Quotient.out q))).det :=
      cellKer_eq_bot_iff' _
    rw [hker]
    constructor
    · intro hC
      obtain ⟨hh, hS⟩ := of_lower_unit _ hspec.2 hC
      set lam := (lowerC (ratOf (Quotient.out q)))⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (Quotient.out q)) with hlam
      let b : HermQ D n := ⟨lam, fun i j => congrFun (congrFun hh i) j⟩
      let l : ratHerm D n := ⟨⟨lam.map (incA D), adj_map_herm b⟩, ⟨lam, rfl⟩⟩
      have hbl : (β l).1 = lam := Matrix.map_injective incA_injective (hβ l)
      refine ⟨l, ?_⟩
      have hmk := (GlobalTheory.CompanionTheory.EisCellsAsm.mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l) (Quotient.out q)
        (cellM_det _) (hc l) (mat_ratOf _)).2 (by rw [hbl]; exact hS)
      exact hmk.trans (Quotient.out_eq q)
    · rintro ⟨l, rfl⟩
      have hmk : mk ((P D n).subgroupOf (GF D n)) (c l) =
          mk ((P D n).subgroupOf (GF D n)) (Quotient.out (mk ((P D n).subgroupOf (GF D n)) (c l))) :=
        (Quotient.out_eq _).symm
      exact lower_unit hspec.1 _ ((GlobalTheory.CompanionTheory.EisCellsAsm.mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l) _
        (cellM_det _) (hc l) (mat_ratOf _)).1 hmk)
  · intro f hf l y
    exact term_mk hf y (c l)

end GlobalTheory.CompanionTheory.SwUnf.BigCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterQuadraticFormIdentity
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RCellP

variable {D : D7} {n r t : ℕ}

theorem maj_mem {θ : InfFam D} {a b : ℕ} {φ : Mx D a b → ℂ} (hφ : φ ∈ schwartzA θ a b) :
    ∃ F ∈ schwartzA θ a b, ∀ x, (F x).im = 0 ∧ ‖φ x‖ ≤ (F x).re := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨F₀, hF₀⟩ := GlobalTheory.T.schwartz_exists_real_majorant _ f
    refine ⟨fun x => F₀ (fun τ i j => compAt θ τ x i j) * (fun u => ((‖g u‖ : ℝ) : ℂ)) (fun i j => finPart D (x i j)),
      Submodule.subset_span ⟨F₀, fun u => ((‖g u‖ : ℝ) : ℂ), ⟨?_, ?_⟩, rfl⟩, fun x => ?_⟩
    · exact hg.1.comp fun z => ((‖z‖ : ℝ) : ℂ)
    · exact hg.2.comp_left (g := fun z => ((‖z‖ : ℝ) : ℂ)) (by simp)
    · have h := hF₀ (fun τ i j => compAt θ τ x i j)
      constructor
      · simp [Complex.mul_im, h.1]
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, norm_mul]
        exact mul_le_mul_of_nonneg_right h.2 (norm_nonneg _)
  | zero => exact ⟨0, Submodule.zero_mem _, fun x => by simp⟩
  | add φ₁ φ₂ _ _ h₁ h₂ =>
    obtain ⟨F₁, m₁, e₁⟩ := h₁
    obtain ⟨F₂, m₂, e₂⟩ := h₂
    refine ⟨F₁ + F₂, Submodule.add_mem _ m₁ m₂, fun x => ⟨?_, ?_⟩⟩
    · simp [(e₁ x).1, (e₂ x).1]
    · simpa using (norm_add_le _ _).trans (add_le_add (e₁ x).2 (e₂ x).2)
  | smul c φ _ h =>
    obtain ⟨F, m, e⟩ := h
    refine ⟨((‖c‖ : ℝ) : ℂ) • F, Submodule.smul_mem _ _ m, fun x => ⟨?_, ?_⟩⟩
    · simp [(e x).1]
    · simpa [norm_smul] using mul_le_mul_of_nonneg_left (e x).2 (norm_nonneg c)

theorem exists_real_schwartz_majorant {θ : InfFam D} {a b : ℕ} (Φ : schwartzA θ a b) :
    ∃ F : schwartzA θ a b, ∀ x, (F.1 x).im = 0 ∧ ‖Φ.1 x‖ ≤ (F.1 x).re :=
  let ⟨F, m, e⟩ := maj_mem Φ.2
  ⟨⟨F, m⟩, e⟩

theorem c_jn_cont (hn : r + t = n) {a : ℕ} : Continuous (fun z : Mx D a r × Mx D a t => jn hn z.1 z.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun z : Mx D a r × Mx D a t => Matrix.fromCols z.1 z.2 i ((finSumFinEquiv.trans (finCongr hn)).symm j)
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = c
  rcases c with c | c
  · exact continuous_fst.matrix_elem i c
  · exact continuous_snd.matrix_elem i c

theorem inner_product_mul_eq_pairing (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (x : Mx D V.rank r) (v : Mx D V.rank t) (y : Mx D r t) :
    ip V (mm x y) v = pr b₀ y (yv V b₀ (x, v)) := by
  have h1 : (b₀.1.map (incA D) : Mx D r r) * rat b₀.1⁻¹ = 1 := by
    show b₀.1.map (incA D) * b₀.1⁻¹.map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hb)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  simp only [ip, pr, yv, mm, adj_mul]
  rw [← Matrix.mul_assoc (b₀.1.map (incA D)), h1, Matrix.one_mul, Matrix.mul_assoc]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : AF D.host.F) : conj (ψ u) = ψ (-u) := by
  have h1 : ψ u * conj (ψ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.2.1 u]
    simp
  have h2 : ψ u * ψ (-u) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ u ≠ 0 := fun h => by simp [h] at h1
  exact mul_left_cancel₀ h0 (h1.trans h2.symm)

theorem character_quadratic_form_identity (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D r) (b : hermA D t)
    (z : Mx D V.rank r × Mx D V.rank t) :
    pch ψ b.1 (ip V z.2 z.2) * conj (ψ (halfTr (Matrix.trace (mm b.1 (pr b₀ (yv V b₀ z) (yv V b₀ z)))))) = pch ψ b.1 (qv V b₀ z) := by
  rw [conj_psi hψ]
  simp only [pch, qv, mm]
  rw [← AddChar.map_add_eq_mul, Matrix.mul_sub, Matrix.trace_sub]
  congr 1
  simp only [halfTr, trA, map_sub]
  ring

theorem integrable_schwartz_slice {θ : InfFam D} (hθ : IsInfFam θ) {a : ℕ} (hn : r + t = n) (μt : Measure (Mx D a t)) [μt.IsAddHaarMeasure]
    (Φ : schwartzA θ a n) (x : Mx D a r) : Integrable (fun v => Φ.1 (jn hn x v)) μt := GlobalTheory.T.integrable_schwartz_restriction_columns hθ hn μt Φ x

theorem fub {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Y} {ν : Measure X} [SFinite μ] [SFinite ν]
    {P : X → ℂ} {e : Y → X → ℂ} {O : Y → ℂ} (hP : Integrable P ν) (hO : Integrable O μ)
    (he : AEStronglyMeasurable (fun q : Y × X => e q.1 q.2) (μ.prod ν)) (hn : ∀ y z, ‖e y z‖ = 1)
    (hem : ∀ y, AEStronglyMeasurable (e y) ν) :
    (∀ y, Integrable (fun z => P z * e y z) ν) ∧
    ∫ y, (∫ z, P z * e y z ∂ν) * O y ∂μ = ∫ z, P z * ∫ y, e y z * O y ∂μ ∂ν := by
  have hIPe : ∀ y, Integrable (fun z => P z * e y z) ν := fun y =>
    hP.mono (hP.aestronglyMeasurable.mul (hem y)) (ae_of_all _ fun z => by simp [hn])
  refine ⟨hIPe, ?_⟩
  have hbase := Integrable.mul_prod hO hP
  have hIF : Integrable (Function.uncurry fun (y : Y) z => P z * e y z * O y) (μ.prod ν) := by
    refine hbase.mono ?_ (ae_of_all _ fun q => ?_)
    · exact (hP.aestronglyMeasurable.comp_snd.mul he).mul hO.aestronglyMeasurable.comp_fst
    · simp [Function.uncurry, hn, mul_comm]
  calc ∫ y, (∫ z, P z * e y z ∂ν) * O y ∂μ = ∫ y, ∫ z, P z * e y z * O y ∂ν ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        beta_reduce
        rw [integral_mul_const]
    _ = ∫ z, ∫ y, P z * e y z * O y ∂μ ∂ν := integral_integral_swap hIF
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        beta_reduce
        simp only [mul_assoc]
        rw [integral_const_mul]

theorem integrable_fib (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D}
    (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕)
    (b₀ : HermE D r) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib)
    (Φ : schwartzA θ V.rank n) {w : G D t} (hw : IsW w) :
    Integrable (fun z => Φ.1 (jn hn z.1 z.2)) (fib.prod μt) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -⟩ := lattice_Mx D V.rank t
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank t) := ⟨rfl⟩
  haveI := hfib.fin
  haveI := hμt.choose_spec.1
  obtain ⟨F, hF⟩ := exists_real_schwartz_majorant Φ
  have hPa := hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt
  have hm : ∀ x, ∫ v, F.1 (jn hn x v) ∂μt = (ω (M.emb w) F).1 (jn hn x 0) := by
    intro x
    rw [(hPa F).2.2 w hw x 0]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    have : ip V (0 : Mx D V.rank t) v = 0 := by
      simp [ip, mm, adj]
    simp [this]
  have hφ := (hPa (ω (M.emb w) F)).2.1
  have hint := (hfib.int _ hφ).1
  have hcF : Continuous fun z : Mx D V.rank r × Mx D V.rank t => F.1 (jn hn z.1 z.2) :=
    (GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ F).comp (c_jn_cont hn)
  have hcΦ : Continuous fun z : Mx D V.rank r × Mx D V.rank t => Φ.1 (jn hn z.1 z.2) :=
    (GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ Φ).comp (c_jn_cont hn)
  have hIF : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => F.1 (jn hn z.1 z.2)) (fib.prod μt) := by
    refine (integrable_prod_iff hcF.aestronglyMeasurable).2 ⟨ae_of_all _ fun x => integrable_schwartz_slice hθ hn μt F x, ?_⟩
    refine (hint.re).congr (ae_of_all _ fun x => ?_)
    have e1 : ∀ v, ‖F.1 (jn hn x v)‖ = (F.1 (jn hn x v)).re := by
      intro v
      have h := hF (jn hn x v)
      have h0 : 0 ≤ (F.1 (jn hn x v)).re := (norm_nonneg _).trans h.2
      rw [← Complex.re_add_im (F.1 (jn hn x v)), h.1]
      simp [abs_of_nonneg h0]
    simp only [e1]
    show (RCLike.re ((ω (M.emb w) F).1 (jn hn x 0))) = _
    rw [← hm x]
    exact (integral_re (integrable_schwartz_slice hθ hn μt F x)).symm
  exact hIF.mono hcΦ.aestronglyMeasurable (ae_of_all _ fun z =>
    (hF _).2.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _)))

theorem core (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D}
    (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕)
    (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib)
    {Ω : G D t → Mx D r t → ℂ} (hΩ : IsTh ψ χ θ b₀ m.μ Ω)
    (Φ : schwartzA θ V.rank n) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t)
    (hI : Integrable (fun z => Φ.1 (jn hn z.1 z.2)) (fib.prod μt)) :
    Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω (w * nb b) =
        ∫ z, Φ.1 (jn hn z.1 z.2) * conj (Ω 1 (yv V b₀ z)) * pch ψ b.1 (qv V b₀ z) ∂(fib.prod μt) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -⟩ := lattice_Mx D V.rank t
  obtain ⟨k1, k2, k3, k4, -⟩ := lattice_Mx D r t
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank t) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r t) := ⟨rfl⟩
  haveI := hfib.fin
  haveI := hμt.choose_spec.1
  haveI := m.hμ.1
  obtain ⟨hc1, hc2, hc3, hc4, hn1, hn2⟩ := GlobalTheory.T.continuous_theta_kernel_components (t := t) hψ V b₀ b
  have hcΦ : Continuous fun z : Mx D V.rank r × Mx D V.rank t => Φ.1 (jn hn z.1 z.2) :=
    (GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ Φ).comp (c_jn_cont hn)
  have hcP : Continuous fun z : Mx D V.rank r × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2) * Φ.1 (jn hn z.1 z.2) := hc1.mul hcΦ
  have hIP : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2) * Φ.1 (jn hn z.1 z.2)) (fib.prod μt) :=
    hI.mono hcP.aestronglyMeasurable (ae_of_all _ fun z => by simp [hn1])
  have hcΩ : Continuous (Ω (w * nb b)) := hΩ.cont.comp (continuous_const.prodMk continuous_id)
  have hIΩ : Integrable (fun y => conj (Ω (w * nb b) y)) m.μ :=
    (GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ m.μ ⟨_, hΩ.mem (w * nb b)⟩).mono
      (Complex.continuous_conj.comp hcΩ).aestronglyMeasurable (ae_of_all _ fun y => by simp)
  obtain ⟨hIPe, hsw⟩ := fub (μ := m.μ) (ν := fib.prod μt) (e := fun y z => ψ (trA (Matrix.trace (pr b₀ y (yv V b₀ z))))) hIP hIΩ
    hc3.aestronglyMeasurable (fun y z => hn2 _)
    (fun y => (hc3.comp (Continuous.prodMk_right y)).aestronglyMeasurable)
  have hW : ∀ y, Wz M m ψ b₀ (fun g => (ω g Φ).1 0) (M.sh y * M.emb (w * nb b) * 1) =
      ∫ z, pch ψ b.1 (ip V z.2 z.2) * Φ.1 (jn hn z.1 z.2) * ψ (trA (Matrix.trace (pr b₀ y (yv V b₀ z)))) ∂(fib.prod μt) := by
    intro y
    rw [GlobalTheory.T.weil_representation_theta_integral hP M m V hψ hχ hη hθ hμ hω hμr hμt b₀ hfib Φ, integral_prod _ (hIPe y)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    beta_reduce
    rw [GlobalTheory.T.weil_representation_fourier_coefficient hP M V hψ hχ hη hθ hμ hω hμr hμt Φ hnb hw b y x]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    beta_reduce
    rw [inner_product_mul_eq_pairing V b₀ hb x v y]
  unfold Rsec
  simp only [hW]
  rw [hsw]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  beta_reduce
  rw [GlobalTheory.T.theta_fourier_coefficient_weyl_integral hψ hχ hΩ hnb hw b (yv V b₀ z), map_mul, ← character_quadratic_form_identity V hψ b₀ b z]
  ring

theorem rcell : WMaj → PartFT → RCell := by
  intro _ hP D n t B W d hn ψ χ θ μB μW ωB ωW hS M m b₀ hb μr μt hμr hμt fib hfib Ω hΩ Φ nb hnb w hw
  obtain ⟨𝓕, h𝓕⟩ := hS.hμB
  have hn0 : 0 < n := by
    have := hS.pos
    have := hS.lt
    omega
  have hη : ResEta D χ B.rank := GlobalTheory.RegSch.JointCont.resEta_of_isWeilSch hn0 hS.hψ hS.hθ h𝓕 hS.hB
  have hI := integrable_fib hP M m B hS.hψ hS.hχ hη hS.hθ ⟨𝓕, h𝓕⟩ hS.hB hμr hμt b₀ hfib Φ hw
  exact ⟨hI, fun b => core hP M m B hS.hψ hS.hχ hη hS.hθ ⟨𝓕, h𝓕⟩ hS.hB hμr hμt b₀ hb hfib hΩ Φ hnb hw b hI⟩

end GlobalTheory.CompanionTheory.RCellP

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisCells
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCellsChapter

theorem eisCells : PositivityTheory.GramSchwartzFunctions.EisCells :=
  GlobalTheory.T.eisenstein_cells_decomposition GlobalTheory.T.eisenstein_bruhat_decomposition GlobalTheory.T.eisenstein_rational_points GlobalTheory.T.eisenstein_siegel_parabolic_invariance
    (GlobalTheory.T.eisenstein_second_term_from_parts GlobalTheory.T.eisenstein_heisenberg_schwartz GlobalTheory.T.eisenstein_covariance GlobalTheory.T.eisenstein_vanishing GlobalTheory.T.eisenstein_unfolding_second_term GlobalTheory.T.eisenstein_theta_invariance)

end GlobalTheory.CompanionTheory.EisCellsChapter
end


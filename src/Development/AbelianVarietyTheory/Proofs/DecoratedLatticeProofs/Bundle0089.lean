import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0088
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateUnitaryKTypeSameWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypothesesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_bounds_of_standingHypotheses : ∀ M : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1000 ≤ Cl ∧ M ≤ Cl ∧ M ≤ (D.R.m : ℝ) ∧ M ≤ (D.R.k : ℝ) ∧ D.host.rdE ≤ large₂.sc.b ∧ (D.R.k : ℝ) ^ M ≤ large₂.sc.b ∧ (D.R.r : ℝ) ≤ large₂.sc.b ∧ (D.R.m : ℝ) ^ 2 ≤ D.R.k ∧ M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
  first | exact @GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses | exact GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses | (intros; apply GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoundLatLoc
section
noncomputable section

namespace GlobalTheory.LocalLatticeBound

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem abs_zero_le (v : HeightOneSpectrum (𝓞 F)) (C : ℝ≥0) : absFin F v (0 : Fv F v ⊗[F] E) ≤ C :=
  (absFin_le_iff F v).2 fun τ => by rw [map_zero, (absBar_eq_zero F v).2 rfl]; exact zero_le

theorem abs_neg_le (v : HeightOneSpectrum (𝓞 F)) {C : ℝ≥0} {y : Fv F v ⊗[F] E} (h : absFin F v y ≤ C) :
    absFin F v (-y) ≤ C :=
  (absFin_le_iff F v).2 fun τ => by rw [map_neg, absBar_neg]; exact (le_absFin F v τ y).trans h

theorem abs_int_mul_le (v : HeightOneSpectrum (𝓞 F)) {C : ℝ≥0} {c y : Fv F v ⊗[F] E} (hc : c ∈ intLoc F E v)
    (h : absFin F v y ≤ C) : absFin F v (c * y) ≤ C :=
  (absFin_mul_le F v c y).trans ((mul_le_mul' (absFin_le_one_of_mem_intLoc hc) h).trans_eq (one_mul C))

theorem exists_bound_rat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ C : ℝ≥0, ∀ x ∈ L, ∀ i, absFin F v ((1 : Fv F v) ⊗ₜ[F] x i) ≤ C := by
  obtain ⟨S, rfl⟩ := hL
  refine ⟨S.sup fun s => Finset.univ.sup fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i), fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem s hs =>
    exact (Finset.le_sup (f := fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i)) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun s : Fin n → E => Finset.univ.sup fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i)) hs)
  | zero => rw [Pi.zero_apply, TensorProduct.tmul_zero]; exact abs_zero_le v _
  | add x y _ _ hx hy =>
    rw [Pi.add_apply, TensorProduct.tmul_add]
    exact (absFin_add_le F v _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    have e : (1 : Fv F v) ⊗ₜ[F] (c • x) i = ((1 : Fv F v) ⊗ₜ[F] (c : E)) * ((1 : Fv F v) ⊗ₜ[F] x i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
    rw [e]
    exact abs_int_mul_le v (tmul_mem_intLoc (one_mem _) c) hx

theorem exists_bound_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i : Fin n, absFin F v (y i) ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_rat L (Submodule.IsLattice.fg (A := E)) v
  refine ⟨C, fun y hy i => ?_⟩
  change y ∈ AddSubgroup.closure _ at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have e : a ⊗ₜ[F] x i = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]; simp
    change absFin F v (a ⊗ₜ[F] x i) ≤ C
    rw [e]
    exact abs_int_mul_le v (tmul_mem_intLoc ha 1) (hC x hx i)
  | zero => exact abs_zero_le v C
  | add y z _ _ hy hz => exact (absFin_add_le F v _ _).trans (max_le hy hz)
  | neg y _ hy => exact abs_neg_le v hy

end GlobalTheory.LocalLatticeBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletio
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.GraphShear

open Matrix

theorem mem_GLint_of_entries {L : Type} [Field L] {ι : Type} [Fintype ι] [DecidableEq ι] {O : Subring L}
    {x : GL ι L} (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ Formalism.UG.GLint ι O := by
  unfold Formalism.UG.GLint Formalism.UG.bc
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix ι ι O →+* Matrix ι ι L) := fun A B h => by
    ext i j
    exact congrFun (congrFun h i) j
  have hA : O.subtype.mapMatrix (Matrix.of fun i j => (⟨x.1 i j, h1 i j⟩ : O)) = x.1 := by
    ext i j
    rfl
  have hB : O.subtype.mapMatrix (Matrix.of fun i j => (⟨(x⁻¹).1 i j, h2 i j⟩ : O)) = (x⁻¹).1 := by
    ext i j
    rfl
  refine ⟨⟨Matrix.of fun i j => (⟨x.1 i j, h1 i j⟩ : O), Matrix.of fun i j => (⟨(x⁻¹).1 i j, h2 i j⟩ : O), ?_, ?_⟩, ?_⟩
  · apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.mul_inv x
  · apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.inv_mul x
  · exact Units.ext hA

theorem exists_kappa {L : Type} [Field L] {O : Subring L} {n : ℕ} {ϖ : L} (h0 : ϖ ≠ 0) (hϖO : ϖ ∈ O)
    (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) L) (ht : t.1 = Matrix.diagonal (fun i => ϖ ^ d i))
    (hk₁ : k₁ ∈ Formalism.UG.GLint (Fin n) O) (hk₂ : k₂ ∈ Formalism.UG.GLint (Fin n) O) :
    ∃ κ ∈ Formalism.UG.GLint (Fin (n + n)) O,
      KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧
      leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 =
        k₁.1 * Matrix.diagonal (fun i => ϖ ^ max (d i) 0) ∧
      quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 =
        k₁.1 * Matrix.diagonal (fun i => ϖ ^ min (d i) 0) := by
  have hsc : ∀ a : ℤ, (ϖ ^ (-a).toNat - 1) * (ϖ ^ a.toNat - 1) = 0 ∧
      ϖ ^ a.toNat - 1 + 1 = ϖ ^ max a 0 ∧
      ϖ ^ a * (1 + (ϖ ^ (-a).toNat - 1)) = ϖ ^ max a 0 ∧
      ϖ ^ a - (ϖ ^ a.toNat - 1) = ϖ ^ min a 0 := by
    intro a
    rcases le_total 0 a with h | h
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
      have e1 : (-(m : ℤ)).toNat = 0 := by omega
      have e2 : (m : ℤ).toNat = m := by omega
      have e3 : max (m : ℤ) 0 = m := by omega
      have e4 : min (m : ℤ) 0 = 0 := by omega
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1, e2, e3, e4, pow_zero, sub_self, zero_mul, zpow_natCast, zpow_zero,
        sub_add_cancel, add_zero, mul_one] <;> ring
    · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat h
      have e1 : (-(-(m : ℤ))).toNat = m := by omega
      have e2 : (-(m : ℤ)).toNat = 0 := by omega
      have e3 : max (-(m : ℤ)) 0 = 0 := by omega
      have e4 : min (-(m : ℤ)) 0 = -(m : ℤ) := by omega
      have hm : ϖ ^ m ≠ 0 := pow_ne_zero m h0
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [e1, e2, e3, e4, hm, h0]
  have hmem : ∀ (M : Matrix (Fin n) (Fin n) L) (f : Fin n → L), (∀ i, f i ∈ O) → M = Matrix.diagonal f →
      ∀ i j, M i j ∈ O := by
    intro M f hf hM i j
    rw [hM, Matrix.diagonal_apply]
    split_ifs
    · exact hf i
    · exact O.zero_mem
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) L) i j ∈ O :=
    hmem 1 (fun _ => 1) (fun _ => O.one_mem) Matrix.diagonal_one.symm
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) L, B = Matrix.diagonal fun i => ϖ ^ (-d i).toNat - 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin n) (Fin n) L, C = Matrix.diagonal fun i => ϖ ^ (d i).toNat - 1 := ⟨_, rfl⟩
  have hBO : ∀ i j, B i j ∈ O := hmem B _ (fun _ => O.sub_mem (O.pow_mem hϖO _) O.one_mem) hB
  have hCO : ∀ i j, C i j ∈ O := hmem C _ (fun _ => O.sub_mem (O.pow_mem hϖO _) O.one_mem) hC
  have hBC : B * C = 0 := by
    rw [hB, hC, Matrix.diagonal_mul_diagonal]
    simp only [(hsc _).1, Matrix.diagonal_zero]
  have hCB : C * B = 0 := by
    rw [hB, hC, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm (ϖ ^ (d _).toNat - 1), (hsc _).1, Matrix.diagonal_zero]
  have hC1 : C + 1 = Matrix.diagonal (fun i => ϖ ^ max (d i) 0) := by
    rw [hC, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    funext i
    exact (hsc (d i)).2.1
  have hTB : t.1 * (1 + B) = Matrix.diagonal (fun i => ϖ ^ max (d i) 0) := by
    rw [ht, hB, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact (hsc (d i)).2.2.1
  have hTC : t.1 - C = Matrix.diagonal (fun i => ϖ ^ min (d i) 0) := by
    rw [ht, hC, Matrix.diagonal_sub]
    congr 1
    funext i
    exact (hsc (d i)).2.2.2
  generalize (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) = e
  have hfb : ∀ (P Q R S : Matrix (Fin n) (Fin n) L), (∀ i j, P i j ∈ O) → (∀ i j, Q i j ∈ O) →
      (∀ i j, R i j ∈ O) → (∀ i j, S i j ∈ O) → ∀ a b, Matrix.fromBlocks P Q R S a b ∈ O := by
    intro P Q R S hP hQ hR hS a b
    rcases a with a | a <;> rcases b with b | b
    · exact hP a b
    · exact hQ a b
    · exact hR a b
    · exact hS a b
  have hUU : Matrix.fromBlocks 1 B C 1 * Matrix.fromBlocks 1 (-B) (-C) 1 = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [hBC, hCB, Matrix.fromBlocks_one]
  have hUU' : Matrix.fromBlocks 1 (-B) (-C) 1 * Matrix.fromBlocks 1 B C 1 = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [hBC, hCB, Matrix.fromBlocks_one]
  let U : GL (Fin (n + n)) L :=
    ⟨(Matrix.fromBlocks 1 B C 1).submatrix e.symm e.symm, (Matrix.fromBlocks 1 (-B) (-C) 1).submatrix e.symm e.symm,
      by rw [Matrix.submatrix_mul_equiv, hUU, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, hUU', Matrix.submatrix_one_equiv]⟩
  have hU : U ∈ Formalism.UG.GLint (Fin (n + n)) O := by
    apply mem_GLint_of_entries
    · intro i j
      exact hfb 1 B C 1 hone hBO hCO hone (e.symm i) (e.symm j)
    · intro i j
      exact hfb 1 (-B) (-C) 1 hone (fun a b => O.neg_mem (hBO a b)) (fun a b => O.neg_mem (hCO a b)) hone
        (e.symm i) (e.symm j)
  have hblk : ∀ x y : GL (Fin n) L, x ∈ Formalism.UG.GLint (Fin n) O → y ∈ Formalism.UG.GLint (Fin n) O →
      blkGL e (x, y) ∈ Formalism.UG.GLint (Fin (n + n)) O := by
    intro x y hx hy
    unfold Formalism.UG.GLint at hx hy ⊢
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨blkGL e (x', y'), bc_blkGL e O.subtype x' y'⟩
  refine ⟨blkGL e (k₂⁻¹, k₁) * U, Subgroup.mul_mem _ (hblk _ _ (Subgroup.inv_mem _ hk₂) hk₁) hU, ?_⟩
  have hprod : blkGL e (k₁ * t * k₂, 1) * (blkGL e (k₂⁻¹, k₁) * U) = blkGL e (k₁ * t, k₁) * U := by
    rw [← mul_assoc, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel_right, one_mul]
  rw [hprod]
  have hsub : ((blkGL e (k₁ * t, k₁) * U : GL (Fin (n + n)) L) : Matrix (Fin (n + n)) (Fin (n + n)) L).submatrix e e =
      Matrix.fromBlocks (k₁.1 * t.1) (k₁.1 * t.1 * B) (k₁.1 * C) k₁.1 := by
    rw [Units.val_mul, val_blkGL]
    show ((Matrix.fromBlocks _ 0 0 _).submatrix e.symm e.symm *
      (Matrix.fromBlocks 1 B C 1).submatrix e.symm e.symm).submatrix e e = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id,
      Matrix.fromBlocks_multiply]
    simp [Units.val_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold KeepsDiag leviMat
    rw [hsub]
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂]
    have h1 : C + 1 = t.1 * (1 + B) := by rw [hC1, hTB]
    calc k₁.1 * C + k₁.1 = k₁.1 * (C + 1) := by rw [mul_add, mul_one]
      _ = k₁.1 * (t.1 * (1 + B)) := by rw [h1]
      _ = k₁.1 * t.1 + k₁.1 * t.1 * B := by rw [mul_add, mul_one, mul_add, mul_assoc]
  · unfold leviMat
    rw [hsub]
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂]
    rw [← hTB, mul_add, mul_one, mul_add, mul_assoc]
  · unfold quotMat
    rw [hsub]
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁]
    rw [← hTC, mul_sub]

theorem ordL_det_mul_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {O : Subring L}
    (hO : ∀ x ∈ O, Valued.v x ≤ (1 : WithZero (Multiplicative ℤ))) {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {k : GL (Fin n) L} (hk : k ∈ Formalism.UG.GLint (Fin n) O) (f : Fin n → ℤ) :
    ordL (k.1 * Matrix.diagonal fun i => ϖ ^ f i).det = ∑ i, f i := by
  have hdet : Valued.v k.1.det = 1 := by
    have hk' := hk
    unfold Formalism.UG.GLint at hk'
    obtain ⟨y, hy⟩ := hk'
    have hkmat : k.1 = O.subtype.mapMatrix y.1 := by
      rw [← hy]
      rfl
    have hinv : (k⁻¹).1 = O.subtype.mapMatrix (y⁻¹).1 := by
      rw [← hy, ← map_inv]
      rfl
    have hm1 : k.1.det ∈ O := by
      rw [hkmat, ← RingHom.map_det]
      exact (y.1.det).2
    have hm2 : (k⁻¹).1.det ∈ O := by
      rw [hinv, ← RingHom.map_det]
      exact ((y⁻¹).1.det).2
    have hmul : k.1.det * (k⁻¹).1.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have hv : Valued.v k.1.det * Valued.v (k⁻¹).1.det = 1 := by
      rw [← map_mul, hmul, map_one]
    refine le_antisymm (hO _ hm1) ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v k.1.det * Valued.v (k⁻¹).1.det := hv.symm
      _ ≤ Valued.v k.1.det * 1 := mul_le_mul' le_rfl (hO _ hm2)
      _ = Valued.v k.1.det := mul_one _
  have hpow : ∀ i, Valued.v (ϖ ^ f i) =
      ((Multiplicative.ofAdd (-(f i)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro i
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul]
    congr 1
    simp
  have hD : Valued.v (Matrix.diagonal fun i => ϖ ^ f i).det =
      ((Multiplicative.ofAdd (-(∑ i, f i)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [Matrix.det_diagonal, map_prod, Finset.prod_congr rfl (fun i _ => hpow i), ← Finset.sum_neg_distrib, ofAdd_sum]
    exact (map_prod (WithZero.coeMonoidHom : Multiplicative ℤ →* WithZero (Multiplicative ℤ)) _ _).symm
  have hord : ∀ (z : L) (s : ℤ),
      Valued.v z = ((Multiplicative.ofAdd (-s) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → ordL z = s := by
    intro z s hz
    unfold Formalism.UG.ordL
    split_ifs with h
    · rw [hz] at h
      exact absurd h WithZero.coe_ne_zero
    · have h2 : WithZero.unzero h = Multiplicative.ofAdd (-s) :=
        WithZero.coe_injective (by rw [WithZero.coe_unzero, hz])
      rw [h2, toAdd_ofAdd, neg_neg]
  rw [Matrix.det_mul]
  exact hord _ _ (by rw [map_mul, hdet, one_mul, hD])

theorem graph_shear : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → k₁ ∈ KGL w n → k₂ ∈ KGL w n → ∃ κ ∈ KGL w (n + n), KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧ ordL (leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, max (d i) 0 ∧ ordL (quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, min (d i) 0 := by
  intro E _ _ w n ϖ hϖ d t k₁ k₂ ht hk₁ hk₂
  have hK : ∀ m, GlobalTheory.LFun.KGL w m = Formalism.UG.GLint (Fin m) (w.adicCompletionIntegers E).toSubring := fun m => rfl
  have hϖ' : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hϖ
  have hO : ∀ x ∈ (w.adicCompletionIntegers E).toSubring, Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) :=
    fun x hx => hx
  have hϖO : ϖ ∈ (w.adicCompletionIntegers E).toSubring := by
    show Valued.v ϖ ≤ 1
    rw [hϖ']
    exact le_of_lt (by decide)
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ'
    exact WithZero.zero_ne_coe hϖ'
  rw [hK] at hk₁ hk₂
  obtain ⟨κ, hκ, h1, h2, h3⟩ := exists_kappa h0 hϖO d t k₁ k₂ ht hk₁ hk₂
  refine ⟨κ, (hK _).symm ▸ hκ, h1, ?_, ?_⟩
  · rw [h2]
    exact ordL_det_mul_diagonal hO hϖ' hk₁ _
  · rw [h3]
    exact ordL_det_mul_diagonal hO hϖ' hk₁ _

end GlobalTheory.GraphShear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingleMemLatLoc
section
open scoped TensorProduct

namespace GlobalTheory.LocalLatticeIntegral

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ r : 𝓞 E, (r : E) = (M : E) * e := by
  have h : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨M, hM, hi⟩ := h.exists_integral_multiple
  exact ⟨M, hM, ⟨M • e, hi⟩, by simp [zsmul_eq_mul]⟩

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    [hL : Submodule.IsLattice E L] (x : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, h1⟩ := hx
    obtain ⟨M, hM, h2⟩ := hy
    refine ⟨N * M, mul_ne_zero hN hM, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.toAddSubgroup.zsmul_mem h1 M
    · rw [mul_smul]; exact L.toAddSubgroup.zsmul_mem h2 N
  | smul e x _ hx =>
    obtain ⟨N, hN, h1⟩ := hx
    obtain ⟨M, hM, r, hr⟩ := exists_int_mul_integral e
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h2 := L.smul_mem r h1
    convert h2 using 1
    funext j
    have : (r • N • x) j = (r : E) * ((N : E) * x j) := by
      simp [Algebra.smul_def, zsmul_eq_mul]
    rw [this, hr]
    simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_mul]
    ring

theorem exists_single_mem_latLoc : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) [Submodule.IsLattice E L] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∃ (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), c ≠ (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧ ∀ (i : Fin n), Pi.single i (c ⊗ₜ[F] (1 : E)) ∈ GlobalTheory.AdelicU.latLoc F L v := by
  intro F E _ _ _ _ _ n L _ v
  choose N hN hmem using fun i : Fin n => exists_int_smul_mem L (Pi.single i (1 : E))
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hN i
  haveI : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :=
    charZero_of_injective_algebraMap (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).injective
  refine ⟨((∏ i, N i : ℤ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), Int.cast_ne_zero.2 hP, fun i => ?_⟩
  obtain ⟨k, hk⟩ : N i ∣ ∏ j, N j := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  have h1 : (∏ j, N j) • (Pi.single i (1 : E) : Fin n → E) ∈ L := by
    rw [hk, mul_comm, mul_smul]; exact L.toAddSubgroup.zsmul_mem (hmem i) k
  generalize (∏ j, N j) = P at h1
  refine AddSubgroup.subset_closure ⟨1, one_mem _, _, h1, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_same, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      zsmul_eq_mul, mul_one]
  · rw [Pi.single_eq_of_ne hj, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, TensorProduct.tmul_zero]

end GlobalTheory.LocalLatticeIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimUnitaryKTypeEqDualWeylModuleStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms
open scoped InnerProductSpace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_unitary_K_type_eq_dual_weyl_module : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (lamH : Fin k → ℝ), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ (Formalism.QuantumDeterminants.lowK (allPos k) lamH) ⊤ → (∀ i : Fin k, -lamH (Fin.rev i) = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∃ (j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ℕ) (b : Module.Basis (Fin d) ℂ H), (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ a a', normFock lam (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (σ (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  first | exact @GlobalTheory.DualWeylType.dual_weyl_type | exact GlobalTheory.DualWeylType.dual_weyl_type | (intros; apply GlobalTheory.DualWeylType.dual_weyl_type <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqMulOfSplit
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem charAt_eq_locChar_mul_locChar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) * (locChar χ w' (Units.map (toCompl h').toMonoidHom x) : ℂˣ) := by
  intro F E _ _ _ _ _ χ v w h w' h' hne hall x
  have key : ideleAt F E v x = locIdele F w (Units.map (toCompl h).toMonoidHom x) *
      locIdele F w' (Units.map (toCompl h').toMonoidHom x) := by
    refine Units.ext (tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun u => ?_)))
    · rw [Units.val_mul, map_mul, infTens_locIdele, infTens_locIdele, mul_one]
      exact map_extUnit_zero (fstA F) _ _ (fun a => rfl) x
    · rw [Units.val_mul, map_mul (finTens F E), map_mul, finTens_locIdele, finTens_locIdele]
      have hc : ∀ u' : HeightOneSpectrum (𝓞 F), Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u') (AlgHom.id F E)
          (finTens F E (ideleAt F E v x)) = (unitFin F E u' (ideleAt F E v x) : Fv F u' ⊗[F] E) := fun u' => by
        change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
        rw [← Algebra.TensorProduct.map_comp]
        rfl
      change _ = Neutral.B1.finiteSingle E w (Units.map (toCompl h).toMonoidHom x) u *
        Neutral.B1.finiteSingle E w' (Units.map (toCompl h').toMonoidHom x) u
      by_cases hu : u.under (𝓞 F) = v
      · rw [finAdEquiv_apply hu, hc, unitFin_ideleAt_self]
        rcases (hall u).1 hu with rfl | rfl
        · rw [finSingle_self, finSingle_ne hne, mul_one]
          rfl
        · rw [finSingle_self, finSingle_ne (Ne.symm hne), one_mul]
          rfl
      · rw [finAdEquiv_apply rfl, hc, unitFin_ideleAt_ne hu, Units.val_one, map_one,
          finSingle_ne (fun e => hu (by rw [e]; exact h)), finSingle_ne (fun e => hu (by rw [e]; exact h')), mul_one]
  show ((χ (ideleAt F E v x) : Circle) : ℂ) = _
  rw [key, map_mul]
  rfl

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.LFun

theorem ideleAt_eq_locIdele_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w)
    (x : (Fv F v ⊗[F] E)ˣ) :
    ideleAt F E v x = locIdele F w (Units.map (toCompl h).toMonoidHom x) := by
  refine eq_locIdele ?_ ?_
  · exact map_extUnit_zero (fstA F) (inFin v) (inFin_mul v) (fun _ => rfl) x
  · refine FiniteAdeleRing.ext _ fun u => ?_
    rw [finAdEquiv_apply rfl]
    have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F (u.under (𝓞 F))) (AlgHom.id F E)
        (finTens F E (ideleAt F E v x : AF F ⊗[F] E)) = (unitFin F E (u.under (𝓞 F)) (ideleAt F E v x) : Fv _ _ ⊗[F] E) := by
      change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) _) = _
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
      rfl
    rw [e]
    by_cases hu : u.under (𝓞 F) = v
    · obtain rfl : u = w := (InertChart.under_eq_iff hw u).1 hu
      subst h
      rw [unitFin_ideleAt_self]
      exact (finSingle_self u _).symm
    · rw [unitFin_ideleAt_ne hu, Units.val_one, map_one]
      exact (finSingle_ne (fun e : u = w => hu (e ▸ h)) _).symm

theorem charAt_eq_locChar_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) := by
  intro F E _ _ _ _ _ χ v w h hw x
  show ((χ (ideleAt F E v x) : Circle) : ℂ) = ((Circle.toUnits (χ (locIdele F w _)) : ℂˣ) : ℂ)
  rw [GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw x]
  rfl

end GlobalTheory.LFun
end
end


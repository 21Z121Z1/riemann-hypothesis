import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0505
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0066
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0064
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0731
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecomposition
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0092

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMultiplePathTrivialCharacter
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum.Level

variable {D : D7} {r : ℕ}

def eFin (D : D7) : AF D.host.F := 1 - GlobalTheory.FinTranslate.eInf D

theorem eFin_mul (D : D7) (x : AF D.host.F) : eFin D * x = pairA D.host.F 0 (sndA D.host.F x) := by
  show ((1 : Ainf D.host.F × Af D.host.F) - (1, 0)) * (x : Ainf D.host.F × Af D.host.F) =
    ((0 : Ainf D.host.F), (x : Ainf D.host.F × Af D.host.F).2)
  refine Prod.ext ?_ ?_
  · show ((1 : Ainf D.host.F) - 1) * x.1 = 0
    rw [sub_self, zero_mul]
  · show ((1 : Af D.host.F) - 0) * x.2 = x.2
    rw [sub_zero, one_mul]

theorem finPart_eInf (D : D7) : finPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 0 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  exact TensorProduct.zero_tmul _ _

theorem infPart_eInf (D : D7) : infPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 1 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem rs_one {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    rs σ 1 = GlobalTheory.FinTranslate.eInf D • (1 : AE D) := by
  refine sub_eq_zero.mp (hσ.ext _ ?_ ?_)
  · rw [map_sub, finPart_eInf, sub_zero]
    exact hσ.fin _
  · intro τ
    rw [map_sub, map_sub, infPart_eInf, map_one]
    simp only [rs, hσ.comp]
    simp

theorem diff_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1).1 = eFin D • a.1.map (incA D) := by
  show GlobalTheory.MixModel.rat a.1 - rs σ 1 • a.1.map (incA D) = eFin D • a.1.map (incA D)
  rw [rs_one hσ, smul_one_smul, eFin, sub_smul, one_smul]
  rfl

def S (V : HSp D) (A : Mx D r r) (y : Mx D V.rank r) : AF D.host.F :=
  halfTr (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))

theorem halfTr_smul (c : AF D.host.F) (x : AE D) : halfTr (c • x) = c * halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_smul, smul_eq_mul]
  ring

theorem halfTr_nsmul (n : ℕ) (x : AE D) : halfTr (n • x) = n • halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA]
  rw [map_nsmul]
  simp only [nsmul_eq_mul]
  ring

theorem halfTr_add (x x' : AE D) : halfTr (x + x') = halfTr x + halfTr x' := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_add]
  ring

theorem halfTr_zero : halfTr (0 : AE D) = 0 := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_zero, mul_zero]

theorem halfTr_trace_nsmul (n : ℕ) (M B : Mx D r r) :
    halfTr (Matrix.trace (HMul.hMul (n • M) B : Mx D r r)) = n • halfTr (Matrix.trace (HMul.hMul M B : Mx D r r)) := by
  rw [Matrix.smul_mul, Matrix.trace_smul, halfTr_nsmul]

theorem pow_eq_one_of_compact {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    {C : Set (Af F)} (hC : IsCompact C) : ∃ N : ℕ, 0 < N ∧ ∀ c ∈ C, ψ (pairA F 0 c) ^ N = 1 := by
  obtain ⟨N1, hN1, hK⟩ := GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_mem_Oh_of_isCompact F C hC
  obtain ⟨N2, hN2, hU⟩ :=
    GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_Oh_subset F _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  refine ⟨N2 * N1, Nat.mul_pos hN2 hN1, fun c hc => ?_⟩
  have h1 : ψ (pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c))) = 1 := hU _ (hK c hc)
  have h2 : (N2 * N1) • pairA F 0 c = pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c)) := by
    show (N2 * N1) • ((0 : Ainf F), c) = ((0 : Ainf F), (N2 : Af F) * ((N1 : Af F) * c))
    rw [Prod.smul_mk, smul_zero, ← mul_assoc, ← Nat.cast_mul, ← nsmul_eq_mul]
  rw [← AddChar.map_nsmul_eq_pow, h2, h1]

private theorem supp_lemma_5 {θ : InfFam D} {m n : ℕ} {φ : Mx D m n → ℂ} (hφ : φ ∈ schwartzA θ m n) :
    ∃ K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsCompact K ∧
      ∀ y, φ y ≠ 0 → (fun i j => finPart D (y i j)) ∈ K := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine ⟨tsupport g, (show IsLocallyConstant g ∧ HasCompactSupport g from hg).2, fun y hy => subset_tsupport g ?_⟩
    exact right_ne_zero_of_mul hy
  | zero => exact ⟨∅, isCompact_empty, fun y hy => (hy rfl).elim⟩
  | add x y _ _ hx hy =>
    obtain ⟨K1, hK1, h1⟩ := hx
    obtain ⟨K2, hK2, h2⟩ := hy
    refine ⟨K1 ∪ K2, hK1.union hK2, fun z hz => ?_⟩
    by_cases hxz : x z = 0
    · right
      apply h2
      simpa [hxz] using hz
    · left
      exact h1 z hxz
  | smul a x _ hx =>
    obtain ⟨K, hK, h⟩ := hx
    refine ⟨K, hK, fun y hy => h y ?_⟩
    intro h0
    apply hy
    simp [h0]

private theorem continuous_sigRf_lemma_7 : Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig) := by
  let f : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[Af D.host.F] (Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig
      map_add' := map_add _
      map_smul' := fun c z => by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  exact IsModuleTopology.continuous_of_linearMap f

private theorem trace_bc_lemma_8 (z : AE D) :
    sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) =
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero] <;> rfl
  | tmul a e =>
    have h1 : (a ⊗ₜ[D.host.F] e : AE D) = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : finPart D (a ⊗ₜ[D.host.F] e) = sndA D.host.F a • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [Formalism.L2.Theta.finPart]
    rw [h2, h1]
    simp only [map_smul, GlobalTheory.CompanionTheory.HermPoisson.trace_one_tmul', smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem level_pow {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (A : Mx D r r)
    {θ : InfFam D} {φ : Mx D V.rank r → ℂ} (hφ : φ ∈ schwartzA θ V.rank r) :
    ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (eFin D * S V A y) ^ N = 1 := by
  obtain ⟨K, hK, hKy⟩ := supp_lemma_5 hφ
  let Φ : (Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → Af D.host.F := fun w =>
    algebraMap D.host.F (Af D.host.F) (1 / 2) *
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
        (Matrix.trace (A.map (finPart D) *
          (((Matrix.of w).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
            ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of w))))
  have hΦ : Continuous Φ := by
    have hσc := continuous_sigRf_lemma_7 (D := D)
    have htr : Continuous (Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)) := by fun_prop
    have hof : Continuous (fun w : Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => Matrix.of w) :=
      continuous_id
    exact continuous_const.mul (htr.comp (Continuous.matrix_trace (continuous_const.matrix_mul
      ((hof.matrix_map hσc).matrix_transpose.matrix_mul (continuous_const.matrix_mul hof)))))
  have hS : ∀ y : Mx D V.rank r, sndA D.host.F (S V A y) = Φ (fun i j => finPart D (y i j)) := by
    intro y
    have hM : (HMul.hMul A (inner V y y) : Mx D r r).map (finPart D) =
        A.map (finPart D) * (((Matrix.of fun i j => finPart D (y i j)).map
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
          ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of fun i j => finPart D (y i j))) := by
      ext i j
      simp [Matrix.mul_apply, GlobalTheory.MixModel.adj, GlobalTheory.StdUnn.inner, map_sum, GlobalTheory.CompanionTheory.WSum.finPart_cA]
    have ht : ∀ M : Mx D r r, finPart D (Matrix.trace M) = Matrix.trace (M.map (finPart D)) := by
      intro M
      simp [Matrix.trace, map_sum]
    show sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))) = _
    rw [map_mul, AlgHom.commutes, trace_bc_lemma_8, ht, hM]
  obtain ⟨N, hN, hC⟩ := pow_eq_one_of_compact hψ (hK.image hΦ)
  refine ⟨N, hN, fun y hy => ?_⟩
  rw [eFin_mul, hS y]
  exact hC _ ⟨_, hKy y hy, rfl⟩

theorem level : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) (φ : Mx D V.rank r → ℂ), φ ∈ schwartzA θ V.rank r → ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1 := by
  intro D r V ψ hψ θ σ hσ a φ hφ
  obtain ⟨N, hN, hy⟩ := level_pow hψ V (a.1.map (incA D)) hφ
  refine ⟨N, hN, fun y hy0 => ?_⟩
  rw [AddSubgroup.coe_nsmul, diff_eq hσ a, halfTr_trace_nsmul, Matrix.smul_mul, Matrix.trace_smul, halfTr_smul,
    AddChar.map_nsmul_eq_pow]
  exact hy y hy0

end GlobalTheory.CompanionTheory.WSum.Level
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegral
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthConv

open GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def rmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := rmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    mul_add (Matrix.of z) (Matrix.of x) (Matrix.of y)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.mul_smul (Matrix.of z) c (Matrix.of x)

def lmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := lmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.smul_mul c (Matrix.of x) (Matrix.of z)

theorem continuous_rmul : Continuous (rmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (rmulLin (E := E) (a := a)).continuous_of_finiteDimensional

theorem continuous_lmul : Continuous (lmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (lmulLin (E := E) (a := a)).continuous_of_finiteDimensional

def bnd (c : GL (Fin a) (Cinf E)) : ℝ := 1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖

theorem height_mul_le_bnd (c y : GL (Fin a) (Cinf E)) : height (y * c) ≤ bnd c * height y := by
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height bnd
  rw [h1, h2]
  nlinarith

theorem toGL_inv (u : AutomorphicForm.archGroup E a) : toGL E a u⁻¹ = (toGL E a u)⁻¹ := by
  simp only [toGL, map_inv]

theorem continuous_bnd : Continuous fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u) := by
  have hm : Continuous (mMap E a) := (mMap E a).continuous_of_finiteDimensional
  have hv : Continuous fun u : AutomorphicForm.archGroup E a =>
      ((u : (AutomorphicForm.ArchMatrix E a)ˣ) : AutomorphicForm.ArchMatrix E a) :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun u : AutomorphicForm.archGroup E a => toL (toGL E a u).val := by
    simp_rw [toL_toGL]
    exact hm.comp hv
  have h2 : Continuous fun u : AutomorphicForm.archGroup E a => toL ((toGL E a u)⁻¹).val := by
    simp_rw [← toGL_inv, toL_toGL]
    exact hm.comp (hv.comp continuous_inv)
  unfold bnd
  exact (continuous_const.add (continuous_rmul.comp h1).norm).add (continuous_lmul.comp h2).norm

theorem growth_conv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ ψ : GA E a → ℂ), Continuous φ → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ D : AutomorphicForm.archGroup E a → ℂ, Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * AutomorphicForm.infEmb E a y) * D y ∂ν) → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a _ _ ν _ φ ψ _ hgrow D hD hDc hψ g
  obtain ⟨C, N, hC⟩ := hgrow g
  have hpos : ∀ y : GL (Fin a) (Cinf E), 0 ≤ height y := fun y => by
    linarith [one_le_height y]
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (f := fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u))
    hDc continuous_bnd.continuousOn
  have hint : Integrable (fun u => ‖D u‖) ν := (hD.integrable_of_hasCompactSupport hDc).norm
  refine ⟨C * B ^ N * ∫ u, ‖D u‖ ∂ν, N, fun y => ?_⟩
  have pt : ∀ u, ‖φ (g * infGL E a y * AutomorphicForm.infEmb E a u) * D u‖ ≤
      (C * (B * height y) ^ N) * ‖D u‖ := fun u => by
    by_cases hu : u ∈ tsupport D
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have e : g * infGL E a y * AutomorphicForm.infEmb E a u = g * infGL E a (y * toGL E a u) := by
        rw [infEmb_eq, mul_assoc, map_mul]
      rw [e]
      refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _) ?_ N) C0)
      exact (height_mul_le_bnd _ y).trans
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hB u hu)) (hpos y))
    · rw [image_eq_zero_of_notMem_tsupport hu]
      simp
  have key := norm_integral_le_of_norm_le (hint.const_mul (C * (B * height y) ^ N)) (Filter.Eventually.of_forall pt)
  rw [hψ]
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul, mul_pow]
  ring

end GlobalTheory.CompanionTheory.GrowthConv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLattice
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem poisson_herm : ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∀ f : hermA D r → ℂ, Continuous f → (∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖f (b + c.1)‖ ≤ u c) → Integrable f lam ∧ (Summable (fun t : ratHerm D r => ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) → ∑' c : ratHerm D r, f c.1 = ∑' t : ratHerm D r, ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
  intro D r ψ hψ lam 𝓖 h𝓖 f hf hu
  obtain ⟨hH, hD, hD1⟩ := h𝓖
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) :=
    (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  have hmem : ∀ q : ratHerm D r, q.1.1 ∈ ratMx D r r := fun q => AddSubgroup.mem_comap.1 q.2
  haveI : Countable (ratHerm D r) := by
    choose g hg using fun q : ratHerm D r => mem_ratMx.1 (hmem q)
    exact Function.Injective.countable (f := g) fun a b h =>
      Subtype.ext (Subtype.ext (by rw [← hg a, ← hg b, h]))
  haveI := hH
  obtain ⟨-, K, hK, hKx⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)
  let ι : ratHerm D r →+ hermA D r := (ratHerm D r).subtype
  have hι : Function.Injective ι := Subtype.val_injective
  have hr : ι.range = ratHerm D r := AddSubgroup.range_subtype _
  have hD' : IsAddFundamentalDomain ι.range 𝓖 lam := by
    rw [hr]
    exact hD
  have hc : ∀ x : hermA D r, ∃ l ∈ ratHerm D r, x - l ∈ K := fun x => by
    obtain ⟨γ, hγ, h⟩ := hKx x
    refine ⟨-γ, neg_mem hγ, ?_⟩
    rwa [sub_neg_eq_add, add_comm]
  have hx : ∀ x : hermA D r, ∃ a, x - ι a ∈ K := fun x => by
    obtain ⟨l, hl, h⟩ := hc x
    exact ⟨⟨l, hl⟩, h⟩
  let Eh : ratHerm D r → hermA D r → ℂ := fun t b => chi ψ t.1.1 b
  have hEc : ∀ t, Continuous (Eh t) := fun t => continuous_chi hψ t.1.1
  have hEn : ∀ t b, ‖Eh t b‖ = 1 := fun t b => hψ.2.1 _
  have hEp : ∀ t x c, Eh t (x + ι c) = Eh t x := fun t x c => by
    show chi ψ t.1.1 (x + c.1) = chi ψ t.1.1 x
    rw [chi_add_right, chi_rat hψ (hmem t) c, mul_one]
  have hE0 : ∀ t, Eh t 0 = 1 := fun t => chi_zero_right ψ t.1.1
  have hself : ∀ t x, Eh t x * Eh (-t) x = 1 := fun t x => by
    show chi ψ t.1.1 x * chi ψ (-t.1.1) x = 1
    rw [← chi_add_left, add_neg_cancel, chi_zero_left]
  have horth : ∀ s t, t ≠ s → ∫ x in 𝓖, Eh t x * Eh (-s) x ∂lam = 0 := fun s t hts => by
    obtain ⟨a, ha⟩ := exists_chi_ne hψ (t - s) (sub_ne_zero.2 hts)
    have hm : t.1.1 + -s.1.1 = (t - s).1.1 := by
      rw [← sub_eq_add_neg]
      rfl
    have he : ∀ x, Eh t x * Eh (-s) x = chi ψ (t - s).1.1 x := fun x => by
      rw [← hm, chi_add_left]
      rfl
    simp only [he]
    exact Formalism.IndefR.Tow.fd_setIntegral_char_eq_zero hD (a := a)
      (fun x y => chi_add_right ψ _ x y) (fun g hg => chi_rat hψ (hmem (t - s)) ⟨g, hg⟩) ha
  have hcomp : ∀ g : hermA D r → ℂ, Continuous g → (∀ x c, g (x + ι c) = g x) →
      (∀ t, ∫ b in 𝓖, g b * Eh (-t) b ∂lam = 0) → ∀ x, g x = 0 := fun g hg hp hz x => by
    refine GlobalTheory.CompanionTheory.FourierComplete.eq_zero_of_coeffs_vanish (ratHerm D r) lam hD hK hc (T := ratHerm D r)
      Eh hEc (fun t x l hl => hEp t x ⟨l, hl⟩) (fun y => chi_zero_left ψ y) (fun s t y => chi_add_left ψ _ _ y)
      (fun t y => ?_) (fun a b hab => ?_) g hg (fun y l hl => hp y ⟨l, hl⟩) hz x
    · show star (ψ _) = chi ψ (-t.1.1) y
      rw [star_psi' hψ, chi_neg_left]
    · refine rat_of_chi hψ _ fun t => ?_
      have h1 := chi_add_right ψ t.1.1 (-a) b
      have h2 := chi_add_right ψ t.1.1 (-a) a
      rw [neg_add_cancel, chi_zero_right] at h2
      have h3 : chi ψ t.1.1 a = chi ψ t.1.1 b := hab t
      rw [h1, ← h3, ← h2]
  have hu' : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable ι f := hu
  have main := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.poisson_gen (V := hermA D r) (C := ratHerm D r) (ι := ι) hι
    (μ := lam) hD' hD1 hK hx (E := Eh) hEc hEn hEp hE0 hself horth hcomp hf hu'
  have hneg : ∀ (t : ratHerm D r) b, Eh (-t) b =
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) := fun t b => chi_neg_left ψ t.1.1 b
  simp only [hneg] at main
  exact main

end GlobalTheory.CompanionTheory.HermPoisson
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHoldsStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_sequence_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.resSeq | exact GlobalTheory.CompanionTheory.BZRes.resSeq | (intros; apply GlobalTheory.CompanionTheory.BZRes.resSeq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductEmbeddingsStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_embeddings : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [∀ i, TopologicalSpace (Hl i)] [∀ i, T2Space (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH : ∀ i, Subgroup (Hl i))
    (hpc : ∀ i, Continuous (p i)) (hec : ∀ i, Continuous (e i))
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hKc : IsCompact (K : Set Γ))
    (hKo : ∀ i, IsOpen (KH i : Set (Hl i))) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)),
    ∃ V : ∀ i, Subgroup (Hl i), (∀ i, IsOpen (V i : Set (Hl i))) ∧ (∀ i, V i ≤ KH i) ∧
      (∀ᶠ i in cofinite, V i = KH i) ∧ ∀ u, (∀ i, p i u ∈ V i) → u ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open | exact GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open | (intros; apply GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductJacquetShuffleCountStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_product_jacquet_shuffle_count : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Γ i) (x i).rep) → ∀ W : List (IrrGL k), (∀ w ∈ W, w.IsCusp) → jmL W (prodIrr x hd) = (shuffleCount W (fun i => decWord (Γ i)) : ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr | exact GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr | (intros; apply GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_multiplicativity : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.DictInf → PositivityTheory.RgEis.CMGood → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.SgAll → SiegelEisensteinSeries.BRoad.SiegelMult := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of | exact GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of | (intros; apply GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOverPlaces
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.DxN

theorem selfDual_isEulerProd_n : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → GlobalTheory.CompanionTheory.SW.IsEulerProd b dx 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (fun v => GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M) ∧ ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (latV b v) = 1 := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ hM ψ hψ dx hdx d b laminf lam hinf hlam
  exact selfDual_isEulerProd_tuple F E σ hCM M J hJ n hM ψ hψ dx hdx d b laminf lam hinf hlam

end GlobalTheory.CompanionTheory.SiegelND.DxN

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHolds
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem sliceBranches : GroundTheory.Heights₂.Heights.SliceBranches.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranches.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.full
    GlobalTheory.T.branch_proper_at_point_holds
    GroundTheory.Heights₂.Heights.SliceMatricesOpen.full
    GroundTheory.Heights₂.Heights.ImplicitCurve.full

end GlobalTheory.CompanionTheory.Ar.SliceBranch
end


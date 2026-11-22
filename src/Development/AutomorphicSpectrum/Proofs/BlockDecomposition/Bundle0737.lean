import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0732
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0735
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0089
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0124
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0734
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonrepresentedSignatureObstruction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0085
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteIrreducibleFixedVectors
section
noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.TypeSpace

section Abstract

variable {K X : Type*} [Group K] [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def restrictRep (π : K →* (X →L[ℂ] X)) (Y : Submodule ℂ X) (hY : ∀ g, ∀ v ∈ Y, π g v ∈ Y) :
    Representation ℂ K Y where
  toFun g := ((π g : X →L[ℂ] X) : X →ₗ[ℂ] X).restrict (hY g)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

theorem span_orbit_stable' (π : K →* (X →L[ℂ] X)) (F : X) (g : K) :
    ∀ v ∈ Submodule.span ℂ (Set.range fun k : K => π k F),
      π g v ∈ Submodule.span ℂ (Set.range fun k : K => π k F) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul]
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

end Abstract

theorem exists_typeSpace : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧ (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧ (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧ ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ, (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) → (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) → B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) → ∀ v ∈ X, B v ∈ X := by
  intro E _ _ _ a μ _ _ H hH hI F hFH hK
  obtain ⟨hSo, hfd⟩ := hK
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a

  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | R (latticeGL E a) μ (finGL E a k) F = F}
      mul_mem' := fun {x y} hx hy => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        have hy' : R (latticeGL E a) μ (finGL E a y) F = F := hy
        change R (latticeGL E a) μ (finGL E a (x * y)) F = F
        rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hy', hx']
      one_mem' := by
        change R (latticeGL E a) μ (finGL E a 1) F = F
        simp
      inv_mem' := fun {x} hx => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        change R (latticeGL E a) μ (finGL E a x⁻¹) F = F
        conv_lhs => rw [← hx']
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel]
        simp }
  have hSo' : IsOpen (S : Set (GL (Fin a) (Af E))) := hSo
  let U : Subgroup (GL (Fin a) (Af E)) := K0 ⊓ S
  have hUo : IsOpen (U : Set (GL (Fin a) (Af E))) := hK0o.inter hSo'
  have hUc : IsCompact (U : Set (GL (Fin a) (Af E))) := hK0c.inter_right (S.isClosed_of_isOpen hSo')

  let π : Kinf E a →* (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) :=
    (R (latticeGL E a) μ).comp ((infGL E a).comp Unitary.toUnits)
  have hcomm : ∀ (u : GL (Fin a) (Af E)) (k : Kinf E a) (v : L2 (latticeGL E a) μ),
      R (latticeGL E a) μ (finGL E a u) (π k v) = π k (R (latticeGL E a) μ (finGL E a u) v) := by
    intro u k v
    have e := congrArg (fun g => R (latticeGL E a) μ g v) (infGL_comm (E := E) (a := a) (Unitary.toUnits k) u)
    simp only [map_mul, ContinuousLinearMap.mul_apply] at e
    exact e.symm
  let Y : Submodule ℂ (L2 (latticeGL E a) μ) := Submodule.span ℂ (Set.range fun k : Kinf E a => π k F)
  haveI : FiniteDimensional ℂ Y := hfd
  have hYs : ∀ g, ∀ v ∈ Y, π g v ∈ Y := span_orbit_stable' π F
  have hFY : F ∈ Y := Submodule.subset_span ⟨1, by simp⟩
  have hYP : ∀ v ∈ Y, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨hI.1.2 _ _ hFH, fun u hu => ?_⟩
      exact (hcomm u k F).trans (congrArg (π k) hu.2)
    | zero => exact ⟨H.zero_mem, fun _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      exact ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add, hx.2 u hu, hy.2 u hu]⟩
    | smul c x _ hx =>
      exact ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩
  let ρ : Representation ℂ (Kinf E a) Y := restrictRep π Y hYs
  let C : (Y →ₗ[ℂ] L2 (latticeGL E a) μ) → Prop := fun T =>
    (∀ k w, T (ρ k w) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w)) ∧
      ∀ w, T w ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (T w) = T w
  let X : Submodule ℂ (L2 (latticeGL E a) μ) := ⨆ (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T), LinearMap.range T
  have hXf : FiniteDimensional ℂ X := GlobalTheory.T.cuspidal_K_type_finite E a μ H hH hI U hUo Y ρ
  have hmem : ∀ T, C T → ∀ w, T w ∈ X := fun T hT w =>
    (le_iSup₂_of_le (f := fun (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T) => LinearMap.range T) T hT le_rfl)
      ⟨w, rfl⟩
  have hXP : ∀ v ∈ X, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    let P : Submodule ℂ (L2 (latticeGL E a) μ) :=
      { carrier := {v | v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v}
        zero_mem' := ⟨H.zero_mem, fun _ _ => map_zero _⟩
        add_mem' := fun {x y} hx hy =>
          ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add, hx.2 u hu, hy.2 u hu]⟩
        smul_mem' := fun c x hx => ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩ }
    have hle : X ≤ P := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      exact hT.2 w
    exact hle hv
  refine ⟨U, hUo, hUc, X, hXf, ?_, fun v hv => (hXP v hv).1, ?_, fun u hu v hv => (hXP v hv).2 u hu, ?_⟩
  · exact hmem Y.subtype ⟨fun k w => rfl, fun w => hYP _ w.2⟩ ⟨F, hFY⟩
  · intro k v hv
    have hle : X ≤ X.comap ((R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) :
        L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
      iSup₂_le fun T hT => by
        rintro _ ⟨w, rfl⟩
        change R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w) ∈ X
        rw [← hT.1 k w]
        exact hmem T hT _
    exact hle hv
  · intro B hB1 hB2 v hv
    have hle : X ≤ X.comap B := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      refine hmem (B ∘ₗ T) ⟨fun k w => ?_, fun w => hB2 _ (hT.2 w).1 (hT.2 w).2⟩ w
      change B (T (ρ k w)) = _
      rw [hT.1 k w, hB1]
      rfl
    exact hle hv

end GlobalTheory.CompanionTheory.TypeSpace

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequencesStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leibniz_order_of_exact_sequences : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k → PsiGP k → PhiGP k → PsiPG k → PhiPG k → PhiPG0 k → LeibnizOrd k := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | exact GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LelongLimitAtBranches
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Lelong

open GroundTheory.Heights₂.Heights

theorem lelongLimitAtBranches : LelongLimitAtBranches.Statement :=
  LelongLimitAtBranches.proof GlobalTheory.CompanionTheory.Ar.branchIntDecompose GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranchInt
    PolydiscLelongLimit.proof GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint

end GlobalTheory.CompanionTheory.Ar.Lelong
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingHeightBound
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1.Height
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem norm_one_le : ‖(1 : Cinf E)‖ ≤ 1 := by
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

theorem norm_lev_le (y : GL (Fin r) (Cinf E)) :
    ‖toL (lev (Cinf E) r s (y, 1)).val‖ ≤ ‖toL y.val‖ + 1 := by
  have n0 := norm_nonneg (toL y.val)
  have hent : ∀ i j, ‖(y.val i j : Cinf E)‖ ≤ ‖toL y.val‖ := fun i j =>
    (norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix _ _ (Cinf E)) i j‖ ≤ _
  rw [GlobalTheory.SmGL.val_emb₂]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa using (hent i' j').trans (by linarith)
  · simp; linarith
  · simp; linarith
  · have h1 : ‖((1 : Matrix (Fin s) (Fin s) (Cinf E)) i' j')‖ ≤ 1 := by
      by_cases h : i' = j'
      · subst h; simpa using norm_one_le
      · simp [Matrix.one_apply_ne h]
    simpa using h1.trans (by linarith)

theorem height_lev_le (y : GL (Fin r) (Cinf E)) :
    height (lev (Cinf E) r s (y, 1)) ≤ 3 * height y := by
  have e : (lev (Cinf E) r s (y, 1))⁻¹ = lev (Cinf E) r s (y⁻¹, 1) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_lev_le (s := s) y
  have h2 := norm_lev_le (s := s) y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.CompanionTheory.CTFin.Slice1.Height

theorem GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  intro E _ _ _ r s c
  have hb : 0 ≤ GlobalTheory.CompanionTheory.GrowthConv.bnd c := by
    unfold GlobalTheory.CompanionTheory.GrowthConv.bnd
    positivity
  refine ⟨3 * GlobalTheory.CompanionTheory.GrowthConv.bnd c, by positivity, fun y => ?_⟩
  refine (GlobalTheory.CompanionTheory.GrowthConv.height_mul_le_bnd c _).trans ?_
  have := mul_le_mul_of_nonneg_left (Height.height_lev_le (s := s) y) hb
  linarith

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieDerivativeConvolutionKernelStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_derivative_convolution_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a), IsAutForm φ → ∀ X : Lie E a, ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a, (lie E a X φ).1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.LieConv.lie_eq_conv | exact GlobalTheory.CompanionTheory.LieConv.lie_eq_conv | (intros; apply GlobalTheory.CompanionTheory.LieConv.lie_eq_conv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieGeneratorsGlRelations
section
noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed GlobalTheory.CompanionTheory.GLK
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.GLK.Pair

section Ring

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem brk_ee (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r - Complex.I • s))
      - ((1 / 2 : ℂ) • (r - Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q))
      = (1 / 2 : ℂ) • (P - Complex.I • Q) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  linear_combination (norm := skip) (-(Complex.I / 4)) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ff (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p + Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      - ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p + Complex.I • q))
      = (1 / 2 : ℂ) • (P + Complex.I • Q) := by
  subst h1 h2
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ef (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      = ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q)) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (1 / 4 : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

end Ring

section Main

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def eP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z - Complex.I • D (Complex.I • Z))

def fP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z + Complex.I • D (Complex.I • Z))

theorem first_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : e1 D a b = eP D (Matrix.single a b 1) := by
  simp [e1, eP, Matrix.smul_single]

theorem second_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : f1 D a b = fP D (Matrix.single a b 1) := by
  simp [f1, fP, Matrix.smul_single]

variable {D : Mat n → Module.End ℂ V}

theorem D_neg (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (X : Mat n) : D (-X) = -D X := by
  simpa using hs (-1) X

theorem D_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : D (0 : Mat n) = 0 := by
  simpa using hs 0 0

theorem D_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : D (X - Y) = D X - D Y := by
  rw [sub_eq_add_neg, ha, D_neg hs, sub_eq_add_neg]

theorem eP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : eP D (0 : Mat n) = 0 := by
  simp [eP, D_zero hs]

theorem fP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : fP D (0 : Mat n) = 0 := by
  simp [fP, D_zero hs]

theorem eP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : eP D (X - Y) = eP D X - eP D Y := by
  simp only [eP, smul_sub, D_sub ha hs]
  abel

theorem fP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : fP D (X - Y) = fP D X - fP D Y := by
  simp only [fP, smul_sub, smul_add, D_sub ha hs]
  abel

theorem brk_four (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    D Z * D W - D W * D Z = D (Z * W - W * Z) ∧
    D (Complex.I • Z) * D W - D W * D (Complex.I • Z) = D (Complex.I • (Z * W - W * Z)) ∧
    D Z * D (Complex.I • W) - D (Complex.I • W) * D Z = D (Complex.I • (Z * W - W * Z)) ∧
    D (Complex.I • Z) * D (Complex.I • W) - D (Complex.I • W) * D (Complex.I • Z) = -D (Z * W - W * Z) := by
  refine ⟨(hb Z W).symm, ?_, ?_, ?_⟩
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb, ← D_neg hs]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel

theorem eP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * eP D W - eP D W * eP D Z = eP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ee _ _ _ _ _ _ h1 h2 h3 h4

theorem fP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    fP D Z * fP D W - fP D W * fP D Z = fP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ff _ _ _ _ _ _ h1 h2 h3 h4

theorem eP_fP_comm (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * fP D W = fP D W * eP D Z := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ef _ _ _ _ _ _ h1 h2 h3 h4

theorem single_brk (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 - Matrix.single c d (1 : ℂ) * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  have h : ∀ a b c d : Fin n, (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
    intro a b c d
    split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne a b c h 1 (c := (1 : ℂ))
  rw [h, h]

theorem eP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    e1 D a b * e1 D c d - e1 D c d * e1 D a b =
      (if b = c then e1 D a d else 0) - (if d = a then e1 D c b else 0) := by
  simp only [first_generator_eq_single]
  rw [eP_brk hs hb, single_brk, eP_sub ha hs]
  split_ifs <;> simp [eP_zero hs]

theorem fP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    f1 D a b * f1 D c d - f1 D c d * f1 D a b =
      (if b = c then f1 D a d else 0) - (if d = a then f1 D c b else 0) := by
  simp only [second_generator_eq_single]
  rw [fP_brk hs hb, single_brk, fP_sub ha hs]
  split_ifs <;> simp [fP_zero hs]

end Main

theorem gl_pair : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V),
    (∀ X Y, D (X + Y) = D X + D Y) → (∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) →
    (∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) →
    Formalism.REAL.GlRel (e1 D) ∧ Formalism.REAL.GlRel (e2 D) ∧ ∀ a b c d, e1 D a b * e2 D c d = e2 D c d * e1 D a b := by
  intro n V _ _ D ha hs hb
  refine ⟨fun a b c d => eP_units ha hs hb a b c d, fun a b c d => ?_, fun a b c d => ?_⟩
  · have h := fP_units ha hs hb b a d c
    simp only [e2, neg_mul_neg]
    rw [h]
    simp only [eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
    split_ifs <;> simp <;> abel
  · simp only [e2, mul_neg, neg_mul, first_generator_eq_single, second_generator_eq_single]
    rw [eP_fP_comm hs hb]

end GlobalTheory.CompanionTheory.GLK.Pair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegralStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderate_growth_convolution_integral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ ψ : GA E a → ℂ), Continuous φ → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ D : AutomorphicForm.archGroup E a → ℂ, Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * AutomorphicForm.infEmb E a y) * D y ∂ν) → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.CompanionTheory.GrowthConv.growth_conv | exact GlobalTheory.CompanionTheory.GrowthConv.growth_conv | (intros; apply GlobalTheory.CompanionTheory.GrowthConv.growth_conv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonrepresentedSignatureObstructionStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonrepresented_signature_obstruction : ∀ (D : D7) (r : ℕ) (V : HSp D), 2 * r < V.rank → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → ∃ (ρ : D.what₂.Tau) (ε : ℝ) (S : Submodule ℂ (Fin r → ℂ)), (ε = 1 ∨ ε = -1) ∧ GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.NonnegOn ε (β.1.map (tauE D ρ)) S ∧ ∀ T : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (gramAt D V ρ) T → Module.finrank ℂ T < Module.finrank ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHoldsStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_pg_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG k := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.phiPG | exact GlobalTheory.CompanionTheory.BZPhiPG.phiPG | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.phiPG <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_hermitian_lattice : ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∀ f : hermA D r → ℂ, Continuous f → (∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖f (b + c.1)‖ ≤ u c) → Integrable f lam ∧ (Summable (fun t : ratHerm D r => ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) → ∑' c : ratHerm D r, f c.1 = ∑' t : ratHerm D r, ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
  first | exact @GlobalTheory.CompanionTheory.HermPoisson.poisson_herm | exact GlobalTheory.CompanionTheory.HermPoisson.poisson_herm | (intros; apply GlobalTheory.CompanionTheory.HermPoisson.poisson_herm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOverPlacesStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_product_over_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → GlobalTheory.CompanionTheory.SW.IsEulerProd b dx 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (fun v => GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M) ∧ ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (latV b v) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.DxN.selfDual_isEulerProd_n | exact GlobalTheory.CompanionTheory.SiegelND.DxN.selfDual_isEulerProd_n | (intros; apply GlobalTheory.CompanionTheory.SiegelND.DxN.selfDual_isEulerProd_n <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_branches_holds : GroundTheory.Heights₂.Heights.SliceBranches.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | exact GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | (intros; apply GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches <;> assumption)
end


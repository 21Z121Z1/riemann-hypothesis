import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulBrStdOfEquivariant
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterIrrIsoWeylRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0112
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0060
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwiseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepChainStepMatrixCoefficientTwisted

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulBrStdOfEquivariantStatement
section
open Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_smul_brStd_of_equivariant : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1), 1 ≤ n → ∀ (Λ : ι → DomWeight N) (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) → ∀ φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ, (∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v)) → ∃ c : ℂ, φ = c • Formalism.L2.Col.Br.brStd hN Λ σ := by
  first | exact @GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant | exact GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant | (intros; apply GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactDetSqrtCoverMaxCompact
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem isClosed_Kset {p q : ℕ} (T : GrpData p q) : IsClosed T.Kset := by
  have h : T.Kset = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : T.G | matG T x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
  exact isClosed_eq ((continuous_matG T).matrix_elem a b) continuous_const

theorem isCompact_Kset : ∀ (p q : ℕ) (T : GrpData p q), IsCompact T.Kset := by
  intro p q T
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Ix p q) (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const) (fun M hM => hM)
  refine ((GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).isCompact_preimage (hc.prod hS)).of_isClosed_subset
    (isClosed_Kset T) fun x hx => ⟨matG_star_mul T hx, ?_⟩
  simpa using GlobalTheory.RealPar.Cover.norm_sq x

end GlobalTheory.PolarU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyGrpData
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.DetSqrtCover

theorem nonempty_grpData : ∀ p q : ℕ, Nonempty (GrpData p q) :=
  fun p q => ⟨grpOf p q MeasureTheory.Measure.haar⟩

end GlobalTheory.DetSqrtCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterIrrIsoWeylRepStatement
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.outer_irr_iso_weylRep_of_pos : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ), 0 < n → ∀ (lam : ι → ℕ → ℤ) (μ : ι → DomWeight n), (∀ τ (i : Fin n), (μ τ).w i = lam τ i) → Iso (outer fun τ => irr n (μ τ)) (weylRep n lam) := by
  first | exact @GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep | exact GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep | (intros; apply GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexTwoBlockParahoricConjTorusDiagElement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.ParIdx

theorem relIndex_parahoric_conj_mtor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℝ) := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric
  | exact @_root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric
  | exact _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric
  | (apply _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric <;> assumption)
  | (intros; apply _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ParahoricConjugateOpen.relIndex_conj_parahoric ..)

end GlobalTheory.ParIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosetsStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_parahoricBiTransforming_doubleCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ →
  ∀ φ : GL (Fin r ⊕ Blocks l t) k → ℂ, IsBiType ξ φ →
    (∀ x y, φ (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (x, y)) ≠ 0 → x ∈ KO k (Fin r)) →
    ∀ g, φ g ≠ 0 → ∃ e : Fin (l * t) → ℤ, Antitone e ∧ g ∈ dcell ϖ (e ∘ (blkEquiv l t).symm) := by
  first | exact @GlobalTheory.ChainStepSupp.support_dcell | exact GlobalTheory.ChainStepSupp.support_dcell | (intros; apply GlobalTheory.ChainStepSupp.support_dcell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepChainStepMatrixCoefficientTwistedStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_chainStep_matrixCoefficient_twisted : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r t l : ℕ) (ξ μ₀' : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → IsUnram μ₀' → IsUnitaryChar μ₀' →
  let μ' : kˣ →* ℂˣ := μ₀' * ξ
  let Φ : Matrix (Fin r ⊕ Blocks (l + 1) t) (Fin r ⊕ Blocks l t) k → ℂ := datum ξ
  let c : GL (Fin r ⊕ Blocks l t) k → ℂ := fun g => ip ν (om μ' g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) Φ) Φ
  IsBiType ξ c ∧
  (∀ x y, c (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (x, y)) ≠ 0 → x ∈ KO k (Fin r)) ∧
  ∀ e : Blocks l t → ℤ, c (mtor ϖ e) = (μ' ϖ : ℂ) ^ (∑ i, e i) *
    ((volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ : ℝ) : ℂ) *
    (resCard k : ℂ) ^ (-((r + (l + 1) * t : ℕ) : ℂ) / 2 * (sumAbs e : ℂ)) := by
  first | exact @GlobalTheory.ChainStepCoef.coef | exact GlobalTheory.ChainStepCoef.coef | (intros; apply GlobalTheory.ChainStepCoef.coef <;> assumption)
end


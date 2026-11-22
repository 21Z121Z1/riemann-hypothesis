import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0320
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdPlaces
section
noncomputable section

open Formalism.BasicNotions IsDedekindDomain NumberField Matrix Formalism.L2.DIV Formalism.IndefR.Lev GlobalTheory.StdFrames GlobalTheory.AdIsom
open scoped TensorProduct

namespace GlobalTheory.LevNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

@[reducible] def kField {E : Type} [Field E] [NumberField E] (Q : Pl E) : Field (kP Q) :=
  haveI := Q.isMaximal
  Ideal.Quotient.field Q.asIdeal

attribute [local instance] kField

def adPlaces (D : D7) : PlaceSys (EAf D) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Pl D.host.E) (fun Q => kP Q)
    (fun Q => resS D.host.F Q) where
  K Q := Q.adicCompletion D.host.E
  O Q := Q.adicCompletionIntegers D.host.E
  p Q := cpt Q
  e Q := idem Q
  surj Q x := by
    classical
    obtain ⟨z, hz⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
      (⟨Pi.single Q x, by
        refine Filter.mem_of_superset (Set.finite_singleton Q).compl_mem_cofinite fun Q' h => ?_
        show (Pi.single Q x : ∀ v : Pl D.host.E, v.adicCompletion D.host.E) Q' ∈ Q'.adicCompletionIntegers D.host.E
        rw [Pi.single_eq_of_ne h]
        exact zero_mem _⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    refine ⟨z, ?_⟩
    change toAd D z Q = _
    rw [hz]
    exact Pi.single_eq_same (M := fun v : Pl D.host.E => v.adicCompletion D.host.E) Q x
  e_self Q := ((isPlIdem_iff Q _).1 (isPlIdem_idem Q)).1
  e_ne Q := ((isPlIdem_iff Q _).1 (isPlIdem_idem Q)).2
  ext a h := cpt_ext fun Q => by rw [h Q, map_zero]
  int a := mem_OA a
  fin a := Filter.eventually_cofinite.1 (toAd D a).2
  r_surj Q y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, resS_oToS Q x⟩
  r_ker Q s := (resS_eq_zero_iff_cpt Q s).trans
    ((Valuation.isEquiv_valuation_valuationSubring Valued.v).lt_one_iff_lt_one)

end GlobalTheory.LevNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → IsMaj T b → HasIw d (Kmax T b) := by
  first | exact @GlobalTheory.Core.Rk.IwAd.hasIw_Kmax | exact GlobalTheory.Core.Rk.IwAd.hasIw_Kmax | (intros; apply GlobalTheory.Core.Rk.IwAd.hasIw_Kmax <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorDoubledHermitianSpaceDecomp
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnAnnDec

theorem mul_split {b n k : ℕ} (W : Matrix (Fin b) (Fin (n + n)) ℂ) (N : Matrix (Fin (n + n)) (Fin k) ℂ) :
    W * N = W.submatrix id (fun i => finSumFinEquiv (Sum.inl i)) * N.submatrix (fun i => finSumFinEquiv (Sum.inl i)) id
      + W.submatrix id (fun i => finSumFinEquiv (Sum.inr i)) * N.submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_add]

theorem annih_dec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (μ : D.host.E), IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ), ∃ (X X' : Matrix (Fin B.rank) (Fin A.rank) ℂ) (c : ℂ), ∀ f, IsThetaFunO ψ (dblSp A) B f → annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) Y f = annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f + c • annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X' * (dblDec A).qX.map (tauE D τ)) f := by
  intro D ψ hψ θ hθ A B μ hμ s' sB hs hsB τ Y
  have hLine : LineAtExists D := fun θ hθ m n τ z => ⟨_, GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z⟩
  obtain ⟨hadd, hsm, -⟩ := Formalism.IndefR.Fock.DRho.dRhoLin D ψ θ hψ hθ hLine (dblSp A) B τ
  have hs2 : s' τ * s' τ = 1 := (GlobalTheory.CartStd.isCartanInv_stdInv D A μ hμ s' hs τ).1
  have hB2 : sB τ * sB τ = 1 := (hsB τ).1

  obtain ⟨-, hdet, hinv⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hTR : Tm A μ * (Tm A μ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hMN : (Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hTR, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have htop : (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id =
      (dblDec A).qX.map (tauE D τ) := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl]
  have hbot : (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inr i)) id =
      (μ⁻¹ • (dblDec A).qY).map (tauE D τ) := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr]
  have hμ0 : tauE D τ μ ≠ 0 := (map_ne_zero (tauE D τ)).2 hμ.1
  have hn0 : (‖tauE D τ μ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hμ0)
  set q := (dblDec A).qX.map (tauE D τ) with hq
  set k : ℂ := (tauE D τ μ)⁻¹ * (‖tauE D τ μ‖ : ℂ) with hk
  have hqs := GlobalTheory.StdUnnAnnih.qX_mul_stdInv A μ hμ s' hs τ
  have hbot' : (μ⁻¹ • (dblDec A).qY).map (tauE D τ) = k • (q * s' τ) := by
    rw [hqs, smul_smul, hk, mul_assoc, mul_inv_cancel₀ hn0, mul_one]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  set W := Y * (Tm A μ).map (tauE D τ) with hW
  set P := W.submatrix id (fun i => finSumFinEquiv (Sum.inl i)) with hP
  set R := W.submatrix id (fun i => finSumFinEquiv (Sum.inr i)) with hR
  have hYd : Y = P * q + R * (k • (q * s' τ)) := by
    have h1 : Y = W * ((Tm A μ)⁻¹).map (tauE D τ) := by rw [hW, Matrix.mul_assoc, hMN, Matrix.mul_one]
    rw [h1, mul_split, htop, hbot, hbot']
  refine ⟨P, (-Complex.I * k) • (sB τ * R), -Complex.I, fun f hf => ?_⟩
  set J := cplxO (s' τ) (sB τ) with hJ
  have hJadd : ∀ Z Z' : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ, J (Z + Z') = J Z + J Z' := by
    intro Z Z'
    simp only [hJ, cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
  have hJJ : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ, J (J Z) = -Z := by
    intro Z
    simp only [hJ, cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
    simp only [Matrix.mul_assoc]
    rw [hs2, ← Matrix.mul_assoc (sB τ) (sB τ), hB2, Matrix.one_mul, Matrix.mul_one, neg_one_smul]
  have hneg : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      dRho (heisO ψ (dblSp A) B) θ τ (-Z) f = -dRho (heisO ψ (dblSp A) B) θ τ Z f := by
    intro Z
    have h := hsm (-1) Z f hf
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul] at h
    exact h
  have hAadd : ∀ Z Z' : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ (dblSp A) B) θ τ J (Z + Z') f =
        annih (heisO ψ (dblSp A) B) θ τ J Z f + annih (heisO ψ (dblSp A) B) θ τ J Z' f := by
    intro Z Z'
    simp only [Formalism.IndefR.Datum.annih]
    rw [hJadd, hadd _ _ f hf, hadd _ _ f hf, smul_add]
    abel
  have hAJ : ∀ Z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ (dblSp A) B) θ τ J (J Z) f = (-Complex.I) • annih (heisO ψ (dblSp A) B) θ τ J Z f := by
    intro Z
    simp only [Formalism.IndefR.Datum.annih]
    rw [hJJ, hneg]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (dRho (heisO ψ (dblSp A) B) θ τ (J Z) f x) * Complex.I_sq
  have hdir : J (((-Complex.I * k) • (sB τ * R)) * q) = R * (k • (q * s' τ)) := by
    have hc : Complex.I * (-Complex.I * k) = k := by linear_combination (-k) * Complex.I_sq
    simp only [hJ, cplxO, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (sB τ) (sB τ), hB2, Matrix.one_mul]
  rw [hYd, ← hdir, hAadd, hAJ]

end GlobalTheory.StdUnnAnnDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorSchroedingerFunctionsDoubledStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ), sch ψ A B ν 𝓨 (annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f) = annS B l sB θ τ X (sch ψ A B ν 𝓨 f) := by
  first | exact @GlobalTheory.StdUnnAnnih.annih_sch | exact GlobalTheory.StdUnnAnnih.annih_sch | (intros; apply GlobalTheory.StdUnnAnnih.annih_sch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiContractedIsThetaFunctionEachVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ContrTheta

theorem continuous_linkKappa {D : D7} {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (S : HSp D) : Continuous (l.κ S) := by
  unfold Link.κ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have h : Continuous fun w : WO S L' => giA S ⬝ (adj (rat l.τ ⬝ w) ⬝ gA B.L) :=
    Continuous.matrix_mul continuous_const (Continuous.matrix_mul
      (GlobalTheory.MixModel.continuous_adj.comp (continuous_const.matrix_mul continuous_id)) continuous_const)
  exact h.const_smul ((incA D) (-D.host.xi0⁻¹))

theorem integrable_restrict_of_bdd {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs : μ s = 1) (f : X → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f (μ.restrict s) := by
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ, hs]; exact ENNReal.one_lt_top⟩
  exact (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hC x)

theorem contr_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → (∀ v, IsThetaFunO ψ B.A J.W₀ fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) ∧ ∀ p, (IsThetaFunO ψ J.W₀ B'.A fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) ∧ ∀ v, oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 = ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) * oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 ∂vL.μ := by
  intro D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' _ _ hoa _ _ _ Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have hstd : IsStdChar D ψ (-1) := hoa.std
  haveI hbor : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  have hκ : Continuous (l.κ J.W₀) := continuous_linkKappa l J.W₀
  have hκm : Measurable (l.κ J.W₀) := hκ.measurable
  have hvol : vL.μ vL.𝓕 = 1 := vL.covol.2.2
  have ha : ∀ v, Integrable (fun w => Ξ₂ ((B'.o.resT J.W₀).symm (v, w))) (vL.μ.restrict vL.𝓕) := by
    intro v
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hstd Ξ₂ hΞ₂
    exact integrable_restrict_of_bdd _ _ hvol _ (hΞ₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp
      (Continuous.prodMk continuous_const continuous_id))) C (fun w => hC _)
  have hG : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (fun x => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, (B.o.resS J.W₀ x).2)))
      (B.o.resS J.W₀ x).1) := fun p =>
    (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha 0) p).1
  have hb : ∀ p, Integrable (fun w => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0)
      (vL.μ.restrict vL.𝓕) := by
    intro p
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hstd _ (hG p)
    have heq : (fun w => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0) = fun w =>
        (fun x => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, (B.o.resS J.W₀ x).2))) (B.o.resS J.W₀ x).1)
          ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) := by
      funext w; simp only [AddEquiv.apply_symm_apply]
    rw [heq]
    exact integrable_restrict_of_bdd _ _ hvol _ ((hG p).cont.comp ((OrthDec.continuous_resS_symm _ _).comp
      (Continuous.prodMk continuous_const hκ))) C (fun w => hC _)
  have hcom : ∀ p v, oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 = ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) *
      oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 ∂vL.μ := fun p v =>
    (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha v) p).2 0
  refine ⟨fun v => ?_, fun p => ⟨?_, hcom p⟩⟩
  · exact GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hstd B.V₀ B.A B.L J.W₀ B.o Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha v)
  · have h := GlobalTheory.T.isThetaFun_superposition_target_orthSummand D ψ hstd B'.V₀ B'.A B'.L J.W₀ B'.o Ξ₂ hΞ₂ _ (vL.μ.restrict vL.𝓕) id _ measurable_id (hb p)
    have heq : (fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) = fun v =>
        ∫ w, oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 * Ξ₂ ((B'.o.resT J.W₀).symm (v, id w))
          ∂(vL.μ.restrict vL.𝓕) := by
      funext v; rw [hcom]; congr 1; funext w; rw [mul_comm]; rfl
    rw [heq]; exact h

end GlobalTheory.ContrTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaPreservesSupportedMatricesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLink_kappa_preserves_supported_matrices : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (w : WO S L'), MxAt P w → MxAt P (l.κ S w) := by
  first | exact @GlobalTheory.LinkKapMx.mxAt_linkKappa | exact GlobalTheory.LinkKapMx.mxAt_linkKappa | (intros; apply GlobalTheory.LinkKapMx.mxAt_linkKappa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaSurjectiveSupportedConjugateHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLink_kappa_surjective_supported_conjugateHalf : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (h : WO B.L S), ∃ x : WO S L', l.κ S x = h ∧ (MxAt P h → MxAt P x) ∧ ∀ e : AE D, IsHalf e h → IsHalf (cA D e) x := by
  first | exact @GlobalTheory.LinkKapInv.kappa_inv | exact GlobalTheory.LinkKapInv.kappa_inv | (intros; apply GlobalTheory.LinkKapInv.kappa_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepIteratedQuotientIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.Assemble

section Quot

variable {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}

theorem quotient_integral_finset_sum_eq {ι : Type} (s : Finset ι) (F : ι → G → ℂ) (Z : ι → ℂ)
    (hF : ∀ i ∈ s, IsQuotIntL1 μR μG (F i) (Z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i ∈ s, F i x) (∑ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsQuotIntL1.zero
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have h3 := h1.add h2
    rw [Finset.sum_insert ha]
    convert h3 using 1
    funext x
    rw [Finset.sum_insert ha]
    rfl

theorem quotient_integral_finset_sum_smul {ι : Type} (s : Finset ι) (a : ι → ℂ) (F : ι → G → ℂ) (Z : ι → ℂ)
    (hF : ∀ i ∈ s, IsQuotIntL1 μR μG (F i) (Z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i ∈ s, a i * F i x) (∑ i ∈ s, a i * Z i) :=
  quotient_integral_finset_sum_eq s (fun i x => a i * F i x) (fun i => a i * Z i) fun i hi => (hF i hi).smul (a i)

end Quot

end GlobalTheory.SeeSaw.Assemble

end

noncomputable section

namespace GlobalTheory.SeeSaw.Assemble

set_option maxHeartbeats 4000000 in

theorem doubleStep_tuple : ∀ (D : D7) (c : Comm D) (t : Tup c), DoubleStep D → c.Is → t.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ), (∀ a, IsContAut (c.X j) (φ a)) → RapidDec _ f → RapidDec _ (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) → ∃ F₁ : GA D (c.V (j + 1)) → ℂ, IsQuotIntL1 (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ F₁ (t.perF j (σ + 1) h φ (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁))) ∧ ∀ h₁, IsQuotIntL1 (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ (t.integrand j σ h P₁ P₂ φ f h₁) (F₁ h₁) := by
  intro D c t hDS hc ht j σ h P₁ P₂ φ f hφ hf hrap
  obtain ⟨hom₁, hvW₁⟩ := ht.sBF j (σ + 1) h
  obtain ⟨hom₂, hvW₂⟩ := ht.sFB j σ h
  have hj1 : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  have hΦ₁ := ht.pt j hj1 P₁
  have hΦ₂ := ht.pt (j + 1) hj2 P₂

  have hstep : ∀ α, ∀ g : GA D (c.V j), ∃ f₁ : GA D (c.V (j + 1)) → ℂ,
      IsQuotIntL1 (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ f₁
        ((c.B j (σ + 1) h).per c.ψ (φ α) (rTrans g (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
          (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁)))) ∧
      ∀ h₁, IsQuotIntL1 (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ
        (fun h₂ => (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
          (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (t.pt j P₁) (t.pt (j + 1) P₂) (φ α) g h₁ h₂)
          (rTrans h₂ f)) (f₁ h₁) := by
    intro α g
    have hr : RapidDec _ ((t.sFB j σ h).lift f (t.pt (j + 1) P₂)) := by
      unfold Step.lift; rw [hom₂, hvW₂]; exact hrap
    obtain ⟨-, f₁, h1, h2⟩ := hDS c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (t.pt j P₁) (t.pt (j + 1) P₂) (φ α) f g
      hΦ₁ hΦ₂ (hφ α) hf hr
    refine ⟨f₁, ?_, fun h₁ => ?_⟩
    · have h1' := h1
      unfold Step.lift at h1'
      rw [hom₁, hvW₁, hom₂, hvW₂] at h1'
      exact h1'
    · have h2' := h2 h₁
      rw [hvW₂] at h2'
      exact h2'
  choose f₁ hf₁ using hstep

  have hw := (t.sBF j (σ + 1) h).weil
  rw [hom₁] at hw
  have hcont := (GlobalTheory.Unf.LiftRapid.lift_conv_cont_growth D c.ψ (c.V j) (c.V (j + 1)) _ _ (t.om j) hw (c.vol (j + 1))
    (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁) hrap hΦ₁).2.2.1
  refine ⟨fun h₁ => ∑ α, ∑ g ∈ (t.e j α).support, t.e j α g * f₁ α g h₁, ?_, fun h₁ => ?_⟩
  · have hper : ∀ α, (c.B j (σ + 1) h).per c.ψ (φ α) (trc (t.e j α) (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁))) =
        ∑ g ∈ (t.e j α).support, t.e j α g * (c.B j (σ + 1) h).per c.ψ (φ α) (rTrans g (liftS (t.om j) (c.vol (j + 1)).μ
          (c.vol (j + 1)).𝓕 (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂))
          (t.pt j P₁))) := fun α =>
      ((GlobalTheory.T.besselPeriod_linear_and_translationCombination D c.ψ hc.std (σ + 1) (c.B j (σ + 1) h) (φ α) (hφ α)).2 (t.e j α) _ hcont).2
    unfold Tup.perF
    simp only [hper]
    exact quotient_integral_finset_sum_eq _ _ _ fun α _ =>
      quotient_integral_finset_sum_smul _ _ _ _ fun g _ => (hf₁ α g).1
  · unfold Tup.integrand
    exact quotient_integral_finset_sum_eq _ _ _ fun α _ =>
      quotient_integral_finset_sum_smul _ _ _ _ fun g _ => (hf₁ α g).2 h₁

end GlobalTheory.SeeSaw.Assemble

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesLatticeCompletion_on_off_iff_all_finitePlaces : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop), (GlobalTheory.FinPl.Moves S g L L (fun p => ¬ P p) ∧ GlobalTheory.FinPl.Moves S g L L P) ↔ GlobalTheory.FinPl.Moves S g L L (fun _ => True) := by
  first | exact @GlobalTheory.FinPl.moves_iff_moves_on_off | exact GlobalTheory.FinPl.moves_iff_moves_on_off | (intros; apply GlobalTheory.FinPl.moves_iff_moves_on_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSizeHypothesisExplicitConstantSiegelMass
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg
theorem xiSizes_explicit : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), 1 ≤ Cl → Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (Cnt.NT D u) (BridgeLemma.XiB D large₂ u C) := by
  intro hS C hC D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hCl hH
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hmax : max 1 (1 / Cl) ≤ 1 := max_le le_rfl (by rw [div_le_one (by linarith)]; exact hCl)
  have hM2 := Formalism.MainNotions.BridgeLemma₂.plane_mass_bound_parameters D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8
    (le_trans (mul_le_mul_of_nonneg_left hmax (by norm_num)) (by norm_num))
  have hX := Formalism.MainNotions.BridgeLemma.first_bound_of_mass_ratio D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8 408
    (Formalism.MainNotions.BridgeLemma.lattice_count_first_of_siegel hS D) hM2 (by norm_num) le_rfl hCl
  have hCX : |(408 : ℝ)| * max 1 |Real.exp 1 * Real.pi| ≤ C := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 408), abs_of_pos (by positivity), max_eq_right he]; exact hC
  have hXi := Formalism.MainNotions.BridgeLemma.xiHyp_of_stX D large₂ hH hX hCX (by linarith)
  rw [← Formalism.MainNotions.BridgeLemma.d_m_eq D]
  exact hXi
end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankTwoCountBoundsOfRowCountBoundsUniform
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem corankTwoCountBounds_of_rowCountBoundsUniform : ∀ S : Set ℝ, CntOn S → CountBoundOn S := by
  intro S h Cg cb Cu cT CT
  obtain ⟨c3, cH, cS, c4, thr, hthr⟩ := h Cg cb Cu cT CT
  exact ⟨c3, cH, thr, fun C0 hC0 C' Cl h1 h2 D large₂ u =>
    ⟨(hthr C0 hC0 C' Cl h1 h2 D large₂ u).1, (hthr C0 hC0 C' Cl h1 h2 D large₂ u).2.1⟩⟩

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrimeStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime : ∀ (D : D7) (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ), (∀ x y, psiEf (x + y) = psiEf x * psiEf y) → (∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1) → (∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1) → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1 := by
  first | exact @GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one | exact GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one | (intros; apply GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one <;> assumption)
end


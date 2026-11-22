import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0805
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0002
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0005
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0015
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0005
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0002

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmG14OfAux
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.ClosingLocalInputs
theorem galoisFamilyConditions_of_sumRepresentations_alt (D : D7) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) : _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) :=
  fun i r hr => (h41 i).2.2 r hr
theorem main_alt_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris →
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C : ℝ) (CT : ℕ), 40 ≤ CT → 8 * (CT : ℝ) ≤ C → (∃ P : Pend D, admDZ P ∧ EigSpan P) →
    SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionG6 D →
    ResidualIrreducibleRankR D → GlobalTheory.TypeLeaf.SerLoc D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D → TieInePoly D → tieChi (D := D) →
    _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro hGAR hBS hFB hBKL hLTD hLEC D HW F Cm C CT hCT hC hP htie0 hadm1 hadm2 hadm5 h41 hG5 hG6 hN9 hSer hO
    hIne hChi
  obtain ⟨P, hDZ, hEig⟩ := hP
  have hT : admT (D := D) CT := GlobalTheory.T.crystallinePeriodBound_all_constant_ge_forty hBS hFB hBKL hLTD hLEC D HW F Cm CT hCT
  have hLOC : LocalPushoutProposition (D := D) := GlobalTheory.T.local_absorption_length_bound_of_blochKato hBKL hLTD hLEC D HW F Cm
  have hRbar : ResidualAbsIrreducible (D := D) := GlobalTheory.Pass.residualRep_spans_matrixAlgebra_of_goodPoint D hN9
  have hN5g : TypePrimeChoiceLemmas (D := D) := _root_.GlobalTheory.typePrimeCongruences_forall D ⟨hadm5, h41, hN9, hO⟩
  have hTB : admTB (D := D) HW F := GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hBKL hLTD hLEC D HW F Cm
  have hBK : admBK (D := D) := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBKL hLTD hLEC D
  exact _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions hGAR D P HW F C CT hC hadm5 hEig hIne hT hLOC hRbar hN5g hDZ
    (_root_.GlobalTheory.ClosingLocalInputs.galoisFamilyConditions_of_sumRepresentations_alt D h41) hG5 hG6 hSer hTB hBK hadm1 hadm2 htie0 hChi
end GlobalTheory.ClosingLocalInputs
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltAlt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
theorem main_alt_alt_alt : ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.AdmissibleResidualTameEigenvalues D := by
  intro D h0 hG hA hL
  obtain ⟨hLP, hAut, -⟩ := h0
  have hW : GlobalTheory.TypeLeaf.WildOne D := hL.1
  have hGal : _root_.UpperTheory.GalS.GalAwayN D := _root_.GlobalTheory.AdmTame.galAwayOfS' hG
  have hF : GlobalTheory.TypeLeaf.FrobDense D := by
    intro T hT
    rw [dense_iff_closure_eq]
    exact hA.2.2.1 T hT
  have hCL : GlobalTheory.TypeLeaf.CharLaws D := by
    intro w a χ χ' hχ hχ'
    obtain ⟨-, -, -, h4, h5, -⟩ := hLP w a a χ χ' 0 hχ hχ'
    exact ⟨h4, h5⟩
  have hM : GlobalTheory.TypeLeaf.MultOne D := by
    intro a π π' ha h
    have hp := hA.1 [⟨a, π, 1⟩] [⟨a, π', 1⟩] (by simp [ha]) (by simp [ha])
      (Filter.Eventually.of_forall fun w => by simp [isoLoc, spehLoc, h w])
    rw [List.singleton_perm_singleton] at hp
    simp only [Formalism.BasicNotions.Part.mk.injEq, heq_eq_eq, true_and] at hp
    exact hp.1
  have hT : GlobalTheory.TypeLeaf.TwistInv D := GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne D hCL hM
  have hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
    intro τ z hz
    obtain ⟨m, hm⟩ := D.R.t_odd
    obtain ⟨h1, h2⟩ := hAut.2.1 τ
    rw [h2] at hz
    rcases h1 with h1 | h1 <;> rw [h1] at hz <;> simp at hz <;> subst hz
    · refine ⟨-(m : ℤ) - 1, ?_⟩
      rw [hm]; push_cast; ring
    · refine ⟨-(m : ℤ), ?_⟩
      rw [hm]; push_cast; ring
  have hP : GlobalTheory.TypeLeaf.PointPar D := GlobalTheory.TypeLeaf.pointPar_of_twist D hT hAut.1.1 hz
  intro i Sig hx hf hsq hc ρ hρ
  exact _root_.GlobalTheory.TypeLeaf.tameSum_of_inputs_alt D hW (GlobalTheory.T.firstCharacter_trivial_wildInertia_typePrime D) hGal hF hP i Sig hx
    (_root_.UpperTheory.GalS.fullLabS_of_fullLabS_trivial ⟨hf, fun k v => hL.2 k v _ (hf k v) (hsq k v) (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by
      obtain ⟨π, rfl⟩ := hc
      rw [GlobalTheory.InertialTypesCmp.lpDim_isoLoc]
      simp [rankIso, Ranks.nV]))⟩) hc ρ hρ
end GlobalTheory.AdmTame
end
end
end


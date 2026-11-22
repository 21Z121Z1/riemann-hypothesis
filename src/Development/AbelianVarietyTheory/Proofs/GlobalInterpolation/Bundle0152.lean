import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0151
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0147

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePoints
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

noncomputable section

open Formalism.UG

namespace GlobalTheory.InfUCompact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem compactSpace_UJ (E : Type) [Field E] (n : ℕ) :
    CompactSpace (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))) := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) (Cinf E)) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
  let f : Matrix.unitaryGroup (Fin n) (Cinf E) → GL (Fin n) (Cinf E) := fun u =>
    ⟨u.1, star u.1, Matrix.mem_unitaryGroup_iff.1 u.2, Matrix.mem_unitaryGroup_iff'.1 u.2⟩
  have hf : Continuous f :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hr : Set.range f =
      (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) : Set (GL (Fin n) (Cinf E))) := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      change cT (starRingEnd (Cinf E)) u.1 * 1 * u.1 = 1
      rw [mul_one]
      exact Matrix.mem_unitaryGroup_iff'.1 u.2
    · intro hg
      have h : cT (starRingEnd (Cinf E)) (g : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * g = 1 := hg
      rw [mul_one] at h
      exact ⟨⟨g.1, Matrix.mem_unitaryGroup_iff'.2 h⟩, Units.ext rfl⟩
  exact isCompact_iff_compactSpace.1 (hr ▸ isCompact_range hf)

theorem range_infPt : Set.range (GlobalTheory.DefiniteDense.infPt (E := E) (n := n)) = (infU E n : Set (UA E n)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact pFin_infGL _
  · intro hx
    have hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a) :=
      fun a => (infEq E).symm_apply_apply _
    have hM : GeneralLinearGroup.map (pInf E) x.1 ∈
        UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) := by
      have h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1 := x.2
      rw [mul_one] at h0
      have e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) =
          (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E) := by
        ext i j
        simp [Formalism.UG.cT, hp]
      change cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 *
        (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1
      rw [e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨_, hM⟩, Subtype.ext (ga_ext ?_ ?_)⟩
    · exact pInf_infGL _
    · exact (pFin_infGL _).trans (Eq.symm hx)

theorem compactSpace_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    CompactSpace (infU E n) := by
  intro E _ _ _ n
  haveI := compactSpace_UJ E n
  have h : IsCompact (infU E n : Set (UA E n)) :=
    range_infPt (E := E) (n := n) ▸ isCompact_range GlobalTheory.DefiniteDense.continuous_infPt
  exact isCompact_iff_compactSpace.1 h

end GlobalTheory.InfUCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHermitianSpaceSelfDualLatticeSignatureStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianSpace_with_signature : ∀ (D : D7) (P Q : ℕ), ∃ U : HSpace D.host.E, U.SigOK ∧ ∀ τ, U.sig τ = (P, Q) := by
  first | exact @GlobalTheory.exists_hSpace_sigOK_sig | exact GlobalTheory.exists_hSpace_sigOK_sig | (intros; apply GlobalTheory.exists_hSpace_sigOK_sig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralCoordinatesTwistedTrueChain
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem pendTw_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (l0 : I.Law0 l) (u : B.Word) (a : I.ι), ∃ P : GlobalTheory.PerQ.PendTw (I.rec7 l Z) (I.tw l l0 Z) u a, ∀ τ,
      P.br τ = brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ) := by
  intro B X I hI l Z l0 u a
  exact ⟨{ br := fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
              (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)
           coM := fun w c => coM I u a w c
           coP := fun w => coP I u a w
           Pt_eq := GlobalTheory.T.localCoords_evaluationLowerRowMap_eq_tensor_branching I hI l Z l0 u a
           lat_co := GlobalTheory.T.lastStepIntegralForm_localCoords_mem_integralSpan I hI l Z l0 u a
           pt_co := fun w z hz => ⟨GlobalTheory.T.hyperplaneFormIntegral_localCoords_mem_integralSpan I hI l Z l0 u a w z hz, GlobalTheory.T.exists_integralHyperplaneForm_of_localCoords_integral I hI l Z l0 u a w z hz⟩ }, fun _ => rfl⟩

end GlobalTheory.PerQ.Co
end


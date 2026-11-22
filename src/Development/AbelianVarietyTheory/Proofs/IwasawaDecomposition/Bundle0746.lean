import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LambdaPrimeEqLambdaThree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0727
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0731
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepsMatHeqRefl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def KeepsMat {D : D7} (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) : Prop :=
  ∃ hF : D.host.F = maximalRealSubfield D.host.E, ∀ i : Fin D.R.m, ∃ hn : (Vc D i).rank = D.R.nV, ∀ κ a b,
    finMat D.sp.cm.sig (Vc D i).gram (p i κ) a b = (GlobalTheory.Mem.R3.swapCast hF).symm
      ((κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))

theorem keepsMat_heq_refl (D : D7) : ∀ (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) (p' : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)),
    KeepsMat p → KeepsMat p' → ∀ (j : Fin D.R.m) (j' : Fin D.R.m), (j : ℕ) = j' →
    HEq (fun g => (finHom (Vc D j)).rangeRestrict (p j g)) fun g => (finHom (Vc D j')).rangeRestrict (p' j' g) := by
  rintro p p' ⟨hF, hp⟩ ⟨hF', hp'⟩ j j' hj
  cases Fin.ext hj
  obtain ⟨hn, hp⟩ := hp j
  obtain ⟨hn', hp'⟩ := hp' j
  exact heq_of_eq (funext fun g => Subtype.ext (Units.ext (Matrix.ext fun a b => (hp g a b).trans (hp' g a b).symm)))

theorem keepsMat_heq (h : CopyTw D D' ι e) : ∀ (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) (p' : ∀ i : Fin D'.R.m, GAf D'.host.E D'.R.nV → GA D' (Vc D' i)),
    KeepsMat p → KeepsMat p' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    HEq (fun g => (finHom (Vc D j)).rangeRestrict (p j g)) fun g => (finHom (Vc D' j')).rangeRestrict (p' j' g) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((keepsMat_heq_refl D) :))

theorem low_copy_refl (D : D7) : (LowIn D → LowIn D) ∧
    (∀ (bad : D.ntw.Tw → ℕ) (bad' : D.ntw.Tw → ℕ), HEq bad bad' → (∀ i, bad i = normProd (D.ntw.S0 i)) →
      ∀ i, bad' i = normProd (D.ntw.S0 i)) ∧
    ((∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) →
      ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) := by
  refine ⟨id, fun _ _ hb H => ?_, id⟩
  subst hb; exact H

theorem low_copy (h : CopyTw D D' ι e) : (LowIn D → LowIn D') ∧
    (∀ (bad : D.ntw.Tw → ℕ) (bad' : D'.ntw.Tw → ℕ), HEq bad bad' → (∀ i, bad i = normProd (D.ntw.S0 i)) →
      ∀ i, bad' i = normProd (D'.ntw.S0 i)) ∧
    ((∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) →
      ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D'.R.m) → Subsingleton (D'.nexp.Fm i j b)) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((low_copy_refl D) :))

theorem pq_copy_refl (D : D7) : ∀ (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
      (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), HEq Pq Pq' →
      (∀ (ch : D.ntw.Tw → Set (Pl D.host.E)) (ch' : D.ntw.Tw → Set (Pl D.host.E)), HEq ch ch' →
        (∀ i P, IsSplitPl D.host P → (P ∈ ch i ↔ P ∈ Set.range Pq)) → ∀ i P, IsSplitPl D.host P → (P ∈ ch' i ↔ P ∈ Set.range Pq')) ∧
      ∀ (i' : D.ntw.Tw) (k : ℕ) (Q' : Finset (PlE D.host)) (ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i' k)ˣ),
        ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
          HEq (NX.qpOf D Pq Q) (NX.qpOf D Pq' Q') ∧ HEq (NX.qpOf D Pq (D.ntw.pD i)) (NX.qpOf D Pq' (D.ntw.pD i')) := by
  refine fun Pq Pq' hPq => ⟨fun _ _ hc H => ?_, fun i k Q ψ => ?_⟩
  · subst hPq; subst hc; exact H
  · subst hPq; exact ⟨i, Q, ψ, .rfl, .rfl, .rfl, .rfl, .rfl⟩

theorem pq_copy (h : CopyTw D D' ι e) : ∀ (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
      (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D'.host.E)) → PlE D'.host), HEq Pq Pq' →
      (∀ (ch : D.ntw.Tw → Set (Pl D.host.E)) (ch' : D'.ntw.Tw → Set (Pl D'.host.E)), HEq ch ch' →
        (∀ i P, IsSplitPl D.host P → (P ∈ ch i ↔ P ∈ Set.range Pq)) → ∀ i P, IsSplitPl D'.host P → (P ∈ ch' i ↔ P ∈ Set.range Pq')) ∧
      ∀ (i' : D'.ntw.Tw) (k : ℕ) (Q' : Finset (PlE D'.host)) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ),
        ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
          HEq (NX.qpOf D Pq Q) (NX.qpOf D' Pq' Q') ∧ HEq (NX.qpOf D Pq (D.ntw.pD i)) (NX.qpOf D' Pq' (D'.ntw.pD i')) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((pq_copy_refl D) :))

theorem join_copy_refl (D : D7) : ∀ (i' : D.ntw.Tw) (j : Fin D.R.m) (j' : Fin D.R.m), (j : ℕ) = j' → ∀ (b : Bool) (k : ℕ)
    (Q' : Finset (PlE D.host)) (ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i' k)ˣ), TwOK i' k Q' ψ' →
    ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
      TwOK i k Q ψ ∧ PolF D (Wc D j).rank (Vc D j).rank = PolF D (Wc D j').rank (Vc D j').rank ∧
      HEq (inferInstance : AddCommGroup (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : AddCommGroup (PolF D (Wc D j').rank (Vc D j').rank)) ∧
      HEq (inferInstance : Module ℂ (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : Module ℂ (PolF D (Wc D j').rank (Vc D j').rank)) ∧
      ∀ (ek : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ) (ek' : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ),
        HEq ek ek' → HEq (ek i b k) (ek' i' b k) ∧
        ∀ (r : ∀ k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))
          (r' : ∀ k Q ψ, D.nexp.MtV i' ((j' : ℕ) + 1) b k Q ψ →ₛₗ[ek' i' b k]
            (Bridge.Gf (Vc D j') → PolF D (Wc D j').rank (Vc D j').rank)), HEq r r' →
          ∀ (p : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j)) (p' : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j')), HEq p p' →
            HEq (fun f g => r k Q ψ f (p g)) fun f g => r' k Q' ψ' f (p' g) := by
  intro i j j' hj b k Q ψ hT
  cases Fin.ext hj
  refine ⟨i, Q, ψ, .rfl, .rfl, .rfl, hT, rfl, .rfl, .rfl, fun _ _ hek => ?_⟩
  subst hek
  refine ⟨.rfl, fun _ _ hr _ _ hp => ?_⟩
  subst hr; subst hp
  rfl

theorem join_copy (h : CopyTw D D' ι e) : ∀ (i' : D'.ntw.Tw) (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ (b : Bool) (k : ℕ)
    (Q' : Finset (PlE D'.host)) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), TwOK i' k Q' ψ' →
    ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
      TwOK i k Q ψ ∧ PolF D (Wc D j).rank (Vc D j).rank = PolF D' (Wc D' j').rank (Vc D' j').rank ∧
      HEq (inferInstance : AddCommGroup (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : AddCommGroup (PolF D' (Wc D' j').rank (Vc D' j').rank)) ∧
      HEq (inferInstance : Module ℂ (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : Module ℂ (PolF D' (Wc D' j').rank (Vc D' j').rank)) ∧
      ∀ (ek : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ) (ek' : ∀ i, Bool → ∀ k, FractionRing (D'.ntw.Ok i k) →+* ℂ),
        HEq ek ek' → HEq (ek i b k) (ek' i' b k) ∧
        ∀ (r : ∀ k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))
          (r' : ∀ k Q ψ, D'.nexp.MtV i' ((j' : ℕ) + 1) b k Q ψ →ₛₗ[ek' i' b k]
            (Bridge.Gf (Vc D' j') → PolF D' (Wc D' j').rank (Vc D' j').rank)), HEq r r' →
          ∀ (p : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j)) (p' : GAf D'.host.E D'.R.nV → Bridge.Gf (Vc D' j')), HEq p p' →
            HEq (fun f g => r k Q ψ f (p g)) fun f g => r' k Q' ψ' f (p' g) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((join_copy_refl D) :))

def ExpMove (X : NExpTied D) (X' : NExpTied D') : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)),
    HEq Q Q' → ∀ (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), HEq ψ ψ' →
    ∀ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h2' : j ≤ D'.R.m) (hA' : Formalism.L2.NX.AdmTw D' i' k Q' ψ'), ∃ hA : Formalism.L2.NX.AdmTw D i k Q ψ,
      HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV i' j b k Q' ψ' h1 h2' hA').QP ∧
      HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV i' j b k Q' ψ' h1 h2' hA').DP ∧
      ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (ε' : FractionRing (D'.ntw.Ok i' k) →+* ℂ), HEq ε ε' →
        ∀ (V V' : Type) [aV : AddCommGroup V] [mV : Module ℂ V] [aV' : AddCommGroup V'] [mV' : Module ℂ V'], V = V' → HEq aV aV' →
          HEq mV mV' → ∀ (r : D.nexp.MtV i j b k Q ψ → GAf D.host.E D.R.nV → V) (r' : D'.nexp.MtV i' j b k Q' ψ' → GAf D'.host.E D'.R.nV → V'),
            HEq r r' → GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V r → GlobalTheory.HeightCounting.Reads X' i' j b k Q' ψ' h1 h2' hA' ε' V' r'

def PqLaw (X : NExpTied D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Prop :=
  ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : Formalism.L2.NX.AdmTw D i k Q ψ),
    (X.mtV i j b k Q ψ h1 h2 hadm).QP = NX.qpOf D Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = NX.qpOf D Pq (D.ntw.pD i)

theorem pqLaw_move (h : CopyTw D D' ι e) {X : NExpTied D} {X' : NExpTied D'} (hX : ExpMove X X') {Pq Pq'} (hPq : HEq Pq Pq')
    (L : PqLaw X Pq) : PqLaw X' Pq' := by
  intro i' j b k Q' ψ' h1 h2' hA'
  have h2 : j ≤ D.R.m := by rw [h.gal.R]; exact h2'
  obtain ⟨i, Q, ψ, hi, hQ, hψ, e1, e2⟩ := (pq_copy h Pq Pq' hPq).2 i' k Q' ψ'
  obtain ⟨hA, q1, q2, -⟩ := hX i i' hi j b k Q Q' hQ ψ ψ' hψ h1 h2 h2' hA'
  obtain ⟨l1, l2⟩ := L i j b k Q ψ h1 h2 hA
  exact ⟨eq_of_heq (q1.symm.trans ((heq_of_eq l1).trans e1)), eq_of_heq (q2.symm.trans ((heq_of_eq l2).trans e2))⟩

end GlobalTheory.HeightCounting.SerCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamPOfPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique

open Formalism.IndefR.RecTie GlobalTheory.LamPrimeTransport
open scoped InnerProductSpace

set_option maxHeartbeats 4000000 in

theorem eigenvalue_of_part : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix),
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    D.what₂.lamP D.what₂.mu0 ((i : ℕ) + 1) π = R.lam3 i A3.A.μ0 c A3.A.v0 := by
  intro hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i π p hne hle
  have hC := hP.char
  have hEx := hH.aux.ex
  have hA := hH.prim.thmA
  have hGE := hH.prim.gEquiv
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hC.base.thP hEx
  have hM : R.toRealDat.IsModels := hC.base.models
  have hμ : Used0 D D.what₂.mu0 := Or.inl rfl
  have hT := Y.tied.lift
  have htup : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hread := thetaP_read R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hC.base.lev hC.base.grp hM hE Y.IL hT D.what₂.mu0 hμ i
  rw [← htup]
  refine hT.lamP D.what₂.mu0 hμ i π _ hne fun y hy' => ?_
  have hw0p : Y.mj.eW i y ∈ R.Wp3 i p := hle hy'
  have hw0e : PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) = (Y.IL.jMj i y).1 := (Y.mjRead i y).symm
  have hw0W : PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) ∈
      (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc i := by
    rw [hw0e]; exact (Y.IL.jMj i y).2
  have haS := GlobalTheory.LamPrimeTransport.adjoint_mem_base_level R F hCRD hC hEx hGE Y.tupT Y.hm Y.hTop Y.hinj i (Y.mj.eW i y) hw0W
  obtain ⟨a, ha⟩ : ∃ a, LinearMap.adjoint (R.thG i (Y.tupT D.what₂.mu0)) (Y.mj.eW i y) = a := ⟨_, rfl⟩
  rw [ha] at haS
  obtain ⟨x', hx'⟩ : ∃ x', Y.IL.jMt D.what₂.mu0 hμ i x' = ⟨R.toRealDat.extV i (Y.tupT D.what₂.mu0) a, haS⟩ :=
    ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  have hprex : pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i x') = a := by
    apply Y.hinj i (Y.tupT D.what₂.mu0)
    rw [ext_pre, hx']
  have hTx : D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = x' := by
    refine ext_inner_left ℂ fun u => ?_
    have e1 : ⟪u, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y⟫_ℂ = ⟪D.what₂.thetaP D.what₂.mu0 ((i : ℕ) + 1) u, y⟫_ℂ :=
      LinearMap.adjoint_inner_right _ _ _
    rw [e1, hT.mj i, hT.mt D.what₂.mu0 hμ i, hread u, ← hw0e]
    erw [ipWc_lift R.toRealDat hM.HW F.lv2 Y.tupT Y.hm Y.hTop Y.hinj i]
    rw [← ext_pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i u),
      ← ext_pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i x'),
      ipA_ext, hprex, ← ha, LinearMap.adjoint_inner_right]
  rw [hTx]
  apply (Y.IL.jMj i).injective
  apply Subtype.ext
  rw [hread x', hprex, ← ha, hA i (Y.tupT D.what₂.mu0) p (Y.mj.eW i y) hw0p, LinearEquiv.map_smul, Submodule.coe_smul, ← hw0e]
  rw [map_smul]
  exact map_smul _ _ _

end GlobalTheory.Mem.R3.ScalarComponentUnique
end

noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique

open Formalism.L2.Col GlobalTheory.HeckeLifts₂

set_option maxHeartbeats 4000000 in

theorem part_unique : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) π (c p : A3.fam3.base3.Ix),
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i p).comap (Y.mj.eW i) → c = p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i π c p hne hc hp
  by_contra hcp
  obtain ⟨hW, hHk⟩ := hH.prim.hecke.2
  have hu := untw_of_hH hP.char hHk
  have hd0 := disjoint_eigSum (hu.comm i) (C := SysC A3 i c) (C' := SysC A3 i p) fun y h h' =>
    h.elim fun x hx => h'.elim fun x' hx' => by
      have e : x = x' := funext fun k => D.what₂.embLL.injective ((congrFun hx.2 k).symm.trans (congrFun hx'.2 k))
      subst e
      exact (A3.liftI i A3.A.fam.μ0).excl3 (hH.sep c.1 c.2 p.1 p.2 (fun h => hcp (Subtype.ext h)) i) x hx.1 hx'.1
  have hd : Disjoint (R.Wp3 i c) (R.Wp3 i p) := hd0.mono (hu.parts i c).le (hu.parts i p).le
  have hinj : ∀ x, Y.mj.eW i x = 0 → x = 0 := fun x hx => by
    have h1 := Y.mj.eW_norm i x
    rw [hx, norm_zero] at h1
    have hn := RealDat.nP_pos (F := F.lv2) false
    have h2 : ‖x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 (show RealDat.nP F.lv2 false * ‖x‖ ^ 2 = 0 by rw [← h1]; ring) with h | h
      · exact absurd h hn.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  apply hne
  refine eq_bot_iff.2 fun x hx => ?_
  have h1 : Y.mj.eW i x ∈ R.Wp3 i c := hc hx
  have h2 : Y.mj.eW i x ∈ R.Wp3 i p := hp hx
  exact (Submodule.mem_bot ℂ).2 (hinj x ((Submodule.disjoint_def.1 hd) _ h1 h2))

end GlobalTheory.Mem.R3.ScalarComponentUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieBasisExpCoordsDetBoundedAlongArcStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieBasis_expCoords_det_bounded_along_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C := by
  first | exact @GlobalTheory.ArcNormal.lieCoord_det_bounded | exact GlobalTheory.ArcNormal.lieCoord_det_bounded | (intros; apply GlobalTheory.ArcNormal.lieCoord_det_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentConsBalancedFormOfCoordNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem linearIndependent_cons_of_coord_ne_zero :
    ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    c j ≠ 0 → j ∉ Set.range e → LinearIndependent ℤ (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) := by
  intro O _ bar X _ _ m p δ β c j e hδ hβ hcj hj
  rw [Fintype.linearIndependent_iff] at hδ ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg

  have hgB : g 0 • (β : LinearMap.BilinForm ℤ X) + ∑ k, g k.succ • (δ (e k) : LinearMap.BilinForm ℤ X) = 0 := by
    have := congrArg Subtype.val hg
    simpa [Submodule.coe_sum] using this

  let s : Fin m → ℝ := fun i => ∑ k, if e k = i then (g k.succ : ℝ) else 0
  let r : Fin m → ℝ := fun i => (g 0 : ℝ) * c i + s i
  have hind : ∀ (d : Fin 0 → ℤ) (a : Fin m → ℤ),
      ∑ i, a i • (δ i : LinearMap.BilinForm ℤ X) = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) → a = 0 := by
    intro d a h
    have h' : ∑ i, a i • δ i = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum] using h
    funext i
    exact hδ a h' i
  have hrel : ∑ i, r i • toReal (δ i : LinearMap.BilinForm ℤ X) =
      ∑ k : Fin 0, (0 : Fin 0 → ℝ) k • toReal (Fin.elim0 k : LinearMap.BilinForm ℤ X) := by
    apply LinearMap.ext₂
    intro x y
    have h1 := LinearMap.congr_fun₂ hβ x y
    have h2 := LinearMap.congr_fun₂ hgB x y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, LinearMap.add_apply, smul_eq_mul,
      LinearMap.zero_apply] at h1 h2
    have h2' : (g 0 : ℝ) * (((β : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) + ∑ k, (g k.succ : ℝ) * (((δ (e k) : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) = 0 := by
      exact_mod_cast h2
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, Finset.univ_eq_empty,
      Finset.sum_empty, LinearMap.zero_apply]
    rw [← h2', h1]
    simp only [r, s, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul, mul_assoc]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hr : r = 0 := eq_zero_of_toReal_rel hind hrel
  have hsj : s j = 0 := Finset.sum_eq_zero fun k _ => by
    rw [if_neg]
    intro h
    exact hj ⟨k, h⟩
  have hg0 : g 0 = 0 := by
    have := congrFun hr j
    simp only [r, hsj, add_zero, Pi.zero_apply] at this
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hcj
  intro i
  refine Fin.cases hg0 (fun k => ?_) i
  have := congrFun hr (e k)
  have hs : s (e k) = (g k.succ : ℝ) := by
    simp only [s]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      rw [if_neg]
      exact fun h => hk' (e.injective h)
    · simp
  simp only [r, hs, hg0, Int.cast_zero, zero_mul, zero_add, Pi.zero_apply] at this
  exact_mod_cast this

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorValueInvariantHostFixingAutStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedFormIndicatorValue_invariant_hostFixingAut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ lab : InvFun (𝓞 E)) (i : ℕ), IsTwInv H ψ → IsTwInv H lab → ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 → ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), markVal H.bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal H.bar ψ lab i n B := by
  first | exact @GlobalTheory.PolFan.Mark.markVal_twist | exact GlobalTheory.PolFan.Mark.markVal_twist | (intros; apply GlobalTheory.PolFan.Mark.markVal_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaxSimplicialCellMultiplicityLtTopOfIsPolyFanStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSimplicialCellMultiplicity_lt_top_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → maxMult H.bar q φ < ⊤ := by
  first | exact @GlobalTheory.PolFan.maxMult_lt_top | exact GlobalTheory.PolFan.maxMult_lt_top | (intros; apply GlobalTheory.PolFan.maxMult_lt_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureSumIndecomposableFaceOfAdditiveStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_sum_indecomposable_face_of_additive : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (∀ x y, InFace bar ψ lab β x → InFace bar ψ lab β y → InFace bar ψ lab β (x + y) ∧ ψ.evalZ (x + y) = ψ.evalZ x + ψ.evalZ y) → (∀ x, InFace bar ψ lab β x → ∃ n : ℤ, ψ.evalZ x = n) → (∀ x, InFace bar ψ lab β x → x ≠ 0 → 0 < ψ.evalZ x) → ∀ x, InFace bar ψ lab β x → x ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} := by
  first | exact @GlobalTheory.PolFan.Mark.mem_closure_isIndec | exact GlobalTheory.PolFan.Mark.mem_closure_isIndec | (intros; apply GlobalTheory.PolFan.Mark.mem_closure_isIndec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveThetaOfReadRelation
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Fin3

theorem emtTheta_L {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : LC hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0)
    (hY : YRel L Y) : EMtTheta Y (ysL L l) (chD L l) := by
  intro v i hv y hy n a f h
  have h2 := HEq.trans (heq_of_eq h) (hY.eW i _)
  exact (by with_unfolding_all exact ((l.c.th ((by with_unfolding_all exact (v :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (hv :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (hy :))) n ((by with_unfolding_all exact (a :))) ((by with_unfolding_all exact (f :))) ((by with_unfolding_all exact ((eq_of_heq h2) :)))) :))

end GlobalTheory.HeightCounting.Fin3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtInputOf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.JumpsSt

theorem mtInput_of {D : D7} {cf : CharFrame D} {M : MtFam D} {ch : NChoice D} (tp : TupTied D cf ch)
    {xi : D.what₂.Tup → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (h : MtInput D M (fun μ j => cf.mu0 j * xi μ) Q) (hx : tp.xi = xi) (hQ : ch.Q = Q) : MtInput D M tp.tup ch.Q := by
  subst hx hQ
  exact h

set_option maxHeartbeats 2000000 in

theorem main : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.HeightCounting.HtCard → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → JumpsCard D'.nd D'.naut := by
  intro hL _ hH
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l
  refine ⟨fun _ => ∅, fun L hB _ => ?_⟩
  obtain ⟨Sp, ⟨Au⟩, hs⟩ := hB
  let b : NBuilt hL (withLoc L) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := mtInput_of l.c.tp l.mt.mt l.c.xi_eq l.c.Q_eq, big := fun _ => ∅, L := L, Sp := Sp, Au := Au, ss := hs,
      eq := rfl }
  exact JumpsAt.jumpsCard_of_built hH b l.a.fr l.a.pht

end GlobalTheory.HeightCounting.JumpsSt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParametersParametersNonemptyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sizeData_parameterChoice : (∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧ AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧ ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) := by
  first | exact @GlobalTheory.HeightCounting.Up.SizePar.exists_params | exact GlobalTheory.HeightCounting.Up.SizePar.exists_params | (intros; apply GlobalTheory.HeightCounting.Up.SizePar.exists_params <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsPolyGrowthOfBoundedCoisotropicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_polyGrowth_of_bounded_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic | exact GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic <;> assumption)
end


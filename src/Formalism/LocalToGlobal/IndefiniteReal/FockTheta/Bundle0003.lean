import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.TraceSingleMulSingle
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.DeltaPf
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.IoExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0015

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FockTheta.NormDeltaLowOfFockDeltaLow
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Fock.Sk

namespace Formalism.IndefR.Fock.Final

theorem ccrTheta_of_drho {D : D7} (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) : CCRTheta D :=
  Formalism.IndefR.Fock.CCR.ccrTheta_of Formalism.IndefR.Fock.Alg.unitBracket hT hL hC

theorem fockNormO_of_drho {D : D7} (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) : FockNormO D :=
  Formalism.IndefR.Fock.Norm.fockNormO_of (ccrTheta_of_drho hT hL hC) Formalism.IndefR.Fock.Alg.fockNormAbs
    (Formalism.IndefR.Fock.Skew.dRhoSkew_of D hT) (Formalism.IndefR.Fock.Skew.thetaIntO D) hT

theorem fockNormO (D : D7) : FockNormO D :=
  fockNormO_of_drho (Formalism.IndefR.Fock.DRho.thetaDRho D) (Formalism.IndefR.Fock.DRho.dRhoLin D) (Formalism.IndefR.Fock.DRho.dRhoComm D)

open Formalism.IndefR.Datum in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem fockNormO_lines (D : D7) :
    ∀ (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (S T : Formalism.BasicNotions.TH.HSp D) sS sT BS BT
      (pS pT : D.what₂.Tau → ℕ), PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (Formalism.L2.Theta.ratL T S) μ 𝓕 →
      ∀ f : Formalism.IndefR.Datum.WO S T → ℂ, Formalism.IndefR.Datum.IsThetaFunO ψ S T f →
        (∀ τ, Formalism.IndefR.Datum.IsFockVacAt (Formalism.IndefR.Datum.heisO ψ S T) θ τ
          (Formalism.IndefR.Datum.cplxO (sS τ) (sT τ)) f) →
        ∀ P Q : MvPolynomial (Formalism.IndefR.Datum.FVar D T.rank S.rank) ℂ,
          ∫ w in 𝓕, Formalism.IndefR.Datum.pureTensorO ψ θ S T sS sT BS BT f P w *
              starRingEnd ℂ (Formalism.IndefR.Datum.pureTensorO ψ θ S T sS sT BS BT f Q w) ∂μ =
            Formalism.REAL.fockF P Q * ∫ w in 𝓕, f w * starRingEnd ℂ (f w) ∂μ :=
  fockNormO D (Formalism.IndefR.Eqv.lineAtExists_holds D)

end Formalism.IndefR.Fock.Final

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ParabolicAtStandardWeylElement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.FrobeniusOrbits Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Links Formalism.IndefR.Mult Finset

namespace Formalism.IndefR.Fock.KV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem tauE_injective {τ ρ : D.what₂.Tau} (h : tauE D τ = tauE D ρ) : τ = ρ :=
  D.eTau.injective (Subtype.ext (Formalism.IndefR.Conj.emb_injective h))

theorem tauE_ne_conj (τ ρ : D.what₂.Tau) : tauE D τ ≠ (starRingEnd ℂ).comp (tauE D ρ) := by
  intro h
  unfold tauE at h
  rw [Formalism.IndefR.Conj.conj_comp_emb] at h
  have e1 : (D.eTau τ).1.1.2 = ((D.eTau ρ).1 * D.R.cc).1.2 :=
    congrArg (fun g : D.R.GG => g.1.2) (Formalism.IndefR.Conj.emb_injective h)
  have hc := Formalism.IndefR.Conj.snd_side (D := D) false
  simp only [Bool.false_eq_true, if_false] at hc
  rw [show ((D.eTau ρ).1 * D.R.cc).1.2 = (D.eTau ρ).1.1.2 * (D.R.cc).1.2 from rfl] at e1
  rw [(Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2, (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2, one_mul, hc] at e1
  exact absurd e1 (by decide)

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sig_Wc (i : Fin D.R.m) (τ : D.what₂.Tau) : (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) :=
  D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _

end Formalism.IndefR.Fock.KV

end
end


import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsEtOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0039
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0038
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0049
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFwdPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0040
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0094
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0019
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GridsRichITc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsClosed
section
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsClosed

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem rhoSurj_X : Function.Surjective (AllRowsRhoX.rhoX X) := Formalism.L2.SG.Pf.RhoSurjW.reduction_map_surjective D X

theorem redKerOne_holds : RedKerOne X := redKerOne_of (X := X) (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1)

theorem etUniv_holds : EtUniv X := etUniv_of (X := X) (redKer_of (X := X) (redKerOne_holds X))

theorem etUnip_holds (k : Fin 2) (S : Set (Tup D k)) : EtUnip X k S := etUnip_of (X := X) k (AllRowsRedKer.redKerP_holds X (1 - k)) S

theorem kppShape_holds : AllRowsKpp.KppShape X := Formalism.L2.SG.Pf.AllRowsKpp.kppShape_of_fwd (X := X) (rhoSurj_X X) (Formalism.L2.SG.Pf.KppFwdPf.kppFwd_holds (X := X))

theorem etAlg_holds (S : Set (Tup2 D)) : EtAlg X S := Formalism.L2.SG.Pf.AllRowsEtAlg.etAlg_of (X := X) (rhoSurj_X X) S

theorem etOne_holds (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) : EtOne X ψ₀ := Formalism.L2.SG.Pf.AllRowsEtOne.etOne_of (X := X) (rhoSurj_X X) (kppShape_holds X) ψ₀ hψ₀

theorem isAdmIdem_cyl (k : Fin 2) (S : Set (Tup D k)) :
    X.B.I.IsAdmIdem X.B.μf X.B.g (D.host.g (1 - k)) (eT X (cyl D k S)) := isAdmIdem_eT_cyl (X := X) k S (etAlg_holds X (cyl D k S)) (etUnip_holds X k S)

theorem kcrt_g (k : Fin 2) : KCRT X.B.I (D.host.g (1 - k)) (D.host.g k) := by
  refine AllRowsKCRT.kcrt_holds X.B.I ((Nat.coprime_primes (D.host.g_prime _) (D.host.g_prime _)).2 ?_)
  fin_cases k
  · exact D.host.g_ne.symm
  · exact D.host.g_ne

def allRowsOfL (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) (hL : RowsLab X) : AllRows D :=
  allRowsOfP X ψ₀ (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1) (etOne_holds X ψ₀ hψ₀) hL

theorem admissibleCount_allRows_level (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) (hL : RowsLab X)
    {n₀ : ℕ} {Alev C₃ c₃ cb : ℝ}
    (hC1 : Formalism.MainNotions.S.CountE.CountIdempotentsClass Formalism.MainNotions.S.CountE.PCount D n₀ Alev C₃ c₃ cb) (hL6 : ConclusionL D)
    (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) (hB : CountBase X n₀ Alev C₃ cb)
    (hP : Formalism.MainNotions.N.CylinderCountFamily.PCountTie D (allRowsOfL X ψ₀ hψ₀ hL).toAt) (hAd : TieAdmG D) :
    Formalism.MainNotions.N.CylinderCountFamily.CylinderCountUniformAt D (allRowsOfL X ψ₀ hψ₀ hL).toAt n₀ Alev C₃ c₃ cb 6 := admissibleCount_allRows_partner (X := X) ψ₀ (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1)
  (etOne_holds X ψ₀ hψ₀) hL hψ₀ hC1 hL6 hg hB (fun k S => etAlg_holds X (cyl D k S)) hP hAd

end Formalism.L2.SG.Pf.AllRowsClosed
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EnergyCompactTestBound
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem energy_compact_test_bound {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) {θ : ℝ} (C : Choice T.X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie T.X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j)) (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j))
    (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j)) (cc : Fin (nfE D) → ℂ)
    (i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (T.X.Vloc u (tauE T.X e j)) (T.X.Vloc u' (tauE T.X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf T.X C u u' e j).base.π
      (towersOf T.X C u u' e j).base.z (m0E T.X C u u' e j *ᵥ nuE T.X C u' e i0' j)) (A₀ : ℝ)
    (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd Cb Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0b i0b' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
    (hpin : JointPin.PinCov (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))))
    (hBuilt : Formalism.FourierDecayAlt.D.IsBuilt (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE T.X C u' e i0') (m0E T.X C u u' e) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀) :
    (∏ v, (Formalism.FourierDecayAlt.B.normSq ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T v).base ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc v)).toReal /
        Formalism.FourierDecayAlt.D.GamLev (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.k (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.r (Formalism.FourierDecayAlt.D.kapG (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E))
          (Formalism.FourierDecayAlt.D.deG (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0) =
      (Formalism.L2.SG.SpectralTiesReal.massDataY T.X T.hb T.Y u u' X0 T.ψ sd Cb Th vR Q i0b i0b' νq).IntN := by
  have hFX : (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).FromX :=
    BaseOf.fromX T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
      (nuE T.X C u' e i0') (m0E T.X C u u' e) (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hg0 : 0 < (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.g := by
    show 0 < D.host.g 0 * D.host.g 1
    exact Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  have hZ := zhatTr_carrierOf T.X u u' e he hv C CA de de' l (gridT e l) (grid1T e l) (towersOf T.X C u u' e)
    (Tz_towersOf_base_eq_T T.X C u u' e) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1)) (nuE T.X C u' e i0') (m0E T.X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hPN := JointPin.placeNormG_of_pin (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl hpin
    (JointPinNormSt.normBridge_of_zhat _ rfl hZ) hFX hBuilt hg0
  have hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE Formalism.FourierDecayAlt.S6.rd
    rw [Int.cast_abs, one_div]
  have hk1 : 1 ≤ (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.G.k := by
    show 1 ≤ D.R.k
    have := Formalism.MainNotions.BridgeLemma.five_le_k D
    omega
  exact EnergyNF.energy_norm_bound_third_form T.hb T.Y X0 T.ψ sd Cb Th vR Q i0b i0b' νq (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl rfl
    (fun v => Tz_towersOf_base_eq_T T.X C u u' e _) rfl hrd hg0 hk1 (Formalism.L2.SG.WConst.card_places T.X) T.ψ_char T.ψ_std
    (Formalism.L2.SG.Pf.ProdConvCut2.prodConv_holds T u u') (Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds T.X u u' T.ψ) hPN

end Formalism.L2.SG.Pf.CarrierXAll
end
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0549
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0550
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0551
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVector
section
noncomputable section

namespace GlobalTheory.SmallFix

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isDetRoot_one (V : HSp D) : IsDetRoot V (1 : GA D V) (1 : (AE D)ˣ) := by
  show ((1 : (AE D)ˣ) : AE D) = _
  rw [map_one, Units.val_one]
  simp

theorem suppPl_one (ε : AF D.host.F) (V : HSp D) : SuppPl ε V (1 : GA D V) := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem suppAt_one (e : AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V (1 : GA D V) := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem inert_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : NonSplitAt D v ε) (g : GA D S) (hg : SuppPl ε S g)
    (hst : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔
      actO S T g 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    om (g, 1) f = f := by
  obtain ⟨η, hη⟩ := hη
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨om₀, h0, hv, -⟩ := GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ ΛS ΛT hS hT η hη
  obtain ⟨om₁, h1, htw⟩ := GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ ((η ^ S.rank)⁻¹ * χS) ((η ^ T.rank)⁻¹ * 1) om₀ h0
    (GlobalTheory.VacInert.hecke_quot hW.hecS h0.hecS) (GlobalTheory.VacInert.hecke_quot hW.hecT h0.hecT)
    (GlobalTheory.VacInert.resEta_quot hW.resS h0.resS) (GlobalTheory.VacInert.resEta_quot hW.resT h0.resT)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at h1
  obtain ⟨x, hx, xi, -, x1, x2⟩ := GlobalTheory.VacInert.exists_unit_root hε S g hg
  have hlat : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) ↔
      actO S T g 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) := fun u => by
    rw [GlobalTheory.VecInvInert.mem_place_iff hε.1, GlobalTheory.VecInvInert.mem_place_iff hε.1, ← hst, ← GlobalTheory.FinWeilO.actO_smul,
      (GlobalTheory.VecInvInert.act_injective g 1).eq_iff]
  have hfix : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v),
      heisO ψ S T u f = f := fun u hu => by
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hε
    have e1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε.1 hu]
    have e2 := hvac.1 (a • u)
      (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
    rwa [e1] at e2
  rw [GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ S T χS 1 om om₁ hW h1 _ f hf, htw g 1 x 1 hx (isDetRoot_one T), LinearMap.smul_apply,
    hv v ε hε g 1 hg (suppPl_one ε T) hlat f hf hfix]
  simp [hη.2.1 x xi x1 x2]

theorem local_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (frS : IsFrame βS ΛS) (frT : IsFrame βT ΛT)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (g : GA D S) (hg : Stab S βS g)
    (sg : SuppPl ε S g) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    om (g, 1) f = f := by
  have hlat := mem_latO_iff frS frT (h := (1 : GA D T)) hg.2 (Stab.one T βT).2
  by_cases hsp : ∃ e', IsSplitIdem D e' ∧ e' + cA D e' = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e', he', hb⟩ := hsp
    have := GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D ψ S T ΛS ΛT χS 1 om hW hS hT e' he' g 1 (fun i j => by rw [hb]; exact sg i j)
      (suppAt_one e' T) hlat _ _ (isDetAt_detAt e' he'.1 S g) (isDetAt_detAt e' he'.1 T 1) f hf hvac
    rw [this, splitFacO, map_one, map_one, MonoidHom.one_apply, inv_one, one_mul, Circle.coe_one, one_smul]
  · exact inert_one hW hS hT hη ⟨hε, hsp⟩ g sg hlat f hf hvac

theorem vac_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (frS : IsFrame βS ΛS) (frT : IsFrame βT ΛT)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f)
    (g : GA D S) (hg : Stab S βS g) : om (g, 1) f = f := by
  let H : Subgroup (GA D S × GA D T) :=
    { carrier := {p | om (p.1, 1) f = f}
      one_mem' := by
        change om ((1 : GA D S), (1 : GA D T)) f = f
        rw [Prod.mk_one_one, map_one, Module.End.one_apply]
      mul_mem' := fun {p q} hp hq => by
        change om ((p * q).1, (1 : GA D T)) f = f
        have e : ((p * q).1, (1 : GA D T)) = (p.1, (1 : GA D T)) * (q.1, 1) := Prod.ext rfl (mul_one 1).symm
        have hq' : om (q.1, 1) f = f := hq
        have hp' : om (p.1, 1) f = f := hp
        rw [e, map_mul, Module.End.mul_apply, hq', hp']
      inv_mem' := fun {p} hp => by
        change om (p⁻¹.1, (1 : GA D T)) f = f
        have hp' : om (p.1, 1) f = f := hp
        have e : (p⁻¹.1, (1 : GA D T)) = (p.1, (1 : GA D T))⁻¹ := Prod.ext rfl inv_one.symm
        rw [e]
        calc om (p.1, (1 : GA D T))⁻¹ f = om (p.1, (1 : GA D T))⁻¹ (om (p.1, 1) f) := by rw [hp']
          _ = f := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hcl : IsClosed (H : Set (GA D S × GA D T)) := by
    have : (H : Set (GA D S × GA D T)) = ⋂ w, {p | om (p.1, 1) f w = f w} := by
      ext p
      rw [Set.mem_iInter]
      exact funext_iff
    rw [this]
    exact isClosed_iInter fun w => isClosed_eq
      ((hW.om_cont f hf w).comp (continuous_fst.prodMk continuous_const)) continuous_const
  exact GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs D S T βS βT H hcl (fun v ε hε g' h' hg' _ sg' _ =>
    local_one hW hS hT hη frS frT hε g' hg' sg' f hf hvac) g 1 hg (Stab.one T βT)

end GlobalTheory.SmallFix

end

noncomputable section

namespace GlobalTheory.SmallFix

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
open Classical in

theorem prin_fixes_stepVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ κ ∈ prin A β Z, om (κ, 1) f = f := by
  intro D ψ θ A H χA om sA sH hθ hη hW cA' cH hrk β Z hPl βH f₀ f hfrH hv hthf κ hκ
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have dA := frameLat_isSelfDualC A
  have dH := frameLat_isSelfDualC H
  have hlev : Formalism.IndefR.Lev.finE A κ ∈ Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z) := hκ.2
  have sg : Formalism.IndefR.Lev.finE A κ ∈ Formalism.L2.DIV.St β := Formalism.L2.DIV.parLev_St hlev.1
  have sh : Formalism.IndefR.Lev.finE H 1 ∈ Formalism.L2.DIV.St βH := by rw [map_one]; exact Subgroup.one_mem _
  have h1 : om (κ, 1) f₀ = (1 : ℂ) • f₀ := by
    rw [one_smul]
    exact GlobalTheory.SmallFix.vac_one hW dA dH hη hPl.frame hfrH f₀ hf.2.theta hf.2.lat κ ⟨hκ.1, sg⟩
  have hoG := GlobalTheory.T.levelPlacesDatum_mul_right_source_level D A.rank H.rank (prinDat A Z) (fun _ => 1)
    (fun PP => Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE A κ)) (fun PP hP => Formalism.L2.DIV.parLev_g hlev.1 hP) hlev.2
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D ψ A H χA 1 om hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D ψ hW.std A H (frameLat A) (frameLat H) dA dH e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D A H (frameLat A) (frameLat H) β βH dA dH hPl.frame hfrH κ 1 sg sh) 1 1 one_ne_zero h1 (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D A H β βH κ 1 sg sh x
      have i0 : Formalism.IndefR.Datum.IsHalf e (actO A H κ⁻¹ 1⁻¹ x) ↔ Formalism.IndefR.Datum.IsHalf e x :=
        ⟨fun H' => GlobalTheory.AdelicLatMove.actO_actO_inv A H κ 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO κ 1 H',
          fun H' => GlobalTheory.SplitHecke.isHalf_actO _ _ H'⟩
      by_cases hx : Formalism.IndefR.Datum.IsHalf e x ∧ Formalism.IndefR.Datum.IsIntM (frMapO A H β βH x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), GlobalTheory.ChainOnto.StepLevLaw.omegaQ_empty,
          GlobalTheory.ChainOnto.StepLevLaw.omegaQ_empty, mul_one, mul_one]
        simp only [map_one, Formalism.L2.DIV.redFn_one, inv_one, Units.val_one, Matrix.one_mul]
        rw [hoG]
        congr 1
        rw [show (prinDat A Z).s = 0 from rfl, Finset.range_zero]
        simp only [Finset.prod_empty, Finset.prod_const_one, MonoidHom.one_apply, inv_one, mul_one]
        exact (congrArg Units.val (show (prinDat A Z).P.chi _ = 1 from rfl)).trans Units.val_one
      · beta_reduce
        rw [if_neg hx, if_neg fun H' => hx ⟨i0.1 H'.1, i1.1 H'.2⟩, mul_zero])
  rw [h2, mul_one, one_smul]

end GlobalTheory.SmallFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAtOneGluedPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem SmallPl.exists_card_withLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] :
    ∃ N : ℕ, 0 < N ∧ ∀ Q : Pair k n, (withLat Q.lat).card = N := by
  by_cases h : Nonempty (Pair k n)
  · obtain ⟨Q₀⟩ := h
    refine ⟨(withLat Q₀.lat).card, Finset.card_pos.2 ⟨Q₀, mem_withLat.2 rfl⟩, fun Q => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
    refine Finset.card_nbij' (fun P => g⁻¹ • P) (fun P => g • P) ?_ ?_ ?_ ?_
    · intro P hP
      have hP' : P.lat = g • Q₀.lat := mem_withLat.1 hP
      refine Finset.mem_coe.2 (mem_withLat.2 ?_)
      rw [Pair.smul_lat, hP', inv_smul_smul]
    · intro P hP
      have hP' : P.lat = Q₀.lat := mem_withLat.1 hP
      refine Finset.mem_coe.2 (mem_withLat.2 ?_)
      rw [Pair.smul_lat, Pair.smul_lat, hP']
    · intro P _
      exact smul_inv_smul g P
    · intro P _
      exact inv_smul_smul g P
  · exact ⟨1, one_pos, fun Q => (h ⟨Q⟩).elim⟩

theorem SmallPl.liftA_contAut {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V₀ A L S : HSp D} (o : OrthDec V₀ A L)
    (hA : CoCpt A) {χV χW : (AE D)ˣ →* Circle} {om : Om V₀ S} (hW : IsWeilDatumO ψ V₀ S χV χW om) (vA : Vol A)
    {φ : GA D A → ℂ} (hφ : IsContAut A φ) {Ξ : WO V₀ S → ℂ} (hΞ : IsThetaFunO ψ V₀ S Ξ) :
    IsContAut S fun h => liftA o om vA φ Ξ h 0 := by
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hlift : (fun h => liftA o om vA φ Ξ h 0) = fun h =>
      ∫ h₀ in vA.𝓕, φ h₀ * om (o.emb (h₀, 1), h) Ξ 0 ∂vA.μ := by
    funext h
    simp only [liftA]
    congr 1
    funext h₀
    rw [show ((0 : WO A S), (0 : WO L S)) = 0 from rfl, map_zero]
  rw [hlift]
  have jc := GlobalTheory.Unf.jointCont_all D ψ V₀ S χV χW om hW Ξ hΞ
  have hK₂c : Continuous (Function.uncurry fun (x : GA D A) (h : GA D S) => φ x * om (o.emb (x, 1), h) Ξ 0) := by
    have hmap : Continuous fun z : GA D A × GA D S => ((o.emb (z.1, 1), z.2), (0 : WO V₀ S)) :=
      ((o.continuous_emb.comp (continuous_fst.prodMk continuous_const)).prodMk continuous_snd).prodMk
        continuous_const
    exact (hφ.2.comp continuous_fst).mul (jc.comp hmap)
  have hK₂a : ∀ γ ∈ GQ A, ∀ (x : GA D A) (h : GA D S),
      φ (γ * x) * om (o.emb (γ * x, 1), h) Ξ 0 = φ x * om (o.emb (x, 1), h) Ξ 0 := by
    intro γ hγ x h
    have e : o.emb (γ * x, 1) = o.emb (γ, 1) * o.emb (x, 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    have hq := GlobalTheory.Unf.om_rat_mul D ψ V₀ S _ _ om hW Ξ hΞ (o.emb (γ, 1))
      (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (o.emb (x, 1)) h 0
    rw [one_mul] at hq
    rw [hφ.1 γ hγ x, e, hq, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨fun γ hγ h => ?_,
    (GlobalTheory.CocompactParam.continuous_integral_param D A hA vA (GA D S) _ hK₂c hK₂a).2.1⟩
  dsimp only
  congr 1
  funext x
  have hq := GlobalTheory.Unf.om_rat_mul D ψ V₀ S _ _ om hW Ξ hΞ 1 (one_mem _) γ hγ (o.emb (x, 1)) h 0
  rw [one_mul] at hq
  rw [hq, Matrix.mul_zero, Matrix.zero_mul]

theorem SmallPl.integral_sum_translates {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hS : CoCpt S)
    {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hW : IsWeilDatumO ψ S T χS χT om) (vS : Vol S) {Φ₂ : WO S T → ℂ}
    (hθ : IsThetaFunO ψ S T Φ₂) {ι : Type} (s : Finset ι) (b : ι → GA D S) (hfix : ∀ i ∈ s, om (b i, 1) Φ₂ = Φ₂)
    {G : GA D S → ℂ} (hG : IsContAut S G) (c : ℂ) (h' : GA D T) :
    (∫ h in vS.𝓕, om (h, h') Φ₂ 0 * (c * ∑ i ∈ s, G (h * b i)) ∂vS.μ) =
      c * s.card * ∫ h in vS.𝓕, om (h, h') Φ₂ 0 * G h ∂vS.μ := by
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hHc : Continuous fun h => om (h, h') Φ₂ 0 :=
    (hW.om_cont Φ₂ hθ 0).comp (continuous_id.prodMk continuous_const)
  have hHa : ∀ γ ∈ GQ S, ∀ h, om (γ * h, h') Φ₂ 0 = om (h, h') Φ₂ 0 := by
    intro γ hγ h
    have hq := GlobalTheory.Unf.om_rat_mul D ψ S T _ _ om hW Φ₂ hθ γ hγ 1 (one_mem _) h h' 0
    rw [one_mul] at hq
    rw [hq, Matrix.mul_zero, Matrix.zero_mul]
  have hHb : ∀ i ∈ s, ∀ h, om (h * b i, h') Φ₂ 0 = om (h, h') Φ₂ 0 := by
    intro i hi h
    have : ((h * b i, h') : GA D S × GA D T) = (h, h') * (b i, 1) := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [this, map_mul, Module.End.mul_apply, hfix i hi]
  obtain ⟨K, hK⟩ : ∃ K : GA D S → ℂ, K = fun h => om (h, h') Φ₂ 0 * G h := ⟨_, rfl⟩
  have hKc : Continuous K := hK ▸ hHc.mul hG.2
  have hKa : ∀ γ ∈ GQ S, ∀ h, K (γ * h) = K h := fun γ hγ h => by
    rw [hK]
    dsimp only
    rw [hHa γ hγ h, hG.1 γ hγ h]
  have hint : ∀ i ∈ s, IntegrableOn (fun h => c * K (h * b i)) vS.𝓕 vS.μ := by
    intro i _
    refine (GlobalTheory.CocompactParam.continuous_integral_param D S hS vS Unit (fun h _ => c * K (h * b i)) ?_ ?_).1 ()
    · exact (continuous_const.mul (hKc.comp (continuous_mul_right _))).comp continuous_fst
    · intro γ hγ h _
      rw [mul_assoc γ h, hKa γ hγ]
  calc (∫ h in vS.𝓕, om (h, h') Φ₂ 0 * (c * ∑ i ∈ s, G (h * b i)) ∂vS.μ)
      = ∫ h in vS.𝓕, ∑ i ∈ s, c * K (h * b i) ∂vS.μ := by
        refine integral_congr_ae (ae_of_all _ fun h => ?_)
        dsimp only
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hK]
        dsimp only
        rw [hHb i hi h]
        ring
    _ = ∑ i ∈ s, c * ∫ h in vS.𝓕, K h ∂vS.μ := by
        rw [integral_finset_sum _ hint]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S vS.μ vS.𝓕 vS.haar vS.fund K hKa]
    _ = _ := by
        rw [hK, Finset.sum_const, nsmul_eq_mul]
        ring

theorem smallOne : ∀ D : D7, SmallOne D := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ hχ
  obtain ⟨r₀, e, hr₀, hsrc⟩ := GlobalTheory.T.gluedPlaceSourceConstant_proof D k p n n' q χ hχ
  obtain ⟨N, hN0, hN⟩ := SmallPl.exists_card_withLat k n
  refine ⟨r₀ * N, e, mul_pos hr₀ (Nat.cast_pos.2 hN0), ?_⟩
  intro ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hW₁ hWT hV hW hχS hχT vA vS vT α α₀ β hsum P Q s L₁ L₂ L₂' L₃
    f₁ Ξ Ξ' Φ₂ hΞ hΞ' hsd₂ hsd₃ hlat hvac φ₀ hφ₀ F hF
  obtain ⟨φ, hφ, rfl⟩ := hφ₀
  obtain ⟨χr, hχr⟩ : ∃ χr, χr = resChar χ hχ q := ⟨_, rfl⟩
  rw [← hχr] at hΞ' hsrc ⊢
  have hob := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hW₁.std V₀ S α₀ β L₁ L₂ hΞ.1 hΞ.2.1 f₁ hΞ.2.2.1
  have hsb := GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts k n n'

  obtain ⟨Ξ'', hΞ'', -⟩ := hob.1 (tensCol (phiOne P (s • Q)) (charInd χr (s • Q)))
    (hsb.1 _ _ (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _) (hsb.2.2 _ _))
  have hram := (GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k p n' q χ hχ χr hχr s A α P).2.1 φ hφ
  have hram1 := ((GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k p n' q χ hχ χr hχr 1 A α P).2.1 φ hφ).1
  rw [map_one, Module.End.one_apply] at hram1

  have hmove : liftA o om₁ vA (FFStar q χr φ P) Ξ'' = liftA o om₁ vA (sOp α P q χr s (φ P)) Ξ' := by
    obtain ⟨lS, hlS, hθ⟩ := GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift D k p n n' ψ V₀ A L S o ζ hζ hA vA χV χW om₁ hW₁ α α₀ β hsum
    obtain ⟨θ, hθv, hθe⟩ := hθ L₁ L₂ f₁ hΞ.1 hΞ.2.1 hΞ.2.2.1
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n' k) P (s • P)
    have hgs : g ∈ latStab P.lat := by
      change g • P.lat = P.lat
      rw [← Pair.smul_lat, hg, Pair.dia_lat]
    have h1 := hθe g ⟨FFStar q χr φ P, hram1.2.2 P⟩ _ hΞ''.2.2.2.1
    have b2 : (fun x => tensCol (phiOne P (s • Q)) (charInd χr (s • Q)) (x * (SrcGl.blk g).val)) =
        tensCol (phiOne P Q) (charInd χr (s • Q)) := by
      funext x
      rw [SrcGl.tensCol_mul_blk]
      congr 1
      funext x₀
      rw [← SrcGl.phiOne_smul_left, hg, phiOne_dia]
    rw [b2, hθv _ _ _ hΞ', hθv _ _ _ hΞ'', GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n' P.lat inferInstance g hgs lS (hlS hW), Units.val_one,
      inv_one, one_smul, SrcGl.caRep_apply] at h1
    rw [hram.2, dia_apply, ← hg, hram1.1 g P]
    exact h1.symm

  obtain ⟨lS, lT, -, hlT, -, -, hlin⟩ := GlobalTheory.T.linearModel_splitPlace_characterEquivariance D k p q ψ V₀ S χV χW om₁ hW₁
  choose gs hgs using fun Q' : Pair k n => MulAction.exists_smul_eq (GL n k) (s • Q) Q'
  have hstab : ∀ Q' ∈ withLat Q.lat, gs Q' • Q.lat = Q.lat := fun Q' hQ' => by
    rw [← Pair.dia_lat s Q, ← Pair.smul_lat, hgs, mem_withLat.1 hQ', Pair.dia_lat]
  have hfix : ∀ Q' ∈ withLat Q.lat, omT (β.gl (gs Q'), 1) Φ₂ = Φ₂ := by
    intro Q' hQ'
    obtain ⟨-, -, -, hfr, -, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β
    obtain ⟨Λ', -, hΛ', hK⟩ := hfr L₂' hsd₂
    have hΛQ : Λ' = Q.lat := Submodule.ext fun x => (hΛ' x).trans (hlat x).symm
    have hk1 : InK S L₂' (· = p.v) (β.gl (gs Q')) := (hK _).2 (hΛQ ▸ hstab Q' hQ')
    have hk2 : InK T L₃ (· = p.v) 1 := ⟨one_mem _, fun y _ => by simp [Formalism.L2.Theta.mt]⟩
    exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ S T χS χT omT hWT L₂' L₃ hsd₂ hsd₃ (· = p.v)
      (fun v hv => by subst hv; exact ⟨GlobalTheory.T.isTameFinitePlaceHermitian_all D _, hχS, hχT⟩) Φ₂ hvac _ _ hk1 hk2
  have hOver : ∀ Q' ∈ withLat Q.lat, Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q') (charInd χr Q'))
      (om₁ (1, β.gl (gs Q')) Ξ'') := by
    intro Q' hQ'
    have h0 := hlin n (n' ⊕ Fin 1) α₀ β L₁ L₂ f₁ _ Ξ'' hΞ'' 1 (gs Q')
    rw [GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n Q.lat inferInstance (gs Q') (hstab Q' hQ') lT (hlT hV)] at h0
    convert h0 using 1
    · funext x
      simp only [map_one, Units.val_one, one_mul, Matrix.mul_one]
      rw [tensCol_phiOne_charInd_smul, hgs]
    · rw [map_one]
  have hfun := hsrc ψ V₀ A L S o ζ hζ hA vA χV χW om₁ hW₁ hV hW α α₀ β hsum P Q.lat L₁ L₂ f₁ Ξ
    (fun Q' => om₁ (1, β.gl (gs Q')) Ξ'') hΞ hOver φ hφ
  have hterm : ∀ (f : GA D A → ℂ) b h,
      liftA o om₁ vA f (om₁ (1, b) Ξ'') h 0 = liftA o om₁ vA f Ξ'' (h * b) 0 := by
    intro f b h
    simp only [liftA]
    congr 1
    funext h₀
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hG := SmallPl.liftA_contAut o hA hW₁ vA (hram1.2.2 P) (hob.2.1 _ _ hΞ'').1
  simp only [smallPair]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun h' => ?_)
  dsimp only
  have key := SmallPl.integral_sum_translates hS hWT vS hvac.1 (withLat Q.lat) (fun Q' => β.gl (gs Q')) hfix hG
    ((r₀ : ℂ) * chrPow χW (p.idele q.unit) e) h'
  rw [hfun, ← hmove]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hterm]
  rw [key, hN]
  push_cast
  ring

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairStabiliserMemChartLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPair_stabiliser_mem_chartLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → (β j i).gl g ∈ A.U j b := by
  first | exact @GlobalTheory.AdForm.StabLev.stab_mem_level | exact GlobalTheory.AdForm.StabLev.stab_mem_level | (intros; apply GlobalTheory.AdForm.StabLev.stab_mem_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelNormSqModerateGrowthLargeStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_normSq_moderateGrowth_large : GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧ GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  first | exact @GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big | exact GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big | (intros; apply GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelSplitPlacesEqJetClassicalThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_splitPlaces_eq_jet_classicalTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ s : ℂ, (∀ f, IsHol θ S T ψ f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP S T hS hT s (xiN θ S T hS hT δ sc f) P) → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ c : ℕ, 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ, (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Φ (actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r)) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ), (xiN θ S T hS hT δ sc (om (g, h) vac) = fun z => κ * E z) → ∀ P, thetaKO om g h (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) w P) = κ * jetP S T hS hT s (thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E) P := by
  first | exact @GlobalTheory.KJInf.CoreG.thetaKernel_eq_jet_thC | exact GlobalTheory.KJInf.CoreG.thetaKernel_eq_jet_thC | (intros; apply GlobalTheory.KJInf.CoreG.thetaKernel_eq_jet_thC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsVolumeConstantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_exists_volume_constant : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∃ VT : ℂ, VT ≠ 0 ∧ ∀ t (J : QJ a t), J.Reads → J.VolT VT := by
  first | exact @GlobalTheory.TopVol.main | exact GlobalTheory.TopVol.main | (intros; apply GlobalTheory.TopVol.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_bound : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (J : ∀ t, QJ a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (S : ∀ t j, GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ), (∀ t α, s t 0 α = 1) →
    (∀ t, ∃ w, PinChL (pk W) a.g (colOf a J kom dd S s cV cK cP t) a.c₀ (J t).A (J t).ι w) →
    GlobalTheory.MiTop.ChartZero (a.fam row (colOf a J kom dd S s cV cK cP)) := by
  first | exact @GlobalTheory.Fam.chartZero_colOf | exact GlobalTheory.Fam.chartZero_colOf | (intros; apply GlobalTheory.Fam.chartZero_colOf <;> assumption)
end


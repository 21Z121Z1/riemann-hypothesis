import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0589
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationIdentity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0577
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem mainX_of_lawsX (hR : GlobalTheory.Published.CuspRapidDecay) (hH : GlobalTheory.Published.HarishChandraModules) :
    ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), LawsX t → MainX t := by
  intro D c 𝒯 t L
  have hTwo : TwoX t :=
    GlobalTheory.T.seeSawDoubleLiftCombination_of_laws D c 𝒯 t (GlobalTheory.T.seeSawWeilBiAction_commutes D) (GlobalTheory.T.centralEigenTheta_isFockVector_bounded_degree D) (GlobalTheory.SeeSaw.LiftSumProof.liftSum D)
      L.com L.tup L.real L.ker L.rd
  have hRap : RapidVal D := GlobalTheory.SeeSaw.rapidVal_of_cuspRapidDecay hR D
  have hStep : StepX t :=
    GlobalTheory.T.seeSaw_doubleStep_linearRelations_periods hH D c 𝒯 t (GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D (GlobalTheory.Desc.weil_data_descend D)) hRap
      (GlobalTheory.ValMoveProof.valMove D) (GlobalTheory.SeeSaw.perSum_all D) L.com L.tup L.loc L.val hTwo L.rd
  have hLast : LastX t :=
    GlobalTheory.T.seeSaw_lastTwoSteps_transport_linear_relations hH D c 𝒯 t hRap L.com L.tup L.last hTwo L.per L.rd
  exact GlobalTheory.SeeSaw.mainX_of_stepX_lastX D c 𝒯 t L.tup hStep hLast

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallVectorCoefficientVanishesOffPrincipalLevel
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

open Classical

namespace GlobalTheory.Core.Rk.Exh.SmallSupp

theorem selfDual_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem wcoef_eq_zero_off_prin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef om ν 𝓕 f f g = 0 := by
  intro D ψ θ A H χA om sA sH _hθ _hη hW _hcA _hcH hrank β Z hP βH f₀ f hβH hvec hthf ν 𝓕 hν g hg hnot
  have sdA := selfDual_frameLat A
  have sdH := selfDual_frameLat H
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  have hQ : (prinDat A Z).Q = ∅ := rfl
  have hPg : (prinDat A Z).Pg = Z := rfl
  have hint : ∀ v, (∀ PP ∈ (prinDat A Z).Pg, PP.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig A.gram (frameLat A) v := by
    intro v hv
    apply hg v
    intro hmem
    simp only [under, Finset.mem_image] at hmem
    obtain ⟨PP, hPP, hPPv⟩ := hmem
    exact hv PP (hPg ▸ hPP) hPPv
  have hsupp := fun x hx => by_contra fun h => hnot
    (GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero D A H (frameLat A) β βH (prinDat A Z) (fun _ => 1) (fun _ => 1) e sdA hP.frame hrank hQ he g hint x hx h)
  have hsb := GlobalTheory.T.thetaChainStep_finiteDatum_isSchwartzBruhat_half D A H (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) (fun _ => 1)
    ((prinDat A Z).Pg ∪ ∅) e sdA sdH hP.frame hβH he
  obtain ⟨n, a, y, -, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D ψ A H hW.std (frameLat A) (frameLat H) sdA sdH
    ((prinDat A Z).Pg ∪ ∅) e he f₀ _ f hsb hth g hsupp
  exact GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D ψ A H χA 1 om hW ν 𝓕 hν f hthf g n a y h1 h2

end GlobalTheory.Core.Rk.Exh.SmallSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumEqMulHalves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DatumHalves

variable {D : D7}

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  simp

theorem omegaG_of_empty {a b : ℕ} (L : LevDat D.host.E ℂ a) (hL : L.Pg = ∅) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaG L χj y = 1 := by
  have hn : ∀ PP, PP ∉ L.Pg := fun PP h => Finset.notMem_empty PP (hL ▸ h)
  haveI : IsEmpty ↥L.Pg := ⟨fun PP => hn PP.1 PP.2⟩
  have h1 : ∀ g : G0 L.Pg L.r, g = 1 := fun g => funext fun PP => isEmptyElim PP
  have h2 : ∀ g : L.P.H, L.P.chi g = 1 := fun g => by
    rw [show g = 1 from Subtype.ext (h1 _), map_one]
  unfold omegaG
  rw [dif_pos ⟨fun PP h => absurd h (hn PP), fun PP => isEmptyElim PP, fun PP => isEmptyElim PP, fun PP => isEmptyElim PP,
    by rw [h1 (fun PP => _)]; exact L.P.H.one_mem⟩, h2, Fintype.prod_empty, Fintype.prod_empty]
  simp

theorem omegaG_datY {n b : ℕ} (r t j : ℕ) (hr : r ≤ n) (Pg Q Q' : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin n) (kP PP)) :
    omegaG (datY n r t j hr Pg Q P χ ξ Frm.B) χj y = omegaG (datY n r t j hr Pg Q' P χ ξ' Frm.B) χj y := rfl

theorem isHalf_smul {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {S T : HSp D} (x : WO S T) :
    IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]

set_option maxHeartbeats 800000 in

theorem stepDatum_eq_mul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (eG eQ : AE D), IsIdemSum eG Pg → IsIdemSum eQ Q → eG * eQ = 0 → ∀ x : WO S T, (if IsHalf (eG + eQ) x ∧ IsIntM (frMapO S T βS βT x) then omegaG (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q (datY S.rank r t j hr Pg Q P χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) = (if IsHalf eG (eG • x) ∧ IsIntM (frMapO S T βS βT (eG • x)) then omegaG (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eG • x))) * omegaQ ∅ (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO S T βS βT (eG • x))) else 0) * (if IsHalf eQ (eQ • x) ∧ IsIntM (frMapO S T βS βT (eQ • x)) then omegaG (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eQ • x))) * omegaQ Q (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT (eQ • x))) else 0) * (if IsHalf (eG + eQ) x then 1 else 0) := by
  intro D S T βS βT r t j hr Pg Q P χ χj ξ eG eQ hG hQ _ x
  obtain ⟨iG, rG⟩ := GlobalTheory.InnerSteps.resS_idemSum hG
  obtain ⟨iQ, rQ⟩ := GlobalTheory.InnerSteps.resS_idemSum hQ
  have hsm : ∀ e : AE D, frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x :=
    fun e => GlobalTheory.RedHalfDrop.frMapO_smul_eq βS βT e x
  have hhG : IsHalf eG (eG • x) := isHalf_smul hG x
  have hhQ : IsHalf eQ (eQ • x) := isHalf_smul hQ x
  by_cases hx : IsHalf (eG + eQ) x
  swap
  · rw [if_neg hx, if_neg (fun h => hx h.1), mul_zero]
  have hxx : (eG + eQ) • x = x := funext fun a => funext fun b => hx a b
  have hNs := hsm (eG + eQ)
  rw [hxx, RingHom.map_add, add_smul] at hNs
  rw [if_pos hx, hsm, hsm]
  generalize frMapO S T βS βT x = N at hNs ⊢
  by_cases hI : IsIntM N
  · have iGN : IsIntM (toEAf D eG • N) := fun a b => mul_mem iG (hI a b)
    have iQN : IsIntM (toEAf D eQ • N) := fun a b => mul_mem iQ (hI a b)
    have e1 := GlobalTheory.PlaceDatum.omegaG_congr (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj
      (fun PP => redM PP (toEAf D eG • N)) (fun PP => redM PP N)
      (fun PP hPP => GlobalTheory.LocSuppTw.redM_smul_of_res iG PP (rG PP hPP) hI)
    have e2 := GlobalTheory.PlaceDatum.omegaQ_congr Q r ξ 1 (fun PP => redM PP (toEAf D eQ • N)) (fun PP => redM PP N)
      (fun PP hPP => GlobalTheory.LocSuppTw.redM_smul_of_res iQ PP (rQ PP hPP) hI)
    rw [if_pos (And.intro hx hI), if_pos (And.intro hhG iGN), if_pos (And.intro hhQ iQN), omegaQ_empty,
      omegaG_of_empty (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) rfl, e1, mul_one, mul_one, one_mul,
      omegaG_datY r t j hr Pg Q ∅ P χ ξ (fun _ => 1)]
    exact congrArg _ e2.symm
  · rw [if_neg (fun h : IsHalf (eG + eQ) x ∧ IsIntM N => hI h.2)]
    by_cases h1 : IsIntM (toEAf D eG • N)
    · have h2 : ¬ IsIntM (toEAf D eQ • N) := fun h2 => hI fun a b => by
        have e : N a b = (toEAf D eG • N) a b + (toEAf D eQ • N) a b := congrFun (congrFun hNs a) b
        exact e.symm ▸ Subring.add_mem _ (h1 a b) (h2 a b)
      rw [if_neg (fun k : IsHalf eQ (eQ • x) ∧ IsIntM (toEAf D eQ • N) => h2 k.2), mul_zero, zero_mul]
    · rw [if_neg (fun k : IsHalf eG (eG • x) ∧ IsIntM (toEAf D eG • N) => h1 k.2), zero_mul, zero_mul]

end GlobalTheory.DatumHalves
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCoefVanishesOffLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical

namespace GlobalTheory.ChainOnto.CoefSuppPf

theorem coefSupp : ∀ D : D7, CoefSupp D := by
  intro D _hgap c hc k _hk s s' hs hs' p hp m X hX φ g hg hnot
  obtain ⟨ξ, f₀, hvec⟩ := hp.vec
  have hthf : IsThetaFunO c.ψ s.V s'.V p.f := GlobalTheory.VecTheta.isThetaFunO_stepVec hvec
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  obtain ⟨hr, ξL, hL⟩ := hs.lev
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hrank : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  have hint : ∀ v, (∀ PP ∈ s.L.Pg, PP.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v := by
    intro v hv
    apply hg v
    intro hmem
    simp only [Com.S, Finset.mem_image] at hmem
    obtain ⟨PP, hPP, hPPv⟩ := hmem
    exact hv PP (hPg ▸ hPP) hPPv
  have hsupp := fun x hx => by_contra fun h => hnot
    (GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero D s.V s'.V s.Λ s.β s'.β s.L (c.chi (k + 1)) ξ e hs.selfDual hs.frame hrank hQ he g hint x hx h)
  have hsb := GlobalTheory.T.thetaChainStep_finiteDatum_isSchwartzBruhat_half D s.V s'.V s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ξ (s.L.Pg ∪ ∅) e
    hs.selfDual hs'.selfDual hs.frame hs'.frame he
  obtain ⟨n, a, y, hy, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D c.ψ s.V s'.V hc.std s.Λ s'.Λ hs.selfDual hs'.selfDual
    (s.L.Pg ∪ ∅) e he f₀ _ p.f hsb hth g hsupp
  obtain ⟨H1, -⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hc.std hc.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n a y (fun i => (hy i).1) φ
  obtain ⟨H2, H0⟩ := GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D c.ψ c.θ s.V s'.V hc.std hc.inf (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f hthf
    n (fun i => conj (a i)) (fun i => actO s.V s'.V g⁻¹ 1 (-(y i))) (fun i => (hy i).2) φ
  have R1 : ∑ i, a i • heisO c.ψ s.V s'.V (y i) (p.pt φ) = p.pt φ := by
    show ∑ i, a i • heisO c.ψ s.V s'.V (y i) (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H1, h1]
    rfl
  have R2 : ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i))) (p.pt φ) = 0 := by
    show ∑ i, conj (a i) • heisO c.ψ s.V s'.V (actO s.V s'.V g⁻¹ 1 (-(y i)))
      (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) p.f φ) = _
    rw [H2, h2, H0]
  exact GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hp.weil m X hX (p.pt φ) (hp.theta φ) g n a y R1 R2

end GlobalTheory.ChainOnto.CoefSuppPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_readsStd_of_readsLow_of_allTrue : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (commOf (pk W) u a.g).Is → ∀ t (J : QJ a t), J.ReadsLow → ∃ J' : QJ a t, J'.ReadsStd := by
  first | exact @GlobalTheory.PenChart.exists_readsStd | exact GlobalTheory.PenChart.exists_readsStd | (intros; apply GlobalTheory.PenChart.exists_readsStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryReductionLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamTraceChi

set_option maxHeartbeats 2000000 in

theorem trace_chi : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ hy : (y : GL _ _) ∈ (F0 W u).cls0.lev.U, (((F0 W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) * rChi W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hT' row col hc κ hκ y e hy
  have hm := (GlobalTheory.T.true_geometry_local_data W hA u a ha hT' row col hc κ hκ y e).1 hy
  obtain ⟨hg, hr⟩ := rChi_eq_chi W hm
  obtain ⟨x, hx, hc'⟩ := GlobalTheory.T.true_geometry_final_bound W hA u a ha hT' row col hc κ hκ y e hy
  have hl := ((ha.tie row col).2.lev _).2 hg x hx
  rw [hr, hl, Units.coe_prod]
  exact hc'

end GlobalTheory.FamTraceChi
end
end


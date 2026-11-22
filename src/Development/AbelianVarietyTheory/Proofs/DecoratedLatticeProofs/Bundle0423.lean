import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSupportSplitPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0406
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompact
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.KComm

variable {D : D7}

theorem comm_of_unitary_isom {m : ℕ} {u J : Matrix (Fin m) (Fin m) ℂ} (hu : uᴴ * u = 1) (hJ : uᴴ * J * u = J) :
    u * J = J * u := by
  have hu' : u * uᴴ = 1 := mul_eq_one_comm.1 hu
  calc u * J = u * (uᴴ * J * u) := by rw [hJ]
    _ = (u * uᴴ) * J * u := by simp only [Matrix.mul_assoc]
    _ = J * u := by rw [hu', Matrix.one_mul]

theorem compAt_K_comm (θ : InfFam D) (hθ : IsInfFam θ) (n : ℕ) (k : G D n) (hk : k ∈ K D n) (τ : D.what₂.Tau) :
    compAt θ τ (mat k) * blk4 0 1 (-1) 0 = blk4 0 1 (-1) 0 * compAt θ τ (mat k) := by
  have e1 : compAt θ τ (mat k) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = AdelicU.infProj (embOverOf D τ) := AdelicU.eq_infProj hθ (embOverOf D τ) rfl
  have hk' : k ∈ AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (AdelicU.mem_levelAll.1 hk').2 (placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  have hiso := (AdelicU.archEquiv (Jst D n) (isCMExt_host D) (embOverOf D τ)
    (AdelicU.projArch D.sp.cm.sig (Jst D n) (placeOf D τ) k)).2
  have hiso' : (compAt θ τ (mat k))ᴴ * (Jst D n).map (embOverOf D τ).1 * compAt θ τ (mat k) =
      (Jst D n).map (embOverOf D τ).1 := by
    rw [e1, e2, AdelicU.infMat_infProj (Jst D n) (isCMExt_host D)]
    exact hiso
  rw [Jst, GlobalTheory.CartanPt.blkJ_map] at hiso'
  exact comm_of_unitary_isom hunit hiso'

end GlobalTheory.StdUnn.KComm

namespace GlobalTheory.StdUnn.KComm

theorem exists_stdInv_comm_K : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ θ : InfFam D, IsInfFam θ → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ k : GA D (dblSp A), κ k ∈ K D A.rank → ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * s' τ = s' τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  intro D A μ hμ κ hκ θ hθ
  obtain ⟨k₀, -, hk₀⟩ := GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv D θ hθ A.rank μ hμ
  have hch : ∀ g τ, (Tm A μ).map (tauE D τ) * compAt θ τ (mat (κ g)) =
      compAt θ τ (Formalism.L2.Theta.mt (dblSp A) g) * (Tm A μ).map (tauE D τ) := by
    intro g τ
    have h2 := congrArg (compAt θ τ) (hκ g)
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, hr] at h2
    exact h2
  refine ⟨fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀)), fun τ => ?_, fun k hk τ => ?_⟩
  · have h := hch (κ.symm k₀) τ
    rw [κ.apply_symm_apply, hk₀] at h
    exact h.symm
  · dsimp only
    set T := (Tm A μ).map (tauE D τ) with hTdef
    have hT : IsUnit T.det := by
      have h := (GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ).2.1.map (tauE D τ)
      rwa [RingHom.map_det] at h
    set X := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)
    set S := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))
    set U := compAt θ τ (mat (κ k))
    have hX : T * U = X * T := hch k τ
    have hS : T * stdInv A.rank μ τ = S * T := by
      have h := hch (κ.symm k₀) τ
      rw [κ.apply_symm_apply, hk₀] at h
      exact h
    have hU : U * stdInv A.rank μ τ = stdInv A.rank μ τ * U := by
      rw [stdInv, Matrix.mul_smul, Matrix.smul_mul, compAt_K_comm θ hθ A.rank (κ k) hk τ]
    have key : X * S * T = S * X * T := by
      calc X * S * T = X * (T * stdInv A.rank μ τ) := by rw [hS, Matrix.mul_assoc]
        _ = T * U * stdInv A.rank μ τ := by rw [hX, Matrix.mul_assoc]
        _ = T * stdInv A.rank μ τ * U := by rw [Matrix.mul_assoc, hU, Matrix.mul_assoc]
        _ = S * X * T := by rw [hS, Matrix.mul_assoc, hX, Matrix.mul_assoc]
    have h2 := congrArg (· * T⁻¹) key
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.mul_one] using h2

end GlobalTheory.StdUnn.KComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardLocalisationWeilDatumInertPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertFrameLoc

set_option maxHeartbeats 800000 in

theorem exists_isStd_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ (∀ m : M, IsThetaFunO ψ S T m) ∧ ∀ x, ∃ u : WO S T, ∀ m : M, ((ρ x m : M) : WO S T → ℂ) = heisO ψ S T u m := by
  intro D ψ S T χS χT om hW v w h hw uS uT c ϖ eS eT hU hcS hcT f hf hf0
  obtain ⟨hconj, ⟨aS, haS, gS, eSa⟩, kSc⟩ := hcS
  obtain ⟨-, ⟨aT, haT, gT, eTa⟩, kTc⟩ := hcT
  obtain ⟨k, hk⟩ := GlobalTheory.InertLoc.exists_isGen D w
  have h2 := GlobalTheory.T.valued_two_eq_one_inertPlace_cmField D v w hw
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := GlobalTheory.InertLoc.exists_delta_psi hU h2 (thW ψ hw h (k * c k))
    (GlobalTheory.T.inert_place_local_character_conjugation_inverse D ψ v w hw h c k hconj hU.1) (GlobalTheory.T.inertPlace_localTraceCharacter_conductor_integers D ψ v w hw h c ϖ k hW.std hconj hU hk)
  have hadd : ∀ x y, uPt hw h k aS aT (x + y) = uPt hw h k aS aT x + uPt hw h k aS aT y := uPt_add
  have hMθ : spanT ψ (uPt hw h k aS aT) f ≤ GlobalTheory.FinWeilO.thetaSub ψ S T := Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    exact GlobalTheory.FinTranslate.isTheta_heisO_fin hW.std.1 (map_infPart_uPt (hw := hw) (h := h) (k := k) (aS := aS) (aT := aT) x) hf.1)
  let π : GU c S.rank × GU c T.rank →* Module.End ℂ (WO S T → ℂ) :=
    om.comp (((embV S v).comp eS.symm.toMonoidHom).prodMap ((embV T v).comp eT.symm.toMonoidHom))
  have hπ : ∀ p m, π p m = om (embV S v (eS.symm p.1), embV T v (eT.symm p.2)) m := fun _ _ => rfl
  have hstab : ∀ p, ∀ m ∈ spanT ψ (uPt hw h k aS aT) f, π p m ∈ spanT ψ (uPt hw h k aS aT) f := fun p m hm =>
    mem_spanT_of (fun y => by
      rw [hπ, hW.om_heis _ _ _ _ hf.1, GlobalTheory.T.local_group_action_inert_supported_points_frames]
      exact heis_mem_spanT hadd _
        (GlobalTheory.T.weilRep_latticeVacuum_mem_span_inertTranslates D ψ S T χS χT om hW v w hw h uS uT c ϖ k aS aT hU hconj hk haS haT gS gT f hf _ _)) hm
  have hint2 : (2⁻¹ : w.adicCompletion D.host.E) ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := (GlobalTheory.SphTheta.half h2).2
  have hvac : ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E),
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → heisO ψ S T (uPt hw h k aS aT x) f = f := fun x hx => by
    have h1 := hf.2.1 _ (GlobalTheory.T.inert_supported_point_integral_frames_mem_lattice D v w hw h S T k aS aT hk haS haT ((2⁻¹ : w.adicCompletion D.host.E) • x)
      fun i j => mul_mem hint2 (hx i j))
    rwa [two_nsmul, ← uPt_add, GlobalTheory.InertLoc.half_add_half] at h1
  have hfM : f ∈ spanT ψ (uPt hw h k aS aT) f := self_mem_spanT uPt_zero
  have dict := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have unr : ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → GlobalTheory.Hk3.UnrPl w χ := fun χ hχ =>
    dict.2.1 χ fun w' hw' => by rw [(GlobalTheory.LFun.InertChart.under_eq_iff hw w').1 hw']; exact hχ
  have hfix := GlobalTheory.ConjVacFix.vacFix_of_unrPl ψ S T χS χT om w hW (unr χS uS) (unr χT uT)
  refine ⟨δ, ψ', spanT ψ (uPt hw h k aS aT) f, rhoT ψ (uPt hw h k aS aT) f hadd, omT ψ (uPt hw h k aS aT) f π hstab,
    ⟨f, hfM⟩, ⟨⟨hU, GlobalTheory.InertLoc.odd_of_v_two hU h2, antiG_mem _, antiG_mem _, antiJ_herm c _, antiJ_herm c _, hδ, p1, p2,
      ?_, fun x y => ?_, ?_, fun g g' x => ?_, fun g g' hg hg' s hs => ?_⟩,
      fun e => hf0 (congrArg Subtype.val e), fun x hx => Subtype.ext (hvac x hx), span_rhoT_eq_top hadd hfM⟩,
    rfl, fun _ _ _ => rfl, fun m => hMθ m.2, fun x => ⟨uPt hw h k aS aT x, fun _ => rfl⟩⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [coe_rhoT, uPt_zero, GlobalTheory.SplitScalar.heisO_zero]
    rfl
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [Module.End.mul_apply, coe_rhoT, coe_rhoT, GlobalTheory.SplitScalar.heisO_heisO, LinearMap.smul_apply, Submodule.coe_smul,
      coe_rhoT, ← uPt_add, GlobalTheory.T.symplectic_form_inert_supported_points_antidiagonal D ψ v w hw h S T c k aS aT hconj gS gT, ← p3]
    simp only [GlobalTheory.Hk3.locH, one_mul]
  · refine eq_top_iff.2 ((span_rhoT_eq_top hadd hfM).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨x, rfl⟩
    exact ⟨x, ⟨f, hfM⟩, fun y hy => Subtype.ext (hvac y hy), rfl⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    have hinv : (eS.symm g)⁻¹ = eS.symm g⁻¹ := (map_inv eS.symm g).symm
    show π (g, g') (heisO ψ S T (uPt hw h k aS aT x) m) = heisO ψ S T (uPt hw h k aS aT _) (π (g, g') m)
    rw [hπ, hπ, hW.om_heis _ _ _ _ (hMθ m.2), GlobalTheory.T.local_group_action_inert_supported_points_frames]
    refine congrArg (fun z => heisO ψ S T (uPt hw h k aS aT z) (om (embV S v (eS.symm g), embV T v (eT.symm g')) m)) ?_
    rw [← eTa, hinv, ← eSa]
    erw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  · refine Subtype.ext (hfix _ ⟨hMθ s.2, fun e e' he uu huu hh => ?_⟩ _
      ((dict.2.2.1 S _).2 ⟨eS.symm g, (kSc _).2 ((eS.apply_symm_apply g).symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg), rfl⟩) _
      ((dict.2.2.1 T _).2 ⟨eT.symm g', (kTc _).2 ((eT.apply_symm_apply g').symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg'), rfl⟩))
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.exists_integralFramePoint_of_inertHalf_latticePoint D v w hw h S T k aS aT hk haS haT e e' he uu huu hh
    exact congrArg Subtype.val (hs x hx)

end GlobalTheory.InertFrameLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposiStatement
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
theorem _root_.GlobalTheory.T.exists_sum_hyperbolicPlanes_orthogonal_wittDecomposition : ∀ (D : D7) (W : HSp D) (t : ℕ), HSpace.SigOK W → ∃ (H B : HSp D) (_ : OrthDec B W H) (_ : HypDec B W t), HSpace.SigOK H ∧ HSpace.SigOK B ∧ H.rank = 2 * t ∧ (∀ τ, H.sig τ = (t, t)) ∧ ∃ sH : RealMat H, ∀ τ, IsCartanInv (gramAt D H τ) (sH τ) := by
  first | exact @GlobalTheory.HypSumWitt.exists_hypSum_orthDec_hypDec | exact GlobalTheory.HypSumWitt.exists_hypSum_orthDec_hypDec | (intros; apply GlobalTheory.HypSumWitt.exists_hypSum_orthDec_hypDec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThetaLiftSpacesPositiveIndexWithLineNorms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.SeeSaw.YRat

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := Formalism.HC.HostAx.conjE_apply _ _ _
  rw [h1]
  haveI := D.host.isCMField_hostE
  exact IsCMField.complexEmbedding_complexConj _ _ _

theorem posDef_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

theorem defSpace {D : D7} (hX : ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef) {j : ℕ} (hj : j ≤ D.R.m) :
    (D.sp.X j).SigOK ∧ (∀ τ, (D.sp.X j).sig τ = (D.R.N j, 0)) ∧ CoCpt (D.sp.X j) := by
  have hs : (D.sp.X j).SigOK := D.sp.X_sig j
  have hr : (D.sp.X j).rank = D.R.N j := D.sp.X_rank j hj
  refine ⟨hs, fun τ => by rw [hX j hj τ, hr], ?_⟩
  refine (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D (D.sp.X j)).2 fun τ => ?_
  have h1 := hs (tauE D τ)
  rw [hX j hj (tauE D τ)] at h1
  exact posDef_of_sig _ h1

theorem spaces_of_index : ∀ (D : D7) (u : D.what₂.Word), (∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef) → (∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (b : BesAt V (D.sp.X j) ρ), V.rank = D.R.rankY j ∧ V.SigOK ∧ (∀ τ, V.sig τ = sigYD D.R j) ∧ (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ) * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E)) ∧ ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (_ : JacAt V (D.sp.X (j + 1)) ρ), V.rank = D.R.rankY (j + 1) ∧ V.SigOK ∧ ∀ τ, V.sig τ = sigYD D.R (j + 1) := by
  intro D u hX
  have hsum := GlobalTheory.T.exists_orthogonalSum_and_hyperbolicSum_spaces D
  have hvol := GlobalTheory.Unf.VolExist.measures_exist D
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  obtain ⟨π, -, hπ, -⟩ := D.T_norm u
  have hππ : (π : D.host.E) * star (π : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [star_eq_conj]; exact hπ
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by
    have := (D.mem u).A.T_prime.ne_zero
    exact_mod_cast this
  have hπ0 : (π : D.host.E) ≠ 0 := by
    intro h0; apply hT0; rw [← hππ, h0, zero_mul]
  refine ⟨?_, ?_⟩
  · intro j ρ h
    obtain ⟨hXs, hXsig, hXc⟩ := defSpace hX (j := j) (by omega)
    have hXr : (D.sp.X j).rank = D.R.N j := D.sp.X_rank j (by omega)
    set c : D.host.E := (π : D.host.E) / D.host.xi0 ^ (j / 2) with hc
    have hc0 : c ≠ 0 := div_ne_zero hπ0 (pow_ne_zero _ hxi)
    obtain ⟨L, ζ, hline, hLs, hLn, hLsig⟩ := GlobalTheory.T.exists_hermitianLine_vector_prescribed_norm D c (-1) hc0
    obtain ⟨V₀, o, hV₀s, hV₀sig⟩ := hsum.1 (D.sp.X j) L hXs hLs
    obtain ⟨V, d, hVs, hVsig⟩ := hsum.2 V₀ ρ hV₀s
    refine ⟨V, ⟨V₀, L, d, o, ζ, hline, hXc, (hvol.2.1 _ _ _ d).some⟩, ?_, hVs, ?_, ?_⟩
    · have h1 := d.rank_add
      have h2 := o.rank_add
      have h3 : L.rank = 1 := hline.1
      have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
      simp only [Ranks.rankY, Ranks.r]
      rw [hXr] at h2
      simp only [Ranks.N] at h2
      omega
    · intro τ
      have hL : L.sig τ = (0, 1) := by rw [hLsig τ]; decide
      rw [hVsig τ, hV₀sig τ, hXsig τ, hL]
      have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
      simp only [sigYD, Ranks.rankY, Ranks.r, Ranks.N, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> omega
    · show (star ζ ⬝ᵥ L.gram *ᵥ ζ) * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = _
      rw [hLn, ← hππ, hc, star_div₀, star_pow]
      have hs0 : star D.host.xi0 ≠ 0 := star_ne_zero.2 hxi
      field_simp
      push_cast
      ring
  · intro j ρ h
    obtain ⟨hXs, hXsig, hXc⟩ := defSpace hX (j := j + 1) (by omega)
    have hXr : (D.sp.X (j + 1)).rank = D.R.N (j + 1) := D.sp.X_rank (j + 1) (by omega)
    obtain ⟨V, d, hVs, hVsig⟩ := hsum.2 (D.sp.X (j + 1)) ρ hXs
    refine ⟨V, ⟨d, hXc, (hvol.2.1 _ _ _ d).some⟩, ?_, hVs, ?_⟩
    · have h1 := d.rank_add
      rw [hXr] at h1
      have h4 : (j + 1) * (D.R.t + 1) = (j + 1) * D.R.t + (j + 1) := by ring
      simp only [Ranks.N] at h1
      simp only [Ranks.rankY, Ranks.r]
      omega
    · intro τ
      rw [hVsig τ, hXsig τ]
      have h4 : (j + 1) * (D.R.t + 1) = (j + 1) * D.R.t + (j + 1) := by ring
      simp only [sigYD, Ranks.rankY, Ranks.r, Ranks.N, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> omega

end GlobalTheory.SeeSaw.YRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTranslatesOfValuesFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translates_of_values_frames : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), ∃ J, JOf R j J := by
  first | exact @GlobalTheory.AdForm.jOf_exists | exact GlobalTheory.AdForm.jOf_exists | (intros; apply GlobalTheory.AdForm.jOf_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), (IsSplit (E := D.host.E) v → ∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w ∧ Odd (qV D.host.F v) ∧ ∀ c, IsConjAt D.sp.cm.sig h c → ∃ e, IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e) := by
  first | exact @GlobalTheory.ChartsAll.exists_charts | exact GlobalTheory.ChartsAll.exists_charts | (intros; apply GlobalTheory.ChartsAll.exists_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

section Model

variable {X Y G H : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [Monoid G] [Monoid H]

theorem exists_hom_of_model (P : X → Prop) (s : X → Y) (S : Submodule ℂ Y)
    (hadd : ∀ f f', P f → P f' → P (f + f') ∧ s (f + f') = s f + s f')
    (hsmul : ∀ (c : ℂ) f, P f → P (c • f) ∧ s (c • f) = c • s f)
    (hin : ∀ f, P f → s f ∈ S) (honto : ∀ φ ∈ S, ∃ f, P f ∧ s f = φ)
    (hinj : ∀ f f', P f → P f' → s f = s f' → f = f')
    (om : G →* Module.End ℂ X) (hpres : ∀ g f, P f → P (om g f)) (κ : G ≃* H) :
    ∃ ρ : H →* Module.End ℂ S, ∀ g f, P f → ∀ Φ : S, Φ.1 = s f → (ρ (κ g) Φ).1 = s (om g f) := by
  classical
  choose lift hlP hls using fun Φ : S => honto Φ.1 Φ.2
  have hlift : ∀ (Φ : S) f, P f → Φ.1 = s f → lift Φ = f := fun Φ f hf h =>
    hinj _ _ (hlP Φ) hf ((hls Φ).trans h)
  let act : H → Module.End ℂ S := fun h =>
    { toFun := fun Φ => ⟨s (om (κ.symm h) (lift Φ)), hin _ (hpres _ _ (hlP Φ))⟩
      map_add' := fun Φ Ψ => by
        have e : lift (Φ + Ψ) = lift Φ + lift Ψ :=
          hlift _ _ (hadd _ _ (hlP Φ) (hlP Ψ)).1 (by rw [(hadd _ _ (hlP Φ) (hlP Ψ)).2, hls, hls]; rfl)
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [e, map_add]
        exact (hadd _ _ (hpres _ _ (hlP Φ)) (hpres _ _ (hlP Ψ))).2
      map_smul' := fun c Φ => by
        have e : lift (c • Φ) = c • lift Φ :=
          hlift _ _ (hsmul c _ (hlP Φ)).1 (by rw [(hsmul c _ (hlP Φ)).2, hls]; rfl)
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [e, map_smul]
        exact (hsmul c _ (hpres _ _ (hlP Φ))).2 }
  have hact : ∀ h (Φ : S), ((act h Φ : S) : Y) = s (om (κ.symm h) (lift Φ)) := fun _ _ => rfl
  refine ⟨{ toFun := act, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [hact, map_one, map_one]
    exact hls Φ
  · intro h₁ h₂
    refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [Module.End.mul_apply, hact, hact, map_mul, map_mul, Module.End.mul_apply,
      hlift (act h₂ Φ) _ (hpres _ _ (hlP Φ)) (hact h₂ Φ)]
  · intro g f hf Φ hΦ
    show s (om (κ.symm (κ g)) (lift Φ)) = s (om g f)
    rw [κ.symm_apply_apply, hlift Φ f hf hΦ]

end Model

theorem exists_transport_std : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, ∃ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ κ
  have hS := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hW.std θ hθ A B ν 𝓨 hν
  have hL := GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hW.std A B ν 𝓨 hν
  obtain ⟨ρ, hρ⟩ := exists_hom_of_model (IsThetaFunO ψ (dblSp A) B) (sch ψ A B ν 𝓨) (schwartzA θ B.rank A.rank)
    (fun f f' hf hf' => ⟨(hL f f' hf hf' 0).1, (hL f f' hf hf' 0).2.2.1⟩)
    (fun c f hf => ⟨(hL f f hf hf c).2.1, (hL f f hf hf c).2.2.2⟩)
    hS.1 hS.2.1 hS.2.2 (omh.comp (MonoidHom.inl _ _)) (fun g f hf => hW.om_pres _ _ hf) κ
  exact ⟨ρ, fun g f hf Φ hΦ => hρ g f hf Φ hΦ⟩

end GlobalTheory.StdUnn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSupportSplitPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_support_split_places : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), GlobalTheory.Core.Mi.IdE X → ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), IsSplitIdem D e → Formalism.L2.NTheta.IsIdemAt e PP → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ n ∈ flagN B.d, Formalism.L2.Theta.SuppAt e (D.sp.Y 0) n → ((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u)) ∈ rowJ X h → rowChi X h (((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u))) = psiBes ψ B.d 1 (vecB B.o B.ζ) n := by
  first | exact @GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes | exact GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes | (intros; apply GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealCompletion_locally_principal : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ x : D.host.E, x ≠ 0 ∧ ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  first | exact @GlobalTheory.IdVGen.idV_gen | exact GlobalTheory.IdVGen.idV_gen | (intros; apply GlobalTheory.IdVGen.idV_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransferStatement
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
theorem _root_.GlobalTheory.T.global_doubling_zeta_form_selfDual_lattice_transfer : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → GlobalFormAt A L → GlobalFormAt A L' := by
  first | exact @GlobalTheory.Core.Rk.GlobMove.globalFormAt_move | exact GlobalTheory.Core.Rk.GlobMove.globalFormAt_move | (intros; apply GlobalTheory.Core.Rk.GlobMove.globalFormAt_move <;> assumption)
end


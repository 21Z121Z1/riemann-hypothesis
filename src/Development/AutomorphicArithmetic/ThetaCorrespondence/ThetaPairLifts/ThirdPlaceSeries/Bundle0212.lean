import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.Bundle0002
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0201
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0777
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1006
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0775
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0776
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0096
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0773
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.RankOneOfLong
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0063
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0072

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StrCalcO
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigStrCalc
end GlobalTheory.EigStrCalc
namespace GlobalTheory.EigStrCalc
end GlobalTheory.EigStrCalc
namespace GlobalTheory.EigStrCalc
theorem is_split_of_cusp_iso_bcv : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (Q P0 : D.naut.AV i) (Sig : List (Part D.naut.CG)), D.naut.ptV i Q = some x → D.naut.ptV i P0 = some x → IsCuspIso D.nd D.naut Sig → IsBCV D.nd D.naut i P0 (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → w ∉ D.nd.S i → w ∉ D.nd.Q i → D.naut.unr (D.naut.locV i Q w) → ∀ z : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {z⁻¹} → ∃ B' : Multiset ℂ, (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) z D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hAF hL D P h41 h7 _ i x Q P0 Sig hQ hP0 hSig hB w hsplit hS hQw hunr z hz
  have hsp : IsSplitPl D.host w := isSplitPl_of_under D w hsplit
  obtain ⟨π, rfl⟩ := hSig
  have e1 : D.naut.locV i Q w = D.naut.locV i P0 w :=
    (((h41 i).2.1 Q P0 (by rw [hQ]; exact Option.some_ne_none x) (hQ.trans hP0.symm)).2 w hS hQw).1 hsp
  have e2 := hB.2.2.2.1 w hsp
  have e3 : isoLoc D.nd D.naut (twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w =
      D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
        (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    have : spehLoc D.nd D.naut ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ w = D.naut.locG (D.naut.tw π D.naut.etaTinv) w := by
      simp [spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
    rw [← this]
    exact congrArg _ (D.naut.lpSum_zero _)
  have eV : D.naut.locV i Q w = D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
      (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    rw [e1, ← e2, e3]
  rw [eV] at hunr
  obtain ⟨ha, hb⟩ := (D.naut.unr_sum _ _).1 hunr
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hθ := unr_of_speh D.naut _ D.R.t ht w hb
  obtain ⟨-, hblk⟩ := GlobalTheory.RowModelRoad.frobEig_block D.naut _ D.R.t w z⁻¹ hθ hz
  refine ⟨(D.naut.frobEig (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)).map (fun a : ℂ => a⁻¹), ?_, ?_⟩
  · rw [eV, D.naut.frobEig_sum _ _ ha hb, Multiset.map_add, hblk, ← normV_eq_absNorm, inv_block]
  ·
    obtain ⟨hTie, -⟩ := _root_.GlobalTheory.AutomorphismSplitting.tieAut_and_split_alt hAF hL D P
    have hEta : GlobalTheory.LocalInv.EtaType D.nd D.naut := by
      refine ⟨hTie.1.1, fun τ z hz => ?_⟩
      rcases (hTie.2.1 τ).1 with h | h <;> rw [h, Multiset.mem_singleton] at hz <;> subst hz
      · exact ⟨0, by push_cast; ring⟩
      · exact ⟨-1, by push_cast; ring⟩
    have hmem : (⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv := by
      simp [twistIso]
    obtain ⟨hcsd, hralg⟩ := GlobalTheory.LocalInv.part_alg D.nd D.naut hEta (GlobalTheory.LocalInv.weightRegular_definite D) i P0 _ hB _ hmem
      (odd_rank D.R) odd_one
    intro a haB
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp haB
    exact (((_root_.UpperTheory.GalN.tempo' h7 D.R.r _ (odd_rank D.R).pos hcsd hralg w).part_tw hTie ha α hα).1.inv
      (UpperTheory.GalN.one_lt_q w)).le_rpow (UpperTheory.GalN.one_lt_q w) (UpperTheory.GalN.half_le_r D.R)
end GlobalTheory.EigStrCalc
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameLevelValueTrivialAtWildPlace
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.TameUnitOne
open Formalism.L2.NX
end GlobalTheory.TameUnitOne
namespace GlobalTheory.LevCmp
theorem tame_value_eq_one_at_wild_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' l.b.Bs.exp.sgnT u = 1) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ((Dof x).ntw.delta i) P'' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) u = 1) := by
  intro _ hL
  refine StepW.of_all fun _ B _ T _ _ _ _ P x l v i b ψ hA j _ _ _ => ?_
  refine ⟨fun P'' hP'' u hu => ?_, fun P'' hP'' u hu => ?_⟩
  · have hQ : P'' ∈ QOf P v := (cell (D := Dof x) l.b.Bs.exp b hA j).QP_sub hP''
    exact GlobalTheory.TameUnitOne.tameVal_eq_one ψ P'' _ ((Dof x).ntw.l i) hA.2.2.1 (hA.1 P'' hQ).2
      (fun _ _ σ _ => hA.2.2.2.2.1 σ) u hu
  · have hD : P'' ∈ (Dof x).ntw.pD i := (cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP''
    refine GlobalTheory.TameUnitOne.tameVal_eq_one ((Dof x).ntw.delta i) P'' _ 15 ((Dof x).ntw.delta_open i) ?_
      (fun A hA' σ hσ => ⟨1, ?_⟩) u hu
    · intro h
      have h1 := (Dof x).ntw.delta_tame i P'' hD
      have h2 : Ideal.absNorm P''.asIdeal ∣ 15 ^ Module.finrank ℤ (𝓞 (Dof x).host.E) := by
        have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
        rwa [Ideal.absNorm_span_natCast] at this
      have h3 : Nat.Coprime (Ideal.absNorm P''.asIdeal) 15 := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1]
        rfl
      have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ h3) h2
      exact P''.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h4)
    · have h1 := pow_card_eq_one' (x := (⟨(Dof x).ntw.delta i σ, σ, hσ, rfl⟩ :
        (ReciprocityTheory.Gal.Ine (F := (Dof x).host.E) A).map ((Dof x).ntw.delta i)))
      rw [(Dof x).ntw.delta_15 i P'' hD A hA'] at h1
      rw [pow_one]
      exact congrArg Subtype.val h1
end GlobalTheory.LevCmp
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tw_ok_value_trivial_at_twisted_place : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' l.b.Bs.exp.sgnT u = 1) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ((Dof x).ntw.delta i) P'' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) u = 1) := by
  first | exact @_root_.GlobalTheory.LevCmp.tame_value_eq_one_at_wild_place_alt | exact _root_.GlobalTheory.LevCmp.tame_value_eq_one_at_wild_place_alt | (intros; apply _root_.GlobalTheory.LevCmp.tame_value_eq_one_at_wild_place_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLiftOfReference
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.RefPair
theorem GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  intro hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y hH hEx _ _ _ Rw a M tup Q hMA _ j h1 h2 => ?_
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  have hC : z.R.C = TC.cf w.I w.l Z := z.lev.C
  obtain ⟨X, hX⟩ := GlobalTheory.RefTheta.datum_real hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hH hEx M hMA i
  refine ⟨X, ?_⟩
  rw [← hC]
  exact hX
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.RefPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_at_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  first | exact @_root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThirdComponentHeckeCharacterTuple
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.Up.ThirdTied
theorem third_component_hecke_character_tuple_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ μ, Formalism.IndefR.RecTie.Used0 (withLoc L) μ → m.z.R.toLevCh.xiH (r.Y.tupT μ) = (tpL L l.c.tp).xi μ := by
  intro hL hP hX
  refine StepW.of_all fun K B f T w _ _ _ P x => ?_
  intro l big L _ _ m _ _ s r _ μ hμ
  refine (m.z.lev.xiH (r.Y.tupT μ)).trans ?_
  have b := r.Y.tupTie μ hμ
  rw [r.tup, m.tup] at b
  rw [b]
  exact (congrFun l.c.xi_eq μ).symm
end GlobalTheory.HeightCounting.Up.ThirdTied
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThirdComponentsAgree
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ThirdAgree
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.Up.RealOfReading
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
section Copy
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}
end Copy
section Main
set_option maxHeartbeats 4000000 in
theorem third_components_agree_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ (hC : m.z.R.C = cfL L (cfOf x)) (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd) (labPi : E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf (rep : (withLoc L).what₂.FT → NG.FinTyp (withLoc L).host.E (withLoc L).R.r), HEq rep (repOf x.r.Y) → Nonempty (GlobalTheory.NJoin.Agree (GlobalTheory.HeightCounting.Up.RealOfReading.realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi hb htup hg hf) (mtL L l.mt.M) rep) := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ m hcp hco s r hpin hC Xd E labPi hb htup hg hf rep hrep
  have c1 := cV_copy (B := B) (C := w.C) (a := P.Z₀) (GlobalTheory.HeightCounting.Fin3.oL x L).Z P.z m.z m.Xg m.tr ((by with_unfolding_all exact (hcp.core :))) ((by with_unfolding_all exact (hcp.R :)))
  have c0 := cV_copy (B := B) (C := w.C) (a := P.Z₀) x.o.Z P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :)))
  have ecV := cV_two (a := P.Z₀) x.o.Z (GlobalTheory.HeightCounting.Fin3.oL x L).Z c0 c1
  have hJ : HEq m.t.lf.jMt x.m.t.lf.jMt := hco.jMt.trans x.coh.jMt.symm
  have kJ : ∀ μ (i : Fin (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7.R.m) y,
      HEq (m.t.lf.jMt μ i y) (x.m.t.lf.jMt ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))) := fun μ i y => (by with_unfolding_all exact ((heq_apply (D := (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7) (Mt := fun μ j => (P.q.p.sL μ j).A) ecV
      ((m.t.lf.jMt)) ((x.m.t.lf.jMt)) ((hJ)) μ i y) : _))
  have eR1 : m.t.rep = (by with_unfolding_all exact (P.q.t.rep :)) := (by with_unfolding_all exact ((eq_of_heq hco.rep) :))
  have eR0 : x.m.t.rep = (by with_unfolding_all exact (P.q.t.rep :)) := (by with_unfolding_all exact ((eq_of_heq x.coh.rep) :))
  have eRep : rep = (by with_unfolding_all exact ((repOf x.r.Y) :)) := (by with_unfolding_all exact ((eq_of_heq hrep) :))
  have hrep' : ∀ σ, (rep σ).Iso (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT σ)) := by
    intro σ
    have a1 : (rep σ).Iso ((by with_unfolding_all exact ((repOf x.r.Y σ) :))) := (by with_unfolding_all exact ((iso_of_eq (congrFun eRep σ)) :))
    have a2 := x.pin.rep ((by with_unfolding_all exact (σ :)))
    have a3 : ((by with_unfolding_all exact ((x.m.t.rep σ) :)) : NG.FinTyp (withLoc L).host.E (withLoc L).R.r).Iso ((by with_unfolding_all exact ((m.t.rep σ) :))) := (by with_unfolding_all exact ((iso_of_eq ((congrFun eR0 σ).trans (congrFun eR1 σ).symm)) :))
    have a4 := NG.IsoRep.symm (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT σ)).stable (hpin.rep σ)
    exact (by with_unfolding_all exact ((NG.IsoRep.trans a1 (NG.IsoRep.trans a2 (NG.IsoRep.trans a3 a4))) :))
  let DL := (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7
  let jm : ∀ μ, Used0 DL μ → ∀ i : Fin DL.R.m, DL.what₂.Mt μ (i.1 + 1) → GA DL (Vc DL i) →
      (cpV (GlobalTheory.HeightCounting.Fin3.oL x L).Z x.m.z.R.cV i).W :=
    fun μ h i y => (by with_unfolding_all exact ((x.r.Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1 : _))
  have hj : ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (jm μ h i y) := fun μ h i y => (by with_unfolding_all exact (((hpin.jMt μ h i y).trans ((kJ μ i y).trans (x.pin.jMt μ h i y).symm)) :))
  exact (by with_unfolding_all exact ((agree_of_data (D := DL) (R := m.z.R) (F := m.z.F) r.Y (cf := ((cfL L (cfOf x)))) (nch := ((chL L l.c.ch)))
    (((tpL L l.c.tp))) ((hC)) ((Xd)) ((E)) ((labPi)) ((hb)) ((htup)) ((hg)) ((hf)) (((mtL L l.mt.M))) ((rep))
    ((hrep')) _ ecV (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l) ((l.mt.ad.std)) ((l.mt.ad.eW)) jm hj ((l.mt.ad.read)) ((l.mt.ad.rat))
    ((l.mt.ad.wt))) : _))
end Main
end GlobalTheory.HeightCounting.Up.ThirdAgree
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThmAUpper
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
noncomputable section
namespace GlobalTheory.ThmAUpper
theorem thmA_upper_alt : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint →
    (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx →
    (_root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  intro hG hS hdl hF hT
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono (_root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hF) (_root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hT)) ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH hp hd
  refine ⟨hd, fun ⟨hf, ht⟩ w hw => ⟨_root_.GlobalTheory.T.qn_not_mem_asIdeal_of_mu_ne p CF d hp hd w hw, fun l hl hlw i j s Λ Λd z hs1 hs2 hΛ hΛd hz => ?_⟩⟩
  have hw' : D.plEq (D.plEq.symm w) = w := D.plEq.apply_symm_apply w
  have hl' : D.what₂.places.resChar (D.plEq.symm w) = l := resChar_eq _ hl (by rw [hw']; exact hlw)
  have key := _root_.GlobalTheory.T.cm_abelian_field_data_of_toric_ratio_alt p CF d hp hd hG hf ht (D.plEq.symm w) (xiH_twisted p w hw).1 i j s Λ Λd z hs1 hs2
    (by rw [← nuH_twisted p d.G w hw]; exact hΛ) (by rw [hl']; exact hΛd) hz
  rw [hw', hl'] at key
  exact key
end GlobalTheory.ThmAUpper
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistCharacterTamelyRamifiedAtPlace
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.TwTameCell
theorem twist_character_tame_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → (eta (D := Dof x) (cfOf x) w.I.xi v j).TameAt P' := by
  intro _ hL
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j _ _ _ P' _
  have h1 := ((cfOf x).isMu0 j).tame P'
  have hx : w.I.xi ((Dof x).what₂.muTw v) ∈ T.set f := w.xi_range ▸ Set.mem_range_self _
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hx
  have h2 : (w.I.xi ((Dof x).what₂.muTw v)).TameAt P' := by
    rcases hx with (h | h | h) | ⟨w', h⟩
    · rw [h]; exact tameAt_one P'
    · rw [h]; exact f.isDel.tame P'
    · rw [h]; exact f.isDel'.tame P'
    · rw [← h]
      unfold TwDat.xiTw
      split_ifs
      · exact tameAt_mul (f.isDel'.tame P') ((T.psi_is w').tame P')
      · exact tameAt_mul (f.isDel.tame P') ((T.psi_is w').tame P')
  exact tameAt_mul h1 h2
end GlobalTheory.TwTameCell
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_character_tamely_ramified_at_place' : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → (eta (D := Dof x) (cfOf x) w.I.xi v j).TameAt P' := by
  first | exact @_root_.GlobalTheory.TwTameCell.twist_character_tame_at_place_alt | exact _root_.GlobalTheory.TwTameCell.twist_character_tame_at_place_alt | (intros; apply _root_.GlobalTheory.TwTameCell.twist_character_tame_at_place_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistMemWeightOneSubspace
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.InW1TwistAtMember
theorem twist_mem_weightOne_subspace_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  intro _ _ hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  intro a
  rw [n.tie.twOf_eq a]
  exact GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.D Z) nch n.tie B.coeffGaloisSubfield_isGalois _ ((w.D Z).nd.w_tw a)
end GlobalTheory.HeightCounting.InW1TwistAtMember
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_index_place_tw_of : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  first | exact @_root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt | exact _root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt | (intros; apply _root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UbcStringO
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.UbcString
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
end GlobalTheory.UbcString
theorem GlobalTheory.UbcString.ubc_string_o_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc), ∀ x ∈ ZgoodN D.nd D.naut i, ∃ P', D.naut.ptV i P' = some x ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ (B'' : Multiset ℂ) (c : ℂ), D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} ∧ ubc D.R.nV (D.naut.satV i P' w) = B'' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) c D.R.t ∧ ∀ a ∈ B'', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hAF hL D P X _ _ h7 htie i x hx
  obtain ⟨-, Sig, ⟨P', hP', hB⟩, hgood⟩ := hx
  obtain ⟨π, rfl⟩ := GlobalTheory.T.goodLabels_rank_part_parameter_cuspidal D htie i x Sig ⟨P', hP', hB⟩ hgood
  refine ⟨P', hP', fun w hw => ?_⟩
  have hns := GlobalTheory.UbcString.not_isSplitPl_of_inert D.host w hw
  obtain ⟨hunr, hfe⟩ := hB.2.2.2.2.1 w hns
  have e1 : spehLoc D.nd D.naut ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ w =
      D.naut.locG (D.naut.tw π D.naut.etaTinv) w := by
    simp [spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
  have e : isoLoc D.nd D.naut (twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w =
      D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
        (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    simp only [isoLoc, twistIso, muPart, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, D.naut.lpSum_zero, e1]
  rw [e] at hunr hfe
  obtain ⟨ha, hb⟩ := (D.naut.unr_sum _ _).1 hunr
  have hb' : D.naut.unr ((List.range D.R.t).map (fun a : ℕ => (a : ℝ)) |>.foldr
      (fun k acc => D.naut.lpSum (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 - k)) acc) (D.naut.lpZero w)) := by
    rw [← GlobalTheory.LocalInv.list_coe]; exact hb
  have hm : D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) :=
    GlobalTheory.UbcString.unr_of_foldr D.naut _ (fun k : ℝ => ((D.R.t : ℝ) - 1) / 2 - k) _ 0
      (List.mem_map.2 ⟨0, List.mem_range.2 D.R.t_odd.pos, by simp⟩) hb'
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1
    (by rw [D.naut.frobEig_card _ hm, D.naut.locG_dim] :
      Multiset.card (D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)) = 1)
  have hstr : D.naut.frobEig (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) =
      GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) c D.R.t := by
    have h := (GlobalTheory.UbcString.frobEig_foldr D.naut _ hm (fun k : ℝ => ((D.R.t : ℝ) - 1) / 2 - k)
      ((List.range D.R.t).map (fun a : ℕ => (a : ℝ)))).2
    unfold spehLoc
    rw [GlobalTheory.LocalInv.list_coe]
    refine h.trans ?_
    rw [hc]
    simp only [Multiset.map_singleton]
    rw [List.map_map, Function.comp_def, GlobalTheory.UbcString.sum_singletons (fun a : ℕ => c * ((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) - 1) / 2 - (a : ℝ) : ℝ) : ℂ)), GlobalTheory.DownLift.str, Multiset.range, Multiset.map_coe]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    have hq : ((normV w : ℕ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) := rfl
    rw [hq]
    push_cast
    ring_nf
  rw [D.naut.frobEig_sum _ _ ha hb, hstr] at hfe
  refine ⟨D.naut.frobEig (D.naut.locG (D.naut.tw π D.naut.etaTinv) w), c, hc, hfe.symm, ?_⟩
  have hAut := (_root_.GlobalTheory.AutomorphismSplitting.tieAut_and_split_alt hAF hL D P).1
  have hη : GlobalTheory.LocalInv.EtaType D.nd D.naut := by
    obtain ⟨⟨h1, -⟩, h2, -⟩ := hAut
    refine ⟨h1, fun τ z hz => ?_⟩
    rcases (h2 τ).1 with e | e <;> rw [e, Multiset.mem_singleton] at hz <;> subst hz
    · exact ⟨0, by simp⟩
    · exact ⟨-1, by push_cast; ring⟩
  have hpa := GlobalTheory.LocalInv.part_alg D.nd D.naut hη (GlobalTheory.LocalInv.weightRegular_definite D) i P' _ hB
    ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ (by simp [twistIso]) (GlobalTheory.LocalInv.r_odd D.R) odd_one
  intro α hα
  exact ((_root_.UpperTheory.GalN.tempo' h7 D.R.r _ (GlobalTheory.LocalInv.r_odd D.R).pos hpa.1 hpa.2 w).part_tw hAut ha α hα).1.le_rpow
    (UpperTheory.GalN.one_lt_q w) (UpperTheory.GalN.half_le_r D.R)
theorem GlobalTheory.EigStrInert.str_inert_tyz : _root_.GlobalTheory.EigStrInert.strInert_tyz := by
  intro hA hL D P X hAg hconds hadm htie i hμ j hj x hx f hf y hy hy0 h hh s B hE hB w hw hinert
  obtain ⟨P', hP', hw2⟩ := _root_.GlobalTheory.UbcString.ubc_string_o_alt hA hL D P X hAg hconds hadm htie i x hx
  obtain ⟨B'', c, hc, heq, hnorm⟩ := hw2 w hinert
  have h1 := _root_.GlobalTheory.T.theta_eigen_compatibility_seventh_alt hA hL D P X hAg hconds hadm htie i hμ j hj x hx f hf y hy hy0 h hh s B hE hB w hw hinert P' hP'
  have h2 := _root_.GlobalTheory.T.good_place_split_condition_alt hA hL D P X hAg hconds hadm htie i hμ j hj w hw hinert c hc
  exact ⟨B'', by rw [h1, heq, h2], hnorm⟩
end
end


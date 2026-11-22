import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0220
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0914
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0221
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0381
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0009
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0209
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0223
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0216
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0563
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0201
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0210
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0222
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0052
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0584
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0109
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0199

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlocksUniqueOfCgTrue
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Satake
open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.CuspRep Formalism.UG
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
variable [IsTotallyComplex E]
end Satake
section Local
open GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable [IsTotallyComplex E] (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
end Local
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section Record
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {l : ℕ} [Fact l.Prime]
variable {ι : Qbar l ≃+* ℂ}
end Record
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions GlobalTheory.CuspRep Blocks
theorem blocksUnique_of_cgTrue_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL →
    _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.JacquetShalika →
    GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → BlocksUnique D :=
  fun hL hF hG _ hJ hC _ _ C => C.blocksUnique hL hF hG hJ.1 hC
end GlobalTheory.HeightCounting
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterTrivialAbovePlaceAdmissible
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
theorem character_trivial_above_place_admissible_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    Formalism.MainNotions.SumRepresentations.adm5 D := by
  have hrig : IsobaricRigid D.nd D.naut := _root_.GlobalTheory.NPin.isobaricRigid_of_pin_alt hPr.fin hPr.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.cheb D
  exact (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
end GlobalTheory.ChiOneAbove
end
section
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfSeriesLocal
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
theorem depthZeroType_series_local_explicit_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing →
    _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L →
    (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
      TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) →
    GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D := by
  intro hPr hG hZ hDZ hL D P L hLT hκ hCen
  obtain ⟨I⟩ := GlobalTheory.TypeIdent.nonempty_ident D
  obtain ⟨rc, hrc, hcl⟩ := _root_.UpperTheory.One.M.exists_isRc_isClassMapD_alt hL D P.T I
  refine _root_.DiscreteGroups.sglob.DzType.Rt.serLoc_of_tame_param_le D L rc hG hLT (GlobalTheory.T.inertiaInvariantUnderUnramifiedTwist_of_weilDeligne D P.T)
    (_root_.GlobalTheory.T.locComp_of_isRc_of_classMap_of_cenLoc hPr hL D P I rc hrc hcl hCen) (_root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc hZ hL D P.T I rc hrc)
    (fun k => GlobalTheory.DepthZeroCusp.depthZeroCuspidal (D.host.g k)) ?_
  intro k v
  obtain ⟨κ, hκ'⟩ := hκ k v
  exact _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL D P.T I rc hrc L k v κ hκ'
set_option maxHeartbeats 1000000 in
theorem serLoc_of_tame_coupled_and_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.depthZeroType_series_local_explicit_alt
end DiscreteGroups.sglob.DzType.Rt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DictStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eigen_compatibility_eighth_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ D.naut.unr (D.naut.locV i Q w) ∧ (B w).map (fun a : ℂˣ => (a : ℂ)) = (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) := by
  first | exact @_root_.GlobalTheory.StrSplitDict.dict_alt | exact _root_.GlobalTheory.StrSplitDict.dict_alt | (intros; apply _root_.GlobalTheory.StrSplitDict.dict_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsAt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem exists_isAt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → GlobalTheory.MiTop.Framed B → ∃ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hP hF
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.Core.Mi.PinModel.exists_transport_adelic_correction (W.S.tr u)
  obtain ⟨a, haf, hac, hSt⟩ := _root_.GlobalTheory.T.exists_central_stab_of_transport_correction W hW u f B hP hF a₀ ha₀
  have hM := _root_.GlobalTheory.T.central_adapted_element_property_alt W hW u f B hP a₀ ha₀ a haf hac hSt
  have hC := _root_.GlobalTheory.T.central_adapted_element_value_alt W hW u f B hP a₀ ha₀ a haf hac hSt
  have hb : (show GA D (D.sp.Y 0) from f.g.b 0) ∈ GfC (D.sp.Y 0) := by
    obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, hv, ht, -⟩ := hP
    have h1 := hv.b 0
    rw [ht.b 0] at h1
    exact h1
  have hx : (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) ∈ GfC (D.sp.Y 0) :=
    (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq _).1 (by simp)
  have htf : _root_.GlobalTheory.MiTop.translationElement f B a₀ a ∈ GfC (D.sp.Y 0) :=
    mul_mem (mul_mem (inv_mem hx) (GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o (mul_mem ha₀.1 haf))) hb
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    rw [rank_eq W.S.X W.Q.instEq, W.S.X.n_eq]
  refine ⟨a₀, a, ha₀, haf, hac, htf, fun κ => ?_⟩
  rw [inv_inv]
  have h1 := GlobalTheory.FrameConj.levS_conj_frame (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) htf κ
  generalize _root_.GlobalTheory.MiTop.translationElement f B a₀ a * κ * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹ = y at h1 ⊢
  obtain ⟨h2, h3⟩ := oneBlock_lev (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) hn rfl rfl y
  have h4 : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ y ∈ levS (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) := h1.1
  have h5 : Lev.levChi (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) y = _root_.GlobalTheory.MiTop.realCharacter W κ := h1.2
  rw [h2] at h4
  refine ⟨h4.trans ⟨fun h => (hM y h.1 h.2.1).2 h.2.2, fun h => ?_⟩, fun hk => ?_⟩
  · obtain ⟨hf, hs⟩ := (hSt y).2 ⟨h.1, h.2.1⟩
    exact ⟨hf, hs, (hM y hf hs).1 h⟩
  · obtain ⟨hf, hs, hp⟩ := h4.1 hk
    exact (hC y hf hs hp ((hM y hf hs).2 hp)).trans (h3.symm.trans h5)
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsWeilDatumOOmTAtLast
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.GVecAt
section Gen
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
end Gen
end GlobalTheory.GVecAt
namespace GlobalTheory.GVecAt
theorem datum_mid_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ (((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := _root_.GlobalTheory.T.descent_data_chain_step_alt
theorem datum_top_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (M' : GlobalTheory.FinPl.Lat D.sp.X') (o' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), IsSelfDualC (Yc D (j + 1)) M ∧ IsSelfDualC D.sp.X' M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) (comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) ∧ ((omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0 → comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) = κ • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) := _root_.GlobalTheory.T.descent_data_top_step_alt
section Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
theorem exists_isWeilDatumO_omT_at_last (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ χS χT, IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' χS χT
    (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) := by
  have hω := W.Q.charW.base.chain.ωX W.P.A3.A.μ0
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X'
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact hω
  exact ⟨_, _, key _ (GlobalTheory.Fam.idx_top h)⟩
end Fam
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∃ s : ℕ → ℂ, (∀ j, s j ≠ 0) ∧ _root_.GlobalTheory.Fam.GVectorCondition f v s := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR
  have fin : ∀ {S T : HSp D} (P : GlobalTheory.FinPl.Pl D → Prop) (e : WO S T →₀ ℂ), IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) →
      GlobalTheory.FinPl.CombAt P e → IsFinComb e := fun P e hψ he =>
    ((GlobalTheory.DisjComb.main D (_root_.GlobalTheory.Fam.pk_z W).ψ hψ _ _ P (fun _ => False) (fun _ _ h => h)).2.1 e he).1
  have mid : ∀ j, j + 1 < D.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1))
        (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
          (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P)) = c • comb f.c.ψ _ _ (v.eG j) (v.Ψ j P a a') := by
    intro j hj
    by_cases hex : ∃ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀
    swap
    · exact ⟨1, one_ne_zero, fun d hd => absurd ⟨d, hd⟩ hex⟩
    obtain ⟨d₀, hd₀⟩ := hex
    obtain ⟨M, M', o', hM, hM', ho', hg0, ho'v, ho'nz, κ, hκ, hdat⟩ := _root_.GlobalTheory.GVecAt.datum_mid_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT
      n G pl hGP hGR j hj d₀ hd₀
    obtain ⟨o, ho, hΨ⟩ := hVT.Ψ j hj
    have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := hd₀.2.1.1
    have hinf : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hd₀.2.1.2.inf
    have hvth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).vac j) := hd₀.2.1.2.theta
    have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
    have hb : f.g.b j ∈ GfC _ := hVT.b j ▸ hv.b j
    have hb' : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
    have hΨ1 : v.Ψ j 1 1 1 = comb f.c.ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
      rw [hΨ, GlobalTheory.FiniteFock.pureTensorO_one, one_mul, one_mul]
    have hov := vac_mono (· ∈ v.gP) (hΨ1 ▸ hv.Ψ j hj 1 1 (one_mem _) 1 (one_mem _))
    have honz : comb f.c.ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 := by
      intro h0
      obtain ⟨P, hP⟩ := hVT.nz.1 j hj
      apply hP
      rw [hΨ, one_mul, one_mul]
      have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ _ _ _ hWe hinf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (f.g.b j) (f.g.b (j + 1))
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) _ hvth P
      rw [hfin.2, comb_pureTensorO hstd hinf _ _ _ _ (fin _ o hstd ho) (hWe.om_pres _ _ hvth), h0, pureTensorO_zero]
    have hg0nz : (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) ≠ 0 := fun h0 =>
      honz (by rw [h0]; exact comb_zero _)
    obtain ⟨c, hc⟩ := scalar D f.c.ψ _ _ M (v.N j) M' (v.N (j + 1)) v.gP o o' _ hstd hM hM' (hv.sd j (by omega))
      (hv.sd (j + 1) hj) ho ho' hg0 hov ho'v (ho'nz hg0nz)
    have hc0 : c ≠ 0 := fun h0 => honz (by rw [hc, h0, zero_smul])
    refine ⟨κ / c, div_ne_zero hκ hc0, fun d hd P a ha a' ha' => ?_⟩
    have hbase : (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) =
        (κ / c) • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
      rw [hdat d hd, hc, comb_smul, smul_smul, div_mul_cancel₀ _ hc0]
    rw [hΨ P a a']
    exact fock hinf hWe _ _ _ _ (fin _ d hstd hd.1) (fin _ o hstd ho) (fin _ _ hstd (hv.atG j).1) hvth hb hb' hbase P ha ha'
  have top : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c : ℂ, c ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d →
      ∀ P, omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
        (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P)) =
        c • comb f.c.ψ _ _ (v.eGT j h) (v.ΨT j h P) := by
    intro j h
    by_cases hex : ∃ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀
    swap
    · exact ⟨1, one_ne_zero, fun d hd => absurd ⟨d, hd⟩ hex⟩
    obtain ⟨d₀, hd₀⟩ := hex
    obtain ⟨M, M', o', hM, hM', ho', hg0, ho'v, ho'nz, κ, hκ, hdat⟩ := _root_.GlobalTheory.GVecAt.datum_top_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT
      n G pl hGP hGR j h d₀ hd₀
    obtain ⟨o, ho, hΨ⟩ := hVT.ΨT j h
    have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := hd₀.2.1.1
    have hinf : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hd₀.2.1.2.inf
    have hvth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) := hd₀.2.1.2.theta
    obtain ⟨χS, χT, hWe⟩ := _root_.GlobalTheory.GVecAt.exists_isWeilDatumO_omT_at_last W j h
    have hb : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
    have hb' : f.g.bT ∈ GfC _ := hVT.bT.1 ▸ hv.bT
    have hΨ1 : v.ΨT j h 1 = comb f.c.ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) := by
      rw [hΨ, GlobalTheory.FiniteFock.pureTensorO_one]
    have hov := vac_mono (· ∈ v.gP) (hΨ1 ▸ hv.ΨT j h 1)
    have honz : comb f.c.ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0 := by
      intro h0
      obtain ⟨P, hP⟩ := hVT.nz.2 j h
      apply hP
      rw [hΨ]
      have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ _ _ _ hWe hinf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (f.g.b (j + 1)) f.g.bT
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) _ hvth P
      rw [hfin.2, comb_pureTensorO hstd hinf _ _ _ _ (fin _ o hstd ho) (hWe.om_pres _ _ hvth), h0, pureTensorO_zero]
    have hg0nz : omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) ≠ 0 := fun h0 =>
      honz (by rw [h0]; exact comb_zero _)
    obtain ⟨c, hc⟩ := scalar D f.c.ψ _ _ M (v.N (j + 1)) M' v.NT v.gP o o' _ hstd hM hM' (hv.sd (j + 1) (by omega))
      hv.sdT ho ho' hg0 hov ho'v (ho'nz hg0nz)
    have hc0 : c ≠ 0 := fun h0 => honz (by rw [hc, h0, zero_smul])
    refine ⟨κ / c, div_ne_zero hκ hc0, fun d hd P => ?_⟩
    have hbase : omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) =
        (κ / c) • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) := by
      rw [hdat d hd, hc, comb_smul, smul_smul, div_mul_cancel₀ _ hc0]
    rw [hΨ P]
    have := fock hinf hWe (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (fin _ d hstd hd.1) (fin _ o hstd ho) (fin _ _ hstd ((hv.atG j).2.2 h)) hvth hb hb' hbase P
      (one_mem (GinfC _)) (one_mem (GinfC _))
    simpa only [one_mul] using this
  choose cm hcm using mid
  choose ct hct using top
  let s : ℕ → ℂ := fun i => if hi : i + 1 < D.R.m then cm i hi else
    match i with
    | 0 => 1
    | k + 1 => if hk : k + 2 * 0 + 2 = D.R.m then ct k hk else 1
  refine ⟨s, fun i => ?_, fun j hj d hd P a ha a' ha' => ?_, fun j h d hd P => ?_⟩
  · show (if hi : i + 1 < D.R.m then cm i hi else
      (match i with
      | 0 => 1
      | k + 1 => if hk : k + 2 * 0 + 2 = D.R.m then ct k hk else 1)) ≠ 0
    split_ifs with hi
    · exact (hcm i hi).1
    · split
      · exact one_ne_zero
      · split_ifs with hk
        · exact (hct _ hk).1
        · exact one_ne_zero
  · have hs : s j = cm j hj := dif_pos hj
    rw [hs]
    exact (hcm j hj).2 d hd P a ha a' ha'
  · have hs : s (j + 1) = ct j h := by
      show (if hi : j + 1 + 1 < D.R.m then cm (j + 1) hi else if hk : j + 2 * 0 + 2 = D.R.m then ct j hk else 1) = ct j h
      rw [dif_neg (by omega), dif_pos h]
    rw [hs]
    exact (hct j h).2 d hd P
end GlobalTheory.GVecAt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocallySplitLift
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
namespace GlobalTheory.LiftSplitLoc
end GlobalTheory.LiftSplitLoc
namespace GlobalTheory.LiftSplitLoc
end GlobalTheory.LiftSplitLoc
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locally_split_lift_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  first | exact @_root_.UpperTheory.One.M.liftSplitLocal_of_howeDuality_alt | exact _root_.UpperTheory.One.M.liftSplitLocal_of_howeDuality_alt | (intros; apply _root_.UpperTheory.One.M.liftSplitLocal_of_howeDuality_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNbcAuSideStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nbc_auSide_true_of_isEmpty_loc : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), IsEmpty D.nd.Loc → ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A := by
  first | exact @_root_.GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty | exact _root_.GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty | (intros; apply _root_.GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepresentationComponent
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.CoefDuty GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
set_option maxHeartbeats 2000000 in
theorem goodFTAll_pinned_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp), _root_.GlobalTheory.CoefDuty.OPinAlt a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hDZ hL D cf nch tp a hp hloc
  have h0 : GoodFTAll a.nt.D := by
    refine _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_of_local_alt hG hZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.row a.depth hp.lab
      (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) ?_ hloc
    intro I rc hrc k v
    refine _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL a.nt.D a.nt.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) k v (a.nt.A.grp.kv k v) ?_
    rw [← hp.gen k]
    exact a.nt.A.grp.tg_tame k v
  have e : ∀ D', D' = withLoc a.nt.L → GoodFTAll D' := by
    rintro _ rfl
    exact h0
  exact e D a.nt.eq
set_option maxHeartbeats 1000000 in
theorem exists_representation_component_alt : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp), _root_.GlobalTheory.CoefDuty.OPinAlt a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_pinned_alt
end DiscreteGroups.sglob.DzType.Rt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → ∃ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S ∧ _root_.GlobalTheory.SplitRead.LawsAlt S ∧ SuppLaws S := by
  first | exact @_root_.GlobalTheory.TrueReading.exists_true_reading_alt | exact _root_.GlobalTheory.TrueReading.exists_true_reading_alt | (intros; apply _root_.GlobalTheory.TrueReading.exists_true_reading_alt <;> assumption)
end
end


import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0924
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0196
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0214
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0207
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0216
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0217
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0034
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0187
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0199
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0130
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0094

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlaceLabelOfConjugatePlace
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabConjPlace
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
end GlobalTheory.LabConjPlace
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LabConjPlace in
theorem GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ∀ (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  intro hPr hL D P hLab S hS i k v hw hχ u _ hlab w' hc s
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hLab
  have hw'over : w' ∈ placesOver D.host.E (D.host.g k) := by
    have h0 := D.naut.plGw_over k v
    simp only [placesOver, Set.mem_setOf_eq] at h0 ⊢
    exact (hc _ _ (by simp)).1 h0
  rw [hγ3 k w' hw'over, P.T.tw, WD.lab_lpTw]
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin D.R.m, jj.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  set χ := D.naut.tw (D.naut.muC i) D.naut.etaTinv with hχdef
  set μH := P.tp.tup (D.nd.mu i) jj with hμH
  have e1 : (P.chr.e1 χ).1 = μH * P.cf.eta⁻¹ := by
    rw [hχdef, P.chr.tw, P.chr.muC i jj hjj, P.chr.etaTinv]
  have hcomp' : IsComp (P.chr.e1 χ).1 w' ((P.chr.e1 χ).1.loc w') := ⟨ParLaws.isSmoothChar_loc _ w', fun x => rfl⟩
  rw [_root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hPr.fin hL D P χ w' _ hcomp']
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')); obtain ⟨a', ha', ε', H'⟩ := hOpn) | obtain ⟨a', ha', ε', -, H'⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')
  change WD.lab _ _ (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w') (GlobalTheory.LocGL.IrrGL.ofChar ((P.chr.e1 χ).1.loc w') hcomp'.1)) = _
  rw [H'.one]
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, Hw⟩ := hOpn) | obtain ⟨a, ha, ε, -, Hw⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hlab' : WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) = X - C (u : ZMod (D.host.g k)) := by
    rw [← Hw.one _ hχ]; exact hlab
  have HS : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) := by
    by_contra hn
    rw [WD.lab_of_not hn] at hlab'
    have := congrArg natDegree hlab'
    rw [natDegree_one, natDegree_X_sub_C] at this
    exact absurd this (by norm_num)
  have hdeg : (WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ))).natDegree =
      WD.lpDim (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) := by
    rw [hlab', natDegree_X_sub_C]; simp [WD.lpOfChar]
  have htame := WD.tame_of_natDegree_lab hdeg
  rw [WD.lpOfChar] at htame
  have hwild : ∀ σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)), (σ : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) →
      ((S i _ hw).mu.comp a) σ = 1 := by
    intro σ hσ
    have := congrFun (LinearMap.congr_fun ((WD.tame_mk _).mp htame σ hσ) fun _ => 1) 0
    exact Units.ext (by simpa using this)
  have hval := (WD.lab_lpOfChar_eq_iff HS (ha.smooth hχ) hwild u).mp hlab'
  have hμw : μH.loc (D.naut.plGw k v) = (S i _ hw).mu := by
    obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E μH (D.naut.plGw k v)
    exact (huniq _ ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩).trans (huniq _ (hS.mu i _ hw jj hjj)).symm
  obtain ⟨c, hcE, hcA, hcγ⟩ := hγ2 k v w' hc
  set τc : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E) with hτc
  have hcE' : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τc x) := hcE
  have hγ' : γ k w' = GlobalTheory.ConjTransport.conjG c τc hcE' (D.ntypes.tg k v) := by
    ext y
    rw [GlobalTheory.ConjTransport.conjG_apply]
    have := hcγ (c.symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this
  have hIne' : γ k w' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') := by
    rw [hγ']; exact GlobalTheory.ConjTransport.conjG_mem_Ine c τc hcE' hcA HS.2.1
  have HS' : TeichmullerInertiaLabelCondition (D.nd.plOm.1 w') w' (D.ntypes.teichC k) (γ k w') :=
    ⟨GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw'over, hIne', HS.2.2⟩
  have hcsd : IsCSD D.host μH := by
    rw [hμH, ← P.chr.muC i jj hjj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
  obtain ⟨ic, hic, hicE, hicμ⟩ := GlobalTheory.T.conjSelfDual_heckeChar_conjugatePlace_component_inv D.host μH hcsd _ w' hc
  have htr : ∀ (σ : Weil (D.nd.plOm.2 (D.naut.plGw k v))) (σ' : Weil (D.nd.plOm.2 w')),
      (∀ z, c ((σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) z) = (σ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (c z)) →
      μH.loc w' (a' σ') = ((S i _ hw).mu (a σ))⁻¹ := by
    intro σ σ' hσ
    rw [← _root_.GlobalTheory.T.conjugate_places_completion_alt hL (D.nd.plOm.2 (D.naut.plGw k v)) (D.nd.plOm.2 w') c τc.toRingHom ic
      (fun z => (hcA z).symm) hcE' hic hicE Hw H' (μH.loc w') (ParLaws.isSmoothChar_loc _ _) σ σ' hσ, hicμ, hμw]
  have heta : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') →
      P.cf.eta.loc w' (a' σ') = 1 := fun σ' hσ' => loc_artin_ine ha' _ (P.cf.isEta.unr w') σ' hσ'
  have hξ : ∀ σ', ((P.chr.e1 χ).1.loc w') (a' σ') = μH.loc w' (a' σ') * (P.cf.eta.loc w' (a' σ'))⁻¹ := by
    intro σ'; rw [e1, HChar.loc_mul, HChar.loc_inv]
  have hwild' : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 w') →
      (((P.chr.e1 χ).1.loc w').comp a') σ' = 1 := by
    intro σ' hσ'
    have hA' : ∀ y, y ∈ D.nd.plOm.1 w' ↔ c.symm y ∈ D.nd.plOm.1 (D.naut.plGw k v) := fun y => by
      rw [hcA, RingEquiv.apply_symm_apply]
    have hσw : GlobalTheory.ConjTransport.conjG c.symm τc.symm (GlobalTheory.ConjTransport.symm_alg c τc hcE') (σ' : G _ _) ∈
        Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) :=
      GlobalTheory.ConjTransport.conjG_mem_wild c.symm τc.symm _ hA' hσ'
    let σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)) := ⟨_, Ine_le_Weil _ (Wild_le_Ine hσw)⟩
    have h1 := htr σ σ' (fun z => by
      show c (GlobalTheory.ConjTransport.conjG c.symm τc.symm _ (σ' : G _ _) z) = _
      rw [GlobalTheory.ConjTransport.conjG_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply])
    have h2 := hwild σ hσw
    rw [MonoidHom.comp_apply] at h2
    rw [MonoidHom.comp_apply, hξ, h1, heta σ' (Wild_le_Ine hσ'), h2]
    simp
  rw [WD.lab_lpOfChar_eq_iff HS' _ hwild']
  rw [MonoidHom.comp_apply, hξ, htr ⟨D.ntypes.tg k v, Ine_le_Weil _ HS.2.1⟩ _ (fun z => (hcγ z).symm),
    heta _ hIne', inv_one, mul_one]
  have hx : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ≠ 0 :=
    (_root_.map_ne_zero _).2 u.ne_zero
  rw [MonoidHom.comp_apply] at hval
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hval, map_inv₀]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel₀ hx, map_one]
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeLabel_of_conjugate_place_alt : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ∀ (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  first | exact @_root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SerLocOfTiesLe
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf GlobalTheory.SerSys GlobalTheory.SerSys.Bridge
open scoped Classical
attribute [local instance] GlobalTheory.SerSys.Bridge.factT
theorem serLocLe_of_alt (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc) (hP : LabParamLe D.R.nV D L rc) : SerLoc D :=
  have hS : ∀ k, (OfLabel.ofLabel (L k) (five_le D k) hG).IsOf (L k) := fun _ _ _ => rfl
  GlobalTheory.SerLocal.serLoc D _ (hL.sysTie hS) hU (_root_.DiscreteGroups.sglob.DzType.Rt.locType_of_labTie_locComp_labParamLe hL hS hC hP)
theorem serLoc_of_tame_param_le (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) : SerLoc D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.serLocLe_of_alt D L rc hG hL hU hC (labParamLe_of D L rc hG h1 h2 h3)
end DiscreteGroups.sglob.DzType.Rt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SphericalBaseChangeInertCompatible
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.SphInertRef
section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}
end Read
end GlobalTheory.SphInertRef
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sph_inert_cls_of_iso_typ_comap_ne_bot : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → SphericalInertData.SphInert D.nd D.naut D.nbc j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) := by
  first | exact @_root_.UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot | exact _root_.UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot | (intros; apply _root_.UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValuationMultiplicityOfConsecutiveRun
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ValMultRun
section Algebra
open IsLocalRing IsDedekindDomain
open scoped NNReal
end Algebra
section Centre
open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp)
open scoped NNReal
end Centre
section Component
open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.TangentOrigin GlobalTheory.Vanishing.H0
open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp)
open GlobalTheory.AllWt (secZ exOf suppOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (genVal genPoint)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open scoped NNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
end Component
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic GlobalTheory.Vanishing in
set_option maxHeartbeats 1000000 in
theorem valuation_multiplicity_of_consecutive_run_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ValMult Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) (wtOf (dat p i) (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) 0) := by
  intro hP hGD hQ hS hT hL h2 h3 h4
  refine ((((_root_.GlobalTheory.T.exists_nonzero_section_weight_bound_alt_alt hP h2 h3 h4).and (_root_.GlobalTheory.T.exists_section_order_bound_hilbertSamuel_alt hP h2 h3 h4)).and (_root_.GlobalTheory.T.exists_phi_pos_of_centred_off_U0 hP h2 h3 h4)).and _root_.GlobalTheory.HSApp.wtBig_run_alt).imp
    fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩, ⟨C'', hC'', x2, hx2⟩⟩, ⟨C₃, hC₃, x3, hx3⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 x3), fun x hx' hle ι p hp i hi Y hY Z => ?_⟩
  simp only [max_le_iff] at hle
  have hB := hx3 x hx' hle.2.2 ι p hp i hi
  have hP' := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨TF⟩ := @_root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt hP' _ _ _ _ _ _ _ Y.d.Xo₂ Y.d.c₂ hB.one_le
  obtain ⟨θ, hθ, -, hst⟩ := hx x hx' hle.1.1 ι p hp i hi Y hY Z TF
  have hJ := hx1 x hx' hle.1.2 ι p hp i hi Y hY Z TF _ (Or.inl rfl)
  have hD := hx2 x hx' hle.2.1 ι p hp i hi Y hY Z TF
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have h3 : Module.finrank ℚ (Fm.D x ι).host.E = 4 * (Fm.D x ι).R.ord :=
      (Fm.D x ι).host.finrank_cmField
    have h : 4 ≤ (Fm.D x ι).R.ord := (Fm.D x ι).host.four_le_n'
    omega
  have hCI : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF _⟩
  have hfree := _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP' hGD hQ hP.q15 hP.q16 hS hT.toroidalChartsForFan hL _ _ _ _ _ _ TF Z _ Y.U hY.1.geo
    hB.one_le _ (gaps_of_wtBig _ _ _ _ hB _ List.mem_cons_self).2 (hCI _)
  refine valMult_of_section TF.X Z Y.U (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.1.geo) hCI ?_ hfree θ hθ
    fun y hy ν hν => ?_
  · rw [CompHt.uPrime]
    module
  obtain ⟨φ, hφ, hPh⟩ := hD y hy ν hν
  obtain ⟨w, hw, hwb⟩ := hJ y hy ν hν φ hPh
  refine ⟨w, hw, fun j hj j' hj' => ?_⟩
  obtain ⟨hw0, hwm⟩ := hwb j' hj'
  obtain ⟨zw, hzw⟩ := WithZero.ne_zero_iff_exists.1 hw0
  have ew : ν (H0.germ j' y (memTop y) hj' w) =
      ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zw)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [neg_neg, ofAdd_toAdd]; exact hzw.symm
  have bw := hwm _ ew
  by_cases h0 : ν (H0.germ j y (memTop y) hj θ) = 0
  · rw [h0, zero_pow three_ne_zero]
    exact zero_le'
  · obtain ⟨zt, hzt⟩ := WithZero.ne_zero_iff_exists.1 h0
    have et : ν (H0.germ j y (memTop y) hj θ) =
        ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zt)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      rw [neg_neg, ofAdd_toAdd]; exact hzt.symm
    have bt := hst y hy ν hν φ hPh j hj _ et
    have hle' : (3 * Multiplicative.toAdd zt : ℝ) ≤ (8 * Multiplicative.toAdd zw : ℝ) := by
      push_cast at bw bt ⊢
      linarith
    have hle'' : 3 * Multiplicative.toAdd zt ≤ 8 * Multiplicative.toAdd zw := by exact_mod_cast hle'
    rw [← hzt, ← hzw, ← WithZero.coe_pow, ← WithZero.coe_pow, WithZero.coe_le_coe, ← Multiplicative.toAdd_le,
      toAdd_pow, toAdd_pow]
    simpa using hle''
end GlobalTheory.ValMultRun
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ValMult Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) (wtOf (dat p i) (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) 0) := by
  first | exact @_root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt | exact _root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt | (intros; apply _root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt <;> assumption)
end
end
end


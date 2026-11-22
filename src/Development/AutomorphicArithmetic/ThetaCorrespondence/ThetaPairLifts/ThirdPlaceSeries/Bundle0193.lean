import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0191
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0028
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0190
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0155
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0151
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1026
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0171
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0403
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DaAutRepSphAt
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0043
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0009
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0192
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0817
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0163
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotOfPlacedBy
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZero
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem pg_isTypePlaces_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg := by
  have H := W.Q.charW.base.lev
  let M := (_root_.GlobalTheory.Fam.pk_z W).toLevCh
  let μ := W.P.A3.A.μ0
  let M' : LevCh D Unit := { M with xiH := fun _ => M.xiH μ, xi := fun _ => M.xi μ, Q := fun _ => M.Q μ, xiR := fun _ => M.xiR μ }
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := H
  exact GlobalTheory.SeeSaw.ComCols.isTypePlaces_of_levCh (L := M') ⟨h1, h2, fun _ => h3 _, fun _ _ _ => rfl, h5, fun _ => h6 _, fun _ => h7 _,
    fun _ => h8 _, h9, fun _ => h10 _, fun _ => h11 _, fun p hp => (h12 p hp).imp fun _ e _ => e _, fun _ => h13 _, h14, fun _ => h15 _,
    h16, h17, h18, h19⟩
set_option maxHeartbeats 1000000 in
theorem stZero_is_com_zero_of_pkHyp (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hm : 0 < D.R.m) : (_root_.GlobalTheory.LevZero.levelZeroState W).st.Is (_root_.GlobalTheory.BaseChain.com_z W) 0 := by
  have h := _root_.GlobalTheory.BaseChain.stage_y_is W hP 0 hm
  exact ⟨h.rank, h.sigOK, h.sig, h.par, h.selfDual, h.frame, h.base, ⟨r_le_Y 0, fun _ => 1, rfl⟩, h.haar, h.fund⟩
set_option maxHeartbeats 1000000 in
theorem bot_stZero_of_gRead (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hm : 0 < D.R.m) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (hv : v.Is)
    (ht : _root_.GlobalTheory.Fam.CommutingVectorTie f v) {n : ℕ} (G : (_root_.GlobalTheory.Fam.pk_z W).Pg → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hR : _root_.GlobalTheory.Fam.LocalGroupReading f (fun i => G (pl i)) pl) :
    Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G := by
  refine ⟨_root_.GlobalTheory.BaseChain.com_is_alt W hP, rfl, _root_.GlobalTheory.LevZero.stZero_is_com_zero_of_pkHyp W hP hm, ?_, _root_.GlobalTheory.LevZero.pg_isTypePlaces_alt W, ?_, ?_, ?_⟩
  · have h := hv.b 0
    rw [ht.b 0] at h
    exact h
  · intro PP
    obtain ⟨i, rfl⟩ := pl.surjective PP
    exact ⟨(hR.idem i).1, (hR.idem i).2, fun a ha => hR.frame i 0 a ha⟩
  · intro g
    refine (hR.lev g).1.trans ⟨fun h PP => ?_, fun h i => h (pl i)⟩
    obtain ⟨i, rfl⟩ := pl.surjective PP
    exact h i
  · intro g x hx
    have h := (hR.lev g.1).2 g.2 (fun i => x (pl i)) (fun i => hx (pl i))
    exact h.trans (Equiv.prod_comp pl (fun PP => (G PP).S.P.lam (x PP)))
set_option maxHeartbeats 1000000 in
theorem bot_of_placedBy_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.LevZero.PlacedByLocalGroups f B v o G pl → GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP u f B k _ _ _ _ ι v o n G pl h
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have e : (fun i => G (pl.symm (pl i))) = G := funext fun i => by rw [Equiv.symm_apply_apply]
  have hR : _root_.GlobalTheory.Fam.LocalGroupReading f (fun i => G (pl.symm (pl i))) pl := by rw [e]; exact h.read
  exact _root_.GlobalTheory.LevZero.bot_stZero_of_gRead W hP hm f v h.vis h.tie (fun PP => G (pl.symm PP)) pl hR
end GlobalTheory.LevZero
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharpolyGeomFrob
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GeomFrobChar
open GlobalTheory.WeilDeligne Polynomial in
theorem charpoly_inv_frob_eq_prod_X_sub_C : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
      (rc : GlobalTheory.LocGL.IrrGL (w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ S →
    ∀ t : ℝ, GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw t →
    ∀ g : G E Ω, IsFrob (F := E) B (normV w) g →
      (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
        Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ)))).prod := by
  intro E Ω _ _ _ _ _ l _ ι a r hr w hl B h rc hrc σ S hS t hw g hg
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ S).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hS⟩)
  have e := _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake hrc (σ := ParLaws.toRep σ) hα
  let φ : Weil h := ⟨g, mem_Weil_of_isFrob h hg⟩
  have hφ : deg φ = 1 := deg_eq_one_iff.mpr hg
  have h1 := charPol_wdOf hl ι (Units.continuous_val.comp hr) φ⁻¹
  have e' : rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := e
  have h2 : ((WDRep.diag h fun i => (α i)⁻¹).tw t).ρ φ⁻¹ =
      GlobalTheory.WeilDeligne.diagEnd fun i => (α i : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [WDRep.tw_ρ, WDRep.diag_ρ, deg_inv, hφ, Complex.ofReal_neg, Complex.cpow_neg]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply, mul_assoc, mul_left_comm]
  rw [hw, e', WD.lpTw_mk, WD.charPol_mk, h2, charpoly_diagEnd] at h1
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [zpow_neg_one]
  refine (show _ = _ from h1.symm).trans ?_
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp
end GlobalTheory.GeomFrobChar
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ComIsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChain_com_z_is_of_pkHyp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (_root_.GlobalTheory.BaseChain.com_z W).Is := by
  first | exact @_root_.GlobalTheory.BaseChain.com_is_alt | exact _root_.GlobalTheory.BaseChain.com_is_alt | (intros; apply _root_.GlobalTheory.BaseChain.com_is_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCuspValueLePhiOfHilbertSamuel
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
set_option maxHeartbeats 2000000 in
theorem exists_cusp_value_le_phi_of_hilbertSamuel_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  intro h1 h2 h3 h4
  refine ((((_root_.GlobalTheory.T.jets_constant_section_eq_alt h1 h2 h3 h4).and (_root_.GlobalTheory.T.jetNum_thA_ub h3)).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt h3)).and ((_root_.GlobalTheory.T.jetNum_nCol_lenT_bounds_of_quo h3).and h3)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hJ⟩, ⟨C1, hC1, x1, hN⟩⟩, ⟨C2, hC2, x2, hA⟩⟩, ⟨⟨C3, hC3, x3, hB⟩, ⟨C4, hC4, x4, hS⟩⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 (max x3 x4)), fun x hx' hle ι p hp i hi Y hY Z TF la hla y hy T io y' g φT hg hφT hpt => ?_⟩
  have l0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have l1 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have l2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have l3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  have l4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  obtain ⟨-, -, hfin, hquo, -⟩ := hA x hx' l2 ι p hp i hi
  obtain ⟨⟨u1, hu1⟩, -⟩ := (hS x hx' l4 ι p hp i).2.2.2.2.2.2 hi
  have hnum : GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) (1 / 2500) := by
    rcases hla with rfl | hla
    · have := (hB x hx' l3 ι p hp i hi u1 hu1).1
      rwa [hquo u1 hu1] at this
    · rw [Set.mem_singleton_iff] at hla
      subst hla
      exact hN x hx' l1 ι p hp i hi
  obtain ⟨f, hf0, hfb⟩ := hJ x hx' l0 ι p hp i hi Y hY Z TF la hla (1 / 2500) hnum y hy T io y' g φT hg hφT hpt
  have hE : Extends TF.X Z Y.U la := GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace (Fm.D x ι) p.T.toCore ((i : ℕ) + 1) Y _ _ hY.1 hfin Z TF la
  refine ⟨hE.equiv f, ?_⟩
  have e : ofSpace TF.X Z Y.U la (hE.equiv f) = f := hE.equiv.symm_apply_apply f
  rw [e]
  refine ⟨hf0, ?_⟩
  rw [div_eq_mul_one_div, mul_comm]
  exact hfb
end GlobalTheory.HSApp
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_cusp_value_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  first | exact @_root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel_alt | exact _root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel_alt | (intros; apply _root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportAtBundles
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published
namespace GlobalTheory.ExportClose0
theorem exportAt_bundles_alt : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), FieldOk X → _root_.UpperTheory.GalS.GalHodgeN D G.wd → LocalSituation.Conclusion5 D → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  intro hCheb hPT hCD hTame hLF hLTD hLEC hGF hGEC hUO hadm hGW hRCA hCusp hCheb1 hGAR hTor hSR hSI hHI hHT hHRT
  intro D nch xd X Y G hF hGH hconds hTie hBase
  exact _root_.GlobalTheory.T.realization_of_published_alt hCheb hPT hCD hTame hLF hLTD hLEC hGF hGEC hUO hadm hGW hRCA hCusp hCheb1 hGAR hTor D nch xd X Y G
    (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hCusp hGAR hSR hSI D X (twEOf xd) Y hF).1
    (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hCusp hGAR hSR hSI D X (twEOf xd) Y hF).2
    (GlobalTheory.T.heckeOperator_preserves_supLattice_realSide hCusp hHI hHT hHRT D X)
    hGH hconds hF.galois hF.roots hTie hBase
end GlobalTheory.ExportClose0
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerTail
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.SphLoc
section Alg
variable {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
end Alg
section Val
open ValuativeRel Filter Topology
variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
end Val
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end
end GlobalTheory.SphLoc
end
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.SphLoc.main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) x,
    GlobalTheory.AutQuot.LocAt π s.w x → π.SphericalAtPlace s.v → (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) x).unr := by
  intro hL D π s x hx hs
  obtain ⟨s', σ, h, hσ, e⟩ := hx
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  have hsph := _root_.UpperTheory.One.M.Sph.isSph π s' σ hσ (hv ▸ hs)
  have hu := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s'.w)) σ).2 hsph
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 D.host.E)) (_ : u = u') (a : GlobalTheory.LocGL.IrrGL (u.adicCompletion D.host.E))
      (b : GlobalTheory.LocGL.IrrGL (u'.adicCompletion D.host.E)), HEq a b →
      (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 u) a).unr → (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 u') b).unr := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    exact id
  exact key _ _ h _ _ e hu
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InePolOfHas
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
section Loc
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory GlobalTheory.RegType
variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {w : HeightOneSpectrum (𝓞 E)}
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (hDZ : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ
theorem inePol_eq_liftPoly_of_cuspidal {n : ℕ} (hn : 0 < n) (hbig : n = 1 ∨ 16 * n ^ 2 < g) (σ : Irr (w.adicCompletion E) n) (hc : IsCuspidal σ.π) (f : (ZMod g)[X])
    (hf : Has (sysOf L h5 hA) (σ.π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) f) :
    (rc (cls σ.toIrrRep)).inePol t = TameGen.liftPoly L.teich f := by
  have hi' := GlobalTheory.TameRecord.continuous_symm w i hi
  have hc' : IsCuspidal (σ.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)) :=
    GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap i.symm hi σ.π hc
  let ρ : GLRep g := ⟨n, Rep.of (σ.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom))⟩
  have hρ : TameGen.IsSC ρ := ⟨hn, (Model.isIrrRep_iff _).2 (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp σ.irr _
      fun y => ⟨_, GlobalTheory.TameRecord.glMap_apply_symm i y⟩), GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal _ _ _ _ hc'⟩
  obtain ⟨τ, φ, hs, hinj, heq, he⟩ := TameGen.exists_simple_of_has (sysOf L h5 hA) ρ.2.ρ f hf
  have hφ : (fixK1 ρ.2.ρ).subtype ∘ₗ φ ≠ 0 := fun e => by
    have h0 : ∀ u : τ, u = 0 := fun u => hinj (Subtype.ext (by simpa using LinearMap.congr_fun e u))
    exact CategoryTheory.id_nonzero τ (by ext u; exact (h0 _).trans (h0 _).symm)
  have hfix : fixK1 ρ.2.ρ ≠ ⊥ := fun e => hφ (LinearMap.ext fun u => (Submodule.eq_bot_iff _).1 e _ (φ u).2)
  have hτ : FiniteGL.IsCuspidal τ.ρ := fun b hb hb' u hu => hinj (by
    rw [map_zero]
    exact GlobalTheory.DepthZeroCusp.depthZeroCuspidal g ρ hρ hfix b hb hb' _ fun x hx => by rw [← heq, hu x hx])
  refine hDZ E Ω g A w h rc hrc i hi κ L t ht hκ n hbig σ.toIrrRep (IrrGL.isCusp_of.2 ⟨hn, hc⟩) τ f
    (isCuspOf_of_series L h5 hA τ (TameGen.isCusp_character hn τ hs hτ) f he) ⟨_, hφ, fun k u => ?_⟩
  exact (congrArg Subtype.val (heq (red g n k) u)).trans (repK_red ρ.2.ρ k (φ u))
theorem inePol_eq_liftPoly_of_has (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma) {n : ℕ}
    (π : Irr (w.adicCompletion E) n) (hB : 16 * n ^ 2 < g) (f : (ZMod g)[X])
    (hf : Has (sysOf L h5 hA) (π.π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) f) :
    (rc (cls π.toIrrRep)).inePol t = TameGen.liftPoly L.teich f := by
  have hi' := GlobalTheory.TameRecord.continuous_symm w i hi
  obtain ⟨s, d, σ, hs⟩ := GlobalTheory.T.exists_cuspidalSupport_irreducibleSmoothGL hBZ hGL _ n π
  have h1 := hrc.recSupp n s π d σ hs (ineIncl h ⟨t, ht⟩)
  obtain ⟨-, hc, e, U, T, hT⟩ := hs
  obtain ⟨φ⟩ := GlobalTheory.IndField.multiProd_comp_glMap i.symm hi' hi
    (GlobalTheory.SplitWeil.nabs_map_of_homeomorph i.symm hi' hi) e (fun a => (σ a).π)
  have h2 : IsSubquotient (π.π.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom))
      ((multiProd e fun a => (σ a).π).comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)) :=
    ⟨⟨U.toSubmodule, fun x _ hv => U.apply_mem_toSubmodule _ hv⟩, ⟨T.toLinearMap, fun x => T.isIntertwining' _⟩, hT⟩
  obtain ⟨fs, hfs, rfl⟩ := series_of_isSubquotient (sysOf L h5 hA) e
    (fun a => (σ a).π.comp (Matrix.GeneralLinearGroup.map (n := Fin (d a)) i.toRingHom))
    (h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)) f hf
  have hbig : ∀ a, d a = 1 ∨ 16 * d a ^ 2 < g := fun a =>
    Or.inr (lt_of_le_of_lt (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (DiscreteGroups.sglob.DzType.Rt.le_of_sigmaEquiv e a) 2)) hB)
  have h3 : ∀ a, (rc (cls (σ a).toIrrRep)).charPol (ineIncl h ⟨t, ht⟩) = TameGen.liftPoly L.teich (fs a) := fun a => by
    rw [← WD.inePol_of_mem_Ine _ ht]
    exact _root_.DiscreteGroups.sglob.DzType.Rt.inePol_eq_liftPoly_of_cuspidal i hi hrc hDZ κ L h5 hA ht hκ (hc a).1 (hbig a) (σ a) (hc a).2.2 _ (hfs a)
  have h4 : ∀ u : Finset (Fin s), TameGen.liftPoly L.teich (∏ a ∈ u, fs a) = ∏ a ∈ u, TameGen.liftPoly L.teich (fs a) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp [TameGen.liftPoly_one]
    | insert a u ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, TameGen.liftPoly_mul _ (TameGen.Has.monic (hfs a)).ne_zero
        (monic_prod_of_monic _ _ fun b _ => TameGen.Has.monic (hfs b)).ne_zero, ih]
  rw [WD.inePol_of_mem_Ine _ ht, h4]
  exact h1.trans (Finset.prod_congr rfl fun a _ => h3 a)
end Loc
end DiscreteGroups.sglob.DzType.Rt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocAllExists
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting
set_option maxHeartbeats 2000000 in
theorem locAll_exists_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → BlocksUnique D → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam) := by
  intro hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi hO hBU big
  obtain ⟨X, T, ⟨Sp⟩⟩ := _root_.GlobalTheory.T.side_rational_eigen_data_alt hGAR GlobalTheory.HeckeStdFacts.heckeStdPlain D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hO hpsi big
  obtain ⟨Y, Cb, ⟨aut⟩⟩ := _root_.GlobalTheory.T.side_rational_level_data_alt hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi big X T Sp
  obtain ⟨Br, -⟩ := _root_.GlobalTheory.HeightCounting.locBr_of_autSpec_alt D cf jE A M C tp.tup big X T Sp Y Cb aut
  have hchi := _root_.GlobalTheory.T.side_rational_character_data_alt hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  have hMt := _root_.GlobalTheory.HeightCounting.MtIndep.typeV_iSup_indep_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  obtain ⟨Z, hbc, hrb, hmt, hss⟩ := locTy_exists D A.row A.pl X Y hBU hCheb aut.locW aut.iotaQC aut.kFbar Sp.heckeLoc_gamma_places hchi hMt
  exact ⟨{ X := X, T := T, Y := Y, C := Cb, Z := Z, B := Br, bc_tie := hbc, rbar_tie := hrb, mtpar_tie := hmt }, Sp, ⟨aut⟩, hss⟩
end GlobalTheory.HeightCounting
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnr
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
section CharUnr
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
theorem locPar_ofChar_unr_and_frobEig (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).unr ∧
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  have e2 : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, H.one]
    have hs := ha.smooth (ParLaws.isSmoothChar_loc χ w)
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  exact ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), by simp⟩
end CharUnr
section Twist
end Twist
section G
end G
end GlobalTheory.HodgeOfTrue
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParTwistAbsPow
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
include hF in
theorem local_parameter_twist_abs_pow (π : CG E a) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) (h : IsPlaceOver A w) :
    _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (π.twist ν) h = (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpTw s := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  refine (_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL (hσ.twist ν) h).trans ?_
  rw [show _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (Quotient.mk _ π) h = _ from _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h, ← H.nu_eq]
  refine congrArg _ ((GlobalTheory.LocGL.IrrGL.tw_of σ.ρ σ.smooth σ.irred _ (isSmoothChar_loc ν w)).symm.trans ?_)
  unfold GlobalTheory.LocGL.IrrGL.nu
  congr 1
  exact loc_of_isAbsPow hν w
end Local
section Polar
end Polar
section Record
end Record
section True
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
end
end
end


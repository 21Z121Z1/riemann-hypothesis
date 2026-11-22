import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbit
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousNormFactorFlatLineOrthonormalFrame
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrthoFlatFac

theorem sum_wtOf_flatWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) :
    (∑ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ)) = (Dw.q : ℝ) - Dw.p := by
  classical
  have key : ∀ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) =
      (if ρ = conjEmb τ.1 then (Dw.q : ℝ) else 0) - if ρ = τ.1 then (Dw.p : ℝ) else 0 := fun ρ => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hm : Dw.mult ρ = Dw.p := if_pos h
      have h1 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = τ.1 then -1 else 0 := fun i =>
        (wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i (hm ▸ i.2)).trans (by simp [flatWt, parWt, Subtype.ext_iff])
      simp only [h2]
      split_ifs <;> simp_all
    · have hm : Dw.mult ρ = Dw.q := if_neg h
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = conjEmb τ.1 then 1 else 0 :=
        fun i => by
          have := wtOf_small (flatWt Dw τ) 0 ⟨_, conj_mem h⟩ i (hm ▸ i.2)
          simp only [Formalism.L2.Pj.conjEmb_conjEmb] at this
          rw [this]
          by_cases e : ρ = conjEmb τ.1
          · simp [flatWt, parWt, e, Formalism.L2.Pj.conjEmb_conjEmb]
          · have : conjEmb ρ ≠ τ.1 := fun e' => e (by rw [← e', Formalism.L2.Pj.conjEmb_conjEmb])
            simp [flatWt, parWt, Subtype.ext_iff, e, this]
      simp only [h2]
      split_ifs <;> simp_all
  simp only [key, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem homFac_flatWt_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ)
    (τ : Psi H) (k : U.Comp) (w : (U.X k).dom), (U.X k).IsOrtho w.1 →
    GlobalTheory.CompHS.homFac U x (flatWt Dw τ) k w = Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) := by
  intro E _ _ _ H Dw l Xo c σ r U x τ k w ho
  rw [GlobalTheory.CompHS.homFac, GlobalTheory.OrbitNfac.nfac_ortho _ ho, mul_one, lieFacZ, sum_wtOf_flatWt]
  congr 1
  ring

end GlobalTheory.OrthoFlatFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityRealHolds
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
  GlobalTheory.HoweD GlobalTheory.HoweR

namespace GlobalTheory

theorem howeDualityReal_holds : GlobalTheory.Published.HoweDualityReal := by
  intro F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX1 hX2 hW1 hW2 _ _ _ _ hWeil τ hcX hcW
  obtain ⟨P, Q, R, S, A, C, Φ, c, c', hfr, hinj, hrange, hact1, hact2⟩ :=
    GlobalTheory.T.exists_frames_fockMap_polynomial_lie_actions F E σ hCM n d X W M ψ χX χW om hψ hX1 hX2 hW1 hW2 hWeil τ hcX hcW
  obtain ⟨-, hA, hC⟩ := hfr
  have hstab : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ w, Stab (actAt (V := fun w =>
      Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) :=
    fun N hN => GlobalTheory.T.thetaLift_submodule_comap_stable_secondMember F E σ n d X W M ψ om τ P Q R S Φ c' N hCM hN C hC hact2
  have hcoinv : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N →
      tensAny (fun w => coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ :=
    fun N hN => GlobalTheory.T.thetaLift_submodule_contains_firstMember_coinvariants F E σ n d X W M ψ om τ P Q R S Φ c N hCM hN hrange A hA hact1
  obtain ⟨⟨L, hL⟩, hsum⟩ := GlobalTheory.T.howe_duality_characters_fock_tensor_product (InfinitePlace F) P Q R S (fun w => -c w)
  have hmap : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N → (N.comap Φ).map Φ = N := by
    intro N hN
    rw [Submodule.map_comap_eq, hrange]
    exact inf_eq_right.mpr hN.1
  refine ⟨⟨L, fun m N hmono hN => hL m (fun i => (N i).comap Φ) ?_
    (fun k => ⟨hstab _ (hN k), hcoinv _ (hN k)⟩)⟩, ?_⟩
  · intro i j hij
    refine lt_of_le_of_ne (Submodule.comap_mono (hmono hij).le) ?_
    intro h
    have h' := congrArg (Submodule.map Φ) h
    rw [hmap _ (hN i), hmap _ (hN j)] at h'
    exact (hmono hij).ne h'
  · intro N N' hN hN' hne hne' heq
    refine hsum (N.comap Φ) (N'.comap Φ) (hstab _ hN) (hcoinv _ hN) ?_ (hstab _ hN') (hcoinv _ hN') ?_ ?_
    · intro h; apply hne; rw [← hmap _ hN, h, Submodule.map_top, hrange]
    · intro h; apply hne'; rw [← hmap _ hN', h, Submodule.map_top, hrange]
    · apply Submodule.map_injective_of_injective hinj
      rw [Submodule.map_sup, hmap _ hN, hmap _ hN', heq, Submodule.map_top, hrange]

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaBoundLeft
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalUniformizerReal

theorem lUnif_realTB : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.LUnif := by
  intro h1 D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn
  exact GlobalTheory.TiedUnif.uniformisation_every_embedding_thirdKind h1 GlobalTheory.Mem.VolFin.finVol B.T B.Q.Rl _ B.κ B.v₀ B.fw B.O B.Q.charW B.bar B.pins B.rhoGeo B.equivAll hn

end GlobalTheory.LocalUniformizerReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaEqualityStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_equality : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S), B.Q.Rl.toRealDat.ExAt ∧ JEvBar B.T B.Q.Rl.toRealDat B.κ ∧ GeoAct B.T B.Q.Rl.toRealDat B.κ B.v₀ ∧ EvInj B.T B.Q.Rl.toRealDat B.v₀ := by
  first | exact @GlobalTheory.FireAtRealisation.fire | exact GlobalTheory.FireAtRealisation.fire | (intros; apply GlobalTheory.FireAtRealisation.fire <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerExponentSectionMulEqZeroImpEqZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SecRingNonZeroDiv

open GlobalTheory.CompHt GlobalTheory.FlagTan

theorem eq_zero_of_mul_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ) (F : Rul Xo c), F ∈ secZ Xo c e → (∀ Z : Comp Xo c, ∃ y : FrPt Xo c ℂ, LiesOn Z y ∧ evR Xo c F y ≠ 0) → ∀ f ∈ secRing Xo c, F * f = 0 → f = 0 := by
  intro E _ _ _ H Dw l Xo c e F hF hZ f hf hFf
  classical
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have hFZ : ∀ Z : Comp Xo c, genVal Z F ≠ 0 := by
    intro Z h0
    obtain ⟨y, hy, hne⟩ := hZ Z
    exact hne ((genVal_eq_zero_iff E H Dw l Xo c Z e F hF).1 h0 ℂ y hy)
  have hf' : f ∈ ⨆ e, secZ Xo c e := by rw [← GlobalTheory.LevDesc.toSubmodule_secRing]; exact hf
  obtain ⟨a, ha, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hf'
  have key : ∀ Z : Comp Xo c, ∀ d ∈ a.support, genVal Z (a d) = 0 := by
    intro Z
    haveI : CharZero (Om Z) := charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
    let χ : (Ix Dw → ℤ) → ((Ix Dw → (Om Z)ˣ) →* Om Z) := fun d =>
      { toFun := fun t => ((∏ i, t i ^ d i : (Om Z)ˣ) : Om Z)
        map_one' := by simp
        map_mul' := fun t s => by simp [mul_zpow, Finset.prod_mul_distrib] }
    have hχ : Function.Injective χ := by
      intro d d' hdd
      funext i
      let u : (Om Z)ˣ := Units.mk0 2 two_ne_zero
      have hp : ∀ d : Ix Dw → ℤ, χ d (Pi.mulSingle i u) = (2 : Om Z) ^ d i := by
        intro d
        show ((∏ j, (Pi.mulSingle i u : Ix Dw → (Om Z)ˣ) j ^ d j : (Om Z)ˣ) : Om Z) = _
        rw [Finset.prod_eq_single i]
        · simp [u, Units.val_zpow_eq_zpow_val]
        · intro j _ hj
          simp [Pi.mulSingle_eq_of_ne hj]
        · simp
      have h1 : (2 : Om Z) ^ d i = (2 : Om Z) ^ d' i := by
        rw [← hp, ← hp, hdd]
      have h2 : (((2 : ℚ) ^ d i : ℚ) : Om Z) = (((2 : ℚ) ^ d' i : ℚ) : Om Z) := by
        rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]; exact h1
      exact zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) (Rat.cast_injective h2)
    have hli : LinearIndependent (Om Z) (fun d => (χ d : (Ix Dw → (Om Z)ˣ) → Om Z)) :=
      (linearIndependent_monoidHom _ (Om Z)).comp χ hχ
    have hsum : ∑ d ∈ a.support, genVal Z (a d) • (χ d : (Ix Dw → (Om Z)ˣ) → Om Z) = 0 := by
      funext t
      obtain ⟨y', hy'⟩ := SecSeparation.exists_frBor (genFr hG Z) t
      have h1 : evR Xo c (F * a.sum fun _ x => x) y' = 0 := by rw [hFf]; exact evalAt_zero _ _ y'
      have h2 : evR Xo c (F * a.sum fun _ x => x) y' = evR Xo c F y' * evR Xo c (a.sum fun _ x => x) y' :=
        evalAt_mul _ _ _ _ y'
      have h3 : evR Xo c F y' ≠ 0 := by
        rw [evR_frBor hF hy']
        exact mul_ne_zero (Units.ne_zero _) (hFZ Z)
      have h4 : evR Xo c (a.sum fun _ x => x) y' = 0 := (mul_eq_zero.1 (h2.symm.trans h1)).resolve_left h3
      have h5 : evR Xo c (a.sum fun _ x => x) y' = ∑ d ∈ a.support, evR Xo c (a d) y' :=
        map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y') _ _
      rw [h5] at h4
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h4]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [evR_frBor (ha d) hy', mul_comm]
      rfl
    intro d hd
    exact linearIndependent_iff'.1 hli a.support (fun d => genVal Z (a d)) hsum d hd
  refine Finset.sum_eq_zero fun d hd => ?_
  exact secZ_eq_zero_of_genVal (ha d) fun Z => key Z d hd

end GlobalTheory.SecRingNonZeroDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramedPointRestrictCoefficientFieldStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFramedPoint_restrict_coefficient_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (c' : Coeff l) (hle : c.F ≤ c'.F) (T : CDVR) (io' : c'.F →+* T.Fr) (y' : IntFr Xo c' T io'), y'.IsAlg → ∃ y : IntFr Xo c T (io'.comp (IntermediateField.inclusion hle).toRingHom), y.IsAlg ∧ (∀ φ : ℝ, HasPhi y' φ → HasPhi y φ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evI y' (GlobalTheory.FieldBC.rulBC hle f) = evI y f := by
  first | exact @GlobalTheory.RefSum.intFr_res_down | exact GlobalTheory.RefSum.intFr_res_down | (intros; apply GlobalTheory.RefSum.intFr_res_down <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelComponentIrreducible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel.ModelOpen

theorem exists_geomIrr_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ U : (Xo'.XF c').Opens,
    (∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∃ Xw : Y.X.Opens, (Xw : Set Y.X) ⊆ Set.range Y.j ∧ Xw ≤ Y.X.basicOpen (p : Γ(Y.X, ⊤)) ∧
      (∀ z, Y.j z ∈ Xw ↔ z ∈ U) ∧ GeomIrr Y.s Xw := by
  intro E _ _ _ H Dw l' Xo' c' W Y p hp hW U hU
  have hj : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hW Y
  have := c'.fin
  have hV : (p : c'.F) ∈ (c'.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    refine Or.inr fun h => hW.elim (Nat.cast_ne_zero.2 hp.ne_zero) fun h' => h' ?_
    have h2 : c'.F.val.toRingHom (p : c'.F)⁻¹ ∈ W := h
    simpa using h2
  have := GlobalTheory.LocM.BaseMdl.away_of_valuation c'.F (c'.V W) p hp hV
  have hβ : IsOpenImmersion (spMap (c'.V W).subtype) :=
    IsOpenImmersion.of_isLocalization (S := c'.F) ((p : ℕ) : c'.V W)
  refine ⟨Y.j ''ᵁ U, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro _ ⟨z, -, rfl⟩
    have hF : IsUnit (p : Γ(Sp c'.F, ⊤)) := by
      have h0 : IsUnit (p : c'.F) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hp.ne_zero)
      have h1 := h0.map (Scheme.ΓSpecIso (CommRingCat.of c'.F)).inv.hom
      rw [map_natCast] at h1
      exact h1
    have hunit : IsUnit (p : Γ(Xo'.XF c', ⊤)) := by
      have h1 := hF.map (Scheme.Hom.appTop (pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom))).hom
      rw [map_natCast] at h1
      exact h1
    have hz : z ∈ Y.j ⁻¹ᵁ Y.X.basicOpen (p : Γ(Y.X, ⊤)) := by
      rw [Scheme.preimage_basicOpen, map_natCast]
      exact (Scheme.basicOpen_of_isUnit _ hunit).ge trivial
    exact hz
  · intro z
    constructor
    · rintro ⟨z', hz', e⟩
      rwa [← Y.j.isOpenEmbedding.injective e]
    · intro hz
      exact ⟨z, hz, rfl⟩
  · intro k _ f hf
    let β := (c'.V W).subtype
    let f' : c'.F →+* k := IsFractionRing.lift hf
    have hff : f'.comp β = f := by
      ext x
      exact IsFractionRing.lift_algebraMap hf x
    let a := U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)
    have := hU k f'
    let e := Y.j.isoImage U
    have h1 : a ≫ spMap β = e.hom ≫ (Y.j ''ᵁ U).ι ≫ Y.s := by
      rw [Scheme.Hom.isoImage_hom_ι_assoc, GlobalTheory.LocM.BaseMdl.j_s]
      exact Category.assoc _ _ _
    have h2 : spMap f' ≫ spMap β = spMap f := by
      rw [← hff]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    let φ := pullback.map a (spMap f') ((Y.j ''ᵁ U).ι ≫ Y.s) (spMap f) e.hom (𝟙 _) (spMap β) h1
      (by rw [h2, Category.id_comp])
    let ψ : pullback ((Y.j ''ᵁ U).ι ≫ Y.s) (spMap f) ⟶ pullback a (spMap f') :=
      pullback.lift (pullback.fst _ _ ≫ e.inv) (pullback.snd _ _) (by
        rw [← cancel_mono (spMap β)]
        simp only [Category.assoc, h1, Iso.inv_hom_id_assoc, h2]
        exact pullback.condition)
    have hφψ : ψ ≫ φ = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [φ, ψ, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.inv_hom_id,
          Category.comp_id, Category.id_comp]
      · simp only [φ, ψ, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.comp_id, Category.id_comp]
    have hsurj : Function.Surjective φ := fun x => ⟨ψ x, by rw [← Scheme.Hom.comp_apply, hφψ]; rfl⟩
    exact hsurj.irreducibleSpace φ.continuous

end GlobalTheory.FlatModel.ModelOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparison
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem htAt_embV_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
      (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]),
      HTAt Y r ν yb yy P π ψ y → ∀ β : c'.V W →+* 𝓞_ℂ_[p], yb ≫ Y.s = spMap β →
      ∀ σ : E →+* ℂ, β.comp (embV c' W σ) = embInt c P.integers σ := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hov p _ _ _ yb yy P π ψ y hHT β hβ σ
  obtain ⟨⟨h1, -⟩, -, hF, -⟩ := hHT

  set g : Sp ℂ_[p] ⟶ Sp c'.F := yy ≫ pullback.snd _ _ with hg
  have hgm : spMap (Spec.preimage g).hom = g := by
    simp [spMap]
  set gm : c'.F →+* ℂ_[p] := (Spec.preimage g).hom
  have inj : ∀ {A B : Type} [CommRing A] [CommRing B] (f f' : A →+* B), spMap f = spMap f' → f = f' := by
    intro A B _ _ f f' h
    have := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom this
  have e1 : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp β = gm.comp (c'.V W).subtype := by
    apply inj
    have := congrArg (fun t => spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ t) hβ
    rw [← Category.assoc, h1, Category.assoc, Model.j_s, ← Category.assoc] at this
    rw [← spMap_spMap, ← spMap_spMap, ← this, hgm]
  have e2 : gm.comp (IntermediateField.inclusion hle).toRingHom = algebraMap c.F ℂ_[p] := by
    apply inj
    rw [← spMap_spMap, hgm, hg, Category.assoc, ← hov, ← Category.assoc, ← hF]
    exact pullback.lift_snd _ _ _
  refine RingHom.ext fun a => P.integers.hom_inj ?_
  rw [algebraMap_embInt]
  have := congrArg (fun f => f (embV c' W σ a)) e1
  simp only [RingHom.comp_apply] at this
  rw [RingHom.comp_apply, this, ← e2, RingHom.comp_apply]
  exact congrArg gm (Subtype.ext rfl)

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSectionProjectiveOverField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem secClosed_closedPoint (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z : Sp K ⟶ X)
    (_hq : IsProjOver q) (hz : z ≫ q = 𝟙 _) :
    IsClosed ({z (IsLocalRing.closedPoint K)} : Set X) := by
  have : IsClosedImmersion z := isClosedImmersion_of_comp_eq_id q z hz
  have hc : IsClosed (Set.range z.base) := z.isClosedEmbedding.isClosed_range
  convert hc using 1
  ext x
  constructor
  · rintro rfl; exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim y (IsLocalRing.closedPoint K)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingLocalizationPowerSeriesUn
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowerSeriesUniformiser

theorem span_C_eq_ker {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) :
    Ideal.span {(PowerSeries.C ϖ : PowerSeries A)} =
      RingHom.ker (PowerSeries.map (IsLocalRing.residue A)) := by
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    ext n
    simp [PowerSeries.coeff_C_mul, hm, Ideal.mem_span_singleton']
  · intro hf
    have h : ∀ n, ∃ b : A, PowerSeries.coeff n f = ϖ * b := fun n => by
      have : IsLocalRing.residue A (PowerSeries.coeff n f) = 0 := by
        have := congrArg (PowerSeries.coeff n) hf
        simpa using this
      rw [IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at this
      exact this
    choose b hb using h
    refine ⟨PowerSeries.mk b, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hb]

theorem span_C_isPrime {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime := by
  rw [span_C_eq_ker hϖ]
  exact RingHom.ker_isPrime _

theorem isDiscreteValuationRing_atPrime_span {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {π : R}
    (h0 : π ≠ 0) [(Ideal.span {π}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {π})) := by
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π})) =
      Ideal.span {algebraMap R _ π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime (Ideal.span {π}))) :=
    IsLocalization.injective _ (Ideal.span {π}).primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {π})) := fun hf => by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot] at hf
    exact h0 (hinj (hf.trans (map_zero _).symm))
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π}))).IsPrincipal := ⟨_, hm⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).2 hp

theorem main : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ →
    ∃ _ : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)})) := by
  intro A _ _ _ ϖ hϖ
  haveI := span_C_isPrime hϖ
  refine ⟨this, isDiscreteValuationRing_atPrime_span ?_⟩
  intro h
  exact hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))

end GlobalTheory.PowerSeriesUniformiser
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFactorDepthEqSumFactorDepthsStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFactor_depth_eq_sum_factor_depths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx = nuP p y cx ∧ 0 ≤ nuP p y cx ∧ nuP p y cx ≠ ⊤ := by
  first | exact @GlobalTheory.IsoFactorDepth.nuH_vp_eq_nuP | exact GlobalTheory.IsoFactorDepth.nuH_vp_eq_nuP | (intros; apply GlobalTheory.IsoFactorDepth.nuH_vp_eq_nuP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingOfNadelPairsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_of_nadel_pairs : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → IsIntegral X → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef ℂ N) → (letI := algebraΓOfHom p; IsBig ℂ N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  first | exact @GlobalTheory.NadelApp.kawamataViehweg_complex | exact GlobalTheory.NadelApp.kawamataViehweg_complex | (intros; apply GlobalTheory.NadelApp.kawamataViehweg_complex <;> assumption)
end


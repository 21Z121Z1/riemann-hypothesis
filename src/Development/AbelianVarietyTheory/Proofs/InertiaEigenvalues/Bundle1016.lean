import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0927
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0991
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0975
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1012

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatScalarConjTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.FlatConj.flat_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (t t' : T0), VStd D i → FixBase T R i τ → ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ (z : GA D (Vc D i)) (c c' : ℂ) (s : (AE D)ˣ), IsCentAt i (R.Q t) z ∧ f = c • R.ωP i t (z, 1) (R.vP i t) ∧ f' = c' • R.ωP i t' (z, 1) (R.vP i t') ∧ c' = ((R.xi t' s : Circle) : ℂ) * τ c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hQG i τ t t' hV hFix hct f f' hf hf'
  obtain ⟨z, B, ε, r, ψP, hz, hB, hprim, hform⟩ := GlobalTheory.T.heckeChoice_flatVector_factoredForm D G Pl0 T0 A T R F hC hQG i t hV
  obtain ⟨s1, e1⟩ := hform t rfl f hf
  obtain ⟨s2, e2⟩ := hform t' hct.1 f' hf'
  obtain ⟨h1, hne, -, -⟩ := GlobalTheory.ConjRes.conj_res D G Pl0 T0 A T R F κ v₀ hC τ t t' hct
  have hg : ∀ PP ∈ R.Q t, ∃ a : (kP PP)ˣ, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      ((R.xiR t' PP a : ℂˣ) : ℂ) ^ r * GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    intro PP hP
    obtain ⟨a, -, ha⟩ := (@GlobalTheory.complexMatrixGaussSum_norm_integral_galois (kP PP) (GlobalTheory.FlatConj.resField PP) (GlobalTheory.FlatConj.resFintype PP) (Classical.decEq _)
      (ψP PP) (R.xiR t PP) r (hprim PP hP) (hne PP hP) _ rfl).2.2.2 τ (R.xiR t' PP) (h1 PP hP)
    exact ⟨a, ha⟩
  choose a ha using hg
  let v : Pl D.host.E → ℂ := fun PP => if h : PP ∈ R.Q t then ((R.xiR t' PP (a PP h) : ℂˣ) : ℂ) else 1
  obtain ⟨s3, e3⟩ := GlobalTheory.FlatConj.prod_val (R.xi t') (R.Q t) v fun PP hP => by
    simp only [v, dif_pos hP]
    exact GlobalTheory.FlatConj.xiR_val hC t' PP (hct.1 ▸ hP) _
  have hprod : ∏ PP ∈ R.Q t, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      (∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP hP => ?_
    simp only [v, dif_pos hP]
    exact ha PP hP
  refine ⟨z, _, _, s2 * s1⁻¹ * s3 ^ (-((r : ℤ) * ε)), hz, e1, e2, ?_⟩
  have hX : ((R.xi t' s1 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hV3 : ((R.xi t' s3 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have key : τ (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) ^ ε * ((R.xi t s1 : Circle) : ℂ)) =
      B * ((∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε *
        ((R.xi t' s1 : Circle) : ℂ) := by
    rw [map_mul, map_mul, map_zpow₀, map_prod, hprod, hB τ hFix, ← hct.2 s1]
  rw [key, e3]
  simp only [map_mul, map_inv, map_zpow, Circle.coe_mul, Circle.coe_inv, Circle.coe_zpow]
  rw [mul_zpow, ← zpow_natCast, ← _root_.zpow_mul, _root_.zpow_neg]
  have hW : ((R.xi t' s3 : Circle) : ℂ) ^ ((r : ℤ) * ε) ≠ 0 := zpow_ne_zero _ hV3
  field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterStatementAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem parSt_of_prN_sMt : PrN → SMt → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ParSt hL := by
  intro hN hM hL
  have hlift := GlobalTheory.T.lift_all_of_inputs hN hL
  have hloc := GlobalTheory.T.row_local_all hN hL
  have hsz := GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices
  refine Step.trans (Step.and (Step.and (Step.and (Step.of_evLgG (KP := KPx) (p := fun _ _ _ _ => True) hlift)
    (Step.of_evLgG hloc)) (Step.of_evLgG hsz)) hM) (Step.of_all ?_)
  rintro K B f T - hKP - ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ w hS P x l
  obtain ⟨cp⟩ := hS.1
  obtain ⟨⟨M, ad, mt⟩⟩ := h4 w hS P x
  have hpar : ParIn hL (Dof x) (cfOf x) (repOf x.r.Y) l.a.A.row := ParIn.ofSt l.a
  have hLift := h1 hKP w cp x.o.Z _ _ x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt l.a.A.row hpar
    M _ _ ad mt
  have hLoc := h2 hKP w cp x.o.Z _ _ x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt l.a.A.row hpar
  obtain ⟨-, -, -, hEFK, hCM, hDef, -⟩ := h3 hKP T w x.o.Z
  have hLaws := GlobalTheory.T.parameter_laws_empty hN hL (Dof x) (cfOf x) (repOf x.r.Y) l.a.A.row l.a.A.bare hpar
  have hconds := GlobalTheory.T.base_change_of_hypotheses hN.bc hN.what₂.bern hN.ds hN.gen hN.std hL (Dof x) l.a.A.wdT l.a.A.au l.a.cg l.a.au
  exact GlobalTheory.T.good_row_cusp_param (Dof x) l.a.A.row hLaws hconds hEFK hCM hDef hLift hLoc

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftExtremalVectorEqClassSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_extremalVector_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      X.R.thF j t y (X.geo.v₀ j _) = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) F := by
  first | exact @GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum | exact GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum | (intros; apply GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBound
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

open GlobalTheory.TwInputs GlobalTheory.RealGeo Formalism.L2.Pj Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

set_option maxHeartbeats 8000000 in

theorem exists_framed (hP : GlobalTheory.Published.CuspRapidDecay) (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X) :
    ∃ (X' : RealSide D) (Y' : SerSide X' E), FieldOk X' ∧
      (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X'.core X'.R.toRealDat j X'.core.σ₀ hV) ∧
      (∀ i j b, RatRow Y'.YS X'.geo.v₀ Y'.Z.good i j b → RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧
      (XiBdd Y'.Z.rd → XiBdd Y.Z.rd) := by
  have hC : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.thP⟩
  obtain ⟨c', w, hw, hfr, B, hB⟩ := exists_framed_half hP X.size hC X.geo X.unif X.inGeo
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := X.F) (realDatMovedReadingsKeepScalars X.R w)
  have hch : (fullHeckeRealDatMovedReadings X.R w kap lam).Char3 X.F := heckeCharacterisation_transfer_movedReadings X.char hs
  obtain ⟨B', -, hB', -⟩ := @geoHalf_upd D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (moveR X.R.toRealDat w) _ kap X.R.lam
    X.R.err0 B
  obtain ⟨κ, v₀, fw, bar, O, pins, rho, eqa, ct, phase⟩ := B'
  obtain rfl : v₀ = X.geo.v₀ := (eq_of_heq hB').trans hB
  let g : @GeoHalf D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat fun _ => 1 :=
    @GeoHalf.mk D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _
      κ X.geo.v₀ fw bar O pins rho eqa ct phase
  have hpb : X.core.pb = X.R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs X.core.toCore X.R.toRealDat X.geo.fw.laws.toLawsM hC.lev
      ((X.geo.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  obtain ⟨hI, hU, hInt⟩ := @GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral hP D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg
    (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _ g
    ⟨hch.lev, hch.grp.red_R, hch.grp.red_L, hch.grp.record, hch.fam, hch.models, hch.chain, hch.thP⟩ hch.grp.chiW hpb X.size
  have hst : ∀ i, (X.R.FW i).MKStable := fun i => (X.integral i).2.2
  let X' : RealSide D := @RealSide.mk D X.Γ X.grp X.fin X.Pl0 X.I0 X.T X.A3 (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam) X.F X.cG g
    hch X.phs X.guard X.valKs X.idem hU hInt hI X.finT X.host X.std X.size
  let Y' : SerSide X' E :=
    { S := moveS w Y.YS
      YS := moveYS kap lam Y.YS hw hst
      sup := Y.sup
      H := moveH kap lam Y.YS hw hst Y.H
      reads := reads_move kap lam Y.YS hw hst Y.reads
      del := Y.del
      Z := moveZ kap lam hw hst Y.Z
      U_eq := Y.U_eq
      psi_eq := Y.psi_eq
      low := Y.low
      Sb := Y.Sb
      B_range := Y.B_range
      hk_emb := Y.hk_emb
      hk_split := Y.hk_split
      off := Y.off
      all := Y.all }
  refine ⟨X', Y', ⟨hF.galois, hF.star, hF.vals, hF.ray, hF.roots, hF.split⟩, hfr,
    fun i j b => (ratRow_move kap lam Y.YS hw hst X.geo.v₀ Y.Z.good i j b).1, fun h => ?_⟩
  rw [← rd_move kap lam hw hst Y.Z]
  exact h

end GlobalTheory.Unframe

section

open GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf

theorem GlobalTheory.Unframe.rat_and_xiBdd : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧ XiBdd Y.Z.rd := by
  intro hP hA hR hS D X E Y hF
  obtain ⟨X', Y', hF', hfr, h1, h2⟩ := GlobalTheory.Unframe.exists_framed hP X Y hF
  exact ⟨fun i hi j b => h1 i j b (GlobalTheory.T.exists_rational_thetaSeries_of_twistSeriesSideData hA hR D X' E Y' hF' hfr i hi j b), h2 (GlobalTheory.T.universalSeriesCoeff_boundedInSup_of_twistSeriesSideData hA hR hS D X' E Y' hF' hfr)⟩

end
end
end


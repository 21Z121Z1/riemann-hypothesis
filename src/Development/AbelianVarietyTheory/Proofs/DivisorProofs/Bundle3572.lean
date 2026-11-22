import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainTheoremPublishedInputsThirdStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0186
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesGoodOfLocalLanglandsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0188
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0849
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0090
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3535
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3504
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3265
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPosHermOfPositive
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenFirstParametersOfPublishedUE
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.S0.Open0ProofU

theorem open_of_hypothesesUE : S0.HypothesesUE → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ), S0.Open0 (prm1 hL cDep) := by
  intro P hL cDep
  have hNE : ∀ K B f T w Z Wt p0 t nch n xd c, GlobalTheory.HeightCounting.Up.NEl hL cDep K B f T w Z Wt p0 t nch n xd c →
      Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩
  have hB : ∀ (K : Ctx) (q : WPt (prm1 hL cDep).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z) := fun _ q => q.x.nx.2.1.2.down
  have hPA := GlobalTheory.T.entry_hPA_at_parameters hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  have hDc := GlobalTheory.T.entry_point_g_at_parameters hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  have hTie := GlobalTheory.T.nonempty_extension_entries P.discreteSeriesCover P.harishChandraModules P.casselmanWallach P.weilRepresentationUnitaryPair
    P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hNE
  have hJ := GlobalTheory.T.entries_combined_real P.weilRepresentationUnitaryPair P.discreteSeriesExists P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraFinite P.cuspRapidDecay hL _ SExt.none (geoCl anyGeometry) hPA hDc hTie
  have hMi := GlobalTheory.T.main_theorem_published_inputs_third P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules P.casselmanWallach
    GlobalTheory.Hk3.howeUnram_holds P.weilRepresentationUnitaryPair P.weilSiegelFormulaUnitary P.siegelWeilUnitaryConvergent
    P.doublingMethod P.unramifiedDoublingGL P.discreteSeriesClassification P.strongApproxSU P.siegelWeilUnitaryConvergent2
    hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  have hDiv := GlobalTheory.T.bk_law_entries P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.discreteSeriesCover P.harishChandraModules P.casselmanWallach hL _ SExt.none (geoCl anyGeometry) hB hMi.1
  have hLam := GlobalTheory.T.real_group_inputs_combined P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass P.dixmierMalliavinFactorisation
    P.flathFactorisation P.pseudoCoefficientUpq P.harishChandraCharacters P.langlandsClassification P.labesseWaldspurger
    P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  have hKap := GlobalTheory.T.harish_chandra_inputs_combined P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover P.harishChandraModules
    P.casselmanWallach P.harishChandraAnalyticity P.discreteSeriesClassification P.cuspTraceClass
    P.dixmierMalliavinFactorisation P.flathFactorisation P.pseudoCoefficientUpq P.harishChandraCharacters
    P.langlandsClassification P.labesseWaldspurger P.zelevinskyPolynomialRing P.geometricLemma P.greenCuspidal
    hL _ SExt.none (geoCl anyGeometry) hLam
  have hGood := GlobalTheory.T.linked_bundles_good_of_local_langlands (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing
    P.depthZeroInertia hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry) hNE
  have hLab := GlobalTheory.T.good_ft_entries (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) P.zelevinskyPolynomialRing
    P.depthZeroInertia hL _ SExt.none (geoCl anyGeometry) hNE hGood.1
  have hGeo := GlobalTheory.T.geometric_zero_condition_all P.rayClassFieldSt hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry) hNE hDiv hTie
  have hDf := GlobalTheory.T.weil_unitary_entries P.weilRepresentationUnitaryPair P.discreteSeriesExists P.harishChandraFinite P.cuspRapidDecay
    hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
  exact ⟨hPA, hLam, hDiv, hDc, hJ, hTie, hLab, hGood.2, hGeo, hMi.2, hKap, hDf⟩

end GlobalTheory.Fc.S0.Open0ProofU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenPartClassifiedMonomialBoundaryFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.OpenPart

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem pow_eq_one_of_left_eq {S T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (h : a = b)
    (u : Over.mk a ⟶ G) (v : Over.mk b ⟶ G) (huv : u.left = v.left) {n : ℕ} (hu : u ^ n = 1) : v ^ n = 1 := by
  subst h
  obtain rfl : u = v := Over.OverMorphism.ext huv
  exact hu

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem torsRat_of_point {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E))
    {A : Type} [CommRing A] [IsDomain A] {K₀ : Type} [Field K₀] (gA : A →+* K₀) (ρ : K₀ →+* FractionRing A)
    (hρ : ρ.comp gA = algebraMap A (FractionRing A)) (tO : SAB H (Sp A)) (tK : SAB H (Sp K₀))
    (k : SABMap tK tO (spMap gA)) (y : Sp K₀ ⟶ Xo.XF c) (mK : SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) :
    GlobalTheory.TChart.TorsRat tO.G l.M' := by
  intro K _ _ κ x hx
  let κ' : K₀ →+* K := κ.comp ρ
  have e₀ : spMap κ' ≫ spMap gA = spMap κ ≫ jK A := by
    rw [spMap_comp', spMap_comp']
    show spMap (κ.comp (ρ.comp gA)) = _
    rw [hρ]
  have hw : x.left ≫ tO.G.hom = spMap κ' ≫ spMap gA := (Over.w x).trans e₀.symm
  let xK : Over.mk (spMap κ') ⟶ tK.G :=
    Over.homMk (k.cart.1.lift x.left (spMap κ') hw) (k.cart.1.lift_snd _ _ _)
  have hxK : xK ^ l.M' = 1 := by
    have hpush : pushHom k.cart (Over.mk (spMap κ')) xK ^ l.M' = 1 :=
      pow_eq_one_of_left_eq e₀.symm x _ (k.cart.1.lift_fst _ _ _).symm hx
    apply (fun (u v : Over.mk (spMap κ') ⟶ tK.G) (e : pushHom k.cart (Over.mk (spMap κ')) u = pushHom k.cart (Over.mk (spMap κ')) v) =>
      Over.OverMorphism.ext (k.cart.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])))
    rw [map_pow, hpush, map_one]
  let x' := pushHom mK.cart (Over.mk (spMap κ')) xK
  have hx' : x' ^ l.M' = 1 := by rw [← map_pow, hxK, map_one]
  obtain ⟨x₀, -, hx₀⟩ := GlobalTheory.T.universalAbelianScheme_torsion_rational_fieldPoint Xo c φ K₀ K κ' y x' hx'
  have w₀ : x₀.left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ (y ≫ pullback.fst _ _) := by
    rw [Category.id_comp]; exact Over.w x₀
  let s₀ := mK.cart.1.lift x₀.left (𝟙 _) w₀
  have hs₀ : s₀ ≫ tK.G.hom = 𝟙 _ := mK.cart.1.lift_snd _ _ _
  have hK : xK.left = spMap κ' ≫ s₀ := by
    apply mK.cart.1.hom_ext
    · rw [Category.assoc, mK.cart.1.lift_fst]
      exact hx₀
    · rw [Category.assoc, hs₀]
      erw [Category.comp_id]
      exact k.cart.1.lift_snd _ _ _
  have hover : (spMap ρ ≫ s₀ ≫ k.φ) ≫ tO.G.hom = jK A := by
    rw [Category.assoc, Category.assoc, k.cart.1.w, ← Category.assoc s₀, hs₀, Category.id_comp, spMap_comp', hρ]
  refine ⟨Over.homMk (spMap ρ ≫ s₀ ≫ k.φ) hover, ?_⟩
  show x.left = spMap κ ≫ spMap ρ ≫ s₀ ≫ k.φ
  have e₁ : spMap κ ≫ spMap ρ = spMap κ' := spMap_comp' _ _
  calc x.left = xK.left ≫ k.φ := (k.cart.1.lift_fst _ _ _).symm
    _ = (spMap κ' ≫ s₀) ≫ k.φ := by rw [hK]
    _ = spMap κ ≫ spMap ρ ≫ s₀ ≫ k.φ := by rw [← e₁]; simp only [Category.assoc]

end GlobalTheory.UCanon.OpenPart

namespace GlobalTheory.UCanon.OpenPart

theorem ring_facts {R : Type} [CommRing R] [IsDomain R] (f : R) (hf : f ≠ 0) (A : Type) [CommRing A] [IsDomain A]
    [Algebra R A] [IsLocalization.Away f A] :
    ∃ (gA : A →+* FractionRing R) (ρ : FractionRing R →+* FractionRing A),
      gA.comp (algebraMap R A) = algebraMap R (FractionRing R) ∧ ρ.comp gA = algebraMap A (FractionRing A) ∧
      ∀ g : A →+* FractionRing R, g.comp (algebraMap R A) = algebraMap R (FractionRing R) → g = gA := by
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hu : IsUnit (algebraMap R (FractionRing R) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf)
  have hgA : (IsLocalization.Away.lift f hu : A →+* FractionRing R).comp (algebraMap R A) = algebraMap R (FractionRing R) :=
    IsLocalization.Away.lift_comp _ hu
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp (algebraMap R A)) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective A (FractionRing A)).comp (IsLocalization.injective A hle)
  refine ⟨IsLocalization.Away.lift f hu, IsFractionRing.lift (K := FractionRing R) hinj, hgA, ?_, fun g hg =>
    IsLocalization.ringHom_ext (Submonoid.powers f) (hg.trans hgA.symm)⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [RingHom.comp_assoc, hgA]
  exact RingHom.ext fun r => by rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

end GlobalTheory.UCanon.OpenPart

namespace GlobalTheory.UCanon.OpenPart

theorem openCls : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : MonoFam Xo c φ R, OpenCls C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := id hR
  have hf0 : (∏ i, C.s i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => C.s_ne_zero i
  have hle : Submonoid.powers (∏ i, C.s i) ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away (∏ i, C.s i)) := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing (Localization.Away (∏ i, C.s i)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (∏ i, C.s i)) _ hN
  haveI : IsIntegrallyClosed (Localization.Away (∏ i, C.s i)) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (∏ i, C.s i)) hle

  let aR := algebraMap R (Localization.Away (∏ i, C.s i))
  let incl := (IntermediateField.inclusion c.le).toRingHom
  obtain ⟨gA, ρ, hgA, hρ, hgU⟩ := ring_facts _ hf0 (Localization.Away (∏ i, C.s i))
  have eR : spMap gA ≫ spMap aR = jK R := by rw [spMap_comp', hgA]

  obtain ⟨tO, ⟨mO⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap aR) C.t
  obtain ⟨hprop, hamp, hkt⟩ := GlobalTheory.T.isProper_relAmple_kTriv_of_trivialisations_generate R hR C.t C.P (∏ i, C.s i)
    (fun y => C.mono.psiUnitOn y fun p hp => hp) tO mO

  let s' : Sp (FractionRing R) ⟶ Sp (KA l) := (C.y ≫ pullback.fst _ _) ≫ Xo.s
  obtain ⟨oK, ⟨mK⟩⟩ := (GlobalTheory.UCanon.obj_pull_comp_cancel (D := Dw) (l := l)).1 Xo.s Xo.univ (C.y ≫ pullback.fst _ _) s' rfl
  obtain ⟨t', ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  obtain ⟨k₁⟩ := GlobalTheory.TraitOrder.cancel (Category.id_comp _) m₂ mK.toSABMap
  obtain ⟨k₂⟩ := GlobalTheory.TraitOrder.comp (Category.id_comp _) m₁ k₁
  obtain ⟨k₃⟩ := GlobalTheory.TraitOrder.cancel eR mO k₂
  have htors := torsRat_of_point Xo c φ gA ρ hρ tO oK.t k₃ C.y mK.toSABMap
  let b' : c.F →+* Localization.Away (∏ i, C.s i) := aR.comp C.b
  have hs' : s' = spMap gA ≫ spMap (b'.comp incl) := by
    show (C.y ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.y_over, ← eR]
    simp only [Category.assoc, spMap_comp']
  obtain ⟨o, ho, ⟨mo⟩⟩ := GlobalTheory.T.exists_unitaryModuliObject_spread_normal_domain Dw l c _ b' tO hprop hamp hkt htors (FractionRing R) gA s' oK hs' k₃
  obtain ⟨fX, ⟨hfs, ⟨mf⟩⟩, -⟩ := Xo.rep (Sp (Localization.Away (∏ i, C.s i))) (spMap (b'.comp incl)) inferInstance o
  have hfs' : fX ≫ Xo.s = spMap b' ≫ spMap incl := hfs.trans (spMap_comp' _ _).symm
  subst ho
  refine ⟨pullback.lift fX (spMap b') hfs', o.t, ⟨mO⟩, ?_, fun g hg => ?_⟩
  · rw [pullback.lift_fst]
    exact ⟨mf.toSABMap⟩
  obtain ⟨g₀, rfl⟩ := Spec.map_surjective g
  have h₁ : CommRingCat.ofHom (algebraMap R (Localization.Away (∏ i, C.s i))) ≫ g₀ =
      CommRingCat.ofHom (algebraMap R (FractionRing R)) := Spec.map_injective (by rw [Spec.map_comp]; exact hg)
  have hg₀ : g₀ = CommRingCat.ofHom gA := by
    have e := hgU g₀.hom (by
      have := congrArg CommRingCat.Hom.hom h₁
      simpa using this)
    rw [← e]
    rfl
  subst hg₀
  obtain ⟨_, _, huK⟩ := Xo.rep (Sp (FractionRing R)) s' inferInstance oK
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    obtain ⟨n₁, -⟩ := ((GlobalTheory.UCanon.obj_pull_comp_cancel (D := Dw) (l := l)).2 Xo.s (spMap (b'.comp incl)) s' Xo.univ o oK
      fX (spMap gA) mf).1 mo
    exact (huK _ ⟨by rw [Category.assoc, hfs]; exact hs'.symm, ⟨n₁⟩⟩).trans (huK _ ⟨rfl, ⟨mK⟩⟩).symm
  · rw [Category.assoc, pullback.lift_snd, C.y_over, ← eR, Category.assoc, spMap_comp' C.b aR]

end GlobalTheory.UCanon.OpenPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementCoefficientFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem fibre_theta_consts_in_subfield : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (J : Type) (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∀ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
    ∃ v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀, t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) := by
  intro W _ gQ J l hl hlo j hj V V₁ _ _ _ _ _ hCN hlu Q _ ρ _ D e _ C u mo hmo hT K _ _ ev k₀ hk₀ hrat bT t ψ hψ hL
  haveI : IsAlgClosed k₀ := hk₀
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.FamRep.exists_hasTh_field GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 hlo.pow t K (𝟙 _)
  obtain ⟨th, κ, hth, hκ, hy⟩ := GlobalTheory.T.exists_generator_thetaConstants_fibre V₁ D K ev k₀ (8 * gQ) (l ^ j) J bT _ t ψ hψ hL v₀ hv₀
  obtain ⟨M, lam, hM, hA⟩ := GlobalTheory.T.normalisedThetaConstant_eq_scalar_root_mul_unit l hl hlo j hj V₁ hCN hlu D _ C e u mo hmo hT K ev D.rig D.rig_gen th hth
  obtain ⟨c', hc'⟩ := (hmo 0).2
  have hev : ev (u 0 c') ≠ 0 := (hc'.map ev).ne_zero
  have key : ∀ a, ∃ w : K, w ∈ k₀ ∧ κ * v₀ a = lam * ev (u 0 c') * w := by
    intro a
    obtain ⟨y, hya⟩ := hy a
    obtain ⟨c₀, ζ, hζ, hc⟩ := hA y _ hya
    obtain ⟨r, hr, hr'⟩ := hrat 0 c₀ c' hc'
    have hζk : ζ ∈ k₀ := Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)
    exact ⟨ζ * r, k₀.mul_mem hζk hr, by rw [hc, hr']; ring⟩
  choose w hw hkw using key
  by_cases hlam : lam = 0
  · refine ⟨fun _ => 0, ?_⟩
    refine GlobalTheory.GenericObject.hasTh_unit_mul t (𝟙 _) v₀ _ 1 isUnit_one (fun a => ?_) hv₀
    have := hkw a
    rw [hlam, zero_mul, zero_mul] at this
    simp [(mul_eq_zero.1 this).resolve_left hκ]
  · refine ⟨fun a => ⟨w a, hw a⟩, ?_⟩
    refine GlobalTheory.GenericObject.hasTh_unit_mul t (𝟙 _) v₀ _ ((lam * ev (u 0 c'))⁻¹ * κ)
      (IsUnit.mk0 _ (mul_ne_zero (inv_ne_zero (mul_ne_zero hlam hev)) hκ)) (fun a => ?_) hv₀
    show w a = _
    rw [_root_.mul_assoc, hkw a, ← _root_.mul_assoc, inv_mul_cancel₀ (mul_ne_zero hlam hev), _root_.one_mul]

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryGeneratorValueLocalUnitsMulSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetryGenerator_value_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a : D.X, ∃ c ∈ k₀, (val D.sym (spMap ev ≫ (D.c a).left) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.SymVal.sym_val | exact GlobalTheory.USep.EvG.SymVal.sym_val | (intros; apply GlobalTheory.USep.EvG.SymVal.sym_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartBoundaryEquations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanonBd

theorem prime_X {σ A : Type} [CommRing A] [IsDomain A] (i : σ) : Prime (MvPowerSeries.X i : MvPowerSeries σ A) := by
  classical
  have key : ∀ f : MvPowerSeries σ A, MvPowerSeries.X i ∣ f ↔ (1 : ℕ∞) ≤ f.weightedOrder (Pi.single i 1) := fun f => by
    have hw : ∀ d : σ →₀ ℕ, Finsupp.weight (Pi.single i 1 : σ → ℕ) d = d i := fun d => by
      rw [Finsupp.weight_single_one_apply]
    rw [MvPowerSeries.X_dvd_iff]
    refine ⟨fun h => ?_, fun h d hd => ?_⟩
    · exact MvPowerSeries.nat_le_weightedOrder _ (n := 1) fun d hd => h d (by rw [hw] at hd; omega)
    · exact MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (lt_of_lt_of_le (by rw [hw, hd]; simp) h)
  refine ⟨fun h => ?_, fun h => ?_, fun f g h => ?_⟩
  · simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  · simpa using h.map MvPowerSeries.constantCoeff
  · rw [key, MvPowerSeries.weightedOrder_mul] at h
    rw [key, key]
    by_contra hn
    simp only [not_or, not_le, Order.lt_one_iff] at hn
    simp [hn.1, hn.2] at h

theorem isRadical_span_prod_X {σ A : Type} [CommRing A] [IsDomain A] {m : ℕ} (v : Fin m → σ) (hv : Function.Injective v) :
    (Ideal.span {∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ A)}).IsRadical := by
  classical
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  refine GlobalTheory.RelParamRad.prod_dvd_of_forall_dvd m _ (fun i => prime_X (v i)) (fun i j hij => ?_) x
    fun i => (prime_X (v i)).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hn)
  by_contra hne
  have := MvPowerSeries.X_dvd_iff.1 hij (Finsupp.single (v j) 1)
    (Finsupp.single_eq_of_ne fun h => hne (hv h))
  simp [MvPowerSeries.coeff_X] at this

theorem mem_support_of_idlAlong_le {S : Scheme.{0}} (I : S.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S) (p : Sp R) (h : idlAlong I ξ ≤ p.asIdeal) : ξ p ∈ I.support := by
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  let lo := algebraMap R (Localization.AtPrime p.asIdeal)
  have e : (spMap lo ≫ ξ) (closedPoint (Localization.AtPrime p.asIdeal)) = ξ p := by
    change ξ (spMap lo (closedPoint _)) = ξ p
    congr 1
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal
  rw [← e]
  refine (mem_support_iff_stalkId I _).2 fun htop => ?_
  have h₁ : idlAlong I (spMap lo ≫ ξ) = ⊤ := by rw [idlAlong, htop, Ideal.map_top]
  rw [GlobalTheory.TraitOrder.idlAlong_comp] at h₁
  have h₂ : (idlAlong I ξ).map lo ≤ maximalIdeal _ :=
    (Ideal.map_mono h).trans (Localization.AtPrime.map_eq_maximalIdeal).le
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h₁ ▸ h₂))

theorem mem_range_of_away {X S : Scheme.{0}} [S.IsSeparated] (j : X ⟶ S) {R : Type} [CommRing R] [IsDomain R]
    (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X) (hy : y ≫ j = jK R ≫ ξ) (f : R) (yo : Sp (Localization.Away f) ⟶ X)
    (hyo : ∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away f),
      g ≫ spMap (algebraMap R (Localization.Away f)) = jK R → g ≫ yo = y)
    (p : Sp R) (hp : f ∉ p.asIdeal) : ξ p ∈ Set.range j := by
  have hf : f ≠ 0 := fun h => hp (h ▸ p.asIdeal.zero_mem)
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hu : ∀ x : Submonoid.powers f, IsUnit (algebraMap R (FractionRing R) x) := fun x =>
    IsLocalization.map_units (FractionRing R) (⟨x.1, hle x.2⟩ : nonZeroDivisors R)
  let lf : Localization.Away f →+* FractionRing R := IsLocalization.lift hu
  let lo := spMap (algebraMap R (Localization.Away f))
  let κ : Sp (FractionRing R) ⟶ Sp (Localization.Away f) := spMap lf
  have hκ : κ ≫ lo = jK R := by
    rw [← Spec.map_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  have hinj : Function.Injective lf := by
    refine (IsLocalization.lift_injective_iff hu).2 fun x x' => ?_
    rw [(IsLocalization.injective (Localization.Away f) hle).eq_iff, (IsFractionRing.injective R (FractionRing R)).eq_iff]
  haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot lf).1 hinj]; exact bot_le)⟩
  have hξ : lo ≫ ξ = yo ≫ j := by
    refine ext_of_isDominant κ ?_
    rw [← Category.assoc, hκ, ← hy, ← Category.assoc, hyo κ hκ]
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ f]
    exact hp
  obtain ⟨q, hq⟩ := hq
  refine ⟨yo q, ?_⟩
  change (yo ≫ j) q = ξ p
  rw [← hξ, ← hq]
  rfl

theorem boundary_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} ∧ ∃ a : Fin C.m → ℕ, (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns Z zs i OZ N d J S π j _ BD hP hS k _ m e C hT ξ hy
  have hEt := GlobalTheory.T.tautologicalChart_isEtaleCompletion_localRing Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  obtain ⟨-, -, -, ⟨hd, hJ, -⟩, ⟨-, hproj, -, -, -, hπ, hBD, hval⟩, -⟩ := hP
  obtain ⟨hm, hs, ⟨yo, -, -, -, hyo⟩, -⟩ := hT.1
  haveI : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  haveI : IsProper (π ≫ zs) := by
    obtain ⟨n, lo, hlo, h⟩ := hproj
    have := isProper_str c.F n
    rw [← h]
    infer_instance
  haveI : S.IsSeparated := by
    constructor
    rw [← terminal.comp_from (π ≫ zs)]
    infer_instance

  haveI := GlobalTheory.PointStepCompare.projective_of_free E (X := C.P.D.toPre.X)
  have hF := hφ C.P.D.toPre.X C.rank
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  have hex : ∀ i, ∃ a : ℕ, 0 < a ∧ (a : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i) := fun i => by
    obtain ⟨n, hn⟩ := hF.exists_nat (C.cone.mem i) (C.cone.nonneg i)
    have h0 := hF.pos _ (C.cone.mem i) (C.cone.nonneg i) (C.cone.linearIndependent.ne_zero i)
    rw [hn] at h0
    refine ⟨d * (l.M' * n), by have : 0 < n := by exact_mod_cast h0
                               positivity, ?_⟩
    rw [C.cone.evalZ_smul, hn]
    push_cast
    rfl
  choose a ha0 ha using hex
  have hprod : ∀ b : Fin C.m → ℕ, ∏ i, C.s i ^ b i = ∏ i, bdParam k m e i ^ b (Fin.cast hm.symm i) := fun b =>
    Fintype.prod_equiv (finCongr hm) _ _ fun i => by rw [hs]; rfl
  have hs0 : ∀ i, C.s i ≠ 0 := fun i => by rw [hs]; exact (prime_X _).ne_zero

  have hdiv : idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
    rw [hprod]
    refine GlobalTheory.T.ideal_eq_span_monomial_of_orders_along_completeDVR k m e _ _ fun W _ _ _ hW ψ hψ hψl => ?_
    rw [← hprod, ← GlobalTheory.TraitOrder.idlAlong_comp]
    haveI : IsDiscreteValuationRing W := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible
      ((map_ne_zero_iff ψ hψ).2 (hs0 i)) hϖ
    have hκ : spMap (GlobalTheory.ArcPull.fracMap hψ) ≫ jK _ = jK W ≫ spMap ψ :=
      (GlobalTheory.ArcPull.fracMap_sq hψ).symm.trans (Category.id_comp _)
    obtain ⟨t, tK, P, h₁, h₂, be, hbe, hmon, hev⟩ :=
      GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ ⟨hA, inferInstance⟩ C W hW ψ hψ hψl ϖ hϖ w hw _ hκ
    obtain ⟨n, hn, hI⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξ) _ (by rw [Category.assoc, hy, reassoc_of% hκ]) t tK h₁ h₂ P be hbe hmon
    have hn' : n = ∑ i, w i * a i := by
      apply Nat.cast_injective (R := ℝ)
      rw [hn, hev, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [ha]; ring
    rw [hI, hn', Ideal.span_singleton_eq_span_singleton, map_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ _ _ fun i _ => by rw [map_pow, pow_mul]; exact (hw i).symm.pow_pow

  have hset : ∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal := fun p => by
    refine ⟨fun h hp => ?_, mem_range_of_away j ξ C.y hy _ yo hyo p⟩
    have h₁ : ξ p ∈ BD.idealSheaf.support := by
      refine mem_support_of_idlAlong_le _ ξ p ?_
      rw [hdiv, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_of_dvd _ (Finset.prod_dvd_prod_of_dvd _ _ fun i _ => dvd_pow_self _ (ha0 i).ne') hp
    rw [hBD, Scheme.IdealSheafData.support_comap] at h₁
    rw [← hπ] at h
    exact hJ _ h₁ h
  refine ⟨hset, ?_, a, ha, hdiv⟩
  haveI := GlobalTheory.GenFan.essFiniteType_int_stalk c.F S (π ≫ zs) (ξ (closedPoint _))
  haveI := hA.1
  refine GlobalTheory.PolDeg.idlAlong_vanishingIdeal_compl S j.opensRange _ ξ _ ?_ (fun p => ?_)
    (GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ _ hA.2.2.2 hEt
      (GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m e _ hEt))
  · simp only [hs]
    exact isRadical_span_prod_X (fun i => Sum.inl (Fin.cast hm i)) (Sum.inl_injective.comp (Fin.cast_injective hm))
  · rw [Scheme.Hom.coe_opensRange]
    exact hset p

end GlobalTheory.UCanonBd
end


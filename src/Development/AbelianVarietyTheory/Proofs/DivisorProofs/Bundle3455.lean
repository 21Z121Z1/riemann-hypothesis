import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0090
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDvrOfCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3435
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3436
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3417
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3437
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3438

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAtBoundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdLocalExt

theorem exists_extension_of_smooth {A : CommRingCat.{0}} [IsRegularRing A] {X Y : Scheme.{0}} (p : X ⟶ Spec A) [Smooth p]
    [QuasiCompact p] (u : Y ⟶ X) [IsOpenImmersion u] (L : LB Y) (hL : L.IsLB) :
    ∃ M : LB X, M.IsLB ∧ LBIso (M.pull u) L := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x => by
    haveI : Smooth (show X ⟶ Spec (CommRingCat.of A) from p) := ‹Smooth p›
    haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth A p x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) := IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩
  exact GlobalTheory.exists_lineBundle_extension_of_isDomain X Y u inferInstance (fun x => (h x).1) (fun x => (h x).2) L hL

theorem exists_extension_stalk {S X Y : Scheme.{0}} (g : X ⟶ S) [Smooth g] [QuasiCompact g] (e : Y ⟶ X)
    [IsOpenImmersion e] (x : S) [IsRegularLocalRing (S.presheaf.stalk x)] (L : LB Y) (hL : L.IsLB) :
    ∃ M : LB (pullback g (S.fromSpecStalk x)), M.IsLB ∧
      LBIso (M.pull (pullback.map (e ≫ g) (S.fromSpecStalk x) g (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp)))
        (L.pull (pullback.fst (e ≫ g) (S.fromSpecStalk x))) := by
  haveI : IsRegularRing (S.presheaf.stalk x) := GlobalTheory.isRegularRing_of_isRegularLocalRing _
  exact exists_extension_of_smooth (pullback.snd g (S.fromSpecStalk x)) _ _ (pull_isLB hL _)

theorem exists_extension_at_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → Sep Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → ∀ (he : IsGrpPullback tF.G G j e), (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ x : S, x ∉ Set.range j → ∃ M : LB (pullback G.hom (S.fromSpecStalk x)), M.IsLB ∧ LBIso (M.pull (pullback.map (e ≫ G.hom) (S.fromSpecStalk x) G.hom (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp))) (tF.PP.L.pull (pullback.fst (e ≫ G.hom) (S.fromSpecStalk x))) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU _ hpre tF _ G _ _ e hsa he _ x hx
  obtain ⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩ := hU
  haveI := hsa.smooth
  haveI := hsa.quasiCompact
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨k, _, m, n, C, ξ, a, -, -, rfl, het, -⟩ := hpre x hx
  haveI : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  haveI : IsRegularLocalRing (S.presheaf.stalk (ξ (closedPoint _))) :=
    (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ het).1
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) he.1.flip inferInstance
  exact exists_extension_stalk G.hom e _ tF.PP.L tF.PP.isLB

end GlobalTheory.BdLocalExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DenseGlue

open GlobalTheory.PicGlue GlobalTheory.CechPic

theorem cls_pull_comp {P T T' : Scheme.{0}} {W : P.Opens} {L : LB P} (hL : IsOn W L) (g : T ⟶ P)
    (hg : ∀ z, g z ∈ W) (s : T' ⟶ T) {g' : T' ⟶ P} (w : s ≫ g = g') (h : (L.pull g).IsLB)
    (h' : (L.pull g').IsLB) : cls (L.pull g') h' = CechPic.pull s (cls (L.pull g) h) := by
  subst w
  rw [← cls_pull h s (pull_isLB h s)]
  exact ((cls_eq_iff _ _).2 (isOn_pull_comp P _ _ _ L g s hL hg)).symm

theorem exists_rigidify {X P : Scheme.{0}} (p : P ⟶ X) {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {V : X.Opens} {M : LB P}
    (hM : IsOn (p ⁻¹ᵁ V) M) : ∃ M' : LB P, IsOn (p ⁻¹ᵁ V) M' ∧ ∀ (T : Scheme.{0}) (g : T ⟶ P),
      (∀ z, g z ∈ p ⁻¹ᵁ V) → ∀ (h₁ : (M'.pull g).IsLB) (h₂ : (M.pull g).IsLB) (h₃ : (M.pull (g ≫ p ≫ e)).IsLB),
        cls _ h₁ = cls _ h₂ - cls _ h₃ := by
  have hpe := retract_section_apply p e he
  have hι : ∀ z, (p ⁻¹ᵁ V).ι z ∈ p ⁻¹ᵁ V := fun z ↦ z.2
  have hι' : ∀ z, ((p ⁻¹ᵁ V).ι ≫ p ≫ e) z ∈ p ⁻¹ᵁ V := fun z ↦ by
    change p (e (p _)) ∈ V
    rw [hpe]
    exact z.2
  have k₁ := pull_isLB_of_isOn P _ _ M _ hM hι
  have k₂ := pull_isLB_of_isOn P _ _ M _ hM hι'
  obtain ⟨N, hN, hc⟩ := cls_surj (cls _ k₁ - cls _ k₂)
  obtain ⟨M', hM', hi⟩ := exists_isOn_of_openImmersion P _ (p ⁻¹ᵁ V).ι N hN
  rw [Scheme.Opens.opensRange_ι] at hM'
  refine ⟨M', hM', fun T g hg h₁ h₂ h₃ ↦ ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : T ⟶ (p ⁻¹ᵁ V).toScheme, t ≫ (p ⁻¹ᵁ V).ι = g :=
    ⟨IsOpenImmersion.lift (p ⁻¹ᵁ V).ι g (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg z), IsOpenImmersion.lift_fac _ _ _⟩
  have k₃ := pull_isLB_of_isOn P _ _ M' _ hM' hι
  rw [cls_pull_comp hM' _ hι t ht k₃, cls_pull_comp hM _ hι t ht k₁,
    cls_pull_comp hM _ hι' t (by rw [reassoc_of% ht]) k₂, ← map_sub, ← hc, (cls_eq_iff k₃ hN).2 hi]

theorem exists_glue_of_rigid {X P : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [IsReduced X]
    (U : X.Opens) [IsDominant U.ι] (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P}
    (he : e ≫ p = 𝟙 X) {L₀ : LB P} (h₀ : IsOn (p ⁻¹ᵁ U) L₀) (t₀ : ∃ t : LB.Gen (L₀.pull (U.ι ≫ e)), t.IsGen)
    {Ix : Type} (V : Ix → X.Opens) (hV : ∀ y, ∃ i, y ∈ V i) (L : Ix → LB P) (hL : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i))
    (t : ∀ i, ∃ t : LB.Gen ((L i).pull ((V i).ι ≫ e)), t.IsGen)
    (hi : ∀ i, LBIso ((L i).pull (p ⁻¹ᵁ (V i ⊓ U)).ι) (L₀.pull (p ⁻¹ᵁ (V i ⊓ U)).ι)) :
    ∃ N : LB P, N.IsLB ∧ ∀ i, ∃ v : Cmp (p ⁻¹ᵁ V i) N (L i), IsoOn (p ⁻¹ᵁ V i) N (L i) v := by
  have hpe := retract_section_apply p e he
  have hR : ∀ {W : X.Opens} {M : LB P}, IsOn (p ⁻¹ᵁ W) M → (∃ t : LB.Gen (M.pull (W.ι ≫ e)), t.IsGen) →
      ∃ r : RigD e M, RigOn e M r := fun {W M} hM ht ↦
    rigOn_of_triv_open P X e W M (fun a y hy ↦ by
      have : p (e y) ∈ W := hM.le a hy
      rwa [hpe] at this) ht
  obtain ⟨r₀, hr₀⟩ := hR h₀ t₀
  choose r hr using fun i ↦ hR (hL i) (t i)
  have hv : ∀ i, ∃ v : Cmp (p ⁻¹ᵁ (V i ⊓ U)) (L i) L₀, IsoOn _ (L i) L₀ v ∧
      PicGlue.Norm e _ (L i) L₀ v (r i) r₀ := fun i ↦ by
    obtain ⟨w, hw⟩ := isoOn_of_lbIso P _ (L i) L₀ (hi i)
    exact exists_norm P X p e he _ _ _ (L i) L₀ w (r i) r₀ (hL i) h₀ (fun _ h ↦ h.1) (fun _ h ↦ h.2) hw (hr i) hr₀
  choose v hv hn using hv
  obtain ⟨w, hw, hc⟩ := exists_cocycle U p he h₀ r₀ V L hL r v hv hn
  exact lb_glue P Ix (fun i ↦ p ⁻¹ᵁ V i) L w (fun x ↦ hV (p x)) hL hw hc

theorem exists_glue {X P U Q : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : Dense (Set.range j)) (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p]
    {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {a : Q ⟶ P} {π : Q ⟶ U} (sq : IsPullback a π p j) {eU : U ⟶ Q}
    (w : eU ≫ a = j ≫ e) {L : LB Q} (hL : L.IsLB) (hrig : ∃ t : LB.Gen (L.pull eU), t.IsGen)
    (H : ∀ y : X, y ∉ Set.range j → ∃ V : X.Opens, y ∈ V ∧ ∃ M : LB P, IsOn (p ⁻¹ᵁ V) M ∧
      LBIso (M.pull ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a)) (L.pull (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι)) :
    ∃ M : LB P, M.IsLB ∧ LBIso (M.pull a) L := by
  have hpe := retract_section_apply p e he
  have : IsOpenImmersion a := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip ‹_›
  let U₀ : X.Opens := j.opensRange
  have : IsDominant U₀.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hj⟩
  have hD : a.opensRange = p ⁻¹ᵁ U₀ := by
    ext x
    change x ∈ Set.range a ↔ p x ∈ Set.range j
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨π q, by rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]⟩
    · intro hx
      obtain ⟨q, rfl⟩ : x ∈ Set.range (pullback.fst p j) := by
        rw [Scheme.Pullback.range_fst]
        exact hx
      exact ⟨sq.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, sq.isoPullback_inv_fst]⟩
  obtain ⟨L₀, h₀, i₀⟩ := exists_isOn_of_openImmersion P Q a L hL
  rw [hD] at h₀
  have ha : ∀ z, a z ∈ p ⁻¹ᵁ U₀ := fun z ↦ hD ▸ ⟨z, rfl⟩
  have k₀ := pull_isLB_of_isOn P _ _ L₀ a h₀ ha
  have c₀ : cls _ k₀ = cls L hL := (cls_eq_iff _ _).2 i₀

  have z₀ : ∀ (T : Scheme.{0}) (s : T ⟶ X), (∀ z, s z ∈ U₀) → ∀ h : (L₀.pull (s ≫ e)).IsLB, cls _ h = 0 := by
    intro T s hs h
    let κ := IsOpenImmersion.lift j s (by rintro _ ⟨z, rfl⟩; exact hs z)
    have hκ : κ ≫ j = s := IsOpenImmersion.lift_fac _ _ _
    rw [cls_pull_comp h₀ a ha (κ ≫ eU) (by rw [Category.assoc, w, reassoc_of% hκ]) k₀, c₀, pull_comp,
      ← cls_pull hL eU (pull_isLB hL eU), (cls_eq_zero_iff _).2 hrig, map_zero]
  have hse : ∀ {T : Scheme.{0}} (s : T ⟶ X) {W : X.Opens}, (∀ z, s z ∈ W) → ∀ z, (s ≫ e) z ∈ p ⁻¹ᵁ W :=
    fun s W hs z ↦ by
      change p (e (s z)) ∈ W
      rw [hpe]
      exact hs z
  have t₀ : ∃ t : LB.Gen (L₀.pull (U₀.ι ≫ e)), t.IsGen :=
    (cls_eq_zero_iff (pull_isLB_of_isOn P _ _ L₀ _ h₀ (hse U₀.ι fun z ↦ z.2))).1 (z₀ _ U₀.ι (fun z ↦ z.2) _)
  have key : ∀ o : Option X, ∃ (V : X.Opens) (M : LB P), (∀ y, o = some y → y ∉ U₀ → y ∈ V) ∧
      (o = none → V = U₀ ∧ M = L₀) ∧ IsOn (p ⁻¹ᵁ V) M ∧ (∃ t : LB.Gen (M.pull (V.ι ≫ e)), t.IsGen) ∧
      LBIso (M.pull (p ⁻¹ᵁ (V ⊓ U₀)).ι) (L₀.pull (p ⁻¹ᵁ (V ⊓ U₀)).ι) := fun o ↦ by
    by_cases ho : ∃ y, o = some y ∧ y ∉ U₀
    swap
    · have k := pull_isLB_of_isOn P _ _ L₀ (p ⁻¹ᵁ (U₀ ⊓ U₀)).ι h₀ fun z ↦ z.2.1
      exact ⟨U₀, L₀, fun y h h' ↦ (ho ⟨y, h, h'⟩).elim, fun _ ↦ ⟨rfl, rfl⟩, h₀, t₀, (cls_eq_iff k k).1 rfl⟩
    obtain ⟨y, rfl, hy⟩ := ho
    obtain ⟨V, hyV, M, hM, iM⟩ := H y hy
    obtain ⟨M', hM', hc⟩ := exists_rigidify p he hM
    have hb : ∀ z, ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a) z ∈ p ⁻¹ᵁ V := fun z ↦ z.2
    have kb := pull_isLB_of_isOn P _ _ M _ hM hb
    have cmp : ∀ (T : Scheme.{0}) (g : T ⟶ P), (∀ z, g z ∈ p ⁻¹ᵁ (V ⊓ U₀)) → ∀ (h₁ : (M.pull g).IsLB)
        (h₂ : (L₀.pull g).IsLB), cls _ h₁ = cls _ h₂ := fun T g hg h₁ h₂ ↦ by
      let t := IsOpenImmersion.lift ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a) g (by
        rintro _ ⟨z, rfl⟩
        obtain ⟨q, hq⟩ : g z ∈ a.opensRange := hD ▸ (hg z).2
        exact ⟨⟨q, show a q ∈ p ⁻¹ᵁ V from hq ▸ (hg z).1⟩, hq⟩)
      have ht : t ≫ (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a = g := IsOpenImmersion.lift_fac _ _ _
      rw [cls_pull_comp hM _ hb t ht kb, (cls_eq_iff kb (pull_isLB hL _)).2 iM,
        cls_pull_comp h₀ a ha (t ≫ (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι) (by rw [Category.assoc, ht]) k₀, c₀, pull_comp,
        cls_pull hL]
    refine ⟨V, M', fun y' h _ ↦ by cases h; exact hyV, fun h ↦ (by cases h), hM', ?_, ?_⟩
    · have hs := hse V.ι fun z ↦ z.2
      have k₂ := pull_isLB_of_isOn P _ _ M _ hM hs
      have e₁ : (V.ι ≫ e) ≫ p ≫ e = V.ι ≫ e := by rw [Category.assoc, reassoc_of% he]
      refine (cls_eq_zero_iff (pull_isLB_of_isOn P _ _ M' _ hM' hs)).1 ?_
      rw [hc _ _ hs _ k₂ (e₁.symm ▸ k₂), sub_eq_zero]
      exact (cls_pull_comp hM _ hs (𝟙 _) (by rw [Category.id_comp, e₁]) k₂ _).trans (pull_id _) |>.symm
    · let g := (p ⁻¹ᵁ (V ⊓ U₀)).ι
      have hg : ∀ z, g z ∈ p ⁻¹ᵁ (V ⊓ U₀) := fun z ↦ z.2
      have hg' : ∀ z, ((g ≫ p) ≫ e) z ∈ p ⁻¹ᵁ (V ⊓ U₀) := hse (g ≫ p) hg
      have k₁ := pull_isLB_of_isOn P _ _ M' g hM' fun z ↦ (hg z).1
      have k₂ := pull_isLB_of_isOn P _ _ M g hM fun z ↦ (hg z).1
      have k₃ := pull_isLB_of_isOn P _ _ M _ hM fun z ↦ (hg' z).1
      have k₄ := pull_isLB_of_isOn P _ _ L₀ g h₀ fun z ↦ (hg z).2
      have k₅ := pull_isLB_of_isOn P _ _ L₀ _ h₀ fun z ↦ (hg' z).2
      refine (cls_eq_iff k₁ k₄).1 ?_
      rw [hc _ g (fun z ↦ (hg z).1) k₁ k₂ k₃, cmp _ g hg k₂ k₄]
      exact sub_eq_self.2 ((cmp _ _ hg' k₃ k₅).trans (z₀ _ (g ≫ p) (fun z ↦ (hg z).2) k₅))
  choose V M h₁ h₂ h₃ h₄ h₅ using key
  obtain ⟨N, hN, hv⟩ := exists_glue_of_rigid U₀ p he h₀ t₀ V (fun y ↦ by
    by_cases hy : y ∈ U₀
    · exact ⟨none, (h₂ none rfl).1 ▸ hy⟩
    · exact ⟨some y, h₁ _ y rfl hy⟩) M h₃ h₄ h₅
  obtain ⟨v, hv⟩ := hv none
  have i₁ := lbIso_pull_of_isoOn P Q _ N (M none) v a hv fun z ↦ (h₂ none rfl).1 ▸ ha z
  rw [(h₂ none rfl).2] at i₁
  exact ⟨N, hN, (cls_eq_iff (pull_isLB hN a) hL).1 (((cls_eq_iff _ k₀).2 i₁).trans c₀)⟩

end GlobalTheory.DenseGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUnitaryPointGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_unitary_point_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V →
    IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  first | exact @GlobalTheory.TraitSemi.exists_ext_semi | exact GlobalTheory.TraitSemi.exists_ext_semi | (intros; apply GlobalTheory.TraitSemi.exists_ext_semi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatEpiLiftRaynaudExtensionFractionPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_epi_lift_raynaud_extension_fraction_point : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (z : (DegPre.BF Q (FractionRing R)).left), ∃ (Z : Scheme.{0}) (p : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (w : Z) (y : Z ⟶ Y.H.left), p w = z ∧ Epi p ∧ Function.Injective (p.stalkMap w).hom ∧ y ≫ Y.q.left = p ≫ (DegPre.prB Q (FractionRing R)).left := by
  first | exact @GlobalTheory.RayLift.exists_flat_lift | exact GlobalTheory.RayLift.exists_flat_lift | (intros; apply GlobalTheory.RayLift.exists_flat_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointClosureEqOfIsClopen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_genericPoint_closure_eq_of_isClopen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ η ∈ genericPoints (Xo.XF c), closure {C.i η} = A := by
  intro E _ _ _ H Dw _ l Xo c C A hA hirr hne
  obtain ⟨_, hyA, y, rfl⟩ := hne
  have hζ : IsGenericPoint hirr.genericPoint A := hirr.isGenericPoint_genericPoint hA.isClosed
  set ζ := hirr.genericPoint
  have h1 : ζ ⤳ C.i y := hζ.specializes hyA
  have hcomp : C.z (C.i y) = spMap C.b (pullback.snd C.z (spMap C.b) (C.iF y)) := by
    have := congrArg (fun f => f.base (C.iF y)) (pullback.condition (f := C.z) (g := spMap C.b))
    simpa using this
  have hbot : ∀ q : Sp c.F, (spMap C.b q).asIdeal = ⊥ := by
    intro q
    haveI := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
    show Ideal.comap C.b q.asIdeal = ⊥
    rw [hq]
    exact Ideal.comap_bot_of_injective C.b C.inj
  have h2 : C.z ζ = C.z (C.i y) := by
    have hs : C.z ζ ⤳ C.z (C.i y) := h1.map C.z.continuous
    have hle : (C.z ζ).asIdeal ≤ (C.z (C.i y)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 hs
    rw [hcomp, hbot] at hle
    apply PrimeSpectrum.ext
    rw [hcomp, hbot]
    exact le_bot_iff.1 hle
  obtain ⟨p', hp', -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.z) (g := spMap C.b) ζ
    (pullback.snd C.z (spMap C.b) (C.iF y)) (h2.trans hcomp)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := by
    letI := C.b.toAlgebra
    haveI := C.isFractionRing
    haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
    infer_instance
  have h3 : p' ⤳ C.iF y := by
    apply (IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).specializes_iff.1
    rw [hp']
    exact h1
  haveI := C.iF_open
  obtain ⟨η, hη⟩ := h3.mem_open C.iF.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  have hCi : C.i η = ζ := by
    rw [← hp', ← hη]
    rfl
  have hinj : Function.Injective C.i := (IsPreimmersion.isEmbedding C.i).injective
  refine ⟨η, ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩, by rw [hCi]; exact hζ⟩
  have hη' : IsGenericPoint hT.closure.genericPoint (closure T) :=
    hT.closure.isGenericPoint_genericPoint isClosed_closure
  have hs : hT.closure.genericPoint ⤳ η := hη'.specializes (subset_closure (hle (subset_closure rfl)))
  have hs' : C.i hT.closure.genericPoint ⤳ ζ := hCi ▸ hs.map C.i.continuous
  have hmem : C.i hT.closure.genericPoint ∈ A := hs'.mem_open hA.isOpen hζ.mem
  have heq : hT.closure.genericPoint = η := hinj ((hs'.antisymm (hζ.specializes hmem)).eq.trans hCi.symm)
  rw [← heq, hη']
  exact subset_closure

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataAStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringOfIntegers_module_on_tensor_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) ∧ (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) := by
  first | exact @GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data | exact GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data | (intros; apply GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFieldCoefficientsOfLinearVectorFiStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_field_coefficients_of_linear_vectorField : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) →
    ∀ (W : G.left.Opens) (δ : Fld G.left), IsField W δ → (∀ O, O ≤ W → ∀ r, δ O (constFn G.hom O r) = 0) →
    ∃ c : Fin n → Γ(G.left, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  first | exact @GlobalTheory.VertCoeffRing.exists_coeff | exact GlobalTheory.VertCoeffRing.exists_coeff | (intros; apply GlobalTheory.VertCoeffRing.exists_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayTan

theorem smooth_H : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Smooth Y.H.hom := by
  intro R _ _ Q O _ _ _ oa Y
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

theorem exists_basis_isInv : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  intro R _ _ _ _ Q O _ _ _ oa Y
  obtain ⟨n, ⟨v⟩⟩ := GlobalTheory.T.exists_finite_basis_tangentModule_smooth_commGroupScheme R Y.H (smooth_H R Q O oa Y)
  choose dd hdd using fun a => GlobalTheory.T.exists_invariantVectorField_of_tangentVector_origin R Y.H (v a)
  exact ⟨n, v, dd, hdd⟩

end GlobalTheory.RayTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldSemiAbelianTripleAffinStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_vectorField_semiAbelian_triple_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v : TanM (𝟙 (Sp R)) t.G), ∃ dd : Fld t.G.left, IsInv t.G v dd := by
  first | exact @GlobalTheory.InvFieldSemiAb.exists_isInv | exact GlobalTheory.InvFieldSemiAb.exists_isInv | (intros; apply GlobalTheory.InvFieldSemiAb.exists_isInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCoordinatesOnFieldFibresLocalRingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_coordinates_on_field_fibres_local_ring : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R), (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → n = g) ∧ ∀ (k : Type) [Field k] (f : R →+* k), ∃ T : (Fin n → k) → (epsPt (spMap f) ⟶ G), Function.Injective T ∧ (∀ v : epsPt (spMap f) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (v).left = (1 : Over.mk (spMap f) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (t : k) c, (T (t • c)).left = spMap (epsScale t) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c) := by
  first | exact @GlobalTheory.exists_lie_coordinates_fibres | exact GlobalTheory.exists_lie_coordinates_fibres | (intros; apply GlobalTheory.exists_lie_coordinates_fibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_uniformisation_base_change_complete_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ f : V →+* W, Function.Injective f → IsLocalHom f →
    ∀ tW : SAB H (Sp W), Nonempty (SABMap tW t (spMap f)) →
      ∃ (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X),
        ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : Wˣ, PsiCoord PW.D.toPre y (u * f r) := by
  first | exact @GlobalTheory.UnifDvrBaseChange.exists_pelUnif | exact GlobalTheory.UnifDvrBaseChange.exists_pelUnif | (intros; apply GlobalTheory.UnifDvrBaseChange.exists_pelUnif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicTraitLiftFiniteThroughPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicTrait_lift_finite_through_point : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ (p : ℕ) [Fact p.Prime] (Y : Sp (OO p) ⟶ Z) (w : X), f w = (gPt p ≫ Y) (IsLocalRing.closedPoint (PadicAlgCl p)) → ∃ y : Sp (OO p) ⟶ X, y ≫ f = Y ∧ (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) = w := by
  first | exact @GlobalTheory.UPoinc.exists_lift_finite_through_point | exact GlobalTheory.UPoinc.exists_lift_finite_through_point | (intros; apply GlobalTheory.UPoinc.exists_lift_finite_through_point <;> assumption)
end


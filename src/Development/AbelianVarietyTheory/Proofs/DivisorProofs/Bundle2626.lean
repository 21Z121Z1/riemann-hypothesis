import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodRatioAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinFourierExpansionSupport
section
set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion qClass qRel)
open GlobalTheory.PairFourier (pairPt pairCoef qClass_eq tsum_natCast_eq pairPt_ne_zero)

namespace GlobalTheory.HilbFam

theorem fourier_with_support :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ),
      HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧
        a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧
        (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : Emb F, 0 < i ξ) ∧
        ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w)
          ((cK F k : ℂ) * G w / (omegaFactor 𝔞 : ℂ) ^ k) := by
  classical
  intro F _ _ _ k 𝔞 𝔟 G hG
  obtain ⟨Z, hZ, hE⟩ := hG
  set C : ℂ := (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) with hC
  let p : Quotient (qRel 𝔞 𝔟) → F := fun c ↦ (pairPt 𝔞 𝔟 c : F)
  let a' : F → ℂ := fun ξ ↦ ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ)
  have ha' : ∀ ξ, a' ξ = ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ) := fun _ ↦ rfl
  have hfib : ∀ (z : Emb F → ℂ) (ξ : F) (c : p ⁻¹' {ξ}),
      qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * qPow ξ z := by
    rintro z ξ ⟨c, hc⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact qClass_eq 𝔞 𝔟 k z c
  refine ⟨Z, fun ξ ↦ a' ξ + if ξ = 0 then C else 0, hZ, ?_, ?_, ?_, ?_⟩
  · show a' 0 + (if (0 : F) = 0 then C else 0) = C
    rw [if_pos rfl]
    have : IsEmpty (p ⁻¹' {0}) :=
      ⟨fun ⟨c, hc⟩ ↦ pairPt_ne_zero 𝔞 𝔟 c
        (Subtype.ext (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hc)))⟩
    rw [ha']
    simp only [tsum_empty, zero_add]
  · intro ξ hξ
    set z₀ : Emb F → ℂ := fun _ ↦ Complex.I
    have hz₀ : z₀ ∈ upperHalf F := fun _ ↦ by simp [z₀]
    have hq : qPow ξ z₀ ≠ 0 := Complex.exp_ne_zero _
    have hsum : Summable (fun c : p ⁻¹' {ξ} ↦ (pairCoef 𝔞 𝔟 k c : ℂ)) := by
      have := ((hE z₀ hz₀).1.subtype (p ⁻¹' {ξ})).mul_right (qPow ξ z₀)⁻¹
      refine this.congr fun c ↦ ?_
      simp only [Function.comp_apply]
      rw [hfib z₀ ξ c, mul_assoc, mul_inv_cancel₀ hq, mul_one]
    obtain ⟨m, hm⟩ := tsum_natCast_eq _ hsum
    refine ⟨m, ?_⟩
    show a' ξ + (if ξ = 0 then C else 0) = _
    rw [if_neg hξ, add_zero, ha']
    simp only [hm]
    simp
  · intro ξ hξ hne
    have hne' : a' ξ ≠ 0 := by
      intro h
      apply hne
      show a' ξ + (if ξ = 0 then C else 0) = 0
      rw [if_neg hξ, h, add_zero]
    by_cases hem : IsEmpty (p ⁻¹' {ξ})
    · exact absurd (by rw [ha']; exact tsum_empty) hne'
    obtain ⟨c, hc⟩ := not_isEmpty_iff.1 hem
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨(pairPt 𝔞 𝔟 c).2, c.out.2.2.2⟩
  · intro z hz
    obtain ⟨hs, heq⟩ := hE z hz
    have h1 := hs.hasSum.tsum_fiberwise p
    have h2 : (fun ξ ↦ ∑' c : p ⁻¹' {ξ}, qClass 𝔞 𝔟 k z c) = fun ξ ↦ a' ξ * qPow ξ z := by
      funext ξ
      rw [ha', ← tsum_mul_right]
      exact tsum_congr (hfib z ξ)
    rw [h2] at h1
    have h3 : HasSum (fun ξ : F ↦ (if ξ = 0 then C else 0) * qPow ξ z) C := by
      convert hasSum_ite_eq (0 : F) C using 1
      funext ξ
      split_ifs with h
      · subst h; simp [qPow]
      · simp
    have hv : (cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k =
        (∑' c, qClass 𝔞 𝔟 k z c) + C := by rw [heq]; ring
    show HasSum (fun ξ : F ↦ (a' ξ + if ξ = 0 then C else 0) * qPow ξ z)
      ((cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k)
    rw [hv]
    simp only [add_mul]
    exact h1.add h3

end GlobalTheory.HilbFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceSurjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeSubSurj

theorem pullbackSections_fromSpec_surjective {T : Scheme.{0}} (F : T.Modules) [F.IsQuasicoherent]
    {V : T.Opens} (hV : IsAffineOpen V) (t : Γ((Scheme.Modules.pullback hV.fromSpec).obj F, ⊤)) :
    ∃ s, pullbackSections hV.fromSpec F hV.fromSpec_preimage_self.ge s = t := by
  have e := hV.fromSpec_preimage_self.ge
  letI := QCoh.appLEAlgebra hV.fromSpec e
  letI := QCoh.appLEModule hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e
  haveI := QCoh.appLE_isScalarTower hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e
  have H := QCoh.isBaseChange_pullbackSections hV.fromSpec F (isAffineOpen_top _) hV e
  have hs : Function.Surjective (hV.fromSpec.appLE V ⊤ e) := by
    have : hV.fromSpec.appLE V ⊤ e = (Scheme.ΓSpecIso Γ(T, V)).inv := by
      rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
    rw [this]
    exact (ConcreteCategory.bijective_of_isIso _).2
  induction t using H.inductionOn with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s => exact ⟨s, rfl⟩
  | smul r t ih =>
    obtain ⟨s, rfl⟩ := ih
    obtain ⟨r, rfl⟩ := hs r
    exact ⟨r • s, QCoh.pullbackSections_smul _ _ _ _ _⟩
  | add t t' ih ih' =>
    obtain ⟨s, rfl⟩ := ih
    obtain ⟨s', rfl⟩ := ih'
    exact ⟨s + s', map_add _ _ _⟩

section Affine

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isTangent_iff_ptMap (v : epsR R ⟶ G) : IsTangent v ↔
    Pdiv.ptMap (TrivSqZeroExt.fstHom R R R) ≫ (v : Pdiv.specO R (DualNumber R) ⟶ G) =
      toUnit (Pdiv.specO R R) ≫ η[G] := by
  refine ⟨fun h => ?_, fun h => congrArg Over.Hom.left (epsZero_comp (G := G) ⟨v, h⟩)⟩
  have h' : (toUnit (Pdiv.specO R R)).left = 𝟙 (Sp R) := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  ext1
  simp only [Over.comp_left, h']
  exact h.trans (Category.id_comp _).symm

theorem exists_omega [QuasiSeparated G.hom] [Smooth G.hom] (f : Cris.Form (G.hom ≫ 𝟙 _)) :
    ∃ w : Γ(omega G, ⊤), ∀ x : Pdiv.LieG G, tanVal (A := G) x.1 f =
      (Scheme.ΓSpecIso (.of R)).hom (VB.dualApp (tangent x) le_top w) := by
  obtain ⟨w, hw⟩ := (OmegaGlobal.toOmega_bijective R G
    ⟨tangent_injective _ _, TangentSurj.tangent_surjective _ _⟩).2
    ⟨fun x => tanVal (A := G) x.1 f,
      fun x y _ => tanVal_mul ((isTangent_iff_ptMap _).2 x.2) ((isTangent_iff_ptMap _).2 y.2) f,
      fun a x _ => tanVal_epsScale a x.1 f⟩
  exact ⟨w, fun x => (congrArg (fun u => u.1 x) hw).symm⟩

theorem form_eq {T : Scheme.{0}} {A : Over T} [GrpObj A] {b : Sp R ⟶ T} {φ : G.left ⟶ A.left}
    (h : IsGrpPullback G A b φ) (x : Pdiv.LieG G)
    (w : (x.1.left ≫ φ) ≫ A.hom = (Pdiv.specO R (DualNumber R)).hom ≫ b)
    (we : sec (epsZero R) ≫ x.1.left ≫ φ = b ≫ unitSec A) :
    TanFibre.form w we = omegaBase h ≫ cotMap x.1 (epsZero_comp x) ≫ (epsIso R).hom := by
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine congrArg (· ≫ (epsIso R).hom) ?_
  refine Conormal.pullback_hom_ext (sec_hom η[A]) fun W a => ?_
  have k₁ := Conormal.le_of_sq (unitSec_comp h) (le_refl (unitSec A ⁻¹ᵁ W)) le_rfl
  have k₂ := Conormal.le_of_sq we (le_refl (unitSec A ⁻¹ᵁ W)) le_rfl
  refine (Conormal.baseMap_d (sec_hom η[A]) _ w we le_rfl le_rfl k₂ le_rfl a).trans (Eq.symm ?_)
  refine (congrArg ((cotMap x.1 (epsZero_comp x)).app _)
    (omegaBase_dUnit h le_rfl le_rfl k₁ le_rfl a)).trans ?_
  refine (cotMap_d x.1 (epsZero_comp x) k₁ k₂ le_rfl _).trans ?_
  exact congrArg _ (Conormal.appLE_appLE rfl _ _ _ a)

theorem exists_pullback_omega {T : Scheme.{0}} {A : Over T} [GrpObj A] [QuasiSeparated A.hom]
    [Smooth A.hom] {b : Sp R ⟶ T} {φ : G.left ⟶ A.left} (h : IsGrpPullback G A b φ)
    (f : Cris.Form (G.hom ≫ 𝟙 _)) :
    ∃ t : Γ((Scheme.Modules.pullback b).obj (omega A), ⊤), ∀ (v : epsR R ⟶ G), IsTangent v →
      ∀ (w : (v.left ≫ φ) ≫ A.hom = (Pdiv.specO R (DualNumber R)).hom ≫ b)
        (we : sec (epsZero R) ≫ v.left ≫ φ = b ≫ unitSec A),
        tanVal v f = (Scheme.ΓSpecIso (.of R)).hom ((TanFibre.form w we).app ⊤ t) := by
  have : QuasiSeparated G.hom := MorphismProperty.of_isPullback h.1 ‹_›
  have : Smooth G.hom := MorphismProperty.of_isPullback h.1 ‹_›
  obtain ⟨u, hu⟩ := exists_omega f
  have := isIso_omegaBase h
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((omegaBase h).app ⊤)).2 u
  refine ⟨t, fun v hv w we => ?_⟩
  let x : Pdiv.LieG G := ⟨v, (isTangent_iff_ptMap v).1 hv⟩
  have e := form_eq h x w we
  refine (hu x).trans (congrArg (fun a : Γ(Sp R, ⊤) => (Scheme.ΓSpecIso (.of R)).hom a) ?_)
  exact (congr(($e).app ⊤ t)).symm

theorem exists_form {c : primDR G} (hc : c ∈ PrimitiveSubmodule G) : ∃ f : Cris.Form (G.hom ≫ 𝟙 _),
    ∀ (v : epsR R ⟶ G) (k : HdR G), IsLieImage k v → k c = tanVal v f := by
  change c.1 ∈ Cris.F1 _ at hc
  rw [Cris.hodgeFiltration_eq_range] at hc
  obtain ⟨c, hc'⟩ := c
  obtain ⟨f, rfl⟩ := hc
  exact ⟨f, fun v k hk => hk.2 f hc'⟩

end Affine

theorem exists_corr {T : Scheme.{0}} (A : Over T) [GrpObj A] [QuasiSeparated A.hom] [Smooth A.hom]
    {V : T.Opens} (hV : IsAffineOpen V) (c : primDR (onAff A hV)) (hc : c ∈ PrimitiveSubmodule (onAff A hV)) :
    ∃ s, GlobalTheory.HodgeSub.Corr A hV s c := by
  have h : IsGrpPullback (onAff A hV) A hV.fromSpec (pullback.fst A.hom hV.fromSpec) :=
    isGrpPullback_pullback A hV.fromSpec
  obtain ⟨f, hf⟩ := exists_form hc
  obtain ⟨t, ht⟩ := exists_pullback_omega h f
  obtain ⟨s, hs⟩ := pullbackSections_fromSpec_surjective (omega A) hV t
  refine ⟨s, fun v k hk w we => (hf v k hk).trans ((ht v hk.1 w we).trans ?_)⟩
  rw [← hs]
  rfl

theorem main : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V : T.Opens) (hV : IsAffineOpen V) (c : primDR (onAff A hV)), c ∈ PrimitiveSubmodule (onAff A hV) →
      ∃ s, GlobalTheory.HodgeSub.Corr A hV s c := by
  intro _ T A _ g hA hg V hV c hc
  have := hA.proper
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  exact exists_corr A hV c hc

end GlobalTheory.HodgeSubSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftEqComapSystemFiltration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem hodgeFiltration_lift_map_eq_crystalline_kernel (H : CrystallineSmoothLift) {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0)
    {π : R →+* R₀} (hπ : Function.Surjective π) (hk : RingHom.ker π = I) {X₀ X : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}
    {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : IsPullback i s₀ s (spMap π)) (hs : Smooth s) (hs' : IsSeparated s)
    (hs'' : QuasiCompact s) (S : Sys I π s₀) (hP : S.Presents s i)
    (m : IsMor (dp0 R) s (divided₂ hI) (s₀ ≫ spMap π) (RingHom.id R) i) :
    (F1 s).map m.pull1 = S.K hI := by
  have hb := (H.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk X X₀ s s₀ i hs hs' hs'' h m).1
  obtain ⟨e, he, -⟩ := GlobalTheory.T.hodge_cohomology_iso_presented_crystal R R₀ I hI π hπ hk X₀ s₀ S X s i h hP
  have key : ∀ c, m.pull1 c ∈ S.K hI ↔ c ∈ F1 s := fun c ↦ by
    change S.r hI (m.pull1 c) = 0 ↔ toH1O s c = 0
    rw [← he m c, LinearEquiv.map_eq_zero_iff, structureSheaf_comparison_comm]
    exact ⟨fun h0 ↦ cmpO_injective R X s (h0.trans (map_zero _).symm), fun h0 ↦ by rw [h0, map_zero]⟩
  ext x
  obtain ⟨c, rfl⟩ := hb.2 x
  constructor
  · rintro ⟨c', hc', e'⟩
    rw [← hb.1 e']
    exact (key c').2 hc'
  · intro hx
    exact ⟨c, (key c).1 hx, rfl⟩

theorem hodgeFiltration_lift_eq_comap_systemFiltration (H : CrystallineSmoothLift) (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R)
    (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀))
    [GrpObj A₀] (hA : IsProper A₀.hom) (hA' : GeometricallyConnected A₀.hom) (X : Over (Sp R))
    (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)) (hX : Smooth X.hom) (S : Sys I π A₀.hom)
    (hP : S.Presents X.hom i) :
    primitiveCrystalHodgeLiftClasses (divided₂ hI) A₀ X i h.w = (S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype := by
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk, hI]⟩
  have hpr := (GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift R R₀ π hπ hnil X A₀ i h hX hA hA').1
  have e : X.hom ≫ 𝟙 _ = X.hom := Category.comp_id _
  have h' : IsPullback i A₀.hom (X.hom ≫ 𝟙 _) (spMap π) := by rw [e]; exact h
  have hs : Smooth (X.hom ≫ 𝟙 _) := by rw [e]; exact hX
  have hs' : IsSeparated (X.hom ≫ 𝟙 _) := by rw [e]; infer_instance
  have hs'' : QuasiCompact (X.hom ≫ 𝟙 _) := by rw [e]; infer_instance
  have hP' : S.Presents (X.hom ≫ 𝟙 _) i := by rw [e]; exact hP
  unfold primitiveCrystalHodgeLiftClasses
  rw [hodgeFiltration_lift_map_eq_crystalline_kernel H hI hπ hk h' hs hs' hs'' S hP']

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicWeightedSquareIntegrableVanishes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff

namespace GlobalTheory

theorem holo_vanish_of_critical_integrable : ∀ {n : ℕ}, 0 < n → ∀ (u : V n → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) < ⊤ → u 0 = 0 := by
  intro n hn u ρ hρ hu hint
  by_contra hne
  have hb : Metric.ball (0 : V n) ρ ∈ nhds (0 : V n) := Metric.ball_mem_nhds 0 hρ
  set a := ‖u 0‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hne
  have hc : ContinuousAt u 0 := hu.continuousOn.continuousAt hb
  have ev1 : ∀ᶠ z in nhds (0 : V n), a / 2 < ‖u z‖ :=
    hc.norm.eventually (Ioi_mem_nhds (by show a / 2 < a; linarith))
  obtain ⟨δ0, hδ0, hall⟩ := Metric.eventually_nhds_iff.mp (ev1.and (Filter.eventually_of_mem hb fun z hz => hz))
  set δ := min δ0 ρ with hδ
  have hδpos : 0 < δ := lt_min hδ0 hρ
  have hsub : Metric.ball (0 : V n) δ ⊆ Metric.ball (0 : V n) ρ := Metric.ball_subset_ball (min_le_right _ _)
  have hpt : ∀ z ∈ Metric.ball (0 : V n) δ,
      ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
        ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    intro z hz
    have hz0 : dist z 0 < δ0 := by
      rw [Metric.mem_ball] at hz; exact lt_of_lt_of_le hz (min_le_left _ _)
    have h1 := (hall hz0).1
    rw [← ENNReal.ofReal_mul (by positivity), neg_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr : 0 ≤ ‖z‖ ^ (-(2 * (n : ℝ))) := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : (a / 2) ^ 2 ≤ ‖u z‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    exact mul_le_mul_of_nonneg_right h2 hr
  have hlow : ENNReal.ofReal ((a / 2) ^ 2) * ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
      ≤ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
        ≤ ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
      _ ≤ _ := lintegral_mono_set hsub
  rw [ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div hn hδpos,
    ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le]; positivity)] at hlow
  exact absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevels
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] (x : Sp C ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U.1) :
    ∃ g : Sec s U.1 →+* C, spMap g ≫ affPt s U = x := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec x U.2 (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  refine ⟨(x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom, ?_⟩
  change Spec.map (x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) ≫ U.2.fromSpec = x
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem eq_of_spMap_eq {A C : Type} [CommRing A] [CommRing C] {g g' : A →+* C} (h : spMap g = spMap g') : g = g' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem eq_of_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] {g g' : Sec s U.1 →+* C} (h : spMap g ≫ affPt s U = spMap g' ≫ affPt s U) : g = g' := by
  have : Mono (affPt s U) := @IsOpenImmersion.mono _ _ _ (IsAffineOpen.isOpenImmersion_fromSpec U.2)
  exact eq_of_spMap_eq ((cancel_mono _).1 h)

theorem red_over (D : Data) : D.i ≫ D.s = D.t := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  rw [ht, hpb.w]

variable {D : Data} (Λ : Lift D)

theorem Lift.isDPMorphism (U : AffOp D.X) (T : Thick D.κ D.t) (φ : (Λ.L.obj U).B →ₐ[D.R] T.B) :
    IsDPMorphism (Λ.L.obj U).δ T.δ (φ : (Λ.L.obj U).B →+* T.B) := by
  have hI : ∀ r ∈ D.I, algebraMap D.R T.B r ∈ T.J := fun r hr ↦ T.dp.1 (Ideal.mem_map_of_mem _ hr)
  refine IsDPMorphism.on_span (S := algebraMap D.R (Λ.L.obj U).B '' D.I) _ _ (Λ.gen U) ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    simpa using hI r hr
  · rintro n _ ⟨r, hr, rfl⟩
    rw [(Λ.L.obj U).dp.2 r hr]
    simpa using (T.dp.2 (n := n) r hr).symm

theorem Lift.hom_iff (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B) :
    spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔
      ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a := by
  constructor
  · intro h
    let φ : (Λ.L.obj U).B →ₐ[D.R] T.B := y.comp (Λ.e U).symm.toAlgHom
    have hφ : ∀ a, φ (Λ.e U a) = y a := fun a ↦ by simp [φ]
    have hd := Λ.isDPMorphism U T φ
    let φ₀ : (Λ.L.obj U).B₀ →+* T.B₀ := RingHom.liftOfSurjective (Λ.L.obj U).π (Λ.L.obj U).surj
      ⟨T.π.comp (φ : (Λ.L.obj U).B →+* T.B), fun b hb ↦
        (T.ker _).2 (hd.1 (Ideal.mem_map_of_mem _ (((Λ.L.obj U).ker b).1 hb)))⟩
    have hc : ∀ b, φ₀ ((Λ.L.obj U).π b) = T.π (φ b) := fun b ↦
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ b
    refine ⟨⟨φ, φ₀, hc, hd, ?_⟩, hφ⟩
    have := D.mono_i
    rw [← cancel_mono D.i, Category.assoc, ← Λ.pt U, ← h, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ (hc _).trans (congrArg T.π (hφ a))
  · rintro ⟨b, hb⟩
    rw [← b.pt, Category.assoc, ← Λ.pt U, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ ((b.comm _).trans (congrArg T.π (hb a))).symm

theorem Lift.hom_spec : ∀ (D : Data) (Λ : Lift D), (∀ (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B), spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔ ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a) ∧ (∀ (U : AffOp D.X) (T : Thick D.κ D.t), ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ g : Sec D.s U.unop.1 →+* T.B₀, spMap g ≫ affPt D.s U.unop = T.x ≫ D.i ∧ ∀ r, g (algebraMap D.R _ r) = T.π (algebraMap D.R T.B r)) ∧ (∀ (U : AffOp D.X) (C : Type) [CommRing C] (g g' : Sec D.s U.unop.1 →+* C), spMap g ≫ affPt D.s U.unop = spMap g' ≫ affPt D.s U.unop → g = g') ∧ ∃ N₀, ∀ N, N₀ ≤ N → ∀ U, IsLev (Λ.L.obj U).δ N := by
  intro D Λ
  refine ⟨Λ.hom_iff, fun U T h ↦ ?_, fun U C _ g g' h ↦ eq_of_spMap_affPt _ _ h, ?_⟩
  · obtain ⟨g, hg⟩ := exists_spMap_affPt D.s U.unop _ h
    refine ⟨g, hg, fun r ↦ ?_⟩
    have : spMap (g.comp (algebraMap D.R (Sec D.s U.unop.1))) = spMap (T.π.comp (algebraMap D.R T.B)) := by
      rw [Cris.spMap_comp, ← affPt_w, ← Category.assoc, hg, Category.assoc, red_over, T.w]
    exact RingHom.congr_fun (eq_of_spMap_eq this) r
  · obtain ⟨N₀, h⟩ := (isDPNilpotent_iff_exists_isLevel D.κ).1 D.nil
    refine ⟨N₀, fun N hN U ↦ ?_⟩
    have h' : fil D.κ N = ⊥ := eq_bot_iff.2 (le_of_le_of_eq (ExpBij.dpFil_anti D.κ hN) h)
    have := fil_le_map_fil _ _ D.κ _ _ (Λ.L.obj U).δ _ (Λ.L.obj U).dp (Λ.gen U) N
    rw [h', Ideal.map_bot] at this
    exact eq_bot_iff.2 this

end GlobalTheory.PDForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomDescentQb

theorem exists_holUnif (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : ∃ L : LB A.left, Nonempty (HolUnif A L g) := by
  have := hA.proper
  have := hA.comm
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hamp : Out.RelAmple A H :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
  exact ⟨_, GlobalTheory.RealMultChart.exists_holUnif_of_compact A g hg
    (GlobalTheory.RealMultChart.compactSpace_points A H hamp)
    (fun a n hn => GlobalTheory.RealMultChart.exists_pow_eq A hA a n hn)⟩

theorem hom_descends : ∀ (A₀ B₀ : Over (Sp Qb)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B]
    (p : A.left ⟶ A₀.left) (q : B.left ⟶ B₀.left) (g g' : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
    IsAbelianScheme B₀ → SmoothOfRelativeDimension g' B₀.hom →
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p → IsGrpPullback B B₀ (spMap (algebraMap Qb ℂ)) q →
    ∀ α : A ⟶ B, IsMonHom α → ∃ α₀ : A₀ ⟶ B₀, IsMonHom α₀ ∧ α.left ≫ q = p ≫ α₀.left := by
  intro A₀ B₀ _ _ A B _ _ p q g g' hA₀ hgA₀ hB₀ hgB₀ hp hq α hα
  haveI : Countable Qb :=
    (Algebraic.countable ℚ ℂ).mono (fun z hz => mem_algebraicClosure_iff.1 hz) |>.to_subtype
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ hp
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₀ hq
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 hgA₀
  have hgB : SmoothOfRelativeDimension g' B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback hq.1 hgB₀
  obtain ⟨L, ⟨u⟩⟩ := exists_holUnif A g hA hgA
  obtain ⟨L', ⟨u'⟩⟩ := exists_holUnif B g' hB hgB
  exact GlobalTheory.CMLiePeriod.descend hA₀ hB₀ hA hB hgA hgB u u' hp hq α

end GlobalTheory.HomDescentQb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  first | exact @GlobalTheory.TwistFlat.isClosedImmersion_kerι | exact GlobalTheory.TwistFlat.isClosedImmersion_kerι | (intros; apply GlobalTheory.TwistFlat.isClosedImmersion_kerι <;> assumption)
end


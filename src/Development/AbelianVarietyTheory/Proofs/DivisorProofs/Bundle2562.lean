import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentDataChartsCommon
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.CommonChart

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spinj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem flat_generic {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) [Flat φ] :
    φ (genericPoint Y) = genericPoint X := by
  have hg : GeneralizingMap φ := Flat.generalizingMap φ
  obtain ⟨y, hy, e⟩ := hg (genericPoint_specializes (φ (genericPoint Y)))
  have : y = genericPoint Y := (hy.antisymm (genericPoint_specializes y)).eq
  rw [← this, e]

theorem exists_ff {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) [Flat φ] :
    ∃ θ : X.functionField →+* Y.functionField, gp Y ≫ φ = spMap θ ≫ gp X := by
  have h := flat_generic φ
  refine ⟨((X.presheaf.stalkSpecializes (specializes_of_eq h)) ≫ φ.stalkMap (genericPoint Y)).hom, ?_⟩
  show Y.fromSpecStalk _ ≫ φ = Spec.map (_ ≫ _) ≫ X.fromSpecStalk _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem gp_spec (R : CommRingCat.{0}) [IsDomain R] :
    ∃ c : R →+* (Spec R).functionField, Function.Injective c ∧ gp (Spec R) = spMap c :=
  ⟨algebraMap R (Spec R).functionField, IsFractionRing.injective R (Spec R).functionField,
    Spec.fromSpecStalk_eq' _ _⟩

theorem gp_factor {E : Type} [CommRing E] [IsDomain E] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp E) [Flat p] :
    ∃ t : Sp Y.functionField ⟶ Sp (FractionRing E), t ≫ jK E = gp Y ≫ p := by
  obtain ⟨θ, h⟩ := exists_ff p
  obtain ⟨c, hc, this⟩ := gp_spec (CommRingCat.of E)
  have hi : Function.Injective (θ.comp c) := θ.injective.comp hc
  refine ⟨spMap (IsFractionRing.lift hi), ?_⟩
  rw [h, spc]
  rw [this, spc]
  congr 1
  ext z
  simp

theorem ring_part (R R₀ R' O Ω : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] [IsRegularLocalRing R₀]
    [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing O] [IsLocalRing O] [Field Ω]
    [Algebra R O] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime O p]
    (ρ : R →+* R₀) (hρ : ρ.Flat) (φ' : O →+* R') [IsLocalHom φ'] (u : R₀ →+* Ω) (u' : R' →+* Ω)
    (hc : IsAdicComplete (maximalIdeal R') R') (he : IsEtaleCompletion φ')
    (hu : ((residue R').comp φ').FormallyUnramified) (hk : RingHom.ker u' = maximalIdeal R')
    (huu : u.comp ρ = u'.comp (φ'.comp (algebraMap R O))) :
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : R₀ →+* E) (b : R' →+* E)
      (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp ρ = b.comp (φ'.comp (algebraMap R O)) ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (RingHom.ker u).map a = maximalIdeal E := by
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing p.primeCompl O inferInstance
  haveI hq : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
  let R₁ := Localization.AtPrime (RingHom.ker u)
  haveI : IsRegularRing R₀ := isRegularRing_of_isRegularLocalRing R₀
  haveI : IsRegularLocalRing R₁ := IsRegularRing.isRegularLocalRing_localization _
  have h1 : ∀ s : p.primeCompl, IsUnit (((algebraMap R₀ R₁).comp ρ) s) := by
    intro s
    have hs : IsUnit (u (ρ s)) := by
      have := RingHom.congr_fun huu s
      simp only [RingHom.comp_apply] at this
      rw [this]
      exact ((IsLocalization.map_units O s).map φ').map u'
    exact IsLocalization.map_units R₁ (⟨ρ s, fun h => hs.ne_zero h⟩ : (RingHom.ker u).primeCompl)
  have h2 : ∀ s : (RingHom.ker u).primeCompl, IsUnit (u s) := fun s => Ne.isUnit s.2
  let φ₁ : O →+* R₁ := IsLocalization.lift h1
  let u₁ : R₁ →+* Ω := IsLocalization.lift h2
  have e1 : φ₁.comp (algebraMap R O) = (algebraMap R₀ R₁).comp ρ := IsLocalization.lift_comp h1
  have e2 : u₁.comp (algebraMap R₀ R₁) = u := IsLocalization.lift_comp h2
  have hm : (RingHom.ker u).map (algebraMap R₀ R₁) = maximalIdeal R₁ := Localization.AtPrime.map_eq_maximalIdeal
  have k1 : RingHom.ker u₁ = maximalIdeal R₁ := by
    refine ((maximalIdeal.isMaximal R₁).eq_of_le (RingHom.ker_ne_top u₁) ?_).symm
    rw [← hm, Ideal.map_le_iff_le_comap, RingHom.comap_ker, e2]
  have e3 : u₁.comp φ₁ = u'.comp φ' := by
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [RingHom.comp_assoc, e1, ← RingHom.comp_assoc, e2, huu]; rfl
  have fl0 : (algebraMap R₀ R₁).Flat := by
    rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat R₁ (RingHom.ker u).primeCompl
  have fl1 : φ₁.Flat := by
    have hf : (φ₁.comp (algebraMap R O)).Flat := by rw [e1]; exact hρ.comp fl0
    letI : Algebra O R₁ := φ₁.toAlgebra
    letI : Algebra R R₁ := (φ₁.comp (algebraMap R O)).toAlgebra
    haveI : IsScalarTower R O R₁ := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Module.Flat R R₁ := hf
    exact (Module.flat_iff_of_isLocalization O p.primeCompl R₁).mpr this
  have lo : IsLocalHom φ₁ := by
    refine ⟨fun z hz => ?_⟩
    have : u' (φ' z) ≠ 0 := by
      have h := RingHom.congr_fun e3 z
      simp only [RingHom.comp_apply] at h
      rw [← h]; exact (hz.map u₁).ne_zero
    apply isUnit_of_map_unit φ'
    by_contra hn
    exact this (by rw [← RingHom.mem_ker, hk]; exact hn)
  obtain ⟨E, _, _, _, a, b, v, fa, fb, hab, hv, hva, hvb, hma, -⟩ :=
    GlobalTheory.T.exists_complete_regular_local_meet_of_flat_maps O R₁ R' Ω φ₁ φ' u₁ u' fl1 lo hc he hu k1 hk e3
  refine ⟨E, _, inferInstance, inferInstance, a.comp (algebraMap R₀ R₁), b, v, fl0.comp fa, fb, ?_, hv, ?_, hvb, ?_⟩
  · rw [RingHom.comp_assoc, ← e1, ← RingHom.comp_assoc, hab]; rfl
  · rw [← RingHom.comp_assoc, hva, e2]
  · rw [← Ideal.map_map, hm, hma]

theorem gen_part {X S : Scheme.{0}} {j : X ⟶ S} {A : Over X} [GrpObj A] {x : S} (C : Chart j A x)
    {E : Type} [CommRing E] [IsDomain E] (a : C.R →+* E) (ha : a.Flat) :
    ∃ (y : Sp (FractionRing E) ⟶ X)
      (l : ((Over.pullback (jK E)).obj ((Over.pullback (spMap a)).obj C.G)).left ⟶ pullback C.G.hom (jK C.R)),
      y ≫ j = jK E ≫ spMap a ≫ C.ξ ∧
      l ≫ pullback.fst _ _ = pullback.fst ((Over.pullback (spMap a)).obj C.G).hom (jK E) ≫ pullback.fst C.G.hom (spMap a) ∧
      IsGrpPullback ((Over.pullback (jK E)).obj ((Over.pullback (spMap a)).obj C.G)) A y (l ≫ C.α) := by
  have hi : Function.Injective a := by
    letI : Algebra C.R E := a.toAlgebra
    haveI : Module.Flat C.R E := ha
    exact FaithfulSMul.algebraMap_injective C.R E
  have hi' : Function.Injective ((algebraMap E (FractionRing E)).comp a) :=
    (IsFractionRing.injective E (FractionRing E)).comp hi
  let aK : FractionRing C.R →+* FractionRing E := IsFractionRing.lift hi'
  have e : jK E ≫ spMap a = spMap aK ≫ jK C.R := by
    rw [spc, spc]
    congr 1
    ext z
    simp [aK]
  have p := ((isGrpPullback_pullback ((Over.pullback (spMap a)).obj C.G) (jK E)).comp
    (isGrpPullback_pullback C.G (spMap a))).congr e rfl
  have q := isGrpPullback_pullback C.G (jK C.R)
  have w := p.1.w
  rw [← Category.assoc] at w
  refine ⟨spMap aK ≫ C.y, q.1.lift _ _ w, ?_, q.1.lift_fst _ _ w, ?_⟩
  · rw [Category.assoc, C.hy, ← Category.assoc, ← e, Category.assoc]
  · exact (IsGrpPullback.cancel q (p.congr rfl (q.1.lift_fst _ _ w).symm) (q.1.lift_snd _ _ w)).comp C.gen

theorem iso_extend {E : Type} [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E]
    (G H : Over (Sp E)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (e : (Over.pullback (jK E)).obj G ≅ (Over.pullback (jK E)).obj H) [IsMonHom e.hom] :
    ∃ F : G ≅ H, IsMonHom F.hom ∧ (Over.pullback (jK E)).map F.hom = e.hom := by
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := semiAbelian_hom_extend_generic E G H hG hH e.hom inferInstance
  obtain ⟨F', ⟨hF', eF'⟩, -⟩ := semiAbelian_hom_extend_generic E H G hH hG e.inv inferInstance
  refine ⟨⟨F, F', ?_, ?_⟩, hF, eF⟩
  · exact (semiAbelian_hom_extend_generic E G G hG hG (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, eF, eF', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (semiAbelian_hom_extend_generic E H H hH hH (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, eF, eF', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

theorem ring_setup (σ : Setup) (x x' : Sp σ.R) (Ω : Type) [Field Ω] (u : (σ.C x).R →+* Ω) (u' : (σ.C x').R →+* Ω)
    (hk : RingHom.ker u' = maximalIdeal _) (huu : u.comp (σ.ρ x) = u'.comp (σ.ρ x')) :
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : (σ.C x).R →+* E)
      (b : (σ.C x').R →+* E) (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp (σ.ρ x) = b.comp (σ.ρ x') ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (RingHom.ker u).map a = maximalIdeal E := by
  let z : Sp σ.R := (σ.C x').ξ (closedPoint (σ.C x').R)
  haveI : z.asIdeal.IsPrime := z.isPrime
  letI : Algebra σ.R ((Sp σ.R).presheaf.stalk z) := (StructureSheaf.toStalk σ.R z).hom.toAlgebra
  haveI : IsLocalization.AtPrime ((Sp σ.R).presheaf.stalk z) z.asIdeal := StructureSheaf.IsLocalization.to_stalk σ.R z
  have e : (Scheme.stalkClosedPointTo (σ.C x').ξ).hom.comp (algebraMap σ.R ((Sp σ.R).presheaf.stalk z)) = σ.ρ x' := by
    apply spinj
    rw [← spc, ← σ.hρ x']
    have h := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (σ.C x').ξ
    rw [Spec.fromSpecStalk_eq'] at h
    exact h
  have := ring_part σ.R (σ.C x).R (σ.C x').R ((Sp σ.R).presheaf.stalk z) Ω z.asIdeal (σ.ρ x) (σ.flat x)
    (Scheme.stalkClosedPointTo (σ.C x').ξ).hom u u' (σ.C x').complete (σ.C x').etc (σ.C x').unr hk (by rw [e, huu])
  rwa [e] at this

theorem ff_eq (σ : Setup) (x : Sp σ.R) {K : Type} [Field K] (θ : (σ.C x).G.left.functionField →+* K)
    (t : Sp K ⟶ pullback (σ.C x).G.hom (jK (σ.C x).R)) (ht : t ≫ pullback.fst _ _ = spMap θ ≫ gp (σ.C x).G.left) :
    t ≫ (σ.C x).α = spMap (θ.comp (σ.θ x)) ≫ gp σ.A.left := by
  obtain ⟨l, h₁, h₂⟩ := σ.hθ x
  rw [σ.compat x _ t (spMap θ ≫ l) (by rw [ht, Category.assoc, h₁]), Category.assoc, h₂, ← Category.assoc, spc]

end GlobalTheory.Desc.CommonChart

namespace GlobalTheory.Desc
open CommonChart

theorem setup_common : ∀ σ : Setup, σ.Common := by
  intro σ x x' Ω _ u u' hk huu
  obtain ⟨E, _, _, _, a, b, v, fa, fb, hab, hv, hva, hvb, hma⟩ := ring_setup σ x x' Ω u u' hk huu
  haveI : IsIntegrallyClosed E := (isDomain_and_isIntegrallyClosed_of_isRegularLocalRing E).2
  obtain ⟨ya, la, hya, hla, pa⟩ := gen_part (σ.C x) a fa
  obtain ⟨yb, lb, hyb, hlb, pb⟩ := gen_part (σ.C x') b fb
  have hy : yb = ya := by
    rw [← cancel_mono (awayMap σ.f), hya, hyb, σ.hρ, σ.hρ, spc _ a, spc _ b, hab]
  subst hy
  obtain ⟨e, he, hee⟩ := grpPullback_iso pa pb
  have sa := IsSemiAbelian.pullback (spMap a) _ (σ.C x).semi
  have sb := IsSemiAbelian.pullback (spMap b) _ (σ.C x').semi
  obtain ⟨F, hF, eF⟩ := iso_extend _ _ sa sb e
  haveI := sa
  haveI : IsIntegral ((Over.pullback (spMap a)).obj (σ.C x).G).left := isIntegral_left_of_isSemiAbelian _
  have ga := isGrpPullback_pullback (σ.C x).G (spMap a)
  have gb := ((isGrpPullback_of_iso F).comp (isGrpPullback_pullback (σ.C x').G (spMap b))).congr
    (Category.id_comp _) rfl
  haveI : Flat (spMap a) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]; exact fa
  haveI : Flat (spMap b) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]; exact fb
  haveI : Flat (pullback.fst (σ.C x).G.hom (spMap a)) := inferInstance
  haveI : Flat (F.hom.left ≫ pullback.fst (σ.C x').G.hom (spMap b)) :=
    MorphismProperty.of_isPullback (P := @Flat) gb.1.flip inferInstance
  obtain ⟨θa, ha⟩ := @exists_ff _ ((Over.pullback (spMap a)).obj (σ.C x).G).left _ _
    (pullback.fst (σ.C x).G.hom (spMap a)) inferInstance
  obtain ⟨θb, hb⟩ := exists_ff (F.hom.left ≫ pullback.fst (σ.C x').G.hom (spMap b))
  refine ⟨E, _, inferInstance, inferInstance, a, b, v, (Over.pullback (spMap a)).obj (σ.C x).G, inferInstance,
    inferInstance, _, _, θa, θb, fa, fb, hab, hv, hva, hvb, hma, sa, ga, gb,
    ⟨_, Category.comp_id _, ha⟩, ⟨_, Category.comp_id _, hb⟩, ?_⟩
  haveI := sa.smooth
  obtain ⟨t, ht⟩ := gp_factor ((Over.pullback (spMap a)).obj (σ.C x).G).hom
  let m := pullback.lift _ _ ht.symm
  have hm : m ≫ pullback.fst _ _ = gp _ := pullback.lift_fst _ _ _
  have e₁ := ff_eq σ x θa (m ≫ la) (by rw [Category.assoc, hla, ← Category.assoc, hm, ha])
  have hE : e.hom.left ≫ pullback.fst ((Over.pullback (spMap b)).obj (σ.C x').G).hom (jK E) =
      pullback.fst ((Over.pullback (spMap a)).obj (σ.C x).G).hom (jK E) ≫ F.hom.left := by
    rw [← eF]; exact pullback.lift_fst _ _ _
  have e₂ := ff_eq σ x' θb (m ≫ e.hom.left ≫ lb) (by
    rw [Category.assoc, Category.assoc, hlb, reassoc_of% hE, ← Category.assoc, hm, hb])
  haveI : Mono (gp σ.A.left) := by unfold gp; infer_instance
  apply spinj
  rw [← cancel_mono (gp σ.A.left), ← e₁, ← e₂, Category.assoc, Category.assoc, Category.assoc, hee]

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem abelianScheme_constLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (s : R₀ →+* R), π.comp s = RingHom.id R₀ →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left) (_ : IsGrpPullback A₀ A (spMap π) i),
        IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom := by
  intro R R₀ _ _ π s hs A₀ _ g hA hg
  have hAs := isGrpPullback_pullback A₀ (spMap s)
  have hid : spMap π ≫ spMap s = 𝟙 (Sp R₀) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
    exact Spec.map_id _
  have hBA := isGrpPullback_pullback ((Over.pullback (spMap s)).obj A₀) (spMap π)
  have hB0 := (hBA.comp hAs).congr hid rfl
  obtain ⟨e, he, -⟩ := grpPullback_iso hB0 (GlobalTheory.CrysConn.isGrpPullback_refl A₀)
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have h0B := isGrpPullback_of_iso e.symm
  refine ⟨(Over.pullback (spMap s)).obj A₀, inferInstance, _, (h0B.comp hBA).congr (Category.id_comp _) rfl,
    PolPull.isAbelianScheme_of_isGrpPullback hA hAs, ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePresentedBySystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_isCompl_ker_of_projective {R : Type} {M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ∃ C : Submodule R M, IsCompl (LinearMap.ker f) C := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfg : ∀ y, f (g y) = y := fun y ↦ LinearMap.congr_fun hg y
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have : y = 0 := (hfg y).symm.trans hx
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have e : x = (x - g (f x)) + g (f x) := by abel
    rw [e]
    refine Submodule.add_mem_sup ?_ (LinearMap.mem_range_self g _)
    rw [LinearMap.mem_ker, map_sub, hfg, sub_self]

theorem mem_smul_top_of_tmul_eq_zero {R R₀ M : Type} [CommRing R] [CommRing R₀] [AddCommGroup M] [Module R M]
    (π : R →+* R₀) (hπ : Function.Surjective π) {I : Ideal R} (hk : RingHom.ker π = I) (x : M)
    (h : letI := π.toAlgebra; (1 : R₀) ⊗ₜ[R] x = 0) : x ∈ I • (⊤ : Submodule R M) := by
  letI := π.toAlgebra
  subst hk
  let f : (R ⧸ RingHom.ker π) ≃ₐ[R] R₀ :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R R₀) hπ
  let E : R₀ ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker π) • (⊤ : Submodule R M) :=
    (TensorProduct.congr f.toLinearEquiv.symm (LinearEquiv.refl R M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π))
  have h1 : E ((1 : R₀) ⊗ₜ[R] x) = Submodule.Quotient.mk x := by
    have : f.symm (1 : R₀) = Ideal.Quotient.mk _ 1 := by rw [map_one, map_one]
    change TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π) (f.symm 1 ⊗ₜ[R] x) = _
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [h, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
  exact h1

theorem full_and_isCompl : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ S : Sys I π A₀.hom, S.Presents A'.hom i' → S.Full hI ∧ ∃ N, IsCompl (S.K hI) N := by
  intro H HD R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg S hS
  have hpb : IsPullback i' A₀.hom A'.hom (spMap π) := h'.1
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.hodge_cohomology_iso_presented_crystal R R₀ I hI π hπ hk A₀.left A₀.hom S A'.left A'.hom i' hpb hS
  have hsm : Smooth A'.hom := hA.smooth
  haveI : IsProper A'.hom := hA.proper
  have hsep : IsSeparated A'.hom := inferInstance
  have hqc : QuasiCompact A'.hom := inferInstance
  have hw : i' ≫ A'.hom = (A₀.hom ≫ spMap π) ≫ spMap (RingHom.id R) := by
    rw [Cris.spMap_id, Category.comp_id]; exact hpb.w
  let m : IsMor (dp0 R) A'.hom (divided₂ hI) (A₀.hom ≫ spMap π) (RingHom.id R) i' := IsMor.of_dividedPowersZeroIdeal _ hw
  have hm := (H.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk A'.left A₀.left A'.hom A₀.hom i'
    hsm hsep hqc hpb m).1
  have hc := H.bijective_cechDeRhamComparison_degreeOne A'.hom hsm hsep hqc
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hto⟩, hbc⟩ := HD R A' g hA hg
  have key : ∀ c, S.r hI (m.pull1 c) = e (toHO1 A'.hom (cmp1 A'.hom c)) := fun c ↦ (he1 m c).symm
  have hr : Function.Surjective (S.r hI) := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨w, rfl⟩ := hto x
    obtain ⟨c, rfl⟩ := hc.2 w
    exact ⟨m.pull1 c, key c⟩
  haveI : Module.Projective R (GlobalTheory.CatCoh.H1 S.F) := Module.Projective.of_equiv e
  refine ⟨?_, exists_isCompl_ker_of_projective (S.r hI) hr⟩
  intro z hz
  have hz0 : S.redO.pullbackOneCocycle z = 0 := by
    refine Subtype.ext (funext fun U ↦ funext fun V ↦ funext fun a ↦ ?_)
    exact (S.ker V _).2 (hz U V a)
  have h0 : S.redO.pull1 (H1.mk _ z) = 0 := by
    rw [CoefMap.pullCohomologyOne_class, hz0, map_zero]
  set x := e.symm (H1.mk _ z) with hxdef
  have hx0 : IsPullO hpb.w x 0 := by
    have := he2 x
    rwa [hxdef, LinearEquiv.apply_symm_apply, h0] at this
  letI := π.toAlgebra
  obtain ⟨-, -, e', he'⟩ := hbc R₀ A₀.left A₀.hom i' hpb
  have h1 : e' ((1 : R₀) ⊗ₜ[R] x) = 0 := by
    have a := he' x
    unfold IsPullO at a hx0
    exact (pairRes_injective i' A₀.hom).1 (a.symm.trans (hx0.trans (map_zero _).symm))
  have hxI : x ∈ I • (⊤ : Submodule R (HO1 A'.hom)) :=
    mem_smul_top_of_tmul_eq_zero π hπ hk x ((LinearEquiv.map_eq_zero_iff e').1 h1)
  have hzI : H1.mk _ z ∈ I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    have : H1.mk _ z = e x := by rw [hxdef, LinearEquiv.apply_symm_apply]
    rw [this]
    have hm' : e.toLinearMap x ∈ Submodule.map e.toLinearMap (I • ⊤) := Submodule.mem_map_of_mem hxI
    rw [Submodule.map_smul''] at hm'
    exact Submodule.smul_mono le_rfl le_top hm'
  have hsurjI : Submodule.map (S.r hI) (I • ⊤) = I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hr]
  rw [← hsurjI] at hzI
  obtain ⟨c, hc, hcz⟩ := hzI
  exact ⟨c, hc, hcz⟩

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePrimeToCharTorsionRationalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_primeToChar_torsion_rational : ∀ (K₀ K : Type) [Field K₀] [IsAlgClosed K₀] [Field K] (e : K₀ →+* K) (Y : Over (Sp K₀)) [GrpObj Y],
  IsAbelianScheme Y → ∀ n : ℕ, IsUnit (n : K₀) → ∀ y : Over.mk (spMap e) ⟶ Y, y ^ n = 1 →
  ∃ y₀ : Sp K₀ ⟶ Y.left, y.left = spMap e ≫ y₀ := by
  first | exact @GlobalTheory.TorsRat.torsion_point_rational | exact GlobalTheory.TorsRat.torsion_point_rational | (intros; apply GlobalTheory.TorsRat.torsion_point_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilon
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem isLocalRing_dualNumber_field (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

theorem pic_sp_local_eq_zero (R : Type) [CommRing R] [IsLocalRing R] (c : Pic (Sp R)) : c = 0 := by
  obtain ⟨V, hV, h⟩ := exists_pull_eq_zero c (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hV
  have e := pull_eq_zero_of_mem V (𝟙 _) (fun z ↦ by rw [hV']; trivial) h
  rwa [pull_id] at e

theorem ringHom_dualNumber_factor {k K : Type} [CommRing k] [Field K] (φ : DualNumber k →+* K) :
    φ = (φ.comp (dnInl k)).comp (dnFst k) := by
  have hε : φ DualNumber.eps = 0 := by
    have e : φ DualNumber.eps * φ DualNumber.eps = 0 := by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 e
  refine RingHom.ext fun x ↦ ?_
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul, hε, mul_zero, add_zero]
  rfl

theorem fam_of_triv_mod_eps : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k]
    (s : Sp (DualNumber k) ⟶ S) (D : LB (A ⊗ Over.mk s).left) (hD : D.IsLB),
    GlobalTheory.CechPic.pull (A ◁ ptMap s (dnFst k)).left (cls D hD) = 0 → Fam A D := by
  intro S A _ hA k _ s D hD h0
  haveI := isLocalRing_dualNumber_field k
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  haveI : IsNoetherianRing (DualNumber k) := IsNoetherianRing.of_finite k (DualNumber k)
  haveI : IsLocallyNoetherian (Over.mk s).left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))
  refine ⟨hD, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A (Over.mk s) hA D hD ?_ ?_⟩
  · rw [triv_ev_iff hD]
    exact pic_sp_local_eq_zero _ _
  · intro K _ _ s' t
    obtain ⟨φ, hφ⟩ := Spec.map_surjective t.left
    set ψ : k →+* K := φ.hom.comp (dnInl k)
    have ht : t.left = spMap ψ ≫ spMap (dnFst k) := by
      rw [← hφ, ← Spec.map_comp]
      congr 1
      ext1
      exact ringHom_dualNumber_factor φ.hom
    have hN : (ev D (fst A (Over.mk s')) (snd A (Over.mk s') ≫ t)).IsLB := pull_isLB hD _
    refine (isAdditive_iff hN).2 fun Y a a' y ↦ ?_
    have key : ∀ b : Y ⟶ A, evc hN b y = 0 := fun b ↦ by
      rw [evc_ev hD, lift_fst, lift_snd_assoc]
      let u : Y ⟶ Over.mk (spMap (dnFst k) ≫ s) := Over.homMk (y.left ≫ spMap ψ) (by
        have e1 : y.left ≫ s' = Y.hom := by simpa using Over.w y
        have e2 : t.left ≫ s = s' := by simpa using Over.w t
        simp only [Over.mk_hom]
        rw [Category.assoc, ← Category.assoc (spMap ψ), ← ht, e2, e1])
      have hu : y ≫ t = u ≫ ptMap s (dnFst k) := by
        refine Over.OverMorphism.ext ?_
        simp only [Over.comp_left, ptMap_left, ht]
        rfl
      rw [hu, evc, ← lift_whiskerLeft, Over.comp_left, pull_comp, h0, map_zero]
    rw [key, key, key, add_zero]

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleEqMumfordLambdaOfAmpleAlgCloseStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveLineBundle_eq_mumfordLambda_of_ample_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ N : LB (A ⊗ 𝟙_ (Over (Sp K))).left, Fam A N → ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, Same A N (abelian₂ A L) (𝟙 _) a := by
  first | exact @GlobalTheory.AddLineField.additive_eq_lam_of_ample | exact GlobalTheory.AddLineField.additive_eq_lam_of_ample | (intros; apply GlobalTheory.AddLineField.additive_eq_lam_of_ample <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingTupleSmoothConeCmFieldStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportingTuple_smoothCone_cmField : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (φ : InvFun (NumberField.RingOfIntegers E)) (X : Type) [AddCommGroup X] [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X] [Module.Projective (NumberField.RingOfIntegers E) X], IsPolFanOn H.bar φ X → ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports H.bar φ d γ a := by
  first | exact @GlobalTheory.Poinc.exists_supports_cm | exact GlobalTheory.Poinc.exists_supports_cm | (intros; apply GlobalTheory.Poinc.exists_supports_cm <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesSiegelLevelStructure
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSemiAbelianSquareSameProjections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem eq_of_specializes_of_fst_eq_of_snd_eq :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ p q : (G ⊗ G).left, (fst G G).left p = x → (fst G G).left q = x →
        (snd G G).left p = (snd G G).left q → p ⤳ q → p = q := by
  intro R _ _ G _ hG x hx hxc p q hp hq hpq hs
  haveI : Smooth G.hom := hG.smooth
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) := GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed R G inferInstance x hx hxc

  let j : pullback (pullback.fst G.hom G.hom) (G.left.fromSpecResidueField x) ⟶ pullback G.hom G.hom :=
    pullback.fst _ _
  let e := pullbackSymmetry (pullback.fst G.hom G.hom) (G.left.fromSpecResidueField x) ≪≫
    pullbackRightPullbackFstIso G.hom G.hom (G.left.fromSpecResidueField x)
  have hk : j ≫ pullback.snd G.hom G.hom = e.hom ≫ pullback.snd _ _ := by
    simp [e, j, pullbackRightPullbackFstIso_hom_snd]
  have hkf : IsFinite (j ≫ pullback.snd G.hom G.hom) := by rw [hk]; infer_instance
  have hr : Set.range j = (pullback.fst G.hom G.hom) ⁻¹' {x} := by
    simp only [j, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  obtain ⟨p', rfl⟩ : p ∈ Set.range j := by rw [hr]; exact hp
  obtain ⟨q', rfl⟩ : q ∈ Set.range j := by rw [hr]; exact hq
  have hs' : p' ⤳ q' := (j.isEmbedding.toIsInducing.specializes_iff).mp hs
  have := (GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite _ _ _ hkf
    ((j ≫ pullback.snd G.hom G.hom) q')).2 p' q' (by simpa using hpq) rfl hs'
  rw [this]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferBySca
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU

noncomputable section

namespace GlobalTheory.Mum

theorem eqv_eq_smul : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ lab E E', Eqv D.toPre A F N lab E → Eqv D.toPre A F N lab E' → ∃ c : Fˣ, ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ _ I D A F _ _ _ N hN lab E E' hE hE'
  have hN1 : 1 ≤ N := hN.pos
  have hNF : (N : F) ≠ 0 := by
    have h1 : (N : R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : (N : FractionRing R) ≠ 0 := fun h =>
      h1 (IsFractionRing.injective R (FractionRing R) (by rw [map_natCast, map_zero]; exact h))
    intro h
    apply h2
    apply (algebraMap (FractionRing R) F).injective
    rw [map_zero, map_natCast]
    exact_mod_cast h
  let p : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing R)) := jFK (R := R) F
  let mkE : ∀ G : Fam D.toPre F N → SecK A.L (snd (TFK (R := R) F) A.A).left N, Eqv D.toPre A F N lab G →
      (Fam D.toPre F N →ₗ[F] EA A p N) := fun G hG =>
    { toFun := fun s => SecMod.mk _ (G s)
      map_add' := fun s t => SecMod.ext_coord fun j => hG.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => SecMod.ext_coord fun j =>
        hG.smul c s (c • s) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff c s _).2 rfl) j }
  have hbij : ∀ G hG, Function.Bijective (mkE G hG) := fun G hG => hG.bij
  let e := LinearEquiv.ofBijective (mkE E hE) (hbij E hE)
  let T : EA A p N →ₗ[F] EA A p N := (mkE E' hE').comp e.symm.toLinearMap
  have hTe : ∀ s, T (mkE E hE s) = mkE E' hE' s := fun s => by
    show mkE E' hE' (e.symm (e s)) = _
    rw [e.symm_apply_apply]
  obtain ⟨ρ, hact, -, -, -⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns _ A (N : ℤ) (TFK (R := R) F)
  have huniq : ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (a : EA A p N) (b b' : SecK A.L (snd (TFK (R := R) F) A.A).left N),
      IsActOf A.A A.L (N : ℤ) θ a.sec b → IsActOf A.A A.L (N : ℤ) θ a.sec b' → b = b' := fun θ a b b' h h' => by
    have := ((hact θ _ _).1 h).symm.trans ((hact θ _ _).1 h')
    exact SecMod.ext_coord (p := (fst (Over.mk p) A.A).left) (s := SecMod.mk _ b) (t := SecMod.mk _ b')
      fun j => congrFun (congrArg Subtype.val this) j
  have hT : ∀ x : Over.mk p ⟶ A.A, x ^ N = 1 → ∃ θ : ThetaGrp A.A A.L (N : ℤ) (Over.mk p), θ.pt = x ∧
      ∀ v v' : EA A p N, IsActOf A.A A.L (N : ℤ) θ v.sec v'.sec →
        IsActOf A.A A.L (N : ℤ) θ (T v).sec (T v').sec := by
    intro x hx
    obtain ⟨p₀, hp₀⟩ := (hE.onto x).1 hx
    obtain ⟨w, hw⟩ := hE.frame p₀
    obtain ⟨θ, hθ⟩ := hE.lift p₀
    obtain ⟨Φ, hΦ⟩ := ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of GlobalTheory.allSixLaws.1 R I D F N hN1 p₀ w hw.1
    refine ⟨θ, hθ.pt_eq.trans hp₀, fun v v' hvv => ?_⟩
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have hPhi := (hΦ s (Φ s)).2 rfl
    have h₁ := hE.act p₀ w θ s (Φ s) hw hθ hPhi
    have h₂ := hE'.act p₀ w θ s (Φ s) hw hθ hPhi
    have e₁ : v' = mkE E hE (Φ s) := huniq θ _ _ _ hvv h₁
    rw [e₁, hTe, hTe]
    exact h₂
  obtain ⟨c, hc⟩ := GlobalTheory.ThetaCommutant.eq_smul_of_commute A F p N hNF T hT
  have hpos : 0 < Module.finrank F (EA A p N) := by
    rw [GlobalTheory.ThetaCommutant.finrank_eq A F p N hNF]; positivity
  haveI : Nontrivial (EA A p N) := Module.nontrivial_of_finrank_pos hpos
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : EA A p N)
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have h0 : mkE E' hE' s = mkE E' hE' 0 := by rw [← hTe, hc, zero_smul, map_zero]
    have := (hbij E' hE').1 h0
    subst this
    exact hv (map_zero _)
  refine ⟨Units.mk0 c hc0, fun s j => ?_⟩
  have h := congrArg (fun v : EA A p N => v.sec.f j) ((hTe s).symm.trans (hc _))
  exact h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNearPointOfEtaleOnFibreSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem etale_basicOpen_comp_SpecMap_iff (S R : CommRingCat.{0}) (θ : S ⟶ R) (f : R) :
    Etale ((show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := by
  have e : (show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ =
      (basicOpenIsoSpecAway f).hom ≫ Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
    rw [Spec.map_comp, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [e]
  have key : Etale (Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := HasRingHomProperty.Spec_iff (P := @Etale)
  rw [← key]
  constructor
  · intro H
    have e2 : Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) =
        (basicOpenIsoSpecAway f).inv ≫ ((basicOpenIsoSpecAway f).hom ≫
          Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
      (Iso.inv_hom_id_assoc _ _).symm
    rw [e2]; infer_instance
  · intro H; infer_instance

theorem etale_image_comp_of_etale (X Z X' Z' : Scheme.{0}) (h : X ⟶ Z) (h' : X' ⟶ Z') (iX : X' ⟶ X) (iZ : Z' ⟶ Z)
    [IsOpenImmersion iX] [IsOpenImmersion iZ] (sh : iX ≫ h = h' ≫ iZ) (U : X'.Opens) :
    Etale (U.ι ≫ h') → Etale ((iX ''ᵁ U).ι ≫ h) := by
  intro hE
  have e : (iX ''ᵁ U).ι ≫ h = (iX.isoImage U).inv ≫ (U.ι ≫ h') ≫ iZ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc, sh, Category.assoc]
  rw [e]
  infer_instance

end GlobalTheory.Mum

theorem GlobalTheory.Mum.etale_near_of_etale_fibre : ∀ (T X Z : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p), Smooth p → Smooth q → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T) (W : (pullback p x).Opens) (w : ↥(pullback p x)), w ∈ W → Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ V : X.Opens, pullback.fst p x w ∈ V ∧ Etale (V.ι ≫ h) := by
  intro T X Z p q h hh hp hq Ω _ x W w hw hE
  subst hh
  obtain ⟨UA, hUA, hzA, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens)
    (show (h ≫ q) (pullback.fst (h ≫ q) x w) ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨UC, hUC, hzC, hCA⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens)
    (show h (pullback.fst (h ≫ q) x w) ∈ q ⁻¹ᵁ UA by simpa using hzA)
  obtain ⟨UB, hUB, hzB, hBC⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show pullback.fst (h ≫ q) x w ∈ h ⁻¹ᵁ UC from hzC)
  have hUA' : IsAffineOpen UA := hUA
  have hUB' : IsAffineOpen UB := hUB
  have hUC' : IsAffineOpen UC := hUC
  haveI := hUA'.isOpenImmersion_fromSpec
  haveI := hUB'.isOpenImmersion_fromSpec
  haveI := hUC'.isOpenImmersion_fromSpec
  have hxr : Set.range x ⊆ Set.range hUA'.fromSpec := by
    rw [hUA'.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    obtain rfl : y = pullback.snd (h ≫ q) x w := Subsingleton.elim _ _
    have := congrArg (fun g => g w) (pullback.condition (f := h ≫ q) (g := x))
    simp only [Scheme.Hom.comp_apply] at this
    show x (pullback.snd (h ≫ q) x w) ∈ UA
    rw [← this]; simpa using hzA
  set φ := q.appLE UA UC hCA
  set ψ := h.appLE UC UB hBC
  let x' := IsOpenImmersion.lift hUA'.fromSpec x hxr
  let ω : Γ(T, UA) ⟶ CommRingCat.of Ω := Spec.preimage x'
  have sx : Spec.map ω ≫ hUA'.fromSpec = x := by
    simp only [ω, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨W', w', hw', hfst, hE'⟩ := GlobalTheory.T.fibre_etale_restrict_open_alt T X Z _ _ _ (Sp Ω) (h ≫ q) q h rfl
    (Spec.map (φ ≫ ψ)) (Spec.map φ) (Spec.map ψ) (by rw [Spec.map_comp])
    hUA'.fromSpec hUB'.fromSpec hUC'.fromSpec (hUA'.SpecMap_appLE_fromSpec q hUC' hCA).symm
    (hUC'.SpecMap_appLE_fromSpec h hUB' hBC).symm x (Spec.map ω) sx W w hw
    (by rw [hUB'.range_fromSpec]; exact hzB) hE
  obtain ⟨Q', hQ', f, hcomap, hf, hEt⟩ := GlobalTheory.T.etale_localisation_of_etale_affine_fibre' _ _ _ φ ψ Ω ω W' w' hw' hE'
  letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra
  letI : IsScalarTower Γ(T, UA) Γ(Z, UC) Γ(X, UB) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hQ'
  haveI hQprime : (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have hbij := GlobalTheory.T.localization_tensor_prime_comap_compat Γ(T, UA) Γ(Z, UC) Γ(X, UB) Ω (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal Q' f hcomap hf hEt
  haveI : Algebra.Smooth Γ(T, UA) Γ(Z, UC) := HasRingHomProperty.appLE @Smooth q hq ⟨UA, hUA'⟩ ⟨UC, hUC'⟩ hCA
  haveI : Algebra.Smooth Γ(T, UA) Γ(X, UB) := by
    have := HasRingHomProperty.appLE @Smooth (h ≫ q) hp ⟨UA, hUA'⟩ ⟨UB, hUB'⟩ (hBC.trans (h.preimage_mono hCA))
    rw [← Scheme.Hom.appLE_comp_appLE h q UA UC UB hCA hBC] at this
    exact this
  obtain ⟨g, hg, hgEt⟩ := GlobalTheory.T.exists_etale_away_of_bijective_kaehler_mapBaseChange Γ(T, UA) Γ(Z, UC) Γ(X, UB) (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal hbij
  have hR : ((algebraMap Γ(X, UB) (Localization.Away g)).comp ψ.hom).Etale := by
    have := RingHom.etale_algebraMap.mpr hgEt
    rwa [IsScalarTower.algebraMap_eq Γ(Z, UC) Γ(X, UB) (Localization.Away g)] at this
  have hV := (etale_basicOpen_comp_SpecMap_iff _ _ ψ g).mpr hR
  refine ⟨hUB'.fromSpec ''ᵁ (PrimeSpectrum.basicOpen g), ?_,
    etale_image_comp_of_etale X Z _ _ h (Spec.map ψ) hUB'.fromSpec hUC'.fromSpec
      (hUC'.SpecMap_appLE_fromSpec h hUB' hBC).symm _ hV⟩
  rw [← hfst]
  exact Set.mem_image_of_mem _ hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroups
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

open GlobalTheory.EndData GlobalTheory.AbLaw in

theorem exists_hom_of_levels {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {I : Ideal R}
    (hC : IsAdicComplete I R) (Y Z : Over (Spec (CommRingCat.of R))) (sY : Smooth Y.hom) (sZ : Smooth Z.hom)
    (pY : IsProjBy Y.hom) (pZ : IsProjBy Z.hom) (s : Y ⟶ Z) (f : ∀ e, (thickObj R I e Y).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom)
    (hc : ∀ e, thickMap R I e Y ≫ f (e + 1) = f e) :
    ∃ g : Y ⟶ Z, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  have w₁ : (fst Y Z).left ≫ Y.hom = (Y ⊗ Z).hom := Over.w _
  have w₂ : (snd Y Z).left ≫ Z.hom = (Y ⊗ Z).hom := Over.w _
  have sm : Smooth (Y ⊗ Z).hom := by
    show Smooth (pullback.fst Y.hom Z.hom ≫ Y.hom)
    infer_instance
  let p : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ (thickObj R I e Y).left := fun e =>
    ((Over.pullback (thick R I e)).map (fst Y Z)).left
  have hp : ∀ e, p e ≫ pullback.fst Y.hom (thick R I e) = pullback.fst (Y ⊗ Z).hom (thick R I e) ≫ (fst Y Z).left :=
    fun e => map_fst e _
  let F : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ pullback Y.hom Z.hom := fun e =>
    pullback.lift (p e ≫ pullback.fst Y.hom (thick R I e)) (p e ≫ f e) (by
      rw [Category.assoc, Category.assoc, hf])
  have F₁ : ∀ e, F e ≫ pullback.fst _ _ = p e ≫ pullback.fst Y.hom (thick R I e) := fun e => pullback.lift_fst _ _ _
  have F₂ : ∀ e, F e ≫ pullback.snd _ _ = p e ≫ f e := fun e => pullback.lift_snd _ _ _
  have tp : ∀ e, thickMap R I e (Y ⊗ Z) ≫ p (e + 1) = p e ≫ thickMap R I e Y := fun e => trans_map e _
  obtain ⟨g, hg⟩ := EndAlg.exists_end_of_thickenings R I hC (Y ⊗ Z) sm (isProjBy_tensor R Y Z pY pZ) F
    (fun e => by
      show F e ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = _
      rw [← Category.assoc, F₁, hp, Category.assoc, w₁])
    (fun e => by
      show (thickMap R I e (Y ⊗ Z) ≫ F (e + 1) : _ ⟶ pullback Y.hom Z.hom) = F e
      apply pullback.hom_ext
      · rw [Category.assoc, F₁, F₁, ← Category.assoc, tp, Category.assoc, trans_fst]
      · rw [Category.assoc, F₂, F₂, ← Category.assoc, tp, Category.assoc, hc])
  refine ⟨lift (𝟙 Y) s ≫ g ≫ snd Y Z, fun e => ?_⟩
  have hj : ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s)).left ≫ p e = 𝟙 _ := by
    show ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s) ≫ (Over.pullback (thick R I e)).map (fst Y Z)).left = _
    rw [← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id]
    rfl
  have k : F e ≫ (snd Y Z).left = p e ≫ f e := F₂ e
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← map_fst, Category.assoc,
    ← Category.assoc (pullback.fst _ _), hg]
  erw [k]
  rw [← Category.assoc]
  erw [hj]
  exact Category.id_comp _

open GlobalTheory.EndTorus in

theorem exists_abelian_level {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    {D₁ D₂ : DegPre R} {e : ℕ} {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [IsCommMonObj G₁]
    [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ b : thickObj R I e D₁.P.A ⟶ thickObj R I e D₂.P.A, IsMonHom b ∧ g₁.q ≫ b = a ≫ g₂.q := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := g₁.q_hom
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₁.q_flat
  have := g₁.q_surj
  have := g₁.q_affine
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  exact FlatQuotient.exists_desc g₁.q g₁.i (a ≫ g₂.q) g₁.isKernel h1

open GlobalTheory.EndData in

theorem exists_abelian_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ b : D₁.toPre.P.A ⟶ D₂.toPre.P.A, IsMonHom b ∧ Over₀ U₁ U₂ a b := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have hN := hR.1
  have hC := hR.2.2.2
  choose b hb hq using fun e => exists_abelian_level hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  have hql : ∀ e, (U₁.gt e).q.left ≫ (b e).left = ((Over.pullback (thick R I e)).map a).left ≫ (U₂.gt e).q.left :=
    fun e => congrArg (·.left) (hq e)
  obtain ⟨aB, haB⟩ := exists_hom_of_levels hC D₁.toPre.P.A D₂.toPre.P.A D₁.toPre.P.isAb.smooth
    D₂.toPre.P.isAb.smooth (AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _))
    (AbProj.isProjBy_of_isPullback D₂.toPre.P (IsPullback.id_horiz _)) 1
    (fun e => (b e).left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
    (fun e => by
      have w : (b e).left ≫ pullback.snd D₂.toPre.P.A.hom (thick R I e) = pullback.snd _ _ := Over.w (b e)
      rw [Category.assoc, pullback.condition, ← Category.assoc, w, pullback.condition])
    (fun e => by
      have := (U₁.gt e).q_flat
      have := (U₁.gt e).q_surj
      have : Epi (U₁.gt e).q.left := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (U₁.gt e).q.left, ← Category.assoc, ← UnifCompare.trans_comp_q, Category.assoc,
        ← Category.assoc (U₁.gt (e + 1)).q.left, hql, ← Category.assoc (U₁.gt e).q.left, hql, ← Category.assoc,
        ← Category.assoc, trans_map, Category.assoc _ (thickMap R I e G₂), UnifCompare.trans_comp_q,
        Category.assoc, Category.assoc, trans_fst, Category.assoc])
  have hm : ∀ e, (Over.pullback (thick R I e)).map aB = b e := fun e =>
    Over.OverMorphism.ext (pullback.hom_ext ((map_fst e aB).trans (haB e)) ((Over.w _).trans (Over.w (b e)).symm))
  refine ⟨aB, AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D₂.toPre.P.isAb
    D₁.toPre.P.isAb aB fun e => ?_, fun e => ?_⟩
  · rw [hm]; exact hb e
  · rw [hm]; exact (hq e).symm

end GlobalTheory.Mum.Two
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitaryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_action_pullback_universalUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (W : Scheme.{0}) (w : W ⟶ Xo.XF c) (G₀ : Over W) [GrpObj G₀] (β₀ : G₀.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) β₀ → ∃ f₀ : 𝓞 E → (G₀ ⟶ G₀), (∀ a, IsMonHom (f₀ a) ∧ (f₀ a).left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ W) (tT : SAB H T) (mm : SABMap tT Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _)), ∃ γ : tT.G.left ⟶ G₀.left, IsGrpPullback tT.G G₀ x γ ∧ γ ≫ β₀ = mm.φ ∧ LBIso tT.PP.L ((Xo.univ.t.PP.L.pull β₀).pull γ) ∧ ∀ a, (tT.act.act a).left ≫ γ = γ ≫ (f₀ a).left := by
  first | exact @GlobalTheory.PullAction.exists_action_pull | exact GlobalTheory.PullAction.exists_action_pull | (intros; apply GlobalTheory.PullAction.exists_action_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartThetaSystemUnitaryModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.exists_tie_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (R : Subalgebra X.o₁ X.Ω₁) (P' : PolAV (Sp R)) (u' : Sp (ratHull R) ⟶ Xo.XF cf), spMap (ratHull R).val.toRingHom ≫ u' = X.uΩ → UOver Xo cf P' (toRat R) u' → ∃ (G : Over (Sp (ratHull R))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (m : wi.G.left ⟶ G.left) (P₀ : PolAV (Sp X.Ω₁)) (e : P₀.A.left ⟶ wi.G.left), IsGrpPullback G P'.A (spMap (toRat R)) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ IsGrpPullback wi.G G (spMap (ratHull R).val.toRingHom) m ∧ m ≫ β = wi.β ∧ IsGrpPullback P₀.A X.ρ.P.A (spMap X.S.R.val.toRingHom) (e ≫ wi.α) ∧ IsGrpPullback P₀.A P'.A (spMap R.val.toRingHom) (e ≫ m ≫ α) ∧ LBIso P₀.L (X.ρ.P.L.pull (e ≫ wi.α)) ∧ LBIso P₀.L (P'.L.pull (e ≫ m ≫ α)) := by
  intro E _ _ _ H Dw l Xo cf C X wi R P' u' hc h
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have hb : IsGrpPullback wi.G Xo.univ.t.G (spMap (ratHull R).val.toRingHom ≫ u' ≫ pullback.fst _ _) wi.β :=
    wi.hβ.congr (by rw [← hc, Category.assoc]) rfl
  have w₁ : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (ratHull R).val.toRingHom) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact hb.1.w
  have em := hβ.1.lift_fst _ _ w₁
  have hm := hβ.cancel (hb.congr rfl em.symm) (hβ.1.lift_snd _ _ w₁)
  generalize hβ.1.lift _ _ w₁ = m at em hm
  obtain ⟨P₀, φ, hφ, hφL⟩ := exists_pol_baseChange X.ρ.P (spMap X.S.R.val.toRingHom)
  have w₂ : φ ≫ X.ρ.P.A.hom = (P₀.A.hom ≫ 𝟙 _) ≫ spMap X.S.R.val.toRingHom := by
    rw [Category.comp_id]; exact hφ.1.w
  have ee := wi.hα.1.lift_fst _ _ w₂
  have he := wi.hα.cancel (hφ.congr (Category.id_comp _).symm ee.symm) (wi.hα.1.lift_snd _ _ w₂)
  generalize wi.hα.1.lift _ _ w₂ = e at ee he
  subst ee
  have hU := Xo.univ.t.PP.isLB
  refine ⟨G, _, α, β, m, P₀, e, hα, hβ, hL, hm, em, hφ,
    (he.comp (hm.comp hα)).congr ((Category.id_comp _).trans (spMap_val_toRat R)) rfl, hφL, ?_⟩
  have l₁ : LBIso (X.ρ.P.L.pull (e ≫ wi.α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) :=
    GenSpread.lbIso_pull_comp _ rfl rfl wi.hL
  have l₂ : LBIso (P'.L.pull (m ≫ α)) (Xo.univ.t.PP.L.pull (m ≫ β)) := GenSpread.lbIso_pull_comp _ rfl rfl hL
  rw [em] at l₂
  have l₃ : LBIso (P'.L.pull (e ≫ m ≫ α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) := GenSpread.lbIso_pull_comp _ rfl rfl l₂
  exact LBIso.trans P₀.isLB (pull_isLB X.ρ.P.isLB _) (pull_isLB P'.isLB _) hφL
    (LBIso.trans (pull_isLB X.ρ.P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) l₁ l₃.symm)

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.UPoinc.exists_urechart_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (ρ'.pt x).left)) ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
  intro E _ _ _ H Dw _hpq l Xo cf C X wi w hw
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hu₀⟩ := GlobalTheory.UPoinc.ChartAt.exists_affine_chart_ratLift E H Dw l Xo cf C X w hw
  obtain ⟨U₁, h₁, P₁, _hU₁₀, hU₁a, hwU₁, hP₁⟩ := GlobalTheory.UPoinc.LocSpread.exists_uOver_ringOn E H Dw l Xo cf C X U₀ u₀ w hU₀a hwU₀ hw
  have hN : 1 ≤ X.S.N := by have := X.S.N_ge; omega
  obtain ⟨U, h, P', φ, _hUU₁, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.Poinc.exists_univBasis_affineChart X.o₁ X.Ω₁ X.M U₁ w hU₁a hwU₁ P₁ X.S.N hN
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  let u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf :=
    spMap (Subalgebra.inclusion (ratHull_mono (h₁.trans h))).toRingHom ≫ u₀
  have hP' : UOver Xo cf P' (toRat (X.M.ringOn U)) u' := by
    refine (uOver_baseChange_iff hφ hφL (toRat _)).2 ?_
    have := hP₁.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom
    have e : spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫
        spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom ≫ u₀ = u' := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e] at this
    exact this
  have hcomp : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨G, _, α, β, m, P₀, e, hα, hβ, hαβ, hm, hmβ, ha, ha', hL, hL'⟩ :=
    GlobalTheory.UPoinc.exists_tie_of_uOver E H Dw l Xo cf C X wi (X.M.ringOn U) P' u' hcomp hP'
  have hg' : P'.g = X.S.g :=
    (GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ P' P₀ _ _ ha').symm.trans
      ((GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ X.ρ.P P₀ _ _ ha).trans X.ρ.g_eq)
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.Poinc.hypS_of_generic_ringOn X.o₁ X.Ω₁ X.M U hUa hne X.normal X.S.R X.ρ.P P' P₀ _ _ _ ha ha' hL hL' X.ρ.hypS

  obtain ⟨⟨hLw, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI := RatModel.isFractionRing_ringOn hUa hne
  haveI := TorsExtend.isIntegrallyClosed_ringOn X.M ((isNormalScheme_iff_pred _).1 X.normal) hUa hne
  haveI := ArithBase.ded (o := X.o₁) (Ω := X.Ω₁)
  have fg : (X.M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ X.M U hUa hne
  haveI : IsNoetherianRing (X.M.ringOn U) := isNoetherianRing_of_fg fg
  have hn : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (le_trans one_le_two X.S.N_ge)
  have hu : IsUnit ((X.S.r * X.S.N : ℕ) : X.M.ringOn U) := by
    have := X.S.unit.map (algebraMap X.o₁ (X.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', hadd, hbij, h₃, hw0⟩ := TorsExtend.exists_labelled hLw X.S.R.val.toRingHom X.ρ.P P' P₀ _ _ ha ha' hL hL'
    hn hu (M := X.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X.ρ.pt X.ρ.pt_add X.ρ.pt_bij
  have hweil : ∀ x y (c : (X.M.ringOn U)ˣ), (c : (X.M.ringOn U)) = algebraMap X.o₁ (X.M.ringOn U)
      (X.S.ζ ^ (X.S.r * X.S.N * (eStd X.S.g _ x y).val)) →
      WeilIs P'.A P'.L (X.S.r * X.S.N : ℕ) (pt' x) (pt' y) (unitOn c) := fun x y c hc => by
    obtain ⟨c₀, hc₀⟩ := ((X.S.prim.isUnit (by positivity)).pow (X.S.r * X.S.N * (eStd X.S.g _ x y).val)).map
      (algebraMap X.o₁ X.S.R)
    refine h₃ x y c₀ c ?_ (X.ρ.weil x y c₀ hc₀)
    rw [hc₀, hc]
    rfl
  have frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  have hQ : (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P'.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt' x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P'.A.left, IsGrpPullback P₀.A P'.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P'.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt' x).left := by
    refine ⟨⟨G, inferInstance, α, β, hα, hβ, hαβ, m, hm, hmβ, fun x => ?_⟩, _, ha', hL', hw0⟩
    obtain ⟨w0, h₁, h₂⟩ := hw0 x
    exact ⟨w0 ≫ e, by rw [Category.assoc]; exact h₁, by rw [Category.assoc]; exact h₂⟩
  obtain ⟨c₀, hc, hthm, hevm, ρ', ⟨hU', a'', q₂, q₃, q₅⟩, hi₀⟩ := GlobalTheory.ThetaExtend.exists_real_rechart
    GlobalTheory.abelianSchemeLaws_all.1 X.S X.ρ (X.M.ringOn U) fg frac P' P₀ _ _ pt' th b ha ha' hL hL' hg' hyp hadd hbij hweil
    hw0 hth hb
    (fun P pt => (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P.A.left, IsGrpPullback P₀.A P.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left) hQ
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', u', hUa, hwU, ⟨P₀, e ≫ wi.α, a'', ha, q₂, hL, q₃, q₅⟩, hi₀, hU', hcomp⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesSiegelLevelStructureStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_cones_siegel_level_structure : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) → (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) → ∃ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ i, IsCone id φ (γ i)) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → ∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j := by
  first | exact @GlobalTheory.Poinc.Cells.exists_finite_cones | exact GlobalTheory.Poinc.Cells.exists_finite_cones | (intros; apply GlobalTheory.Poinc.Cells.exists_finite_cones <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem stalk_isNoetherian_normal_fractionRing : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z),
    letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra;
    IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧
      IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  intro g n F W Z i X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  have hN := X₁.normal
  refine ⟨GlobalTheory.IsNormalScheme.isDomain_stalk z₁, ?_, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z₁, ?_⟩
  · have : FaithfulSMul (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (X₁.M.stalkHom_injective z₁)
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := X₁.M.O z₁) x
    refine ⟨(X₁.M.stalkEquiv z₁).symm a, (X₁.M.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : X₁.M.O z₁, algebraMap (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ((X₁.M.stalkEquiv z₁).symm c) = c := fun c => by
      change X₁.M.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  · have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
    have := X₁.M.lft
    have : IsLocallyNoetherian (Sp X₁.o₁) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    infer_instance

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopExteriorDualInvertible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvertibleTopExteriorPower

theorem invertible_exteriorPower_top (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ)
    (hn : ∀ p, Module.rankAtStalk (R := R) M p = n) : Module.Invertible R (⋀[R]^n M) := by
  let s : Set R := {a | Module.Free (Localization.Away a) (LocalizedModule.Away a M)}
  have hs : Ideal.span s = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨a, ha, hfree⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M m
      (fun m' _ => by rw [hn, hn])
    exact ha (hsm (Ideal.subset_span hfree))
  have hloc : ∀ r : s, IsLocalizedModule.Away r.1 (exteriorPowerMapOver (Localization.Away r.1) n
      (LocalizedModule.mkLinearMap (Submonoid.powers r.1) M)) := fun r =>
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r.1) (Localization.Away r.1) _).2
      (GlobalTheory.TopForm.isBaseChange_exteriorPower
        (LocalizedModule.isBaseChange (Submonoid.powers r.1) M) n)
  refine GlobalTheory.invertible_of_isLocalizedModule_span s hs (fun r => Localization.Away r.1)
    (fun r => ⋀[Localization.Away r.1]^n (LocalizedModule.Away r.1 M))
    (fun r => exteriorPowerMapOver (Localization.Away r.1) n
      (LocalizedModule.mkLinearMap (Submonoid.powers r.1) M)) fun r => ?_
  have hfree : Module.Free (Localization.Away r.1) (LocalizedModule.Away r.1 M) := r.2
  rcases subsingleton_or_nontrivial (Localization.Away r.1) with hB | hB
  · haveI : Subsingleton (⋀[Localization.Away r.1]^n (LocalizedModule.Away r.1 M)) :=
      Module.subsingleton (Localization.Away r.1) _
    exact Module.Invertible.congr (LinearEquiv.ofSubsingleton (Localization.Away r.1)
      (⋀[Localization.Away r.1]^n (LocalizedModule.Away r.1 M)))
  · obtain ⟨q⟩ : Nonempty (PrimeSpectrum (Localization.Away r.1)) := inferInstance
    have hfr : Module.finrank (Localization.Away r.1) (LocalizedModule.Away r.1 M) = n := by
      have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := Localization.Away r.1)
        (M := LocalizedModule.Away r.1 M)) q
      rw [Module.rankAtStalk_isBaseChange
        (LocalizedModule.isBaseChange (Submonoid.powers r.1) M), hn] at h1
      exact h1.symm
    let b := Module.finBasisOfFinrankEq (Localization.Away r.1) (LocalizedModule.Away r.1 M) hfr
    have hb := GlobalTheory.TopForm.isFreeGen_ιMulti b
    exact Module.Invertible.congr (LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ _) hb)

theorem invertible_alternatingMap_top : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ),
    (∀ p, Module.rankAtStalk (R := R) M p = n) → Module.Invertible R (M [⋀^Fin n]→ₗ[R] R) := by
  intro R _ M _ _ _ _ n hn
  haveI := invertible_exteriorPower_top R M n hn
  exact Module.Invertible.congr
    (exteriorPower.alternatingMapLinearEquiv (R := R) (M := M) (N := R) (n := n)).symm

end GlobalTheory.InvertibleTopExteriorPower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopIsoInvRestrictAppTop
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.EigenDescent
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EigenDescent

theorem topIso_inv_eq_appLE {X : Scheme.{0}} (W : X.Opens) (h : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W) :
    W.topIso.inv = W.ι.appLE W ⊤ h :=
  (Scheme.Opens.topIso_inv W).trans (Eq.trans rfl (Scheme.Opens.ι_appLE W W ⊤ h).symm)

theorem topIso_inv_appTop {X Z : Scheme.{0}} (W : X.Opens) (y : Z ⟶ W.toScheme)
    (h : (⊤ : Z.Opens) ≤ (y ≫ W.ι) ⁻¹ᵁ W) :
    W.topIso.inv ≫ y.appTop = (y ≫ W.ι).appLE W ⊤ h := by
  have h0 : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  rw [topIso_inv_eq_appLE W h0]
  refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE y W.ι W ⊤ ⊤ h0 le_rfl)
  congr 1
  exact (Scheme.Hom.appLE_eq_app _).symm

theorem topIso_inv_restrict_appTop {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) :
    U.topIso.inv ≫ (π ∣_ U).appTop = π.app U ≫ (π ⁻¹ᵁ U).topIso.inv := by
  have h0 : (⊤ : (π ⁻¹ᵁ U).toScheme.Opens) ≤ (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ U) := fun x _ => x.2
  have h1 : ∀ g : (π ⁻¹ᵁ U).toScheme ⟶ Y, g = (π ⁻¹ᵁ U).ι ≫ π → ∀ h : ⊤ ≤ g ⁻¹ᵁ U,
      g.appLE U ⊤ h = π.app U ≫ (π ⁻¹ᵁ U).topIso.inv := by
    rintro _ rfl h
    rw [topIso_inv_eq_appLE _ h0, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [topIso_inv_appTop U (π ∣_ U) (fun x _ => ((π ∣_ U) x).2)]
  exact h1 _ (morphismRestrict_ι π U) _

theorem evU_val_restrict {X Z : Scheme.{0}} (W : X.Opens) (y : Z ⟶ W.toScheme)
    (h : ∀ z, (y ≫ W.ι) z ∈ W) (r : Γ(X, W)ˣ) :
    (evU (y ≫ W.ι) h r).val = y.appTop.hom (W.topIso.inv.hom r.val) := by
  have e := congrArg (fun φ => φ.hom r.val) (topIso_inv_appTop W y (fun z _ => h z))
  exact e.symm

theorem appTop_injective_of_epi {X Y : Scheme.{0}} (Q : X ⟶ Y) [Epi Q] :
    Function.Injective Q.appTop.hom := by
  intro a b hab
  have e : Q ≫ Out.TLinPf.mOf a = Q ≫ Out.TLinPf.mOf b := by
    rw [Out.TLinPf.comp_mOf, Out.TLinPf.comp_mOf, hab]
  rw [cancel_epi] at e
  rw [← Out.TLinPf.fnOf_mOf a, e, Out.TLinPf.fnOf_mOf]

theorem unit_descends : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] [IsAffineHom π] (U : Y.Opens) (r : Γ(X, π ⁻¹ᵁ U)ˣ),
    (∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ∀ z, g₁ z ∈ π ⁻¹ᵁ U) (h₂ : ∀ z, g₂ z ∈ π ⁻¹ᵁ U),
      g₁ ≫ π = g₂ ≫ π → evU g₁ h₁ r = evU g₂ h₂ r) →
    ∃ u : Γ(Y, U)ˣ, pullU π U u = r := by
  intro X Y π _ _ _ U r hr
  have hS : Surjective (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict π U).flip inferInstance
  have hA : IsAffineHom (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict π U).flip inferInstance
  have hE : Epi (π ∣_ U) := Flat.epi_of_flat_of_surjective _
  have key : ∀ {Z : Scheme.{0}} (y₁ y₂ : Z ⟶ (π ⁻¹ᵁ U).toScheme), y₁ ≫ π ∣_ U = y₂ ≫ π ∣_ U →
      evU (y₁ ≫ (π ⁻¹ᵁ U).ι) (fun z => (y₁ z).2) r = evU (y₂ ≫ (π ⁻¹ᵁ U).ι) (fun z => (y₂ z).2) r := by
    intro Z y₁ y₂ e
    refine hr Z _ _ _ _ ?_
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]
  obtain ⟨v, hv⟩ := Out.TLinPf.descend_gen (π ∣_ U) ((π ⁻¹ᵁ U).topIso.inv.hom r.val) (by
    intro Z y₁ y₂ e
    rw [← evU_val_restrict _ y₁ (fun z => (y₁ z).2), ← evU_val_restrict _ y₂ (fun z => (y₂ z).2),
      key y₁ y₂ e])
  obtain ⟨v', hv'⟩ := Out.TLinPf.descend_gen (π ∣_ U) ((π ⁻¹ᵁ U).topIso.inv.hom (r⁻¹).val) (by
    intro Z y₁ y₂ e
    rw [← evU_val_restrict _ y₁ (fun z => (y₁ z).2), ← evU_val_restrict _ y₂ (fun z => (y₂ z).2)]
    have k := key y₁ y₂ e
    simp only [evU, map_inv] at k ⊢
    rw [k])
  have hvv : v * v' = 1 := by
    apply appTop_injective_of_epi (π ∣_ U)
    rw [map_mul, hv, hv', ← map_mul, Units.mul_inv, map_one, map_one]
  have h1 : U.topIso.hom.hom v * U.topIso.hom.hom v' = 1 := by
    rw [← map_mul, hvv, map_one]
  refine ⟨⟨U.topIso.hom.hom v, U.topIso.hom.hom v', h1, by rw [mul_comm, h1]⟩, Units.ext ?_⟩
  change (π.app U).hom (U.topIso.hom.hom v) = r.val
  have e := congrArg (fun φ => φ.hom (U.topIso.hom.hom v)) (topIso_inv_restrict_appTop π U)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [Iso.hom_inv_id_apply, hv] at e
  exact ((π ⁻¹ᵁ U).topIso.symm.commRingCatIsoToRingEquiv.injective e).symm

end GlobalTheory.EigenDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCover
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem frameCover_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V : (gen Y).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) D.p D.q := by
  intro E _ _ _ H D l Xo c O _ β Y V τ hτ z hz
  obtain ⟨U, hU, φ, f, hzU, hs, -⟩ := GlobalTheory.T.exists_affine_stable_lie_eigenspace_frame E H D l Xo c O β Y z
  obtain ⟨⟨v, w, hfr, -⟩, -⟩ := GlobalTheory.DetLine.EigParts.eigFrame_match E H D l Xo c O β Y τ hτ Set.univ
    Γ(gen Y, U) φ hU.fromSpec hs (Set.subset_univ _) f
  obtain ⟨r, hrV, hzr⟩ := hU.exists_basicOpen_le (V := V) ⟨z, hz⟩ hzU
  have hW := hU.basicOpen r
  have hle : (gen Y).basicOpen r ≤ U := (gen Y).basicOpen_le r
  let g : Γ(gen Y, U) →+* Γ(gen Y, (gen Y).basicOpen r) := ((gen Y).presheaf.map (homOfLE hle).op).hom
  have hx : (show Sp Γ(gen Y, (gen Y).basicOpen r) ⟶ gen Y from hW.fromSpec) = spMap g ≫ hU.fromSpec :=
    (hU.map_fromSpec hW (homOfLE hle).op).symm
  obtain ⟨v', w', h', -, -⟩ := exists_pull g hfr hx
  refine ⟨(gen Y).basicOpen r, hW, g.comp φ, v', w', hzr, h'.1, ?_, h'.2.2⟩
  rw [hW.range_fromSpec]
  exact hrV

end GlobalTheory.DetLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointDefinedOverBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem torsion_descends_to_complex : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (N : ℕ), 1 ≤ N → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp ℂ) (y : Over.mk t ⟶ X.A), y ^ N = 1 → ∃ z : 𝟙_ (Over (Sp ℂ)) ⟶ X.A, y = toUnit (Over.mk t) ≫ z := by
  intro F _ _ 𝔠 X N hN Ω _ _ t y hy
  have hM := GlobalTheory.abMulN_holds
  have : CharZero Ω := charZero_of_injective_ringHom (f := (Spec.preimage t).hom) (RingHom.injective _)
  have hSub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have : Flat t := inferInstance
  have : Surjective t := ⟨fun _ => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim _ _⟩⟩
  have : Epi t := Flat.epi_of_flat_of_surjective _
  letI : GrpObj ((Over.pullback t).obj X.A) := Functor.grpObjObj
  have hg : IsGrpPullback ((Over.pullback t).obj X.A) X.A t (pullback.fst X.A.hom t) := isGrpPullback_pullback X.A t
  have hab : IsAbelianScheme ((Over.pullback t).obj X.A) := GlobalTheory.isAbelianScheme_pullback_obj t X.A X.ab
  have hdim : SmoothOfRelativeDimension (Module.finrank ℚ F) ((Over.pullback t).obj X.A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 X.dim
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hg (𝟙 (Sp Ω)) t (Category.id_comp t).symm
  have hNΩ : ((N : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hNC : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h₁ := hM Ω ((Over.pullback t).obj X.A) _ N hab hdim hNΩ
  have h₂ := hM ℂ X.A _ N X.ab X.dim hNC
  let r : {z : 𝟙_ (Over (Sp ℂ)) ⟶ X.A // z ^ N = 1} → {y : Over.mk t ⟶ X.A // y ^ N = 1} := fun z =>
    ⟨toUnit (Over.mk t) ≫ z.1, by rw [← MonObj.comp_pow, z.2, MonObj.comp_one]⟩
  have hl : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  have hr : Function.Injective r := fun a b h => Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 (by
    have := congrArg (fun q => q.1.left) h
    simpa only [r, Over.comp_left, hl] using this)))
  have hc : Nat.card {y : Over.mk t ⟶ X.A // y ^ N = 1} =
      Nat.card {x : 𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj X.A // x ^ N = 1} :=
    (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => by
      change x ^ N = 1 ↔ e x ^ N = 1
      rw [← map_pow, map_eq_one_iff e e.injective])).symm
  have : Finite {y : Over.mk t ⟶ X.A // y ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc, h₁]; positivity)
  obtain ⟨z, hz⟩ := ((Nat.bijective_iff_injective_and_card r).2 ⟨hr, h₂.trans (h₁.symm.trans hc.symm)⟩).2 ⟨y, hy⟩
  exact ⟨z.1, (congrArg Subtype.val hz).symm⟩

end GlobalTheory.RealMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPowValueAtPointCocycleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transitionUnitPowValueAtPoint_cocycle : ∀ {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b c : L.ι) (n : ℤ),
    ⊤ ≤ y ⁻¹ᵁ L.U a → ⊤ ≤ y ⁻¹ᵁ L.U b → ⊤ ≤ y ⁻¹ᵁ L.U c →
    trV L y a b n * trV L y b c n = trV L y a c n := by
  first | exact @GlobalTheory.MBLow.TanGauge.trV_cocycle | exact GlobalTheory.MBLow.TanGauge.trV_cocycle | (intros; apply GlobalTheory.MBLow.TanGauge.trV_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateSectionValuesBoundedIntegralTangentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_section_values_bounded_integral_tangent : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α : N.X, ∃ b : ℝ, ∀ mu : N.X, ‖(trVal ν s gm α mu).fst‖ ≤ b ∧ ‖(trVal ν s gm α mu).snd‖ ≤ b := by
  first | exact @GlobalTheory.MBLow.trVal_bounded | exact GlobalTheory.MBLow.trVal_bounded | (intros; apply GlobalTheory.MBLow.trVal_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateTangentCombinationEqProdStatement
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
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_tangent_combination_eq_prod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {m : ℕ} (v' : Fin m → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (cf : Fin m → Γ(X, U.1)) (va : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U →
    ∀ (g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G) (y : Fin m → (overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G)),
    (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) → IsCombAtG t (GlobalTheory.LogKS.chart U) v' cf va →
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ → (∀ c, (y c).left = spMap (dualMap φ) ≫ v' c) →
    (∀ c, smT (g₀ ≫ t.G.hom) 0 (y c) = 1) ∧
      ∀ w, GlobalTheory.LogKS.IsTranslate t φ g₀ va w →
        w = (g' * (List.ofFn fun c => smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c)).prod).left := by
  first | exact @GlobalTheory.LogKSDiv.translate_comb | exact GlobalTheory.LogKSDiv.translate_comb | (intros; apply GlobalTheory.LogKSDiv.translate_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerDecompositionFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
namespace GlobalTheory.SqDecTransport

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem transport : ∀ (k K k₁ K' : Type) [Field k] [Field K] [Field k₁] [Field K'] (a : k →+* K) (b : k →+* k₁) (c : K →+* K') (d : k₁ →+* K'), c.comp a = d.comp b → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp K)) [GrpObj A] (π : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap a) π → ∀ (L₀ M₀ : LB A₀.left) (L M : LB A.left), L₀.IsLB → M₀.IsLB → L.IsLB → M.IsLB → LBIso L (L₀.pull π) → LBIso M (M₀.pull π) → SqDec ((Over.pullback (spMap b)).obj A₀) (L₀.pull (pullback.fst A₀.hom (spMap b))) (M₀.pull (pullback.fst A₀.hom (spMap b))) → SqDec ((Over.pullback (spMap c)).obj A) (L.pull (pullback.fst A.hom (spMap c))) (M.pull (pullback.fst A.hom (spMap c))) := by
  intro k K k₁ K' _ _ _ _ a b c d hcd A₀ _ A _ π hA L₀ M₀ L M hL₀ hM₀ hLL hML hL hM hD
  have hw : (pullback.fst A.hom (spMap c) ≫ π) ≫ A₀.hom = (pullback.snd A.hom (spMap c) ≫ spMap d) ≫ spMap b := by
    rw [Category.assoc, hA.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      spMap_comp_spMap, spMap_comp_spMap, hcd]
  let π' : pullback A.hom (spMap c) ⟶ pullback A₀.hom (spMap b) := pullback.lift _ _ hw
  have e₁ : π' ≫ pullback.fst A₀.hom (spMap b) = pullback.fst A.hom (spMap c) ≫ π := pullback.lift_fst _ _ _
  have e₂ : π' ≫ pullback.snd A₀.hom (spMap b) = pullback.snd A.hom (spMap c) ≫ spMap d := pullback.lift_snd _ _ _
  have hP : IsGrpPullback ((Over.pullback (spMap c)).obj A) ((Over.pullback (spMap b)).obj A₀) (spMap d) π' := by
    have n := (isGrpPullback_pullback A (spMap c)).comp hA
    rw [spMap_comp_spMap, hcd, ← spMap_comp_spMap, ← e₁] at n
    exact IsGrpPullback.cancel (isGrpPullback_pullback A₀ (spMap b)) n e₂
  obtain ⟨N, a₀, r, e, β, hN, ha₀, hβ, hI⟩ := hD
  have hβ' : ∀ i, ∃ f : (Over.pullback (spMap c)).obj A ⟶ (Over.pullback (spMap c)).obj A,
      IsMonHom f ∧ f.left ≫ π' = π' ≫ (β i).left := fun i => by
    haveI := hβ i
    exact GlobalTheory.HomDescent.exists_isMonHom_pull hP hP (β i)
  choose β' hβ'm hβ'c using hβ'
  have iL : LBIso (L.pull (pullback.fst A.hom (spMap c))) ((L₀.pull (pullback.fst A₀.hom (spMap b))).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull hL _ _ _ π' (fun _ => e₁.symm)
  have iM : LBIso (M.pull (pullback.fst A.hom (spMap c))) ((M₀.pull (pullback.fst A₀.hom (spMap b))).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull hM _ _ _ π' (fun _ => e₁.symm)
  refine ⟨N, a₀, r, e, β', hN, ha₀, hβ'm, ?_⟩
  have j₁ : LBIso (lbPow (L.pull (pullback.fst A.hom (spMap c))) N)
      ((lbPow (L₀.pull (pullback.fst A₀.hom (spMap b))) N).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iL _ _ _ π' (fun _ => by simp)
  have j₂ := GlobalTheory.RigidBundleGlue.LBIso.pull hI π'
  have j₃ : LBIso (LB.LinComb (M.pull (pullback.fst A.hom (spMap c))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β' i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ))
      ((LB.LinComb (M₀.pull (pullback.fst A₀.hom (spMap b))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ)).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iM _ _ _ π' (fun o => by
      cases o with
      | none => simp
      | some i => exact hβ'c i)
  exact LBIso.trans (isLB_lbPow (pull_isLB hLL _) N) (pull_isLB (isLB_lbPow (pull_isLB hL₀ _) N) _)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hML _) _ _) j₁
    (LBIso.trans (pull_isLB (isLB_lbPow (pull_isLB hL₀ _) N) _)
      (pull_isLB (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hM₀ _) _ _) _)
      (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hML _) _ _) j₂ (LBIso.symm j₃))

end GlobalTheory.SqDecTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulSymPairMemSpanBalancedTensorsStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transpose_mul_symPair_mem_span_balancedTensors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (R : Type) [CommRing R] (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (B : Matrix (Fin n) (Fin n') R), (∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0) → ∀ P : GlobalTheory.LogKSDiv.PairIx H Dw, ∃ cf : Fin Dw.dim → R, _root_.Matrix.transpose B * GlobalTheory.LogKSDiv.symPair (R := R) e P * B = ∑ k, cf k • GlobalTheory.LogKSDiv.symPair (R := R) e' (ε' k) := by
  first | exact @GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | exact GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | (intros; apply GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatum
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LBDescent

theorem twist_frame_descent : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∀ (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) →
    ∀ (V' : Y.Opens), V' ≤ V → ∀ u : Γ(X, f ⁻¹ᵁ V')ˣ, (∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u) →
    ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V' ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V' → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V' → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j) := by
  intro X Y f L φ V t ht c hc V' hV' u hu
  have h1 : ∀ i, f ⁻¹ᵁ V' ⊓ L.U i ≤ f ⁻¹ᵁ V' := fun i => inf_le_left
  have h2 : ∀ i, f ⁻¹ᵁ V' ⊓ L.U i ≤ f ⁻¹ᵁ V ⊓ L.U i := fun i =>
    inf_le_inf_right _ (fun x hx => hV' hx)
  refine ⟨fun i => res (h1 i) u * res (h2 i) (t i), ?_, ?_⟩
  · intro i j x hx hi hj
    have mi : (𝟙 X) x ∈ f ⁻¹ᵁ V' ⊓ L.U i := ⟨hx, hi⟩
    have mj : (𝟙 X) x ∈ f ⁻¹ᵁ V' ⊓ L.U j := ⟨hx, hj⟩
    rw [map_mul, map_mul, gm_res _ x _ mi, gm_res _ x _ mi, gm_res _ x _ mj, gm_res _ x _ mj,
      ht i j x (hV' hx) hi hj]
    exact mul_left_comm _ _ _
  · intro z i j hz hi hj
    have hfz : f (pullback.snd f f z) = f (pullback.fst f f z) := by
      have := congrArg (fun g => g z) (congrArg (fun g => g.base) (pullback.condition (f := f) (g := f)))
      simpa using this.symm
    have mi : pullback.fst f f z ∈ f ⁻¹ᵁ V' ⊓ L.U i := ⟨hz, hi⟩
    have mj : pullback.snd f f z ∈ f ⁻¹ᵁ V' ⊓ L.U j := ⟨show f (pullback.snd f f z) ∈ V' by rw [hfz]; exact hz, hj⟩
    rw [map_mul, map_mul, gm_res _ z _ mi, gm_res _ z _ mi, gm_res _ z _ mj, gm_res _ z _ mj, ← hu z hz,
      hc z i j (hV' hz) hi hj]
    group

end GlobalTheory.LBDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAboveDenseOpenEqGlobalMulPullbackStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_above_dense_open_eq_global_mul_pullback : ∀ (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : H ⟶ T) (e : T ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ F : Γ(H, p ⁻¹ᵁ U)ˣ, ∃ (G : Γ(H, ⊤)ˣ) (w : Γ(T, U)ˣ), F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G * pullU p U w := by
  first | exact @GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU | exact GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU | (intros; apply GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU <;> assumption)
end


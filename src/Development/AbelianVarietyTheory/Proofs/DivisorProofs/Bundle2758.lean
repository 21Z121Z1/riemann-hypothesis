import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientAbelianSchemeDescends
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsogModel

theorem exists_model_of_surjective : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (p : A.left ⟶ A₀.left) (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → ∀ ψ : A ⟶ X, IsMonHom ψ →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) →
  ∃ (X₀ : Over (Sp Qb)) (_ : GrpObj X₀) (q : X.left ⟶ X₀.left), IsAbelianScheme X₀ ∧ SmoothOfRelativeDimension g X₀.hom ∧
    IsGrpPullback X X₀ (spMap (algebraMap Qb ℂ)) q := by
  intro A₀ _ A X _ _ p g hA₀ hg₀ hp hX hgX ψ hψ hpts
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ hp
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hp.1 hg₀
  haveI : Surjective ψ.left := GlobalTheory.T.surjective_of_surjective_on_points A X ψ hA hX hpts
  obtain ⟨hfin, hflat⟩ := GlobalTheory.T.isogeny_finite_flat A X g hA hX hgA hgX ψ
  obtain ⟨n, hn, hkn⟩ := GlobalTheory.HolUnifEnd.exists_pow_eq_one_of_surjective A X g hA hX hgA hgX ψ
  set t : Sp ℂ ⟶ Sp Qb := spMap (algebraMap Qb ℂ) with ht
  have hSub : Subsingleton (Sp Qb) := inferInstanceAs (Subsingleton (PrimeSpectrum Qb))
  have : Flat t := inferInstance
  have : Surjective t := ⟨fun _ => ⟨(default : PrimeSpectrum ℂ), Subsingleton.elim _ _⟩⟩
  have : Epi t := Flat.epi_of_flat_of_surjective _
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp ℂ)) t (Category.id_comp t).symm
  have hl : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  let r : (𝟙_ (Over (Sp Qb)) ⟶ A₀) →* (Over.mk t ⟶ A₀) :=
    { toFun := fun c => toUnit (Over.mk t) ≫ c
      map_one' := MonObj.comp_one _
      map_mul' := fun a b => MonObj.comp_mul _ _ _ }
  have hr : Function.Injective r := fun a b h => Over.OverMorphism.ext ((cancel_epi t).1 (by
    have := congrArg (fun q => q.left) h
    simpa only [r, MonoidHom.coe_mk, OneHom.coe_mk, Over.comp_left, hl] using this))
  let ψp : (Over.mk (𝟙 (Sp ℂ)) ⟶ A) →* (Over.mk (𝟙 (Sp ℂ)) ⟶ X) :=
    { toFun := fun x => x ≫ ψ
      map_one' := MonObj.one_comp _
      map_mul' := fun a b => MonObj.mul_comp _ _ _ }
  let C₀ : Subgroup (𝟙_ (Over (Sp Qb)) ⟶ A₀) := (ψp.comp (e.symm.toMonoidHom.comp r)).ker
  have hC : ∀ c, c ∈ C₀ ↔ e.symm (r c) ≫ ψ = 1 := fun c => Iff.rfl
  have hnQ : ((n : ℕ) : Qb) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hfinT := GlobalTheory.Published.AbMulNSt.finite GlobalTheory.abMulN_holds hA₀ hg₀ hnQ
  have hC₀ : Finite C₀ := by
    refine Finite.of_injective (β := {c : 𝟙_ (Over (Sp Qb)) ⟶ A₀ // c ^ n = 1})
      (fun c => ⟨c.1, ?_⟩) (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
    have h1 := hkn (e.symm (r c.1)) ((hC c.1).1 c.2)
    apply hr
    rw [map_pow, map_one, ← e.apply_symm_apply (r c.1), ← map_pow, h1, map_one]
  obtain ⟨X₀, _, π₀, hX₀, hπ₀, hfin₀, het₀, hsurj₀, hker₀⟩ :=
    GlobalTheory.exists_quotient_abelian_by_finite_points Qb A₀ hA₀ C₀ hC₀
  haveI := hπ₀
  have hgX₀ : SmoothOfRelativeDimension g X₀.hom := by
    have := hX₀.smooth
    exact GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover Qb A₀.left X₀.left π₀.left X₀.hom g het₀
      hsurj₀ inferInstance (by rw [Over.w]; exact hg₀)
  let X' : Over (Sp ℂ) := (Over.pullback t).obj X₀
  letI : GrpObj X' := Functor.grpObjObj
  have hX' : IsGrpPullback X' X₀ t (pullback.fst X₀.hom t) := isGrpPullback_pullback X₀ t
  have hXa' : IsAbelianScheme X' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hX₀ hX'
  obtain ⟨e', he'⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hX' (𝟙 (Sp ℂ)) t (Category.id_comp t).symm
  obtain ⟨π, hπ, hπp⟩ := GlobalTheory.HomDescent.exists_isMonHom_pull hp hX' π₀
  haveI := hπ
  have hsq : IsPullback p π.left π₀.left (pullback.fst X₀.hom t) :=
    IsPullback.of_bot (by rw [Over.w π, Over.w π₀]; exact hp.1) hπp.symm hX'.1
  have hπe : Etale π.left := MorphismProperty.of_isPullback (P := @Etale) hsq het₀
  have hπs : Surjective π.left := MorphismProperty.of_isPullback (P := @Surjective) hsq hsurj₀
  have hπf : IsFinite π.left := MorphismProperty.of_isPullback (P := @IsFinite) hsq hfin₀

  have key : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, e' (x ≫ π) = e x ≫ π₀ := fun x => by
    refine Over.OverMorphism.ext ?_
    rw [he', Over.comp_left, Over.comp_left, he, Category.assoc, hπp, Category.assoc]
  have hsep : IsSeparated X.hom := by have := hX.proper; infer_instance
  have hsep' : IsSeparated X'.hom := by have := hXa'.proper; infer_instance

  obtain ⟨Zπ, _, iπ, _, _, hkπ⟩ := GlobalTheory.TorsionKernelModel.exists_kernel π
  have hZπ : Etale Zπ.hom := by
    have h1 : Etale (toUnit Zπ).left :=
      MorphismProperty.of_isPullback (P := @Etale) (hkπ.map (Over.forget _)) hπe
    have h2 : (toUnit Zπ).left = Zπ.hom := by simpa using Over.w (toUnit Zπ)
    rwa [h2] at h1
  haveI : IsReduced Zπ.left := GlobalTheory.isReduced_of_smooth_of_isReduced Zπ.hom
  have hkill1 : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ π = 1 → x ≫ ψ = 1 := by
    refine GlobalTheory.T.morphism_trivial_on_reduced_kernel A X' X Zπ π ψ iπ hkπ fun x hx => ?_
    have h1 : e x ≫ π₀ = 1 := by rw [← key, hx, map_one]
    obtain ⟨c, hc, hcx⟩ := (hker₀ ℂ t (e x)).1 h1
    have : x = e.symm (r c) := by rw [show r c = e x from hcx.symm]; simp
    rw [this]
    exact (hC c).1 hc
  obtain ⟨⟨β, hβ, hβc⟩, hepiπ⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A X' X π ψ hπ hψ
    inferInstance hπs inferInstance hkill1

  obtain ⟨Zψ, _, iψ, _, _, hkψ⟩ := GlobalTheory.TorsionKernelModel.exists_kernel ψ
  have hZψf : IsFinite Zψ.hom := by
    have h1 : IsFinite (toUnit Zψ).left :=
      MorphismProperty.of_isPullback (P := @IsFinite) (hkψ.map (Over.forget _)) hfin
    have h2 : (toUnit Zψ).left = Zψ.hom := by simpa using Over.w (toUnit Zψ)
    rwa [h2] at h1
  letI : GrpObj (Over.mk Zψ.hom) := ‹GrpObj Zψ›
  have hZψ : Etale Zψ.hom := GlobalTheory.etale_of_grpObj_of_isFinite (k := ℂ) Zψ.hom
  haveI : IsReduced Zψ.left := GlobalTheory.isReduced_of_smooth_of_isReduced Zψ.hom
  have hkill2 : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ ψ = 1 → x ≫ π = 1 := by
    refine GlobalTheory.T.morphism_trivial_on_reduced_kernel A X X' Zψ ψ π iψ hkψ fun x hx => ?_
    obtain ⟨c, hc⟩ := GlobalTheory.T.torsion_point_algebraic_model A₀ A p g n hA₀ hg₀ hp hn x (hkn x hx)
    have hxc : e x = r c := Over.OverMorphism.ext (by
      rw [he, hc]
      show t ≫ c.left = (toUnit (Over.mk t) ≫ c).left
      rw [Over.comp_left, hl])
    have hcC : c ∈ C₀ := by
      rw [hC, ← hxc, e.symm_apply_apply]; exact hx
    have h1 : e x ≫ π₀ = 1 := (hker₀ ℂ t (e x)).2 ⟨c, hcC, hxc⟩
    rw [← key] at h1
    exact (map_eq_one_iff e' e'.injective).1 h1
  obtain ⟨⟨κ, hκ, hκc⟩, hepiψ⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A X X' ψ π hψ hπ
    hflat inferInstance inferInstance hkill2
  have h1 : β ≫ κ = 𝟙 X' := (cancel_epi π).1 (by rw [← Category.assoc, hβc, hκc, Category.comp_id])
  have h2 : κ ≫ β = 𝟙 X := (cancel_epi ψ).1 (by rw [← Category.assoc, hκc, hβc, Category.comp_id])
  let iso : X ≅ X' := ⟨κ, β, h2, h1⟩
  haveI : IsMonHom iso.hom := hκ
  refine ⟨X₀, inferInstance, κ.left ≫ pullback.fst X₀.hom t, hX₀, hgX₀, ?_⟩
  exact ((isGrpPullback_of_iso iso).comp hX').congr (Category.id_comp t) rfl

end GlobalTheory.IsogModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionSplitRegularDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem genericPoint_mem_of_mem_opens (Y : Scheme.{0}) [IsIntegral Y] (W : Y.Opens) {y : Y}
    (hy : y ∈ W) : genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨y, trivial, hy⟩

theorem ratsec_split_of_H1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens),
    Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) →
    ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) →
    ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧
      ∀ y ∈ W₂, D.RegularAt y h₂ := by
  intro Y _ D W₁ W₂ hH f hf
  obtain ⟨ρ, hreg, hsurj, hres⟩ := GlobalTheory.T.exists_rationalFunction_maps_of_cartierTwistSections Y D
  by_cases g1 : genericPoint Y ∈ W₁
  · by_cases g2 : genericPoint Y ∈ W₂
    · have g12 : genericPoint Y ∈ W₁ ⊓ W₂ := ⟨g1, g2⟩
      obtain ⟨t, ht⟩ := hsurj (W₁ ⊓ W₂) f g12 hf
      obtain ⟨a, b, hab⟩ := GlobalTheory.T.mayer_vietoris_sections_split Y _ W₁ W₂ hH t
      refine ⟨ρ W₁ a, ρ W₂ b, ?_, fun y hy => hreg W₁ a y hy, fun y hy => hreg W₂ b y hy⟩
      rw [← ht, hab, map_sub, hres W₂ (W₁ ⊓ W₂) inf_le_right b g12,
        hres W₁ (W₁ ⊓ W₂) inf_le_left a g12]
    · refine ⟨ρ W₁ 0, f, by simp, fun y hy => hreg W₁ 0 y hy, fun y hy => ?_⟩
      exact absurd (genericPoint_mem_of_mem_opens Y W₂ hy) g2
  · refine ⟨-f, ρ W₂ 0, by simp, fun y hy => ?_, fun y hy => hreg W₂ 0 y hy⟩
    exact absurd (genericPoint_mem_of_mem_opens Y W₁ hy) g1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratFunc_C_laurent (F : Type) [Field F] : (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C =
    (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  ext1 a
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

theorem sqr_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : sqr G' ≫ φ = φ ≫ sqr G := by
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e := h.2 G' (𝟙 G') (𝟙 G') x₀ x₀ rfl rfl
  have e2 : x₀ * x₀ = x₀ ≫ (𝟙 G * 𝟙 G) := by rw [comp_mul]; simp
  rw [e2] at e
  exact e.symm

theorem ratRigid_of_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (Ω : Type) [Field Ω] [CharZero Ω]
    (b : Sp Ω ⟶ S), RatRigid ((Over.pullback b).obj G) (𝟙 (Sp Ω)) → RatRigid G b := by
  intro S G _ Ω _ _ b hR ξ hξ ⟨β, hβ⟩
  have hp := isGrpPullback_pullback G b
  have hu : unitSec ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = b ≫ unitSec G := unitSec_comp hp
  have hs : sqr ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = pullback.fst G.hom b ≫ sqr G :=
    sqr_comp_of_isGrpPullback hp
  have hsh : sqr ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = pullback.snd G.hom b :=
    Over.w (𝟙 ((Over.pullback b).obj G) * 𝟙 ((Over.pullback b).obj G))
  have hus : unitSec ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = 𝟙 _ := sec_hom _
  let ξ' : Sp (PowerSeries Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift ξ (spMap PowerSeries.C) hξ.base
  have hξ₁ : ξ' ≫ pullback.fst G.hom b = ξ := pullback.lift_fst _ _ _
  have hξ₂ : ξ' ≫ pullback.snd G.hom b = spMap PowerSeries.C := pullback.lift_snd _ _ _
  have hsp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hpath : IsPath ((Over.pullback b).obj G) 2 (𝟙 (Sp Ω)) ξ' := by
    refine ⟨?_, ?_, ?_⟩
    · exact hξ₂.trans (Category.comp_id _).symm
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, hξ.zero, Category.assoc, hu, Category.id_comp]
      · rw [Category.assoc, hξ₂, Category.assoc, hus, Category.id_comp, hsp]
        have : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω := by
          ext a; simp
        rw [this]
        show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = _
        rw [CommRingCat.ofHom_id, Spec.map_id]
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, Category.assoc, hs, ← Category.assoc, hξ₁, hξ.scale]
      · rw [Category.assoc, hξ₂, Category.assoc, hsh, hξ₂, hsp]
        have : (PowerSeries.rescale (2 : Ω)).comp PowerSeries.C = PowerSeries.C := by
          ext1 a; ext n; rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
          rcases n with _ | n <;> simp
        rw [this]
  have hβb : β ≫ G.hom = spMap RatFunc.C ≫ b := by
    apply GlobalTheory.spec_map_field_cancel (algebraMap (RatFunc Ω) (LaurentSeries Ω))
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, ← Category.assoc, ← Category.assoc, hsp, hsp,
      ratFunc_C_laurent]
  let β' : Sp (RatFunc Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift β (spMap RatFunc.C) hβb
  have hrat : IsRatPath ξ' := by
    refine ⟨β', ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hξ₁, hβ]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hξ₂, hsp, hsp, ratFunc_C_laurent]
  have e := hR ξ' hpath hrat
  rw [← hξ₁, e]
  simp only [triv, Category.assoc, hu, Category.id_comp]

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsCommonGenericFibreOfCommonThirdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisations_common_generic_fibre_of_common_third : ∀ (o Ω o₁ o₂ Ω' : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o₁] [CommRing o₂] [Field Ω'] [Algebra o₁ Ω'] [Algebra o₂ Ω'] (S : ThetaSys o Ω) (S₁ : ThetaSys o₁ Ω') (S₂ : ThetaSys o₂ Ω') (ρ : S.Real) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (lab₁ : S.Gam → S₁.Gam) (lab₂ : S.Gam → S₂.Gam) (φ : Ω →+* Ω'), Same ρ ε ρ₁ ε₁ lab₁ φ → Same ρ ε ρ₂ ε₂ lab₂ φ → SameAt ρ₁.P ρ₂.P S₁.R.val.toRingHom S₂.R.val.toRingHom ε₁ ε₂ (fun x => ρ₁.pt (lab₁ x)) (fun x => ρ₂.pt (lab₂ x)) := by
  first | exact @GlobalTheory.Poinc.SameComb.combine | exact GlobalTheory.Poinc.SameComb.combine | (intros; apply GlobalTheory.Poinc.SameComb.combine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartAtUnitaryClassicalTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Points GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPoinc

theorem rechart_at_uClassical_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (U : X.M.Z.Opens) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U → (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) ∈ U → spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ → X.M.ringOn U ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₁ : ratHull (X.M.ringOn U) →+* PadicAlgCl p, (∀ a : X.M.ringOn U, y₁ (toRat _ a) = X.M.val (gPt p ≫ ct.y) a) ∧ spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y ∧ ∀ a : X.o₁, ‖y₁ (toRat _ (algebraMap X.o₁ (X.M.ringOn U) a))‖ ≤ 1 := by
  intro E _ _ _ H Dw hpq l Xo cf C X p _ z ct U u' hU hwU hu'
  haveI := X.ar.char
  set w := (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) with hw
  have hne : (U : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  have hle : X.M.ringOn U ≤ X.M.O w := RatModel.ringOn_le_O hwU
  have hsp : ∀ w', (gPt p ≫ ct.y) w' ⤳ w := fun w' => by
    rw [Subsingleton.elim w' (closedPoint (PadicAlgCl p))]
  let y₀ : X.M.ringOn U →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ ct.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.M.ringOn U, y₀ a = X.M.val (gPt p ≫ ct.y) a := fun a => rfl
  obtain ⟨y₁, hy₁, -⟩ := existsUnique_ratLift (X.M.ringOn U) (K := PadicAlgCl p)
    (fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)) y₀
  have hy₁' : ∀ a : X.M.ringOn U, y₁ (toRat _ a) = y₀ a := fun a => RingHom.congr_fun hy₁ a
  let e : Sp (X.M.ringOn U) ⟶ X.M.Z :=
    Spec.map (CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec
  have he : ∀ {K : Type} [CommRing K] (φ : X.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧
      ∀ f, valR (spMap φ ≫ e) U f = φ (X.M.sectionsEquiv U hne f) := by
    intro K _ φ
    have e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom)) ≫
        hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e2]
    have hx := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom))
    refine ⟨hx, fun f => ?_⟩
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hyU : ⊤ ≤ (gPt p ≫ ct.y) ⁻¹ᵁ U := (le_preimage_iff _ U).2 hwU
  have ha : spMap y₀ ≫ e = gPt p ≫ ct.y := by
    refine ext_of_valR hU (he y₀).1 hyU fun f => ?_
    rw [(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]
    rfl
  have hgen : spMap (X.M.ringOn U).val.toRingHom ≫ e = X.M.pt := by
    refine ext_of_valR hU (he _).1 (X.M.top_le_preimage_pt hne) fun f => ?_
    rw [(he _).2]
    exact (RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)
  have hdom : IsDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  have hgen2 : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ ((spMap (toRat _) ≫ e) ≫ X.π) =
      spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ (u' ≫ C.i) := by
    rw [← Category.assoc, ← Category.assoc, spMap_val_toRat, hgen, X.comp, ← Category.assoc _ u' C.i, hu']
    simp only [USetup.uΩ, Category.assoc]
  have hb : (spMap (toRat _) ≫ e) ≫ X.π = u' ≫ C.i :=
    ext_of_isDominant_of_isSeparated C.z
      (ext_of_isDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) (by
        simp only [← Category.assoc] at hgen2 ⊢; rw [hgen2]))
      (spMap (ratHull (X.M.ringOn U)).val.toRingHom) hgen2
  haveI := C.isPreimmersion_i
  have hy01 : spMap y₁ ≫ spMap (toRat (X.M.ringOn U)) = spMap y₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hy₁]
  have hpt' : spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y := by
    rw [← cancel_mono C.i, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc, hy01, ha, Category.assoc,
      ct.comm, Category.assoc]
  let τ := Spec.preimage (ct.y ≫ X.M.s)
  have hσ : (gPt p ≫ ct.y) ≫ X.M.s = spMap ((OO p).subtype.comp τ.hom) := by
    rw [Category.assoc, ← Spec.map_preimage (ct.y ≫ X.M.s), ← Spec.map_comp]; rfl
  refine ⟨hle, y₁, fun a => (hy₁' a).trans (hy₀ a), hpt', fun a => ?_⟩
  rw [hy₁', hy₀]
  show ‖X.M.val (gPt p ≫ ct.y) (algebraMap X.o₁ X.Ω₁ a)‖ ≤ 1
  rw [RatModel.val_algebraMap hσ a]
  exact (mem_OO_iff _).1 (τ.hom a).2

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefAtPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam

open GlobalTheory.HalfBC in

theorem refAt_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (I : Ideal R) (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg ρ D.toPre D'), RefAt (pol D) ρ D' hD.xe (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf ρ)) := by
  intro R R' _ _ _ _ ρ hρ I D D' hD
  letI := D'.P.isAb.comm
  have gp := pull_grp hD
  refine ⟨sqOf gp, lamIso gp hD.w, gp, isSquare_sqOf gp, isGen_lamIso gp hD.w hD.w_gen, fun a => hD.c_pr a,
    fun κ hκ a b z J J' hJ hJ' => ?_⟩
  obtain rfl : κ = GlobalTheory.ArcPull.genMap hρ := by
    have : Mono (jK R) := Wit.mono_jK
    refine (cancel_mono (jK R)).1 (hκ.trans ?_)
    rw [← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]
  rw [← GlobalTheory.FactorPull.tau_lam hD hρ a b hJ hJ']
  refine congrArg₂ (· * ·) ?_ ((Wit.exists_tau D.toPre (hD.xe a) (hD.xe b)).choose_spec.2 _ _ z J hJ).symm
  symm
  show gw (lamIso gp hD.w) _ z (fun I => J (_ ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I))
    (fun I => J' (_ ≫ GlobalTheory.PrimCocycle.lamφ D'.P.A I)) = _
  refine (gw_lamIso gp hD.w _ z _ _ (fun I => by
      have := hJ ((lift (toUnit (TK R') ≫ D'.c a) (toUnit (TK R') ≫ D'.c b)).left ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I)
      erw [← pt_sqOf gp I]
      exact this) (fun I => hJ' _)).trans ?_
  refine Finset.prod_congr rfl fun I _ => ?_
  show _ = gw hD.w _ z _ _ ^ _
  erw [Category.assoc, ← sqOf_lamφ gp I]
  rfl

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_of_integral_valuation_bound : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (U : V.X.Opens) (f : V.X.functionField), (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (z ≫ V.j) f) ≤ 1) → ∀ x ∈ U, RegAt x f := by
  first | exact @GlobalTheory.Mean4O.Cover.RegCrit.regAt_of_integral_values | exact GlobalTheory.Mean4O.Cover.RegCrit.regAt_of_integral_values | (intros; apply GlobalTheory.Mean4O.Cover.RegCrit.regAt_of_integral_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleLiftOfNilpotentDividedPowersThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_lift_of_nilpotentDividedPowers_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  first | exact @GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP | exact GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP | (intros; apply GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientFreeRankTwiceDimensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reprModTrivialQuotient_free_rank_twice_dimension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → Nonempty (Additive (GlobalTheory.SympQ.Qq N n) ≃+ (Fin (2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X)) → ZMod n)) := by
  first | exact @GlobalTheory.SympQ.qq_free | exact GlobalTheory.SympQ.qq_free | (intros; apply GlobalTheory.SympQ.qq_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingLevelPushEqPowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reprModTrivialQuotient_pairing_levelPush_eq_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n m : ℕ), 0 < n → 0 < m → ∀ p q : N.QT (n * m), N.wp (GlobalTheory.SympQ.pushRep N (n * m) n p) (GlobalTheory.SympQ.pushRep N (n * m) n q) = N.wp p q ^ m := by
  first | exact @GlobalTheory.SympQ.wp_pushRep_pow | exact GlobalTheory.SympQ.wp_pushRep_pow | (intros; apply GlobalTheory.SympQ.wp_pushRep_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingNondegenerateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reprModTrivialQuotient_pairing_nondegenerate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → ∀ x : GlobalTheory.SympQ.Qq N n, (∀ y, GlobalTheory.SympQ.wpQ N n x y = 1) → x = 1 := by
  first | exact @GlobalTheory.SympQ.wpQ_nondeg | exact GlobalTheory.SympQ.wpQ_nondeg | (intros; apply GlobalTheory.SympQ.wpQ_nondeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictProperSectionsBijectiveToFibreOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proper_surjective_sections_bijective_over_fibre_open : ∀ (Y₀ H X'' P'' : Scheme.{0}) (H' : H.Opens) (i : H'.toScheme ⟶ X'') (a'' : X'' ⟶ P'') (b'' : P'' ⟶ Y₀), IsNoetherian Y₀ → IsOpenImmersion i → IsProper a'' → Surjective a'' → (∀ V : P''.Opens, Function.Bijective (a''.app V).hom) → IsFinite b'' → ∃ (P' : Scheme.{0}) (c : P' ⟶ P'') (X : H.Opens) (k : X.toScheme ⟶ H'.toScheme) (a : X.toScheme ⟶ P'), IsOpenImmersion c ∧ IsNoetherian P' ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ k ≫ H'.ι = X.ι ∧ a ≫ c = k ≫ i ≫ a'' ∧ (∀ z : H'.toScheme, (∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i) → H'.ι z ∈ X) ∧ ∀ w : X'', a'' w ∈ Set.range c → w ∈ Set.range (k ≫ i) := by
  first | exact @GlobalTheory.restrict_proper_sections_bijective_to_fibre_open | exact GlobalTheory.restrict_proper_sections_bijective_to_fibre_open | (intros; apply GlobalTheory.restrict_proper_sections_bijective_to_fibre_open <;> assumption)
end


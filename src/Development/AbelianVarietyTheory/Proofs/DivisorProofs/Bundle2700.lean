import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffwiseDerivationMvPowerSeries
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

theorem mvPowerSeries_derivation_coeffwise (σ R : Type) [CommRing R] (D : Derivation ℤ R R) :
    ∃ E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R),
      ∀ F α, MvPowerSeries.coeff α (E F) = D (MvPowerSeries.coeff α F) := by
  classical
  let L : MvPowerSeries σ R →ₗ[ℤ] MvPowerSeries σ R :=
    { toFun := fun F => fun α => D (MvPowerSeries.coeff α F)
      map_add' := by
        intro F G
        funext α
        show D (MvPowerSeries.coeff α (F + G)) = D (MvPowerSeries.coeff α F) + D (MvPowerSeries.coeff α G)
        rw [map_add, map_add]
      map_smul' := by
        intro n F
        funext α
        show D (MvPowerSeries.coeff α (n • F)) = n • D (MvPowerSeries.coeff α F)
        rw [map_zsmul, map_zsmul] }
  have hL : ∀ F α, MvPowerSeries.coeff α (L F) = D (MvPowerSeries.coeff α F) := fun _ _ => rfl
  refine ⟨Derivation.mk' L ?_, ?_⟩
  · intro F G
    ext α
    rw [smul_eq_mul, smul_eq_mul, map_add]
    erw [hL]
    rw [MvPowerSeries.coeff_mul, map_sum,
      MvPowerSeries.coeff_mul, mul_comm G, MvPowerSeries.coeff_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    erw [hL, hL]
    exact congrArg (_ + ·) (mul_comm _ _)
  · intro F α
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangeOfUOver
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_common_baseChange_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (σ : R →+* K) (σ' : R' →+* K) (u : Sp K ⟶ Xo.XF cf), UOver Xo cf P σ u → UOver Xo cf P' σ' u → ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsGrpPullback P₀.A P.A (spMap σ) a ∧ IsGrpPullback P₀.A P'.A (spMap σ') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro E _ _ _ H Dw l Xo cf K R R' _ _ _ P P' σ σ' u h h'
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  obtain ⟨G', _, α', β', hα', hβ', hL'⟩ := h'
  obtain ⟨P₀, φ, hφ, hLφ⟩ := exists_pol_baseChange P (spMap σ)
  obtain ⟨e₀, _, he₀⟩ := grpPullback_iso hφ hα
  obtain ⟨e, _, he⟩ := grpPullback_iso hβ hβ'
  haveI : IsMonHom (e₀ ≪≫ e).hom := inferInstanceAs (IsMonHom (e₀.hom ≫ e.hom))
  have hU := Xo.univ.t.PP.isLB
  have X1 : LBIso (P.L.pull φ) (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp e₀.hom.left he₀.symm rfl hL
  have X2 : LBIso (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) (P'.L.pull ((e₀.hom.left ≫ e.hom.left) ≫ α')) :=
    GlobalTheory.GenSpread.lbIso_pull_comp (e₀.hom.left ≫ e.hom.left) (by rw [← he, Category.assoc]) rfl hL'.symm
  refine ⟨P₀, φ, (e₀.hom.left ≫ e.hom.left) ≫ α', hφ,
    ((isGrpPullback_of_iso (e₀ ≪≫ e)).comp hα').congr (Category.id_comp _) rfl, hLφ,
    LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB P'.isLB _) hLφ
      (LBIso.trans (pull_isLB P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) X1 X2)⟩

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangePolarizedAbelianSchemeOfGe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Extend

theorem exists_factor {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U} [GrpObj G] [GrpObj G'] [GrpObj A]
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {a : A.left ⟶ G.left} (hb : IsGrpPullback G' G f b)
    (ha : IsGrpPullback A G (j ≫ f) a) : ∃ c : A.left ⟶ G'.left, IsGrpPullback A G' j c ∧ c ≫ b = a := by
  have w : a ≫ G.hom = (A.hom ≫ j) ≫ f := by rw [Category.assoc]; exact ha.1.w
  exact ⟨hb.1.lift _ _ w, hb.cancel (ha.congr rfl (hb.1.lift_fst _ _ w).symm) (hb.1.lift_snd _ _ w),
    hb.1.lift_fst _ _ w⟩

theorem exists_end {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U}
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {c : A.left ⟶ G'.left} (hb : IsPullback b G'.hom G.hom f)
    (hc : c ≫ G'.hom = A.hom ≫ j) (e₀ : G ⟶ G) (e : A ⟶ A) (h : e.left ≫ c ≫ b = (c ≫ b) ≫ e₀.left) :
    ∃ e' : G' ⟶ G', e'.left ≫ b = b ≫ e₀.left ∧ c ≫ e'.left = e.left ≫ c := by
  have w : (b ≫ e₀.left) ≫ G.hom = G'.hom ≫ f := by rw [Category.assoc, Over.w, hb.w]
  refine ⟨Over.homMk (hb.lift _ _ w) (hb.lift_snd _ _ w), hb.lift_fst _ _ w, hb.hom_ext ?_ ?_⟩
  · show (c ≫ hb.lift _ _ w) ≫ b = _
    rw [Category.assoc, hb.lift_fst, Category.assoc, h, Category.assoc]
  · show (c ≫ hb.lift _ _ w) ≫ _ = _
    rw [Category.assoc, hb.lift_snd, Category.assoc, hc, ← Category.assoc, Over.w]

theorem exists_sec {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U}
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {c : A.left ⟶ G'.left} (hb : IsPullback b G'.hom G.hom f)
    (hc : c ≫ G'.hom = A.hom ≫ j) (t : S ⟶ G.left) (ht : t ≫ G.hom = 𝟙 S) (w : U ⟶ A.left)
    (h : w ≫ c ≫ b = (j ≫ f) ≫ t) :
    ∃ s : S' ⟶ G'.left, s ≫ b = f ≫ t ∧ s ≫ G'.hom = 𝟙 S' ∧ ((w ≫ A.hom) ≫ j) ≫ s = w ≫ c := by
  have u : (f ≫ t) ≫ G.hom = 𝟙 S' ≫ f := by rw [Category.assoc, ht, Category.comp_id, Category.id_comp]
  have k : ((w ≫ A.hom) ≫ j) ≫ f = j ≫ f := by
    have := congrArg (· ≫ G.hom) h
    simp only [Category.assoc, ht, Category.comp_id, hb.w, reassoc_of% hc] at this
    simpa only [Category.assoc] using this
  refine ⟨hb.lift _ _ u, hb.lift_fst _ _ u, hb.lift_snd _ _ u, hb.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hb.lift_fst, ← Category.assoc, k, Category.assoc w, h]
  · rw [Category.assoc, hb.lift_snd, Category.comp_id, Category.assoc w c, hc, Category.assoc]

theorem lbIso_of_generic {O Ω : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] (H : Over (Sp O)) [GrpObj H]
    (hH : IsAbelianScheme H) {X : Scheme.{0}} {p : X ⟶ Sp Ω} {c : X ⟶ H.left}
    (hc : IsPullback c p H.hom (spMap (algebraMap O Ω))) {L L' : LB H.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : LBIso (L.pull c) (L'.pull c)) : LBIso L L' := by
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have : IsPreimmersion (spMap (algebraMap O Ω)) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have : Flat (spMap (algebraMap O Ω)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors O))
  have : IsDominant (spMap (algebraMap O Ω)) := by
    obtain ⟨_, _⟩ := (IsGenericPointHom.fractionField O Ω).quasiCompact_and_dominant
    infer_instance
  have : QuasiCompact (spMap (algebraMap O Ω)) := inferInstance
  have := hH.smooth
  have := geometricallyIntegral_of_isAbelianScheme H
  refine (GlobalTheory.CechPic.cls_eq_iff hL hL').1
    (GlobalTheory.ZH.EndoExtend.pic_ext (spMap (algebraMap O Ω)) hn H (eSec H) (Over.w η[H]) ?_ ?_)
  · rw [GlobalTheory.DualOpen.pic_sp_local_eq_zero O (GlobalTheory.CechPic.pull (eSec H) _),
      GlobalTheory.DualOpen.pic_sp_local_eq_zero O (GlobalTheory.CechPic.pull (eSec H) _)]
  · exact (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2
      (GenSpread.lbIso_pull_comp hc.isoPullback.inv hc.isoPullback_inv_fst.symm hc.isoPullback_inv_fst.symm h)

end GlobalTheory.Poinc.Extend

open GlobalTheory.Poinc.Extend in

theorem GlobalTheory.Poinc.sameAt_of_generic : ∀ (O Ω R₁ R₂ M Γ : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R₁] [CommRing R₂] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ ((algebraMap O Ω).comp f₁) ((algebraMap O Ω).comp f₂) e₁ e₂ t₁ t₂ → SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ := by
  intro O Ω R₁ R₂ M Γ _ _ _ _ _ _ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ ⟨P, a₁, a₂, h₁, h₂, l₁, l₂, hE, hx⟩
  have spc : ∀ {R : Type} [CommRing R] (f : R →+* O),
      spMap ((algebraMap O Ω).comp f) = spMap (algebraMap O Ω) ≫ spMap f := fun f => by
    rw [← Spec.map_comp]; rfl
  rw [spc] at h₁ h₂
  simp only [spc] at hx
  obtain ⟨Q₁, b₁, g₁, m₁⟩ : ∃ (Q : PolAV (Sp O)) (b : Q.A.left ⟶ P₁.A.left),
      IsGrpPullback Q.A P₁.A (spMap f₁) b ∧ LBIso Q.L (P₁.L.pull b) :=
    ⟨StrictPull.polPull P₁ (spMap f₁), _, isGrpPullback_pullback _ _,
      PolBaseChange.lbIso_refl (pull_isLB P₁.isLB _)⟩
  obtain ⟨Q₂, b₂, g₂⟩ : ∃ (Q : PolAV (Sp O)) (b : Q.A.left ⟶ P₂.A.left),
      IsGrpPullback Q.A P₂.A (spMap f₂) b :=
    ⟨StrictPull.polPull P₂ (spMap f₂), _, isGrpPullback_pullback _ _⟩
  obtain ⟨c₁, k₁, rfl⟩ := exists_factor g₁ h₁
  obtain ⟨c₂, k₂, rfl⟩ := exists_factor g₂ h₂
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have hj : IsGenericPointHom (spMap (algebraMap O Ω)) := IsGenericPointHom.fractionField O Ω
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  have s₁ := isSemiAbelian_of_isAbelianScheme Q₁.A Q₁.isAb
  have s₂ := isSemiAbelian_of_isAbelianScheme Q₂.A Q₂.isAb
  have := s₁.smooth
  have := s₂.smooth
  have := s₁.separated
  have := s₂.separated
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₁ s₂ k₁ k₂ (𝟙 P.A)
  obtain ⟨F', ⟨-, eF'⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₂ s₁ k₂ k₁ (𝟙 P.A)
  rw [Over.id_left, Category.id_comp] at eF eF'
  let I : Q₁.A ≅ Q₂.A :=
    ⟨F, F', ExtUnique.over_hom_ext_of_isPullback k₁.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF, ← eF', Over.id_left, Category.comp_id]),
      ExtUnique.over_hom_ext_of_isPullback k₂.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF', ← eF, Over.id_left, Category.comp_id])⟩
  have : IsMonHom I.hom := hF
  have g₂' : IsGrpPullback Q₁.A P₂.A (spMap f₂) (F.left ≫ b₂) :=
    ((isGrpPullback_of_iso I).comp g₂).congr (Category.id_comp _) rfl
  refine ⟨Q₁, b₁, F.left ≫ b₂, g₁, g₂', m₁, ?_, fun E => ?_, fun x => ?_⟩
  · refine lbIso_of_generic Q₁.A Q₁.isAb k₁.1 Q₁.isLB (pull_isLB P₂.isLB _) ?_
    refine LBIso.trans (pull_isLB Q₁.isLB _) (pull_isLB P₁.isLB _) (pull_isLB (pull_isLB P₂.isLB _) _)
      (GenSpread.lbIso_pull_of_lbIso m₁ c₁ rfl) ?_
    refine LBIso.trans (pull_isLB P₁.isLB _) P.isLB (pull_isLB (pull_isLB P₂.isLB _) _) l₁.symm ?_
    exact LBIso.trans P.isLB (pull_isLB P₂.isLB _) (pull_isLB (pull_isLB P₂.isLB _) _) l₂
      (GenSpread.lbIso_pull_pull P₂.isLB c₁ (by rw [eF, Category.assoc]))
  · obtain ⟨e, u₁, u₂⟩ := hE E
    obtain ⟨d₁, v₁, w₁⟩ := exists_end g₁.1 k₁.1.w (e₁ E) e u₁
    obtain ⟨d₂, v₂, w₂⟩ := exists_end g₂.1 k₂.1.w (e₂ E) e u₂
    have : d₁ ≫ F = F ≫ d₂ := ExtUnique.over_hom_ext_of_isPullback k₁.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, w₁, Category.assoc, ← eF, ← Category.assoc, ← eF, w₂])
    refine ⟨d₁, v₁, ?_⟩
    rw [← Category.assoc, ← Over.comp_left, this, Over.comp_left, Category.assoc, v₂, Category.assoc]
  · obtain ⟨w, u₁, u₂⟩ := hx x
    obtain ⟨d₁, v₁, z₁, w₁⟩ := exists_sec g₁.1 k₁.1.w (t₁ x).left (Over.w (t₁ x)) w u₁
    obtain ⟨d₂, v₂, z₂, w₂⟩ := exists_sec g₂.1 k₂.1.w (t₂ x).left (Over.w (t₂ x)) w u₂
    have : Surjective (w ≫ P.A.hom) :=
      ⟨fun y => ⟨y, Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
    have : d₁ ≫ F.left = d₂ := ext_of_isDominant_of_isSeparated Q₂.A.hom
      (by rw [Category.assoc, Over.w, z₁, z₂]) ((w ≫ P.A.hom) ≫ spMap (algebraMap O Ω))
      (by rw [← Category.assoc, w₁, w₂, eF, Category.assoc])
    exact ⟨d₁, v₁, by rw [← Category.assoc, this, v₂]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldOfFieldPointsSamePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_common_field_of_point_eq : ∀ (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X), a (closedPoint K₁) = b (closedPoint K₂) → ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b := by
  intro X K₁ K₂ _ _ a b h
  obtain ⟨⟨x, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ X).symm.surjective a
  obtain ⟨⟨y, g⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₂ X).symm.surjective b
  have hxy : x = y := by
    have h1 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₁ X).apply_symm_apply ⟨x, f⟩)
    have h2 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₂ X).apply_symm_apply ⟨y, g⟩)
    exact h1.symm.trans (h.trans h2)
  subst hxy
  letI : Algebra (X.residueField x) K₁ := f.hom.toAlgebra
  letI : Algebra (X.residueField x) K₂ := g.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) K₁ K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) K₁ K₂)
  letI : Field ((TensorProduct (X.residueField x) K₁ K₂) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(TensorProduct (X.residueField x) K₁ K₂) ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := X.residueField x) (A := K₁) (B := K₂)).toRingHom, ?_⟩
  change Spec.map _ ≫ Spec.map f ≫ X.fromSpecResidueField x = Spec.map _ ≫ Spec.map g ≫ X.fromSpecResidueField x
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext c
  change Ideal.Quotient.mk m (TensorProduct.tmul _ (algebraMap _ K₁ c) 1) = Ideal.Quotient.mk m (TensorProduct.tmul _ 1 (algebraMap _ K₂ c))
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullDegTraitAndBaseUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_pullDeg_trait_and_base_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → UnifTrait D G L →
    ∀ (D₂ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U₂ : Unif (maximalIdeal R) D₂ A G),
    U₂.LG.L = L → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (φ : R →+* W) (D' : DegPre W),
      Function.Injective φ ∧ Nonempty (IsPullDeg φ D.toPre D') ∧ Nonempty (IsPullDeg φ D₂.toPre D') := by
  first | exact @GlobalTheory.Mum.CommonPull.exists_common_pull | exact GlobalTheory.Mum.CommonPull.exists_common_pull | (intros; apply GlobalTheory.Mum.CommonPull.exists_common_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commonPullback_fractionField_finiteLocalExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegPre R) (E₁ E₂ : DegPre (FractionRing R)), IsPullDeg (algebraMap R (FractionRing R)) D₁ E₁ → IsPullDeg (algebraMap R (FractionRing R)) D₂ E₂ → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (E₃ : DegPre K'), io.Finite → IsPullDeg io E₁ E₃ → IsPullDeg io E₂ E₃ → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (E : DegPre (FractionRing R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) := by
  first | exact @GlobalTheory.CommonCover.exists_common_pull | exact GlobalTheory.CommonCover.exists_common_pull | (intros; apply GlobalTheory.CommonCover.exists_common_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleMapsModPowMaximalIdealBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_maps_mod_pow_maximalIdeal_base_alt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R'] [Module.Finite R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (Γ : Type) (actC : Γ → (C' ≃ₐ[R] C')) (O : Type) [CommRing O] [Algebra R O] (i' : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), (∀ e x y, Ideal.Quotient.mk _ y = i' (e + 1) x → Ideal.Quotient.mk _ y = i' e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i' e x → Ideal.Quotient.mk _ (actC σ y) = i' e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) → ∃ i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C'), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) := by
  first | exact @GlobalTheory.exists_compatible_maps_mod_pow_maximalIdeal_base | exact GlobalTheory.exists_compatible_maps_mod_pow_maximalIdeal_base | (intros; apply GlobalTheory.exists_compatible_maps_mod_pow_maximalIdeal_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimitiveRootsThrough
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.RootSystem

theorem exists_compatible_roots_through (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : ℕ) (ω : K)
    (hA : 0 < A) (hω : IsPrimitiveRoot ω A) :
    ∃ ζ : ℕ → Kˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧
      (ζ A : K) = ω := by
  have hz : IsPrimitiveRoot (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) A := GlobalTheory.HostModel.isPrimitiveRoot_zeta hA
  have hint : IsIntegral ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := (hz.isIntegral hA).tower_top
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A}
  haveI : FiniteDimensional ℚ L := IntermediateField.adjoin.finiteDimensional hint
  let pb := IntermediateField.adjoin.powerBasis hint
  have hroot : Polynomial.aeval ω (minpoly ℚ pb.gen) = 0 := by
    have hm : minpoly ℚ pb.gen = minpoly ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := by
      rw [IntermediateField.adjoin.powerBasis_gen]; exact IntermediateField.minpoly_gen ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A)
    rw [hm, ← Polynomial.cyclotomic_eq_minpoly_rat hz hA, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic]
    exact (hω.isRoot_cyclotomic hA)
  let f : L →ₐ[ℚ] K := pb.lift ω hroot
  obtain ⟨ζ, h1, h2, h3⟩ := GlobalTheory.HostModel.exists_roots L K f.toRingHom
  refine ⟨ζ, h1, h2, ?_⟩
  have hg := h3 A hA (IntermediateField.AdjoinSimple.gen ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A)) rfl
  rw [hg]
  have : f pb.gen = ω := pb.lift_gen ω hroot
  rw [IntermediateField.adjoin.powerBasis_gen] at this
  exact this

example : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : ℕ) (ω : K), 0 < A → IsPrimitiveRoot ω A → ∃ ζ : ℕ → Kˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧ (ζ A : K) = ω :=
  @exists_compatible_roots_through

end GlobalTheory.RootSystem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplAtFactorOfIsAdicComplete
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_complAt_factor_of_isAdicComplete : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W] (I : Type) [Fintype I] (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial I W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ψ : MvPolynomial I W →+* R) (θ : R →+* V), IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) := by
  intro W _ _ I _ V _ _ hV ψV hC
  haveI := hV
  let A := MvPolynomial I W
  let q : Ideal A := (maximalIdeal V).comap ψV
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime q
  haveI : IsRegularRing W := GlobalTheory.isRegularRing_of_isRegularLocalRing W
  haveI : IsRegularLocalRing L := inferInstance
  let R := AdicCompletion (maximalIdeal L) L
  haveI : IsRegularLocalRing R := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion L
  haveI : IsDomain R := inferInstance
  haveI : IsNoetherianRing R := inferInstance
  have hfg : (maximalIdeal L).FG := (maximalIdeal L).fg_of_isNoetherianRing
  have hunit : ∀ y : q.primeCompl, IsUnit (ψV y) := fun y => by
    have := y.2
    exact IsLocalRing.notMem_maximalIdeal.mp this
  let φ : L →+* V := IsLocalization.lift (M := q.primeCompl) (S := L) hunit
  have hφ : φ.comp (algebraMap A L) = ψV := IsLocalization.lift_comp hunit
  have hmL : (maximalIdeal L) = q.map (algebraMap A L) := (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hk : (maximalIdeal L).map φ ^ 1 ≤ maximalIdeal V := by
    rw [pow_one, hmL, Ideal.map_map, hφ]
    exact Ideal.map_comap_le
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.exists_extend_adicCompletion φ (maximalIdeal L) (maximalIdeal V) hk
  let c : L →+* R := algebraMap L R
  let ψ : A →+* R := c.comp (algebraMap A L)
  have hθψ : θ.comp ψ = ψV := by
    show θ.comp (c.comp (algebraMap A L)) = ψV
    rw [← RingHom.comp_assoc]
    show (θ.comp (algebraMap L R)).comp (algebraMap A L) = ψV
    rw [hθ, hφ]
  have hmR : maximalIdeal R = q.map ψ := by
    have h0 := AdicCompletion.maximalIdeal_eq_map (R := L)
    have hmL' : q.map (algebraMap A L) = maximalIdeal L := Localization.AtPrime.map_eq_maximalIdeal
    rw [h0]
    show _ = q.map (c.comp (algebraMap A L))
    rw [← Ideal.map_map, hmL']
  refine ⟨R, inferInstance, inferInstance, inferInstance, ψ, θ, ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩, ?_, hθψ, ?_⟩
  · exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat L q.primeCompl))
      (RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _))
  · apply le_antisymm Ideal.map_comap_le
    have : q ≤ (maximalIdeal R).comap ψ := by
      rw [← Ideal.map_le_iff_le_comap, ← hmR]
    rw [hmR]
    exact Ideal.map_mono (hmR ▸ this)
  · intro r
    obtain ⟨x, hx⟩ := (AdicCompletion.residueField_map_bijective_of_fg (R := L) hfg).2 (residue R r)
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    refine ⟨a, s, ?_, ?_⟩
    · exact (IsLocalization.map_units L s).map c
    · have h1 : residue R (c (IsLocalization.mk' L a s)) = residue R r := by
        rw [← hx, ResidueField.map_residue]
      have h2 : r - c (IsLocalization.mk' L a s) ∈ maximalIdeal R := by
        rw [← residue_eq_zero_iff, map_sub, h1, sub_self]
      have h3 : c (IsLocalization.mk' L a s) * ψ s = ψ a := by
        show c (IsLocalization.mk' L a s) * c (algebraMap A L s) = c (algebraMap A L a)
        rw [← map_mul, IsLocalization.mk'_spec]
      have : r * ψ s - ψ a = (r - c (IsLocalization.mk' L a s)) * ψ s := by
        rw [sub_mul, h3]
      rw [this]
      exact Ideal.mul_mem_right _ _ h2
  · haveI : IsLocalHom (θ.comp (algebraMap L R)) := by
      rw [hθ]
      apply ((IsLocalRing.local_hom_TFAE φ).out 0 2).mpr
      simpa using hk
    exact GlobalTheory.isLocalHom_of_extend_adicCompletion hfg θ
  · refine ⟨fun a ha => hC.map_nonunit a ?_⟩
    have : θ ((ψ.comp MvPolynomial.C) a) = (ψV.comp MvPolynomial.C) a := by
      simp only [RingHom.comp_apply]
      exact congrArg (fun f : A →+* V => f (MvPolynomial.C a)) hθψ
    rw [← this]
    exact ha.map θ

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRComparisonPreUniformised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitCompare

open GlobalTheory.UU GlobalTheory.LN

set_option maxHeartbeats 1000000 in

theorem exists_cmp_under : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (_ : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = maximalIdeal R ∧ GlobalTheory.LN.Under U' U₀.toUnifPre := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨⟨hL, hL2, -, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hEg := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have := hB.1.1
  have := hB.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have := hV.1
  have hBV : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  have := U.gen_hom
  obtain ⟨A', s, w, hw⟩ :=
    GlobalTheory.Mum.TraitSetting.exists_setting_of_evenOn hL U.P U.semi hE A U.gen ⟨U.wA, U.wA_gen⟩ hV φ hφ hc.ge
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := GlobalTheory.PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := GlobalTheory.T.exists_compare_uniformisationData_pullback hL hL2 hEg R V _ _ hB.1 hBV (maximalIdeal.isMaximal V).ne_top φ hle D D'.toPre A A'
    G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  exact ⟨V, _, _, _, φ, D', A', _, _, _, U', U₀, _, C, hV, hφ, hc, hU'⟩

end GlobalTheory.Mum.TraitCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRValuationCompleteNormalLocalStatement
section
open IsLocalRing GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_valuation_completeNormalLocal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → maximalIdeal V ≠ ⊥ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) ∧ ∀ x y : FractionRing V, (∃ r : V', k x = algebraMap V' (FractionRing V') r * k y) → ν x ≤ ν y := by
  first | exact @GlobalTheory.DivBound.exists_cdvr_valuation_le | exact GlobalTheory.DivBound.exists_cdvr_valuation_le | (intros; apply GlobalTheory.DivBound.exists_cdvr_valuation_le <;> assumption)
end


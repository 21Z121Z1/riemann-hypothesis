import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2992
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2945
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianSchemeDescendsFiniteType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.PolModel

open GlobalTheory.SiegApprox GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem polarised_descends : ∀ (B : Type) [CommRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ (B₀ : Subring B) (A₀ : Over (Sp B₀)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left), Algebra.FiniteType ℤ B₀ ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap B₀.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) ∧ (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) ∧ LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) ∧ Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  intro R _ A _ _ P hA hP rig₁ rig₂ hsymm hamp
  classical
  obtain ⟨S, B, _, _, φ, φ₂, P₀, -, hS, hB, hφ, sq, hP₀, hw⟩ := model_exists R A ∅ hA P hP
  have one : (1 : A ⟶ A).left ≫ φ = φ ≫ (1 : B ⟶ B).left := one_comp hφ A B φ hφ.1.w
  have idφ : (𝟙 A : A ⟶ A).left ≫ φ = φ ≫ (𝟙 B : B ⟶ B).left := by simp
  obtain ⟨F₁, hF₁⟩ := rig_descends R S A B φ φ₂ P P₀ (lift 1 (𝟙 A)) (lift 1 (𝟙 B)) hB hφ sq hP hP₀ hw
    (lift_square sq one idφ) rig₁
  obtain ⟨F₂, hF₂⟩ := rig_descends R S A B φ φ₂ P P₀ (lift (𝟙 A) 1) (lift (𝟙 B) 1) hB hφ sq hP hP₀ hw
    (lift_square sq idφ one) rig₂
  obtain ⟨F₃, hF₃⟩ := symm_descends R S A B φ φ₂ P P₀ hB hφ sq hP hP₀ hw hsymm
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have := hB.proper
  have : Flat B.hom := by have := hB.smooth; infer_instance
  obtain ⟨F₄, hF₄⟩ := GlobalTheory.AmpleApprox.relAmple_spread_subring (pull_isLB hP₀ _) hφ.1 (pull_isLB hP _)
    (GlobalTheory.SiegelPull.diag_iso sq hw) hamp
  let F : Finset R := F₁ ∪ F₂ ∪ F₃ ∪ F₄
  obtain ⟨R₁, hSR, hFR, hR₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S F hS
  have hF₁R : (F₁ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₂R : (F₂ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₃R : (F₃ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₄R : (F₄ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  let iS : Sp R₁ ⟶ Sp S := spMap (Subring.inclusion hSR)
  have hiS : spMap S.subtype = spMap R₁.subtype ≫ iS := by
    simp only [iS, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hφ' : IsGrpPullback A B (spMap R₁.subtype ≫ iS) φ := hiS ▸ hφ
  have hφ₁ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor iS (spMap R₁.subtype) hφ'
  set φ₁ := pullback.lift φ (A.hom ≫ spMap R₁.subtype) (by rw [hφ'.1.w, Category.assoc]) with hφ₁def
  let B₁ := (Over.pullback iS).obj B
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.isAbelianScheme_pullback_obj iS B hB
  have hψφ : φ₁ ≫ pφ iS B = φ := pullback.lift_fst _ _ _
  let φ₂₁ := (GlobalTheory.GenericSpread.sqMap hφ₁).left
  have sq₁ : IsSquare φ₁ φ₂₁ :=
    ⟨congrArg (fun z => z.left) (lift_fst (pushPt hφ₁.1.w (fst A A)) (pushPt hφ₁.1.w (snd A A))),
     congrArg (fun z => z.left) (lift_snd (pushPt hφ₁.1.w (fst A A)) (pushPt hφ₁.1.w (snd A A)))⟩
  have hψ₂ : φ₂₁ ≫ pφ₂ iS B = φ₂ := by
    apply adelic_GL2_ext_of_local_components
    · rw [Category.assoc, pφ₂_fst, ← Category.assoc, sq₁.1, Category.assoc, hψφ, sq.1]
    · rw [Category.assoc, pφ₂_snd, ← Category.assoc, sq₁.2, Category.assoc, hψφ, sq.2]
  have hP₁ : (P₀.pull (pφ₂ iS B)).IsLB := pull_isLB hP₀ _
  have r₁ := hF₁ R₁ hSR hF₁R (lift 1 (𝟙 B₁)) (lift_one_id iS B)
  have r₂ := hF₂ R₁ hSR hF₂R (lift (𝟙 B₁) 1) (lift_id_one iS B)
  have s₁ := hF₃ R₁ hSR hF₃R
  have sqp : IsSquare (G' := B₁) (G := B) (pφ iS B) (pφ₂ iS B) := ⟨pφ₂_fst iS B, pφ₂_snd iS B⟩
  have := hB₁.proper
  have amp : Out.RelAmple B₁ ((P₀.pull (pφ₂ iS B)).pull (lift (𝟙 B₁) (𝟙 B₁)).left) :=
    GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP₁ _)
      (GlobalTheory.SiegelPull.diag_iso sqp (GlobalTheory.lbIso_refl hP₁))
      (hF₄ R₁ hSR hF₄R B₁ (pφ iS B) (IsPullback.of_hasPullback B.hom iS))
  refine ⟨R₁, B₁, inferInstance, inferInstance, φ₁, φ₂₁, P₀.pull (pφ₂ iS B), hR₁, hB₁, hφ₁, sq₁, hP₁, ?_, r₁, r₂,
    s₁, amp⟩
  exact LBIso.trans hP (pull_isLB hP₀ _) (pull_isLB hP₁ _) hw
    (GlobalTheory.GenSpread.lbIso_pull_pull hP₀ φ₂₁ hψ₂.symm)

end GlobalTheory.PolModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGalois
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenDesc

open GlobalTheory.Mum

theorem polarisedGeneric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) := by
  intro R _ _ _ _ R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ _ U' a G _ _ β hG hpb hinv
  have hρ : Function.Injective ρ := hfin.2.1
  haveI := hgal.1
  have hκ := GlobalTheory.T.isGrpPullback_genericFibre_fractionFieldMap R R' ρ hρ G' G β hpb
  let L' := U'.LG.L.pull (pullback.fst G'.hom (jK R'))
  have hL' : L'.IsLB := pull_isLB U'.LG.isLB _
  have hiso : LBIso L' (A'.L.pull U'.gen.hom.left) := LBIso.symm U'.ext
  have := U'.gen_hom
  obtain ⟨hP', hdim', hsym', hamp', hkt'⟩ := GlobalTheory.T.principalPolarisation_of_groupScheme_iso _ A' _ U'.gen U'.gen_hom L' hL' hiso
  have hsemi : IsSemiAbelian ((Over.pullback (jK R)).obj G) := Geo.Tor.IsSemiAbelian.pullback (jK R) G hG
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_of_fieldExtension_pullback_proper _ _ (fracMap ρ hρ) ((Over.pullback (jK R)).obj G) _ _ A'.g hsemi hκ hP' hdim'
  obtain ⟨L, hL, hLL⟩ := GlobalTheory.T.exists_lineBundle_galoisDescent_abelianVariety_finite (FractionRing R) (FractionRing R') (fracMap ρ hρ)
    (GlobalTheory.T.fractionFieldMap_finite_of_finite_injective R R' ρ hρ hfin.2.2) (Gal ρ) (fun σ => fracAut σ.1) (fun σ x => fracAut_fracMap hρ σ x)
    (GlobalTheory.T.fixed_mem_range_fractionFieldMap_galoisInvariants R R' ρ hρ hgal) ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G') _ hab hκ L' hL'
    (GlobalTheory.T.exists_galoisConjugate_genericBundle_iso R R' ρ hρ D D' hD A' G' U' a G β hpb.1.w hinv)
  obtain ⟨hrig, hsym⟩ := GlobalTheory.T.rigidified_symmetric_of_symmetric_fieldExtension_pullback _ _ (fracMap ρ hρ) _ _ _ hab hκ L L' hL hL' hLL hsym'
  have := hsemi.quasiCompact
  have := hsemi.separated
  have := hsemi.smooth
  obtain ⟨-, hamp, hkt⟩ := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension (FractionRing R) (FractionRing R')
    (fracMap ρ hρ) ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G') _ hκ L L' hL hL' hLL hP' hamp' hkt'
  let P : PolAV (Sp (FractionRing R)) :=
    { A := (Over.pullback (jK R)).obj G
      isAb := hab
      g := A'.g
      smoothDim := hdim
      L := L
      isLB := hL
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hkt }
  refine ⟨P, Iso.refl _, genMap hρ β hpb.1.w, ?_, genMap_fst _ _ _, ?_⟩
  · show IsMonHom (𝟙 _)
    infer_instance
  · simpa using hLL

end GlobalTheory.Mum.GenDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerDataTensorBundleIsoWithPsiValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerData_tensorBundleIso_with_psi_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D.P.A ⟶ D₀.P.A)) (j : Fin r → (D₀.P.A ⟶ D.P.A)) (h : Fin r → D₀.X → D.X) (k : Fin r → D.X → D₀.X), (∀ a χ, D.c (h a χ) = D₀.c χ ≫ j a) → (∀ a y, D₀.c (k a y) = D.c y ≫ pr a) → (∀ a, PeriodRel D D₀ (pr a) (h a) (k a)) → (∀ a, CmpTwo D D₀ (pr a) (j a)) → Expand D (fun ab : Fin r × Fin r => W ab.1 ab.2) (𝟙 D.P.A) (fun ab => pr ab.2 ≫ j ab.1) → PrimVal D (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) (fun y => ∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y)) → ∃ w : LB.Iso D.P.L (LB.LinComb D₀.P.L (tensφ pr) (tensε W)), w.IsGen ∧ ∀ y z J J', Good D₀.P.L z J → Good D.P.L z J' → val (D.psi y) (𝟙 _) z J' = gm (D.xK y) z _ (w.s (fun k => J (D.xK y ≫ tensφ pr k), J' (D.xK y))) * ∏ a, ∏ b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z J ^ W a b := by
  first | exact @GlobalTheory.Mum.PowData.tens_iso_psi | exact GlobalTheory.Mum.PowData.tens_iso_psi | (intros; apply GlobalTheory.Mum.PowData.tens_iso_psi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveAxesDescendField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem one_tmul_injective_field (K L M : Type) [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    Function.Injective (fun m : M ↦ (1 : L) ⊗ₜ[K] m) := by
  have h1 : Function.Injective ((Algebra.linearMap K L).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
  have h2 : (fun m : M ↦ (1 : L) ⊗ₜ[K] m) = ((Algebra.linearMap K L).rTensor M) ∘ (TensorProduct.lid K M).symm := by
    funext m; simp
  rw [h2]; exact h1.comp (TensorProduct.lid K M).symm.injective

theorem pullHO_injective_field (K L : Type) [Field K] [Field L] [Algebra K L] (X X' : Scheme.{0}) (s : X ⟶ Sp K)
    (s' : X' ⟶ Sp L) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap K L))) (hs : IsSeparated s)
    (hq : QuasiCompact s) :
    Function.Injective (pullHO1 h.w) ∧ Function.Injective (pullHO2 h.w) := by
  obtain ⟨⟨e1, he1⟩, ⟨e2, he2⟩⟩ := GlobalTheory.T.structure_cohomology_flat_base_change K L X X' s s' φ h hs hq
  refine ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_⟩
  · apply one_tmul_injective_field K L
    apply e1.injective
    simp only [he1, hab]
  · apply one_tmul_injective_field K L
    apply e2.injective
    simp only [he2, hab]

theorem noPrimO2_axesO1_descend : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  intro K L _ _ _ A _ B _ φ hφ hA
  have hpA : IsProper A.hom := hA.proper
  have hpAA : IsProper (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨Φ, hΦ, hμ, hf, hs, ha1, ha2⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback K L (algebraMap K L) A B φ hφ
  have injA := pullHO_injective_field K L A.left B.left A.hom B.hom φ hφ.1 inferInstance inferInstance
  have injAA := pullHO_injective_field K L (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom Φ hΦ
    inferInstance inferInstance
  have N := pull_over_baseChange_comm K L (algebraMap K L)
  refine ⟨fun hB z hz ↦ ?_, fun hB y h1 h2 ↦ ?_⟩
  · apply injA.2
    rw [map_zero]
    apply hB
    have e := congrArg (pullHO2 hΦ.w) hz
    rw [map_add] at e
    rw [← (N A (A ⊗ A) B (B ⊗ B) μ[A] μ[B] φ Φ hφ.1.w hΦ.w hμ).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (fst A A) (fst B B) φ Φ hφ.1.w hΦ.w hf).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (snd A A) (snd B B) φ Φ hφ.1.w hΦ.w hs).2]
    exact e
  · apply injAA.1
    rw [map_zero]
    apply hB
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha1).1, h1, map_zero]
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha2).1, h2, map_zero]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectDeterminedOverArtinianPinch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegPinch

theorem glue_hom : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y Z : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (k₁ : Y₁.left ⟶ Z.left) (k₂ : Y₂.left ⟶ Z.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → Flat Z.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback k₁ Y₁.hom Z.hom (Spec.map f₁) → IsPullback k₂ Y₂.hom Z.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → i₁ ≫ j₁ = i₂ ≫ j₂ → i₁ ≫ k₁ = i₂ ≫ k₂ → ∃ φ : Y.left ⟶ Z.left, IsPullback φ Y.hom Z.hom (𝟙 _) ∧ j₁ ≫ φ = k₁ ∧ j₂ ≫ φ = k₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Z Y₁ Y₂ Y₀ j₁ j₂ k₁ k₂ i₁ i₂ hY hZ pj₁ pj₂ pk₁ pk₂ pi₁ w₂ ej ek
  have poY := GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hY pj₁ pj₂ pi₁ ej w₂
  have poZ := GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Z Y₁ Y₂ Y₀ k₁ k₂ i₁ i₂ hZ pk₁ pk₂ pi₁ ek w₂
  let φ : Y.left ⟶ Z.left := poY.desc k₁ k₂ ek
  let ψ : Z.left ⟶ Y.left := poZ.desc j₁ j₂ ej
  have h₁ : φ ≫ ψ = 𝟙 _ := poY.hom_ext
    (by rw [← Category.assoc, poY.inl_desc, poZ.inl_desc, Category.comp_id])
    (by rw [← Category.assoc, poY.inr_desc, poZ.inr_desc, Category.comp_id])
  have h₂ : ψ ≫ φ = 𝟙 _ := poZ.hom_ext
    (by rw [← Category.assoc, poZ.inl_desc, poY.inl_desc, Category.comp_id])
    (by rw [← Category.assoc, poZ.inr_desc, poY.inr_desc, Category.comp_id])
  have hw : φ ≫ Z.hom = Y.hom ≫ 𝟙 _ := poY.hom_ext
    (by rw [Category.comp_id, ← Category.assoc, poY.inl_desc, pk₁.w, pj₁.w])
    (by rw [Category.comp_id, ← Category.assoc, poY.inr_desc, pk₂.w, pj₂.w])
  haveI : IsIso φ := ⟨ψ, h₁, h₂⟩
  exact ⟨φ, IsPullback.of_horiz_isIso ⟨hw⟩, poY.inl_desc _ _ _, poY.inr_desc _ _ _⟩

section Tools

variable {h n : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem srelBy_comp {c : SiegPre h n ζ s} {c' : SiegPre h n ζ' s'} {c'' : SiegPre h n ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left}
    (m : SRelBy c' c 1 1 f φ) (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  simp only [pow_one] at hl hl' ⊢
  refine ⟨hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ ψ₂)
  · simp only [pow_one]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem sq_ext {S : Scheme.{0}} (A : Over S) {X : Scheme.{0}} {a b : X ⟶ (G2 A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem isPullback_sq {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}
    (hp : IsPullback β G'.hom G.hom f) {β₂ : (G2 G').left ⟶ (G2 G).left} (hs : IsSquare β β₂) :
    IsPullback β₂ (G2 G').hom (G2 G).hom f := by
  have e : β₂ = (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left := by
    apply sq_ext
    · rw [hs.1]; exact (congrArg (fun q => q.left) (lift_fst (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))).symm
    · rw [hs.2]; exact (congrArg (fun q => q.left) (lift_snd (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))).symm
  rw [e]
  exact GlobalTheory.Mum.PowCart.isPullback_two hp

theorem sq_comp {G : Over S} {G' : Over S'} {G'' : Over S''} {β : G'.left ⟶ G.left} {β' : G''.left ⟶ G'.left}
    {β₂ : (G2 G').left ⟶ (G2 G).left} {β₂' : (G2 G'').left ⟶ (G2 G').left} (hs : IsSquare β β₂) (hs' : IsSquare β' β₂') :
    IsSquare (β' ≫ β) (β₂' ≫ β₂) :=
  ⟨by rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc],
   by rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]⟩

theorem sq_unique {G : Over S} {G' : Over S'} {β : G'.left ⟶ G.left} {β₂ β₂' : (G2 G').left ⟶ (G2 G).left}
    (hs : IsSquare β β₂) (hs' : IsSquare β β₂') : β₂ = β₂' :=
  sq_ext G (hs.1.trans hs'.1.symm) (hs.2.trans hs'.2.symm)

end Tools

theorem siegPB_of_pinch : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c c' : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c.Principal → c'.Principal → SiegPB c₁ c (Spec.map f₁) → SiegPB c₁ c' (Spec.map f₁) → SiegPB c₂ c (Spec.map f₂) → SiegPB c₂ c' (Spec.map f₂) → SiegPB c' c (𝟙 _) := by
  intro g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ β c c' c₁ c₂ hc hc' m₁ m₁' m₂ m₂'
  have hn0 : n ≠ 0 := by omega
  have hbase : Spec.map g₁ ≫ Spec.map f₁ = Spec.map g₂ ≫ Spec.map f₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hpb.w]
  obtain ⟨c₀, m₀⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) (Spec R₁) (Spec R₀) (Spec.map f₁ ≫ Spec.map β)
    (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β) (Spec.map g₁) rfl (by simp [spMap])).1 c₁
  have m₀₂ : SiegPB c₀ c₂ (Spec.map g₂) := by
    have := GlobalTheory.SiegelPullComp.pb_comp m₁' m₀
    rw [hbase] at this
    exact GlobalTheory.SiegelPullComp.pb_cancel m₂' this
  obtain ⟨ρ₁, r₁⟩ := (sRel_one_one_iff _ _ _).2 m₀
  obtain ⟨ρ₂, r₂⟩ := (sRel_one_one_iff _ _ _).2 m₀₂
  obtain ⟨ψ₁, q₁⟩ := (sRel_one_one_iff _ _ _).2 m₁
  obtain ⟨ψ₁', q₁'⟩ := (sRel_one_one_iff _ _ _).2 m₁'
  obtain ⟨ψ₂, q₂⟩ := (sRel_one_one_iff _ _ _).2 m₂
  obtain ⟨ψ₂', q₂'⟩ := (sRel_one_one_iff _ _ _).2 m₂'
  have e' : ρ₁ ≫ ψ₁' = ρ₂ ≫ ψ₂' :=
    GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) _ _ _ _ c' c₀ _ _ _
      hn hodd hc' (srelBy_comp q₁' r₁) (by rw [hbase]; exact srelBy_comp q₂' r₂)
  have e : ρ₁ ≫ ψ₁ = ρ₂ ≫ ψ₂ :=
    GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) _ _ _ _ c c₀ _ _ _
      hn hodd hc (srelBy_comp q₁ r₁) (by rw [hbase]; exact srelBy_comp q₂ r₂)
  have hfl : Flat c.A.hom := by have := c.ab.smooth; infer_instance
  have hfl' : Flat c'.A.hom := by have := c'.ab.smooth; infer_instance
  obtain ⟨φ, hφp, hφ₁, hφ₂⟩ := glue_hom P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ c'.A c.A c₁.A c₂.A c₀.A ψ₁' ψ₂' ψ₁ ψ₂
    ρ₁ ρ₂ hfl' hfl q₁'.1.1 q₂'.1.1 q₁.1.1 q₂.1.1 r₁.1.1 r₂.1.1.w e' e
  have hφ : IsGrpPullback c'.A c.A (𝟙 _) φ := GlobalTheory.T.isGrpPullback_id_of_baseChanges_artinFibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ c'.A c.A c₁.A c₂.A c₀.A
    ψ₁' ψ₂' ψ₁ ψ₂ ρ₁ ρ₂ φ hfl' q₁'.1 q₂'.1 q₁.1 q₂.1 r₁.1 r₂.1 e' hφp hφ₁ hφ₂
  let φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left := (lift (pushPt hφ.1.w (fst c'.A c'.A)) (pushPt hφ.1.w (snd c'.A c'.A))).left
  have sq : IsSquare φ φ₂ := ⟨congrArg (fun q => q.left) (lift_fst (pushPt hφ.1.w (fst c'.A c'.A)) (pushPt hφ.1.w (snd c'.A c'.A))),
    congrArg (fun q => q.left) (lift_snd (pushPt hφ.1.w (fst c'.A c'.A)) (pushPt hφ.1.w (snd c'.A c'.A)))⟩
  refine ⟨φ, φ₂, hφ, sq, ?_, fun a => ?_⟩
  · obtain ⟨χ₁', sχ₁', wχ₁'⟩ := q₁'.2.1
    obtain ⟨χ₁, sχ₁, wχ₁⟩ := q₁.2.1
    obtain ⟨χ₂', sχ₂', wχ₂'⟩ := q₂'.2.1
    obtain ⟨χ₂, sχ₂, wχ₂⟩ := q₂.2.1
    obtain ⟨τ₁, sτ₁, -⟩ := r₁.2.1
    obtain ⟨τ₂, sτ₂, -⟩ := r₂.2.1
    have eτ : τ₁ ≫ χ₁' = τ₂ ≫ χ₂' := by
      have h1 := sq_comp sχ₁' sτ₁
      have h2 := sq_comp sχ₂' sτ₂
      rw [e'] at h1
      exact sq_unique h1 h2
    have eχ₁ : χ₁' ≫ φ₂ = χ₁ := by
      have h1 := sq_comp sq sχ₁'
      rw [hφ₁] at h1
      exact sq_unique h1 sχ₁
    have pχ₁' := isPullback_sq q₁'.1.1 sχ₁'
    have pχ₂' := isPullback_sq q₂'.1.1 sχ₂'
    have pτ₁ := isPullback_sq r₁.1.1 sτ₁
    have pτ₂ := isPullback_sq r₂.1.1 sτ₂
    have hflat2 : Flat (G2 c'.A).hom := by
      have := hfl'
      exact GlobalTheory.ExtUnique.flat_tensorObj c'.A c'.A
    obtain ⟨hpatch, huniq⟩ := GlobalTheory.T.existsUnique_units_glue_artinFibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (G2 c'.A) (G2 c₁.A) (G2 c₂.A) (G2 c₀.A)
      χ₁' χ₂' τ₁ τ₂ hflat2 pχ₁' pχ₂' pτ₁ eτ pτ₂.w
    have hab₀ : IsAbelianScheme (G2 c₀.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ c₀.ab c₀.ab
    have hlift := GlobalTheory.T.abelianScheme_units_lift_artinPinch P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (G2 c₀.A) hab₀ (G2 c₁.A).left (G2 c₁.A).hom τ₁ pτ₁.w
    have hL' := c'.isLB
    have hM : (c.P.pull φ₂).IsLB := pull_isLB c.isLB φ₂
    have key := GlobalTheory.SmallGlue.cech_patching χ₁' χ₂' τ₁ τ₂ eτ hlift hpatch huniq
      (GlobalTheory.CechPic.cls c'.P hL' - GlobalTheory.CechPic.cls _ hM) ?_ ?_
    · exact (GlobalTheory.CechPic.cls_eq_iff hL' hM).1 (sub_eq_zero.1 key)
    · rw [map_sub, ← GlobalTheory.CechPic.cls_pull hL' χ₁' (pull_isLB hL' _), ← GlobalTheory.CechPic.cls_pull hM χ₁' (pull_isLB hM _),
        sub_eq_zero, GlobalTheory.CechPic.cls_eq_iff]
      refine LBIso.trans (pull_isLB hL' _) c₁.isLB (pull_isLB hM _) wχ₁'.symm ?_
      refine LBIso.trans c₁.isLB (pull_isLB c.isLB _) (pull_isLB hM _) wχ₁ ?_
      rw [← eχ₁]
      exact (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ χ₁').symm
    · have eχ₂ : χ₂' ≫ φ₂ = χ₂ := by
        have h1 := sq_comp sq sχ₂'
        rw [hφ₂] at h1
        exact sq_unique h1 sχ₂
      rw [map_sub, ← GlobalTheory.CechPic.cls_pull hL' χ₂' (pull_isLB hL' _), ← GlobalTheory.CechPic.cls_pull hM χ₂' (pull_isLB hM _),
        sub_eq_zero, GlobalTheory.CechPic.cls_eq_iff]
      refine LBIso.trans (pull_isLB hL' _) c₂.isLB (pull_isLB hM _) wχ₂'.symm ?_
      refine LBIso.trans c₂.isLB (pull_isLB c.isLB _) (pull_isLB hM _) wχ₂ ?_
      rw [← eχ₂]
      exact (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ χ₂').symm
  · have hpo := GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (Over.mk (𝟙 _)) (Over.mk (𝟙 _))
      (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Spec.map f₁) (Spec.map f₂) (Spec.map g₁) (Spec.map g₂)
      (by dsimp; infer_instance) (IsPullback.id_vert _) (IsPullback.id_vert _) (IsPullback.id_vert _) hbase (by simp)
    rw [Category.id_comp]
    have a₁ := q₁'.2.2 a
    have a₂ := q₁.2.2 a
    have a₃ := q₂'.2.2 a
    have a₄ := q₂.2.2 a
    simp only [pow_one] at a₁ a₂ a₃ a₄
    apply hpo.hom_ext
    · rw [← Category.assoc, ← a₁, Category.assoc, hφ₁, a₂]
    · rw [← Category.assoc, ← a₃, Category.assoc, hφ₂, a₄]

end GlobalTheory.SiegPinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigidStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_siegel_object_odd_level_rigid : ∀ (h n n' d' : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (c : SiegPre h n (b.ζ : B) s) (c' : SiegPre h n' ζ' s') (f : S' ⟶ S) (φ φ' : c'.A.left ⟶ c.A.left), 3 ≤ n → Odd n → c.Principal → SRelBy c' c d' 1 f φ → SRelBy c' c d' 1 f φ' → φ = φ' := by
  first | exact @GlobalTheory.SiegRigid.eq_of_sRelBy | exact GlobalTheory.SiegRigid.eq_of_sRelBy | (intros; apply GlobalTheory.SiegRigid.eq_of_sRelBy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPairStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productData_firstFactor_adjointPair : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  first | exact @GlobalTheory.MumProdAdj.adj_first_factor | exact GlobalTheory.MumProdAdj.adj_first_factor | (intros; apply GlobalTheory.MumProdAdj.adj_first_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegenerationFirstFactorAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd

theorem adj_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂
  obtain ⟨wM, hwM, hrig, hpsi⟩ := hS.w
  have hi₁ : IsMonHom i₁ := GlobalTheory.T.isMonHom_of_section_of_isIso_lift _ _ _ _ p₁ p₂ i₁ hS.hom₁ hS.hom₂ hS.lim e₁ e₂
  have m₁ := GlobalTheory.T.partialSum_comp_monHom_eq_partialSum _ _ _ _ 2 p₁ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁ (fun i => by
      fin_cases i
      · simp [e₁]
      · simp)
  have m₂ := GlobalTheory.T.partialSum_insert_killed_coordinate_comp _ _ _ _ p₂ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by simp [e₂])
  obtain ⟨w, hw, hval⟩ := GlobalTheory.T.exists_cubeBundle_iso_externalTensor_first_factor _ _ _ _ _ D.toPre.P.L D₁.toPre.P.L D₂.toPre.P.L D.toPre.P.isLB D₁.toPre.P.isLB
    D₂.toPre.P.isLB p₁ p₂ wM hwM _ _ m₁ m₂
  exact ⟨hi₁, hS.hom₁, fun y => GlobalTheory.T.latticeInclusion_first_factor_over_abelianInclusion _ _ _ _ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ y, fun z => (hS.c_pr₁ z).symm, w, hw,
    GlobalTheory.T.periods_sumDegenerationData_fst_cube_iso R I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ wM hwM hrig hpsi w hval⟩

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem isEmpty_cxPts_of_algebra_zmod {k : Type} [CommRing k] {Y : Scheme.{0}} (q : Y ⟶ Sp k)
    (l : ℕ) [Fact l.Prime] (_ : Algebra (ZMod l) Γ(Y, ⊤)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : ZMod l →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp
    (y.1.appTop.hom.comp (algebraMap (ZMod l) Γ(Y, ⊤)))
  have h := map_natCast f l
  rw [ZMod.natCast_self, map_zero] at h
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h.symm

theorem amb_vertical_or_arithVar : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → (∃ (l : ℕ) (_ : Fact l.Prime), Nonempty (Algebra (ZMod l) Γ(Y, ⊤)) ∧ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) ∨ ∃ e : ℕ, d = e + 1 ∧ IsArithVar q e := by
  intro k _ Y _ q hq d hd
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · have : Fact ℓ.Prime := ⟨hℓ⟩
    exact .inl ⟨ℓ, this, ⟨ZMod.algebra _ ℓ⟩, fun σ => isEmpty_cxPts_of_algebra_zmod q ℓ (ZMod.algebra _ ℓ) σ⟩
  · have hc := CharP.charP_to_charZero Γ(Y, ⊤)
    obtain _ | e := d
    · exact absurd (by simpa using hd) (dim_ne_zero_of_isProjOver q hq.isProjOver hq.finite hc)
    · exact .inr ⟨e, rfl, hq.isDomain, hq.finite, ‹_›, hq.isProjOver,
        (flat_int_iff_charZero _).2 hc, hd⟩

end GlobalTheory.MixHt
end


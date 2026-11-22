import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitUniformisationMumfordBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TraitUnif

theorem exists_generic_fibre_pull : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), Function.Injective φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (AW : PolAV (Sp (FractionRing W))) (genW : ((Over.pullback (jK W)).obj ((Over.pullback (spMap φ)).obj G)) ≅ AW.A) (κ₁ : pullback ((Over.pullback (spMap φ)).obj G).hom (jK W) ⟶ pullback G.hom (jK R)), IsMonHom genW.hom ∧ κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst ((Over.pullback (spMap φ)).obj G).hom (jK W) ≫ pullback.fst G.hom (spMap φ) ∧ LBIso (AW.L.pull genW.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ A gen hgen
  haveI : IsMonHom gen.hom := hgen
  set gφ := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ with hgφ
  have hsq : jK W ≫ spMap φ = spMap gφ ≫ jK R := by
    simp only [hgφ, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  let GV := (Over.pullback (spMap φ)).obj G
  have hβ := isGrpPullback_pullback G (spMap φ)
  let κ₁ : pullback GV.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ)) (pullback.snd GV.hom (jK W) ≫ spMap gφ)
      (by rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ) :=
    pullback.lift_fst _ _ _
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GV).hom ≫ spMap gφ :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GV) ((Over.pullback (jK R)).obj G) (spMap gφ) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GV (jK W)).comp hβ).congr hsq hκf.symm) w
  have hκA : IsGrpPullback ((Over.pullback (jK W)).obj GV) A.A (spMap gφ) (κ₁ ≫ gen.hom.left) :=
    (hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  obtain ⟨P', g, hg, -, hmul, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap gφ) A
  have hP' : IsGrpPullback P'.A A.A (spMap gφ) g := by
    refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
    have ex : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]
    rfl
  obtain ⟨e, he, heq⟩ := grpPullback_iso hκA hP'
  refine ⟨P', e, κ₁, he, hκf, ?_⟩
  have h1 : LBIso (P'.L.pull e.hom.left) ((A.L.pull g).pull e.hom.left) :=
    GlobalTheory.FamRep.lbIso_pull (LBIso.symm ⟨t, ht⟩) _
  have h2 : LBIso ((A.L.pull g).pull e.hom.left) (A.L.pull (e.hom.left ≫ g)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB g e.hom.left
  have h3 : LBIso ((A.L.pull gen.hom.left).pull κ₁) (A.L.pull (κ₁ ≫ gen.hom.left)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB gen.hom.left κ₁
  rw [heq] at h2
  exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB (pull_isLB A.isLB _) _) h1
    (LBIso.trans (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) h2 h3.symm)

theorem extLam_pull_square : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)), IsGrpPullback G₁ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst G₁.hom (jK R') ≫ β → ∀ (L : LB ((Over.pullback (jK R)).obj G).left) (N : LB ((Over.pullback (jK R')).obj G₁).left) (PP : LB (G2 G).left), L.IsLB → N.IsLB → LBIso N (L.pull κ₁) → ExtLam G L PP → ExtLam G₁ N (PP.pull β₂) := by
  intro R R' _ _ _ _ _ _ ρ hρ G _ _ G₁ _ _ β β₂ κ₁ hβ hsqβ hκf L N PP hL hN hNL hExt
  have hsq : jK R' ≫ spMap ρ =
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  have hκ : IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have H1 := Hκ L N _ PP g₂ hL hN hExt.1 hNL (hExt.2 g₂ hg₂)
  have e : β₂κ ≫ g₂ = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (β₂κ ≫ g₂) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      rw [Category.assoc, hg₂.1, ← Category.assoc, hsqκ.1, Category.assoc, hκf, Category.assoc, hsqβ.1,
        reassoc_of% hκ₂.1]
    · show (β₂κ ≫ g₂) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      rw [Category.assoc, hg₂.2, ← Category.assoc, hsqκ.2, Category.assoc, hκf, Category.assoc, hsqβ.2,
        reassoc_of% hκ₂.2]
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hExt.1 _) (pull_isLB (pull_isLB hExt.1 _) _) H1
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => e) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

theorem exists_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G (spMap φ) βW ∧ Geo.Tor.IsSquare βW βW₂ ∧ LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  have := hR.1.1
  have := hR.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨AV, genV, κ₁, hgenV, hκ, hLV⟩ := exists_generic_fibre_pull R V φ hφ G A gen hgen
  obtain ⟨βV₂, hsqV, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G _ _ (isGrpPullback_pullback G (spMap φ))
  have hExtV := extLam_pull_square R V φ hφ G _ _ βV₂ κ₁ (isGrpPullback_pullback G (spMap φ)) hsqV hκ _ _ PP
    (pull_isLB A.isLB _) (pull_isLB AV.isLB _) hLV hPP
  have hGV : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback (spMap φ) G hG
  obtain ⟨R', _, _, _, ρ, D₁, G₁, _, _, β, β₂, A₁, U₁, hR', hρ, hβ, hsq, hLam⟩ :=
    GlobalTheory.T.exists_uniformisation_finiteExt_sameMumfordBundle V hV _ hGV AV genV hgenV _ hExtV
  have hρloc : IsLocalHom ρ := RingHom.IsIntegral.isLocalHom hρ.2.2.to_isIntegral hρ.2.1
  refine ⟨R', _, _, _, ρ.comp φ, G₁, _, _, β ≫ pullback.fst G.hom (spMap φ), β₂ ≫ βV₂, D₁, A₁, U₁, hR',
    hρ.2.1.comp hφ, ?_, ?_, ?_, ?_⟩
  · exact RingHom.isLocalHom_comp ρ φ
  · refine (hβ.comp (isGrpPullback_pullback G (spMap φ))).congr ?_ rfl
    simp [spMap, Spec.map_comp]
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc, hsqV.1, ← Category.assoc, hsq.1, Category.assoc]
    · rw [Category.assoc, hsqV.2, ← Category.assoc, hsq.2, Category.assoc]
  · exact LBIso.trans (DVR.linComb_isLB _ U₁.LG.isLB _ _) (pull_isLB (pull_isLB hPP.1 _) _) (pull_isLB hPP.1 _) hLam
      (GlobalTheory.FamRep.lbIso_pull_pull hPP.1 βV₂ β₂)
end GlobalTheory.Mum.TraitUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtensionSiegelFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.PoincUnif

theorem exists_unif_finExt : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁]
    [IsLocalRing V₁], GlobalTheory.LN.CDvr V₁ → ∀ (y₁ : Sp (FractionRing V₁) ⟶ F.X) (A : PolAV (Sp (FractionRing V₁)))
    (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
    IsGrpPullback A.A F.univ.A y₁ α → IsSquare α α₂ → LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) →
    ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G] (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
    IsSemiAbelian G → IsMonHom gen.hom →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
        (fK : FractionRing V₁ →+* FractionRing W), GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
        ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (D : DegData W (maximalIdeal W))
          (A' : PolAV (Sp (FractionRing W))) (_ : Unif (maximalIdeal W) D A' G') (α' : A'.A.left ⟶ F.univ.A.left)
          (α₂' : (G2 A'.A).left ⟶ (G2 F.univ.A).left),
          IsSemiAbelian G' ∧ IsGrpPullback A'.A F.univ.A (spMap fK ≫ y₁) α' ∧ IsSquare α' α₂' ∧
          LBIso (abelian₂ A'.A A'.L) (F.univ.P.pull α₂') := by
  intro g n o _ ζ F V₁ _ _ _ hV y₁ A α α₂ hα hsq hL G _ _ gen hG hgen
  haveI : IsMonHom gen.hom := hgen
  have hdvr : IsDiscreteValuationRing V₁ := hV.1
  have hLgen : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  obtain ⟨PP, hPP⟩ := GlobalTheory.MumExt.exists_extLam V₁ G hG _ hLgen
  obtain ⟨R', _, _, _, ρ, D₁, G₁, _, _, β, β₂, A₁, U₁, hR', hρ, hβ, hβ₂, hPβ⟩ :=
    GlobalTheory.T.exists_uniformisation_finiteExt_sameMumfordBundle V₁ hV G hG A gen hgen PP hPP
  obtain ⟨-, hinj, hfin⟩ := hρ
  have hloc : IsLocalHom ρ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite V₁ R' := hfin
    exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_algebraMap
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hinj
  let fK : FractionRing V₁ →+* FractionRing R' := IsFractionRing.lift (K := FractionRing V₁) hinj'
  have hfK : ∀ a, fK (algebraMap V₁ _ a) = algebraMap R' _ (ρ a) := fun a =>
    IsFractionRing.lift_algebraMap _ _
  have hbase : jK R' ≫ spMap ρ = spMap fK ≫ jK V₁ := by
    have e : fK.comp (algebraMap V₁ (FractionRing V₁)) = (algebraMap R' (FractionRing R')).comp ρ :=
      RingHom.ext hfK
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom e.symm

  let g₁ : A₁.A.left ⟶ G₁.left := U₁.gen.inv.left ≫ pullback.fst G₁.hom (jK R')
  have hg₁ : IsGrpPullback A₁.A G₁ (jK R') g₁ := GlobalTheory.ThetaBaseChange.grp_generic U₁.toUnifPre
  have hgβ := hg₁.comp hβ
  have hfst : IsGrpPullback ((Over.pullback (jK V₁)).obj G) G (jK V₁) (pullback.fst G.hom (jK V₁)) :=
    isGrpPullback_pullback G (jK V₁)
  have hw : (g₁ ≫ β) ≫ G.hom = (A₁.A.hom ≫ spMap fK) ≫ jK V₁ := by
    have := hgβ.1.w
    simp only [Category.assoc] at this ⊢
    rw [← hbase]; exact this
  let ι' : A₁.A.left ⟶ ((Over.pullback (jK V₁)).obj G).left := hfst.1.lift (g₁ ≫ β) (A₁.A.hom ≫ spMap fK) hw
  have hι'f : ι' ≫ pullback.fst G.hom (jK V₁) = g₁ ≫ β := hfst.1.lift_fst _ _ _
  have hι's : ι' ≫ ((Over.pullback (jK V₁)).obj G).hom = A₁.A.hom ≫ spMap fK := hfst.1.lift_snd _ _ _
  have hι' : IsGrpPullback A₁.A ((Over.pullback (jK V₁)).obj G) (spMap fK) ι' :=
    IsGrpPullback.cancel hfst (hgβ.congr hbase hι'f.symm) hι's
  let ι : A₁.A.left ⟶ A.A.left := ι' ≫ gen.hom.left
  have hι : IsGrpPullback A₁.A A.A (spMap fK) ι :=
    (hι'.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  have hα' : IsGrpPullback A₁.A F.univ.A (spMap fK ≫ y₁) (ι ≫ α) := hι.comp hα

  obtain ⟨ι₂, hι₂⟩ : ∃ m, IsSquare ι m := ⟨_, GlobalTheory.LamPull.exists_isSquare hι.1.w⟩
  obtain ⟨ι'₂, hι'₂⟩ : ∃ m, IsSquare ι' m := ⟨_, GlobalTheory.LamPull.exists_isSquare hι'.1.w⟩
  obtain ⟨g₁₂, hg₁₂⟩ : ∃ m, IsSquare g₁ m := ⟨_, GlobalTheory.LamPull.exists_isSquare hg₁.1.w⟩
  obtain ⟨κ₂, hκ₂⟩ : ∃ m, IsSquare (G' := (Over.pullback (jK V₁)).obj G) (G := G) (pullback.fst G.hom (jK V₁)) m :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hfst.1.w⟩
  have sqc : ∀ {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
      {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left},
      IsSquare ψ ψ₂ → IsSquare φ φ₂ → IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := fun h' h =>
    ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
      by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩
  have hsq' := sqc hι₂ hsq
  have e₂ := GlobalTheory.LamPull.isSquare_unique (sqc hg₁₂ hβ₂) (hι'f ▸ sqc hι'₂ hκ₂)

  have hPPlb : PP.IsLB := hPP.1
  have hA₁L : LBIso A₁.L (U₁.LG.L.pull g₁) := by
    have hgi : U₁.gen.inv.left ≫ U₁.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    exact LBIso.chartPull (h := U₁.gen.inv.left) (chartPullSec A₁.L _ _ hgi)
      (chartPullSame U₁.LG.L _ (fun _ => pullback.fst G₁.hom (jK R')) _ _ fun _ => rfl) U₁.ext
  have lamLB : ∀ {S : Scheme.{0}} (X : Over S) [GrpObj X] [IsCommMonObj X] {M : LB X.left}, M.IsLB →
      (abelian₂ X M).IsLB := fun X _ _ M hM => DVR.linComb_isLB M hM _ _
  have s1 := GlobalTheory.LamPull.lbIso_lam_pull hg₁ U₁.LG.isLB A₁.isLB hA₁L hg₁₂
  have s2 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull hPβ g₁₂
  rw [e₂] at s2
  have s3 := (GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPPlb κ₂)) ι'₂).symm
  have s4 := hPP.2 κ₂ hκ₂
  have s5 := (GlobalTheory.RigidBundleGlue.LBIso.pull s4 ι'₂).symm
  have hιL : LBIso (A.L.pull ι) ((A.L.pull gen.hom.left).pull ι') :=
    (GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl hLgen) ι').symm
  have s6 := (GlobalTheory.LamPull.lbIso_lam_pull hι' hLgen (pull_isLB A.isLB ι) hιL hι'₂).symm
  have s7 := GlobalTheory.LamPull.lbIso_lam_pull hι A.isLB (pull_isLB A.isLB ι)
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A.isLB ι)) hι₂
  have s8 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull hL ι₂
  have t1 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ U₁.LG.isLB) _) (pull_isLB hPPlb _) s1 s2
  have t2 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB hPPlb _) (pull_isLB (pull_isLB hPPlb _) _) t1 s3
  have t3 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (pull_isLB hPPlb _) _) (pull_isLB (lamLB _ hLgen) _) t2 s5
  have t4 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ hLgen) _) (lamLB _ (pull_isLB A.isLB ι)) t3 s6
  have t5 := LBIso.trans (lamLB _ A₁.isLB) (lamLB _ (pull_isLB A.isLB ι)) (pull_isLB (lamLB _ A.isLB) _) t4 s7
  have t6 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ A.isLB) _) (pull_isLB F.univ.isLB _) t5 s8
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap ρ))
    haveI := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap ρ) G hG)
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ, fK, hR', hinj, hloc, hfin, hfK, G₁, inferInstance,
    inferInstance, D₁, A₁, U₁, ι ≫ α, _, hG₁, hα', hsq', t6⟩

end GlobalTheory.PoincUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendRegularThetaSectionAnyFractionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_regularThetaSection_any_fractionField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R K) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R K) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R K) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R K (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R K)) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  first | exact @GlobalTheory.UMin.ExtFrac.ext_any_frac | exact GlobalTheory.UMin.ExtFrac.ext_any_frac | (intros; apply GlobalTheory.UMin.ExtFrac.ext_any_frac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassNumberCentraliserTorusSeparable
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls

theorem exists_finset_cosets {A : Type} [Group A] (U₀ U : Subgroup A) (h : U.relIndex U₀ ≠ 0) :
    ∃ F : Finset A, ∀ u ∈ U₀, ∃ f ∈ F, f ∈ U₀ ∧ ∃ v ∈ U, u = f * v := by
  haveI : (U.subgroupOf U₀).FiniteIndex := ⟨h⟩
  haveI : Finite (U₀ ⧸ U.subgroupOf U₀) := Subgroup.finite_quotient_of_finiteIndex
  haveI := Fintype.ofFinite (U₀ ⧸ U.subgroupOf U₀)
  refine ⟨Finset.univ.image (fun q : U₀ ⧸ U.subgroupOf U₀ => ((q.out : U₀) : A)), ?_⟩
  intro u hu
  set q : U₀ ⧸ U.subgroupOf U₀ := QuotientGroup.mk ⟨u, hu⟩
  refine ⟨((q.out : U₀) : A), Finset.mem_image_of_mem _ (Finset.mem_univ _), (q.out).2,
    ((q.out : U₀) : A)⁻¹ * u, ?_, by group⟩
  have h1 : (q.out)⁻¹ * ⟨u, hu⟩ ∈ U.subgroupOf U₀ := QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

end GlobalTheory.CentCls

namespace GlobalTheory.CentCls

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → ∀ (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∀ r : G.GAf × Gr G 1, ∃ R : Finset (G.GAf × Gr G 1), ∀ c : G.GAf × Gr G 1, c * (toAfF G β x t hx y₀, toP1 G β y₀) = (toAfF G β x t hx y₀, toP1 G β y₀) * c → ∃ y : grp G β, y * y₀ = y₀ * y ∧ ∃ s ∈ R, ∃ k : G.GAf × Gr G 1, k.1 ∈ L.K.toSubgroup ∧ k.2 ∈ K' ∧ c * r = (toAfF G β x t hx y, toP1 G β y) * s * k := by
  intro p hp G L K' hK' β x t hx hsh y₀ _ _ r
  obtain ⟨r₁, r₂⟩ := r
  obtain ⟨F₂, hF₂⟩ := exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hK'.1
  let ι : G.GAf →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
    { toFun := fun g => g, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let U₁ : Subgroup ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    ((L.K.toSubgroup.map (MulAut.conj r₁).toMonoidHom).map ι).comap (psiAway G x)
  let U₂ : Subgroup ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ) :=
    ((KHT p G.m G.n 1 G.Fw).map (MulAut.conj r₂).toMonoidHom).comap (psiP G)
  obtain ⟨O₁, hO₁, h1O₁, hO₁K⟩ :=
    exists_open_psiAway_mem_conj_level p G L β x t hx (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) r₁
  obtain ⟨O₂, hO₂, h1O₂, hO₂K⟩ := GlobalTheory.T.psi_p_neighborhood_in_level_subgroup p G r₂
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeCentraliser_classNumber_finite_borel G.C G.star (β : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) p
    (U₁.prod U₂) ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, ⟨h1O₁, h1O₂⟩,
      fun z hz hT1 _ => Subgroup.mem_prod.mpr ⟨by
        obtain ⟨k, hk, hk'⟩ := hO₁K z.1 hz.1 hT1
        exact Subgroup.mem_comap.mpr
          (Subgroup.mem_map.mpr ⟨r₁ * k * r₁⁻¹, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, hk'⟩), by
        have h2 := hO₂K z.2 hz.2
        refine Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨r₂⁻¹ * psiP G z.2 * r₂, h2, ?_⟩)
        show r₂ * (r₂⁻¹ * psiP G z.2 * r₂) * r₂⁻¹ = psiP G z.2
        group⟩⟩
  let Pf : G.Cˣ × ℚˣ → Prop := fun e =>
    (e.1 : G.C) * β * MulOpposite.unop (G.star e.1) = algebraMap ℚ G.C e.2 * β ∧
      Commute (e.1 : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
  let e₀ : G.Cˣ × ℚˣ := if h : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 then h.choose else 1
  let S' := S ∪ S.image (fun s => dg G.C p e₀ * s)
  let gOf : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ → G.GAf := fun w =>
    if h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w then h.choose else 1
  have hgOf : ∀ w (g : G.GAf), (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w →
      ((gOf w : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := by
    intro w g hg
    have h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := ⟨g, hg⟩
    simp only [gOf, dif_pos h]
    exact h.choose_spec
  refine ⟨(S' ×ˢ F₂).image (fun q => (gOf (psiAway G x q.1.1) * r₁, psiP G q.1.2 * r₂ * q.2)), ?_⟩
  intro c hc
  obtain ⟨c₁, c₂⟩ := c
  have hc1 : c₁ * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c₁ := congrArg Prod.fst hc
  have hc2 : c₂ * toP1 G β y₀ = toP1 G β y₀ * c₂ := congrArg Prod.snd hc
  have hz₁ := inT_psiAway_inv_of_commute p G β x t hx y₀ c₁ hc1
  obtain ⟨z₂, hz₂, hz₂c⟩ := GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split p G β hsh y₀ c₂ hc2
  obtain ⟨γ, hγf, hγc, s, hs, u, hu, hz⟩ := hS (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) hz₁ hz₂
  obtain ⟨γ', ⟨hγ'f, hγ'c⟩, hγ'pos, s', hs', hds⟩ : ∃ γ' : G.Cˣ × ℚˣ, Pf γ' ∧ (0 : ℚ) < (γ'.2 : ℚ) ∧
      ∃ s' ∈ S', dg G.C p γ * s = dg G.C p γ' * s' := by
    rcases lt_or_gt_of_ne (Units.ne_zero γ.2) with hneg | hpos
    · have hex : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 := ⟨γ, ⟨hγf, hγc⟩, hneg⟩
      have he₀ : e₀ = hex.choose := by simp only [e₀, dif_pos hex]
      obtain ⟨⟨he1, he2⟩, he3⟩ := hex.choose_spec
      refine ⟨γ * e₀⁻¹, ⟨?_, ?_⟩, ?_, dg G.C p e₀ * s,
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs), ?_⟩
      · rw [he₀]
        exact form_mul_inv G.star (β : G.C) γ.1 hex.choose.1 γ.2 hex.choose.2 hγf he1
      · rw [he₀]
        show Commute ((γ.1 * hex.choose.1⁻¹ : G.Cˣ) : G.C) _
        rw [Units.val_mul]
        exact hγc.mul_left he2.units_inv_left
      · rw [he₀]
        show (0 : ℚ) < ((γ.2 * hex.choose.2⁻¹ : ℚˣ) : ℚ)
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.mpr he3)
      · rw [map_mul, map_inv]
        group
    · exact ⟨γ, ⟨hγf, hγc⟩, hpos, s, Finset.mem_union_left _ hs, rfl⟩
  let y : grp G β := ⟨γ', hγ'f, hγ'pos⟩
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.mp hu
  obtain ⟨g, hg1, hg⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu1)
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg1
  obtain ⟨k₂, hk₂, hk₂e⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu2)
  obtain ⟨f, hf, -, v, hv, hkv⟩ := hF₂ k₂ hk₂
  have hz' : (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) = dg G.C p γ' * s' * u := by
    rw [hz, hds]
  have hz1 := congrArg Prod.fst hz'
  have hz2 := congrArg Prod.snd hz'
  simp only [Prod.fst_mul, Prod.snd_mul] at hz1 hz2
  have hc₁ : (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    simp [psiAway_apply, mul_assoc]
  have e1 : psiAway G x (dg G.C p γ').1 = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    (toAfF_eq_psiAway G β x t hx y).symm
  rw [hz1, map_mul, map_mul, e1, ← hg] at hc₁
  have hs1 : ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = psiAway G x s'.1 := by
    refine hgOf _ ((toAfF G β x t hx y)⁻¹ * c₁ * g⁻¹) ?_
    show ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)⁻¹ *
      (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * (ι g)⁻¹ = _
    rw [hc₁]
    group
  have hc₁' : c₁ = toAfF G β x t hx y * gOf (psiAway G x s'.1) * g := by
    apply Subtype.ext
    show (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) *
      ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * ι g
    rw [hs1]
    exact hc₁
  have e2 : psiP G (dg G.C p γ').2 = toP1 G β y := (formGroupToPadicPointsDegreeOne_eq_unitaryPoints G β y).symm
  have hc₂' : c₂ = toP1 G β y * psiP G s'.2 * (r₂ * k₂ * r₂⁻¹) := by
    rw [← hz₂c, hz2, map_mul, map_mul, e2, ← hk₂e]
    rfl
  have hg' : g = r₁ * k * r₁⁻¹ := hkg.symm
  have hmem : (s', f) ∈ S' ×ˢ F₂ := Finset.mem_product.mpr ⟨hs', hf⟩
  refine ⟨y, Subtype.ext (Prod.ext (Units.ext hγ'c.eq) (mul_comm _ _)), _,
    Finset.mem_image_of_mem _ hmem, (k, v), hk, hv, ?_⟩
  rw [hc₁', hg', hc₂', hkv]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> simp only [Prod.fst_mul, Prod.snd_mul] <;> group

end GlobalTheory.CentCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealDataThreeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteness_inputs_real_data_three : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  first | exact @GlobalTheory.LowRow.lamLow_closing | exact GlobalTheory.LowRow.lamLow_closing | (intros; apply GlobalTheory.LowRow.lamLow_closing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDivisorIntegralPushforwardStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_divisorIntegral_pushforward : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → IsProjOver q → topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv Y), (∀ z : X, Order.coheight z = 1 → ∑ᶠ (w : Y) (_ : π w = z), Δ'.mult w * (π.residueDegree w : ℤ) = Δ.mult z) → ∀ (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∑ᶠ w, (Δ'.mult w : ℝ) * cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L f z := by
  first | exact @GlobalTheory.Mix.finsum_cycInt_push | exact GlobalTheory.Mix.finsum_cycInt_push | (intros; apply GlobalTheory.Mix.finsum_cycInt_push <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultPullbackRationalSectionPushforwardStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_mult_pullback_rationalSection_pushforward : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), ∀ (B : LB X) (hB : B.IsLB) (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (φ : X → ℝ), ∑ᶠ w, ((divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr)).mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) = (g.residueDegree (genericPoint Y) : ℝ) * ∑ᶠ z, ((divOfRatSec hB hr).mult z : ℝ) * φ z := by
  first | exact @GlobalTheory.PushDiv.finsum_mult_pull | exact GlobalTheory.PushDiv.finsum_mult_pull | (intros; apply GlobalTheory.PushDiv.finsum_mult_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullSecondStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_pull_second : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ (ι : Type) (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (pullF hB hY σ π w φ * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (upperParabolic s m W)) = 0 := by
  first | exact @GlobalTheory.FibVan.fibre_integral_vanish | exact GlobalTheory.FibVan.fibre_integral_vanish | (intros; apply GlobalTheory.FibVan.fibre_integral_vanish <;> assumption)
end


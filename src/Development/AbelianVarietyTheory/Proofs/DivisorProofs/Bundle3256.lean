import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3239
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianHodge

theorem exists_isCompl_ker {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
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

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

theorem mem_F1_iff_supported (hO : Function.Injective (cmpO s)) (c : FirstDeRham s) :
    c ∈ F1 s ↔ cmp1 s c ∈ CechHodgeFiltration s := by
  change toH1O s c = 0 ↔ toHO1 s (cmp1 s c) = 0
  rw [structureSheaf_comparison_comm]
  exact ⟨fun h ↦ h ▸ map_zero _, fun h ↦ hO (h.trans (map_zero _).symm)⟩

theorem hodge_of_cmp (P : Submodule R (FirstDeRham s)) (hP : P = ⊤)
    (hb : Function.Bijective (cmp1 s)) (hO : Function.Injective (cmpO s)) (t : X ⟶ Sp R) (hst : s = t)
    (hcl : ClosedForm t = ⊤) (hinj : Function.Injective (clForm t))
    (hsurj : Function.Surjective (toHO1 t)) (hproj : Module.Projective R (HO1 t)) :
    (∃ N : Submodule R P, IsCompl ((F1 s).comap P.subtype) N) ∧
      Nonempty (((F1 s).comap P.subtype) ≃ₗ[R] GlobForm t) := by
  subst hst
  let E : P ≃ₗ[R] HH1 s := (LinearEquiv.ofTop P hP).trans (LinearEquiv.ofBijective (cmp1 s) hb)
  have hE : ∀ x : P, E x = cmp1 s x.1 := fun _ ↦ rfl
  have hc : (F1 s).comap P.subtype = (CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s) := by
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe, hE]
    exact mem_F1_iff_supported s hO x.1
  obtain ⟨N', hN'⟩ := exists_isCompl_ker (toHO1 s) hsurj
  refine ⟨⟨N'.comap (E : P →ₗ[R] HH1 s), ?_⟩, ⟨?_⟩⟩
  · rw [hc, Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm]
    exact (Submodule.orderIsoMapComap E.symm).isCompl hN'
  · let e1 : ((F1 s).comap P.subtype) ≃ₗ[R] ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)) :=
      LinearEquiv.ofEq _ _ hc
    let e2 : ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)) ≃ₗ[R] CechHodgeFiltration s :=
      E.ofSubmodules _ (CechHodgeFiltration s) (Submodule.map_comap_eq_of_surjective E.surjective _)
    let e3 : CechHodgeFiltration s ≃ₗ[R] LinearMap.range (clForm s) := LinearEquiv.ofEq _ _ (cechHodgeFiltration_eq_range s)
    let e4 : LinearMap.range (clForm s) ≃ₗ[R] ClosedForm s := (LinearEquiv.ofInjective (clForm s) hinj).symm
    let e5 : ClosedForm s ≃ₗ[R] GlobForm s := LinearEquiv.ofTop _ hcl
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

end GlobalTheory.AbelianHodge

namespace GlobalTheory.AbelianHodge

theorem abelianDeRham_hodge (P1 : GlobalTheory.Published.CrystallineSmoothLift) (P2 : GlobalTheory.Published.AbelianHodgeDeRham) :
    GlobalTheory.Published.AbelianDeRham.Hodge := by
  intro R _ A _ g hA hg
  obtain ⟨h0, -⟩ := GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison P1 P2) R A g hA hg
  obtain ⟨-, -, ⟨hGf, hGp, hGr⟩, ⟨-, hOp, -⟩, ⟨hcl, hinj, hsurj⟩, -⟩ := P2 R A g hA hg
  have := hA.smooth
  have := hA.proper
  obtain ⟨hb, -⟩ := cechDeRham_comparison_bijective_cup_smooth P1 R A.left (A.hom ≫ 𝟙 _) inferInstance inferInstance
    inferInstance
  have hO := GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 _)
  obtain ⟨⟨N, hN⟩, ⟨e⟩⟩ := hodge_of_cmp (A.hom ≫ 𝟙 _) (primDR A) h0 hb hO A.hom
    (Category.comp_id _) hcl hinj hsurj hOp
  exact ⟨GlobalTheory.T.hodgeLieSequence_exact_abelianScheme P1 P2 R A g hA hg, ⟨N, hN⟩, Module.Finite.equiv e.symm,
    Module.Projective.of_equiv e.symm, fun p ↦ by
      change Module.rankAtStalk ((F1 (A.hom ≫ 𝟙 _)).comap (primDR A).subtype) p = g
      rw [Module.rankAtStalk_eq_of_equiv e, hGr]⟩

end GlobalTheory.AbelianHodge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructureStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_of_forms_structure : FormSt → PrimitiveExtendedDegTwoVanish → AxesVanishingExtendedDegOne → UnobDim := by
  first | exact @GlobalTheory.Obs.unobDim_of_formSt | exact GlobalTheory.Obs.unobDim_of_formSt | (intros; apply GlobalTheory.Obs.unobDim_of_formSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyStructureSheafCohomologyAnyField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelian_HO_field_any : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧
      Module.finrank K (HO1 A.hom) = g ∧ WedgeO (OAff A.hom) ∧ NoPrimitiveStructureSheafH2 A ∧ AxesVanishingStructureSheafDegOne A := by
  intro K _ A _ g hab hsm
  let L := AlgebraicClosure K
  let σ : K →+* L := algebraMap K L
  have hpb : IsPullback (pullback.fst A.hom (spMap σ)) (pullback.snd A.hom (spMap σ)) A.hom (spMap σ) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨inst, hgp, habB, hsmB⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' K L σ A _ _ _ hpb
  have hB := @GlobalTheory.T.structureSheafCohomology_abelianVariety_algClosed L _ _ (Over.mk (pullback.snd A.hom (spMap σ))) inst g (habB hab) (hsmB g hsm)
  obtain ⟨hfin, hrk, hw, hnp, hax⟩ := hB
  obtain ⟨hfinA, hrkA⟩ := @GlobalTheory.T.structure_h1_rank_descends_field K L _ _ _ A _ _ inst _ hgp hab g hfin hrk
  obtain ⟨hnpA, haxA⟩ := @GlobalTheory.T.primitive_axes_descend_field K L _ _ _ A _ _ inst _ hgp hab
  exact ⟨hfinA, hrkA, @GlobalTheory.T.wedge_property_descends_field K L _ _ _ A _ _ inst _ hgp hab hw, hnpA hnp, haxA hax⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrablePolynomialVanishingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_integrable_polynomial_vanishing : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), GenSmooth q d → IsArithVar p D → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β → ∀ (L : α → HermLB p) (A : β → HermLB q) (M : HermLB p) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb (Sum.elim L fun a => (A a).pull f w) n).ArchIntegrable M D hr) → pol (fun n => (comb (Sum.elim L fun a => (A a).pull f w) n).archInt M D hr) = 0 := by
  first | exact @GlobalTheory.FibreProj.pol_archInt_pull_eq_zero | exact GlobalTheory.FibreProj.pol_archInt_pull_eq_zero | (intros; apply GlobalTheory.FibreProj.pol_archInt_pull_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanProjInclRationalStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_order_uniformization_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ) (φ : I → E →+* ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∃ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α := by
  first | exact @GlobalTheory.LatTorusAct.exists_unif_act_orderC | exact GlobalTheory.LatTorusAct.exists_unif_act_orderC | (intros; apply GlobalTheory.LatTorusAct.exists_unif_act_orderC <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePointAndExponentialHolomorphicInPeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basePoint_and_exponential_holomorphic_in_periods : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), 3 ≤ N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → C D' t → FullMark N D' t → IsOpen B → IsHolPeriods D' ρ B P → (∀ b ∈ B, UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b)) → IsHolTo B y ∧ IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
  first | exact @GlobalTheory.PELUHol.isHolTo_point_and_exp | exact GlobalTheory.PELUHol.isHolTo_point_and_exp | (intros; apply GlobalTheory.PELUHol.isHolTo_point_and_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamClassEqZeroOfPeriodsZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ x, IsPer u.ex u.Λ x 0 → x = 0 := by
  first | exact @GlobalTheory.CechPer.eq_zero_of_isPer_zero | exact GlobalTheory.CechPer.eq_zero_of_isPer_zero | (intros; apply GlobalTheory.CechPer.eq_zero_of_isPer_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionOfGeneratedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_eq_selfIntersection_of_generated : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  first | exact @GlobalTheory.chernInt_eq_topSelf_of_generated | exact GlobalTheory.chernInt_eq_topSelf_of_generated | (intros; apply GlobalTheory.chernInt_eq_topSelf_of_generated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.ClsOrb

theorem clsSum_eq_mass_mul_twOrb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → clsSum S K' f γ = mass (MonoidHom.id _) (ratFinU E n) (finPt γ) * twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) := by
  intro E _ _ _ hU n hn S hS lam K' hK' f hf γ hγ
  obtain ⟨hKo, hKc, hlev⟩ := GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel E hU n hn S hS K' hK'
  have hH := GlobalTheory.T.isHecke_productOfLocalTestFunctions_section E hU n hn S hS K' hK' f hf
  have hcomm := GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm E n γ hγ
  have hcpt := GlobalTheory.T.level_stabiliser_le_centraliser_compact_part E hU n hn S hS K' hK' γ hγ
  have hsupp := GlobalTheory.T.regularRationalPoint_testSupport_doubleCosets_finite E hU n hn S hS K' hK' f hf γ hγ
  have horb := GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel (finU E n) (MonoidHom.id _) (globLev S (KL n)) hKo hKc
    (fun k hk => hk) (globLev S K') hlev (finPt γ) (globFn S f) hH hcpt hsupp
  set T := twCent (MonoidHom.id (finU E n)) (finPt γ) with hT
  have hCT : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
  have hU' : ∀ x : finU E n, T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
      (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0 := fun x =>
    ⟨le_trans (inf_le_inf_left _ (Subgroup.map_mono hlev.2.1)) (hcpt x).1, (hcpt x).2⟩
  have hinv : ∀ t ∈ T, ∀ k ∈ globLev S K', ∀ x : finU E n,
      globFn S f ((t * x * k)⁻¹ * finPt γ * (t * x * k)) = globFn S f (x⁻¹ * finPt γ * x) := by
    intro t ht k hk x
    have ht' : t * finPt γ = finPt γ * t := ht
    have e1 : t⁻¹ * finPt γ * t = finPt γ := by
      rw [mul_assoc, ← ht', ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : (t * x * k)⁻¹ * finPt γ * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * finPt γ * t) * x) * k := by group
    rw [e2, e1, mul_assoc, (hH.2 k⁻¹ (inv_mem hk) _).1, (hH.2 k hk _).2]
  have hreg := GlobalTheory.T.finsum_doubleCoset_regroup_commutative (finU E n) T (ratFinU E n) (cptPart T) (globLev S K')
    (fun x => globFn S f (x⁻¹ * finPt γ * x)) hcomm hCT hU' hinv
  simp only [MonoidHom.id_apply] at horb
  rw [clsSum, horb.1, horb.2, hreg, mass]
  ring

end GlobalTheory.BCT.ClsOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetAbelianGalois
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CxPtSizes

theorem val_le_of_gen {E : Type} [Field E] [NumberField E] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ)
    (hl : (l : R) ∈ IsLocalRing.maximalIdeal R) (hl0 : (l : R) ≠ 0) (σ : E →+* FractionRing R) (ξ ξ' : E) (h0 : ξ' ≠ 0) (n : ℕ) (hn : IsUnit (n : R))
    (a : OF E) (h : (n : E) * ξ' = algebraMap (OF E) E a * ξ) :
    ξ ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ') := by
  have hn0 : (n : E) ≠ 0 := by
    intro h; have : n = 0 := by exact_mod_cast h
    subst this; simp at hn
  have hξ : ξ ≠ 0 := by rintro rfl; simp [hn0, h0] at h
  refine ⟨hξ, ?_⟩
  have hint : IsIntegral ℤ (algebraMap (OF E) E a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (IsScalarTower.toAlgHom ℤ (OF E) E)
  have hint2 : IsIntegral R (σ (algebraMap (OF E) E a)) :=
    IsIntegral.map_of_comp_eq (algebraMap ℤ R) σ (RingHom.ext_int _ _) hint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint2
  set v := (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) with hv
  have h1 : v (σ (algebraMap (OF E) E a)) ≤ 1 := hb ▸ HeightOneSpectrum.valuation_le_one _ _
  have h2 : v (σ (n : E)) = 1 := by
    have : σ (n : E) = algebraMap R (FractionRing R) (n : R) := by simp
    rw [this, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm hn
  have h3 : v (σ ξ') ≤ v (σ ξ) := by
    have := congrArg (fun x => v (σ x)) h
    simp only [map_mul, h2, _root_.one_mul] at this
    rw [this]; exact mul_le_of_le_one_left' h1
  have hs : σ ξ ≠ 0 := (map_ne_zero σ).2 hξ
  have hs' : σ ξ' ≠ 0 := (map_ne_zero σ).2 h0
  have hlK : (l : FractionRing R) = algebraMap R (FractionRing R) (l : R) := by simp
  have hlv : v (l : FractionRing R) < 1 := by rw [hlK, HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hl
  have hlv0 : v (l : FractionRing R) ≠ 0 := by
    rw [hlK]; exact (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hl0)
  have hpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (l : FractionRing R) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw; rw [← hv]; have := (WithZero.log_lt_log hlv0 one_ne_zero).2 hlv; simp at this; omega
  have hle : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ ξ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (σ ξ') := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw; rw [← hv]
    have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hs') ((Valuation.ne_zero_iff _).2 hs)).2 h3; omega
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, hs, hs', if_false, WithTop.coe_le_coe]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by exact_mod_cast hpos.le)

theorem scale_size : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt)
      (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      (∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x)) →
    ∀ (D : R) (cv : ℚ), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D)) = (cv : WithTop ℚ) → (cv : ℝ) = c_vp 𝔣 l →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
      (∀ i, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D))) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A) (w : I → ℂ), (∀ i, U.IsCMVec i (yv i) (w i)) →
      (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
      (∀ i, ((e i (hL.toLie X₀.rm (eH.symm (f' i))) : R) : ℂ) = a i * w i) →
    ∀ i, (Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2 ≠ 0 ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0)
        (a i * (a i * ((Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2) / (D : ℂ)) * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ := by
  intro hPC hADR hADC hPM E _ _ _ _ I _ d φ hFD 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hcm hα j hj φK hφK
    e a he hL n eH c₀ ψ₀ hc₀ hgen hpol hCM hψ₀ D cv hD hcv e' f' hgens hval m hm ψ hψ yv ev w hcmv hyc hec hew
  obtain ⟨ξ, hξgen, hrat⟩ := GlobalTheory.T.auxiliary_set_field_data_congruence hPC hADR hADC hPM E I d φ hFD 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK
    e a he hL n eH c₀ ψ₀ hc₀ hgen hpol hCM hψ₀ D cv hD hcv e' f' hgens hval m hm ψ hψ yv ev w hcmv hyc hec hew
  obtain ⟨j', hj', hchar, hlm, -, -, hSz⟩ := GlobalTheory.PlaceRingFacts.place_ring_facts E l lam R hR
  have hgenv : ξ ≠ 0 ∧ ∀ σ : E →+* FractionRing R, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ 0 := by
    have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
    obtain ⟨ξ', hp', hg'⟩ := (((hPM E hFD.2.2.1 I φ hFD.2.2.2.2.2.2.1 1).1 _ hc y).2.2.2 l Fact.out).1
    obtain ⟨h0', hv'⟩ := GlobalTheory.T.auxiliary_set_l_adic_place hPM E I d φ hFD 𝔣 h𝔣 l Q hQ hQl y hy lam R hR j hj ξ' 1 hp' hg'
    obtain ⟨n', hn', a', ha'⟩ := hξgen.2 ξ' hg'.1
    have hl0 : (l : R) ≠ 0 := by
      haveI := hchar; exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hu : IsUnit (n' : R) := by
      have hc := (Nat.isCoprime_iff_coprime.2 hn').map (Int.castRingHom R)
      simp only [eq_intCast, Int.cast_natCast] at hc
      obtain ⟨s, t, hst⟩ := hc
      by_contra hnu
      have : (1 : R) ∈ IsLocalRing.maximalIdeal R := hst ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 hnu)) (Ideal.mul_mem_left _ _ hlm)
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
    exact ⟨by rintro rfl; have : (n' : E) ≠ 0 := (fun h => by have : n' = 0 := (by exact_mod_cast h); subst this; simp at hu); simp [this, h0'] at ha',
      fun σ => (val_le_of_gen R l hlm hl0 σ ξ ξ' h0' n' hu a' ha').2.trans (hv' σ)⟩
  obtain ⟨hξ0, hξv⟩ := hgenv
  have hjj : j' = j := IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun x => by simp [hj, hj'])
  subst hjj
  obtain ⟨δ, hδ2, hδφ⟩ := hFD.2.2.2.2.2.2.2
  have hdp : d.Prime := hFD.1
  intro i
  set P0 : R := ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) with hP0def
  obtain ⟨r, hr⟩ := hψ₀ i (e' i) (hgens i).1
  have hP0c : ((P0 : R) : ℂ) = ((r : R) : ℂ) * (a i * w i) := by
    rw [hP0def, hr, ← hew i]; push_cast; ring
  have vtop : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (0 : FractionRing R) = ⊤ := by simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp]
  have hD0 : D ≠ 0 := by
    rintro rfl; rw [map_zero, vtop] at hD; exact WithTop.top_ne_coe hD
  have hvP : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) P0) ≤ (cv : WithTop ℚ) := hD ▸ (hval i).2
  have hP00 : P0 ≠ 0 := by
    intro h0; rw [h0, map_zero, vtop] at hvP; exact absurd hvP (by simp)
  have hD0c : (D : ℂ) ≠ 0 := fun h => hD0 (Subtype.ext h)
  have hP0c0 : ((P0 : R) : ℂ) ≠ 0 := fun h => hP00 (Subtype.ext h)
  have hr0 : ((r : R) : ℂ) ≠ 0 := fun h => r.ne_zero (Subtype.ext h)
  have hφξ : φ i ξ ≠ 0 := (map_ne_zero (φ i)).2 hξ0
  obtain ⟨hh0, hrat'⟩ := hrat i
  have hhc : ((U.h i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh0
  have hψ0 : ψ (ev i) (yv i) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hrat'
    exact mul_ne_zero hhc hP0c0 hrat'.symm
  have haw : a i * w i ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hP0c; exact hP0c0 hP0c
  have ha0 : a i ≠ 0 := left_ne_zero_of_mul haw
  have hw0 : w i ≠ 0 := right_ne_zero_of_mul haw
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
    exact_mod_cast this.ne'
  refine ⟨?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpi hhc) (div_ne_zero hD0c hψ0)) (pow_ne_zero _ hw0)
  · have hunit : ∀ q : ℕ, q.Prime → q ≠ l → IsUnit (q : R) := by
      intro q hq hql
      haveI := Fact.mk hq
      have hv : 0 ≤ padicValRat l ((q : ℚ)⁻¹) := by
        rw [padicValRat.inv, padicValRat.of_nat, padicValNat_primes (Ne.symm hql)]; simp
      have hmem := hR.2.2.1 _ hv
      refine IsUnit.of_mul_eq_one (b := ⟨_, hmem⟩) (Subtype.ext ?_)
      have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
      simp [hq0]
    have hl0 : (l : R) ≠ 0 := by
      haveI := hchar; exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      have : ((d : ℕ) : E) = 0 := by simpa using hδ2
      exact hdp.ne_zero (by exact_mod_cast this)
    haveI := hchar
    have hvδ := GlobalTheory.T.valuation_sqrt_neg_prime E l R hlm hunit d hdp δ hδ2 (φK i)
    have hz := GlobalTheory.T.valuation_lower_bound_product R l hlm hl0 (algebraMap R (FractionRing R) P0) (φK i ξ) (φK i δ) r cv (if l = d then 1 / 2 else 0)
      ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hP00) ((map_ne_zero (φK i)).2 hξ0)
      ((map_ne_zero (φK i)).2 hδ0) hvP (hξv (φK i)) hvδ
    have hS := hSz _ (cv + if l = d then 1 / 2 else 0) (by simpa using hz)
    have hφj : ∀ t : E, j' (φK i t) = φ i t := fun t => by rw [← hφK i]; rfl
    have key : j' ((algebraMap R (FractionRing R) (r : R)) ^ 2 / (algebraMap R (FractionRing R) P0 * (φK i δ * φK i ξ))) =
        (a i * (a i * ((Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2) / (D : ℂ)) * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ := by
      have h2I : (2 * Complex.I * φ i ξ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hφξ
      have hψv : ψ (ev i) (yv i) = (U.h i : ℂ) * ((P0 : R) : ℂ) / (2 * Complex.I * φ i ξ) := eq_div_of_mul_eq h2I hrat'
      rw [map_div₀, map_pow, map_mul, map_mul, hj', hj', hφj, hφj, hδφ i, hψv, hP0c]
      field_simp
    have hcast : (((cv + if l = d then 1 / 2 else 0 : ℚ)) : ℝ) = c_vp 𝔣 l + if l = d then 1 / 2 else 0 := by
      rw [Rat.cast_add, hcv]; split_ifs <;> norm_num
    rw [← hcast, ← key]; exact hS

end GlobalTheory.CxPtSizes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodFromEllipticLatticeStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_period_from_elliptic_lattice : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf io 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∃ (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
        (U : Unif φ (lattice c y) 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
        X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p ∧
        (∀ i, U.h i ≠ 0 ∧ IsAlgebraic ℚ ((U.h i : ℂ) * (Real.sqrt d : ℝ))) ∧
        (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧
          a i ≠ 0 ∧ IsAlgebraic ℚ (a i * Ω₀)) ∧
        (∀ b : E, (∀ x ∈ lattice c y, b * x ∈ lattice c y) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
          ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) ∧
        ∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
          ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left := by
  first | exact @GlobalTheory.CMModel.exists_model_of_lattice | exact GlobalTheory.CMModel.exists_model_of_lattice | (intros; apply GlobalTheory.CMModel.exists_model_of_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionIsFormStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvaturePowerSum_transgression_isForm : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k, A.IsForm (fld A (powFld A G k)) ∧ A.IsForm (transFld A G G' k) := by
  first | exact @GlobalTheory.ChernCalc.PairForm.isForm_pow_trans | exact GlobalTheory.ChernCalc.PairForm.isForm_pow_trans | (intros; apply GlobalTheory.ChernCalc.PairForm.isForm_pow_trans <;> assumption)
end


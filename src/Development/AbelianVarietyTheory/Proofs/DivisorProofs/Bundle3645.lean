import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3642
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3622
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCohomologyProjectiveModule
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3638
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3632
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3643
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0016
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSepClosedResidueFieldPowerSeriesComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PreservesFiniteLimitsTensorLeftSheafify
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyEquivEllAdicCohomology
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocModuleUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemisimpleEndomorphismsConjOfCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantIffFrobeniusCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KilledOnGeometricTorsion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleFiniteFactorExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_finite_factor_exists : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  first | exact @GlobalTheory.BotFinRef.exists_match_finData | exact GlobalTheory.BotFinRef.exists_match_finData | (intros; apply GlobalTheory.BotFinRef.exists_match_finData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyEndomorphismEqMapLadic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

theorem charpoly_push_eq_map_charpoly (k : Type) [Field k] [IsAlgClosed k]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)] :
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom k) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with h | h
  · haveI : Fact p.Prime := ⟨h⟩
    exact GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charP p k B f
  · subst h
    haveI : CharZero k := CharP.charP_to_charZero k
    exact GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charZero k B f

theorem charpoly_push_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (f : A ⟶ A) [IsMonHom f] (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
      (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
      ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ A),
      (∀ j x y, ev j (x + y) = ev j x * ev j y) →
      (∀ j x, ev j (φ x) = ev j x ≫ f) →
      (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
      (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
      ∀ [Module.Finite k (HdR A)],
        LinearMap.charpoly (push (dp0 k) (𝟙 _) f) = (LinearMap.charpoly φ).map (Int.castRingHom k) := by
  intro k _ _ A _ _ hA f _ L _ _ _ φ l hl hlk ev hadd hφ hker him _
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k A hA
  let B : GlobalTheory.AV.AbVar k := ⟨A, hA, g, hg⟩
  let f' : B ⟶ B := GlobalTheory.AV.AbVar.Hom.mk (A := B) (B := B) f
  rw [GlobalTheory.T.l_power_torsion_endomorphism_evaluation k B f' L φ l hl hlk ev hadd hφ hker him]
  exact charpoly_push_eq_map_charpoly k B f'

end GlobalTheory.DeRham
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRhamStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_finite_free_reduces_to_deRham : ∀ (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (divided₂ hI) (spMap π) a; letI := tensorModule (dp0 k) (𝟙 _) a; Module.Finite Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ Module.Free Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ ∃ f : Crys (divided₂ hI) (spMap π) A₀ →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] HdR A₀, Function.Surjective f ∧ ∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ (Crys (divided₂ hI) (spMap π) A₀)) := by
  first | exact @GlobalTheory.CrysFree.crys_free_and_red | exact GlobalTheory.CrysFree.crys_free_and_red | (intros; apply GlobalTheory.CrysFree.crys_free_and_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCohomologyProjectiveModuleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_cohomology_projective_module : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k], (∀ (B₀ : Over (Sp (AlgebraicClosure k))) [GrpObj B₀] [IsCommMonObj B₀], IsAbelianScheme B₀ → ∀ b : OAct (𝓞 F) B₀, letI := tensorModule (dp0 (AlgebraicClosure k)) (𝟙 _) b; Module.Projective (AlgebraicClosure k ⊗[ℤ] 𝓞 F) (HdR B₀)) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a; Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  first | exact @GlobalTheory.HdRDescent.projective_of_algebraicClosure | exact GlobalTheory.HdRDescent.projective_of_algebraicClosure | (intros; apply GlobalTheory.HdRDescent.projective_of_algebraicClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHomologyClosedFibreSurjectiveKernel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HdRFibre

set_option maxHeartbeats 1000000 in

theorem fibre_baseChange : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  intro C₀ _ _ A₀ _ _ hA O _ a
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ A₀ hA
  obtain ⟨hFree, -, hBC, -, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hh := isGrpPullback_pullback A₀ (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))
  have hbc := (hBC C₀ A₀ g hA hg (IsLocalRing.ResidueField C₀) _ _ hh).1
  obtain ⟨hfin, hproj, -⟩ := hFree.prim hA hg
  haveI := Module.finitePresentation_of_projective C₀ (primDR A₀)
  haveI : Module.Free C₀ (primDR A₀) := Module.free_of_flat_of_isLocalRing
  refine ⟨hbc.bcMap, ?_, ?_, ?_⟩
  · intro h'
    let l : primDR A₀ →ₗ[C₀] IsLocalRing.ResidueField C₀ :=
      { toFun c := h' ((Published.AbelianDeRham.bcMor hh).pull c)
        map_add' c d := by rw [map_add, map_add]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh', hhl⟩ := Module.projective_lifting_property (Algebra.linearMap C₀ (IsLocalRing.ResidueField C₀)) l
      IsLocalRing.residue_surjective
    exact ⟨hh', hbc.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc := hbc.corr_iff.2 hx
    refine GlobalTheory.CrysFree.mem_smul_top_of_forall _ x fun c ↦ ?_
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (hc c).symm.trans (LinearMap.zero_apply _)
  · intro x h
    haveI := a.hom x
    haveI := (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).hom x
    refine hbc.corr_iff.1 ?_
    exact GrpMor.Corr.push (m := Published.AbelianDeRham.bcMor hh) (Published.AbelianDeRham.bcMor hh)
      (a.act x) ((OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).act x)
      (pullback.lift_fst _ _ _).symm (hbc.corr_iff.2 rfl)

end GlobalTheory.HdRFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpiPowOfIsAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.MulEpi

attribute [local instance] Over.cartesianMonoidalCategory

theorem epi_pow_of_isAbelianScheme (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (k : ℕ) (hk : 0 < k) : Epi ((𝟙 A) ^ k) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA k hk
  haveI : Epi ((𝟙 A) ^ k).left := Flat.epi_of_flat_of_surjective _
  exact (Over.forget S).epi_of_epi_map this

end GlobalTheory.UPel.HT.MulEpi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birigidified_kth_root_pullback_bundle : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), IsAbelianScheme A → IsAbelianScheme D → GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → IsMonHom h → 0 < k → IsUnit (k : Γ(Y, ⊤)) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  first | (exact @GlobalTheory.KthRoot.exists_birigid_kth_root) | (exact GlobalTheory.KthRoot.exists_birigid_kth_root) | (intros; apply GlobalTheory.KthRoot.exists_birigid_kth_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

def graphFil (A₀ : Over (Sp k)) [GrpObj A₀] (f : HdR A₀ →ₗ[k] HdR A₀) :
    Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) where
  carrier := {d | ∃ x ∈ Fil A₀, ∃ y ∈ Fil A₀, ∀ c : primDR A₀,
    d ((constMor A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c + y c)}
  add_mem' := by
    rintro d d' ⟨x, hx, y, hy, e⟩ ⟨x', hx', y', hy', e'⟩
    refine ⟨x + x', add_mem hx hx', y + y', add_mem hy hy', fun c => ?_⟩
    rw [LinearMap.add_apply, e, e']
    ext <;> simp <;> ring
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, fun c => by
    rw [LinearMap.zero_apply]
    ext <;> simp⟩
  smul_mem' := by
    rintro r d ⟨x, hx, y, hy, e⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, r.fst • y + r.snd • x,
      add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, e, smul_eq_mul]
    ext <;> simp <;> ring

variable {A₀ : Over (Sp k)} [GrpObj A₀]

theorem mem_graphFil {f : HdR A₀ →ₗ[k] HdR A₀} {d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀} :
    d ∈ graphFil A₀ f ↔ ∃ x ∈ Fil A₀, ∃ y ∈ Fil A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c + y c) := Iff.rfl

theorem isBC_constMor (hA : IsAbelianScheme A₀) : (constMor A₀).IsBC :=
  GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k k A₀ hA (SqExt.dual k).sq (constMor A₀)

theorem exists_crys (hA : IsAbelianScheme A₀) (u v : HdR A₀) :
    ∃ d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c) := by
  obtain ⟨d₁, h₁⟩ := (isBC_constMor hA).exists u
  obtain ⟨d₂, h₂⟩ := (isBC_constMor hA).exists v
  refine ⟨d₁ + (TrivSqZeroExt.inr (1 : k) : DualNumber k) • d₂, fun c => ?_⟩
  rw [LinearMap.add_apply, LinearMap.smul_apply, h₁ c, h₂ c]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

set_option maxHeartbeats 1000000 in

theorem crys_ext (hA : IsAbelianScheme A₀) {d d' : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀}
    (h : ∀ c : primDR A₀, d ((constMor A₀).pull c) = d' ((constMor A₀).pull c)) : d = d' := by
  refine LinearMap.ext fun c' => ?_
  obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c'
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

def coordOf (g : DualNumber k →ₗ[k] k) (d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) : HdR A₀ where
  toFun c := g (d ((constMor A₀).pull c))
  map_add' a b := by rw [map_add, map_add, map_add]
  map_smul' r a := by
    rw [map_smulₛₗ, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul]
    rfl

theorem exists_coords (d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) :
    ∃ u v : HdR A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c) := by
  refine ⟨coordOf (TrivSqZeroExt.fstHom k k k).toLinearMap d, coordOf (TrivSqZeroExt.sndHom k k) d, fun c => ?_⟩
  ext <;> simp [coordOf]

end GlobalTheory.HTRealise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualMapEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.TateHondaBridge

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AV GlobalTheory.AV.AbVar ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Published.AbVarRed

def toAbVar {k : Type} [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A] (hA : IsAbelianScheme A) :
    AbVar k where
  X := A
  ab := hA
  dim := (GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA).choose
  smooth := (GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA).choose_spec

end GlobalTheory.TateHondaBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoCompEqOfSiegRelBy
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.SiegFactor

theorem comp_id_pow {S : Scheme.{0}} {T A : Over S} [GrpObj A] (x : T ⟶ A) (k : ℕ) :
    x ≫ (𝟙 A) ^ k = x ^ k := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem id_pow_comp {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (χ : A ⟶ B) [IsMonHom χ]
    (k : ℕ) : ((𝟙 A) ^ k) ≫ χ = χ ≫ (𝟙 B) ^ k := by
  rw [MonObj.pow_comp, Category.id_comp, comp_id_pow]

theorem isMonHom_epi_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {k : ℕ}
    (hk : 0 < k) : IsMonHom ((𝟙 A) ^ k) ∧ Epi ((𝟙 A) ^ k) := by
  have := hA.comm
  have hm : IsMonHom ((𝟙 A) ^ k) := GlobalTheory.AbLaw.MulN.isMonHom_mulA A k
  obtain ⟨hfl, hsu, hqc⟩ := SiegUniqBase.flat_surjective_qc_pow S A hA k hk
  exact ⟨hm, (GlobalTheory.exists_monHom_factor_of_flat_surjective S A A A _ _ hm hm hfl hsu hqc
    fun _ _ h => h).2⟩

end GlobalTheory.UPel.HT.SiegFactor

namespace GlobalTheory.UPel.HT

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoOfSameKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SameKer

theorem exists_iso_of_sameKer : ∀ (Tb : Scheme.{0}) (G' B A' : Over Tb) [GrpObj G'] [GrpObj B] [GrpObj A'] (π' : G' ⟶ B) (χ₁ : A' ⟶ G') (χ₁' : G' ⟶ A') (k : ℕ), IsAbelianScheme A' → IsUnit (k : Γ(Tb, ⊤)) → IsMonHom π' → IsMonHom χ₁ → IsMonHom χ₁' → Flat π'.left → Surjective π'.left → QuasiCompact π'.left → χ₁ ≫ χ₁' = (𝟙 A') ^ k → (∀ (T : Over Tb) (x : T ⟶ G'), x ≫ χ₁' = 1 ↔ x ≫ π' = 1) → ∃ β : A' ⟶ B, IsIso β ∧ IsMonHom β ∧ χ₁' ≫ β = π' := by
  intro Tb G' B A' _ _ _ π' χ₁ χ₁' k hA hk hπ hχ hχ' fl su qc hcomp hker
  obtain ⟨⟨α, hα, hαeq⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Tb G' B A' π' χ₁' hπ hχ' fl su qc
    (fun T x hx => (hker T x).2 hx)
  have ker : ∀ (T : Over Tb) (x : T ⟶ B), x ≫ α = 1 → x = 1 := by
    intro T x hx
    have pb := (IsPullback.of_hasPullback x π').map (Over.forget Tb)
    have : Flat (pullback.fst x π').left := MorphismProperty.of_isPullback (P := @Flat) pb.flip fl
    have : Surjective (pullback.fst x π').left :=
      MorphismProperty.of_isPullback (P := @Surjective) pb.flip su
    have : Epi (pullback.fst x π').left := Flat.epi_of_flat_of_surjective _
    have : Epi (pullback.fst x π') := Over.epi_of_epi_left _
    have h1 : pullback.snd x π' ≫ χ₁' = 1 := by
      rw [← hαeq, ← Category.assoc, ← pullback.condition, Category.assoc, hx, MonObj.comp_one]
    have h2 := (hker _ _).1 h1
    rw [← cancel_epi (pullback.fst x π'), pullback.condition, h2, MonObj.comp_one]
  have hmono : Mono α := ⟨fun {Z} u v huv => by
    have h : (u * v⁻¹) ≫ α = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
    exact mul_inv_eq_one.1 (ker _ _ h)⟩
  obtain ⟨hkm, hkf, hke, hks⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective Tb A' k hA hk
  obtain ⟨⟨β, hβ, hβeq⟩, hepik⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Tb A' A' B ((𝟙 A') ^ k)
    (χ₁ ≫ π') hkm inferInstance inferInstance hks inferInstance (fun T x hx => by
      have h := (hker T (x ≫ χ₁)).1 (by rw [Category.assoc, hcomp, hx])
      rw [Category.assoc] at h
      exact h)
  have e1 : β ≫ α = 𝟙 A' := by
    rw [← cancel_epi ((𝟙 A') ^ k), ← Category.assoc, hβeq, Category.assoc, hαeq, hcomp, Category.comp_id]
  have e2 : α ≫ β = 𝟙 B := by
    rw [← cancel_mono α, Category.assoc, e1, Category.comp_id, Category.id_comp]
  refine ⟨β, ⟨⟨α, e1, e2⟩⟩, hβ, ?_⟩
  rw [← hαeq, Category.assoc, e2, Category.comp_id]

end GlobalTheory.SameKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosed
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDivPt

theorem exists_pow_eq_of_isAlgClosed : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n →
      ∀ g : Over.mk x ⟶ A, ∃ g' : Over.mk x ⟶ A, g' ^ n = g := by
  intro S A _ hA k _ _ x n hn g
  have hc := hA.comm
  obtain ⟨hfin, -, hsurj⟩ := GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S A hA n hn
  have : IsFinite (pullback.snd (mulN A n).left g.left) := by
    haveI := hfin; infer_instance
  have : Surjective (pullback.snd (mulN A n).left g.left) := by
    haveI := hsurj; infer_instance
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (pullback.snd (mulN A n).left g.left)
  have hb' : (t ≫ pullback.fst (mulN A n).left g.left) ≫ (mulN A n).left = g.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulN A n).left g.left) ≫ A.hom = (Over.mk x).hom := by
    rw [← Over.w (mulN A n), ← Category.assoc, hb', Over.w g]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk x ⟶ A, b ^ n = b ≫ mulN A n := fun b => by
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
  rw [e]
  exact Over.OverMorphism.ext hb'

end GlobalTheory.AbDivPt
end
end


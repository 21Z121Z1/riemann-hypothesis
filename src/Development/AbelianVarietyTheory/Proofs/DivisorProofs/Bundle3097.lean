import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionDescendsFromAlgClosedField
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsSurjectiveOfLargerAlgClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabels_surjective_of_larger_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (N : ℕ), 1 ≤ N → ∀ (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)), LabExt em lab lab' → (∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x) → ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x := by
  first | exact @GlobalTheory.Mum.Desc.lab_onto_of_labExt | exact GlobalTheory.Mum.Desc.lab_onto_of_labExt | (intros; apply GlobalTheory.Mum.Desc.lab_onto_of_labExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointSectionAlongSpreadingTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusPointSection_along_spreadingTrait : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁] (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂] (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left) (ρ : D₂.toPre.X →+ D₁.toPre.X), Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (c : D₁.toPre.X →+ ℤ), (∀ (κ : Type) [Field κ] (b : V₁ →+* κ) (hb : ∀ y ∈ maximalIdeal V₁ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G₁.left) (hm : IsGrpPullback Gκ G₁ (spMap b) m) (τ : Multiplicative D₁.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₁ ζ) ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₁.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ ξ₁' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb hm).left ≫ m ≫ β₁) → ∃ (κ : Type) (_ : Field κ) (b : V₂ →+* κ) (hb : ∀ y ∈ maximalIdeal V₂ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) (_ : GrpObj Gκ) (m : Gκ.left ⟶ G₂.left) (hm : IsGrpPullback Gκ G₂ (spMap b) m) (τ : Multiplicative D₂.toPre.X →* κˣ) (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₂.toPre.X), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₂ ζ) ^ (c.comp ρ) χ) ∧ (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) ∧ spMap b ≫ ξ₂' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₂.gt 0) hb hm).left ≫ m ≫ β₂ := by
  first | exact @GlobalTheory.SpreadTorSection.trait_section | exact GlobalTheory.SpreadTorSection.trait_section | (intros; apply GlobalTheory.SpreadTorSection.trait_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapCommutesEndomorphismsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_spread_lattice_map_commutes_endomorphisms : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (Fm : H ⟶ H) (E₁ : EndU U₁.toUnifPre) (E₂ : EndU U₂.toUnifPre), E₁.aG.left ≫ β₁ = β₁ ≫ Fm.left → E₂.aG.left ≫ β₂ = β₂ ≫ Fm.left → ∀ y, ρ (E₂.h y) = E₁.h (ρ y) := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm | exact GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm | (intros; apply GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_spread_lattice_map_surjective : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → Function.Surjective ρ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.spread₂_surjective | exact GlobalTheory.Poinc.Sep.Spz.spread₂_surjective | (intros; apply GlobalTheory.Poinc.Sep.Spz.spread₂_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionDescendsFromAlgClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitExpansion_descends_from_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k) (c : F), c ≠ 0 → (∀ F₀, ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀) → (∀ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F₀, T.Exp a b (Φ F₀) F₀ := by
  first | exact @GlobalTheory.Mum.TraitDescent.exp_of_values | exact GlobalTheory.Mum.TraitDescent.exp_of_values | (intros; apply GlobalTheory.Mum.TraitDescent.exp_of_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionsSameFamilyProportionalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitExpansions_same_family_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (a₁ b₁ a₂ b₂ : W), T.Exp a₁ b₁ s₁ F → T.Exp a₂ b₂ s₂ F → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom (b₂ * a₁)) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom (b₁ * a₂)) * sval s₂ p' z J := by
  first | exact @GlobalTheory.Mum.Trait.exp_pair | exact GlobalTheory.Mum.Trait.exp_pair | (intros; apply GlobalTheory.Mum.Trait.exp_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitUniformisationPullbackFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitUniformisation_pullback_finiteExtension : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁]
    (ρ : R →+* R₁), Base R → FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D₁ : DegData R₁ (maximalIdeal R₁)),
    Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R₁))
    [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G₁ G (spMap ρ) β₁ →
    ∀ L : LB G.left, L.IsLB → UnifTrait D G L → UnifTrait D₁ G₁ (L.pull β₁) := by
  first | exact @GlobalTheory.Mum.TraitExt.unifTrait_pull | exact GlobalTheory.Mum.TraitExt.unifTrait_pull | (intros; apply GlobalTheory.Mum.TraitExt.unifTrait_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffCompHolomorphicJacobianSqStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgressionTopCoeff_comp_holomorphic_jacobian_sq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → DifferentiableAt ℝ ρ (φ w) → MContDiffAt 2 G₀ (φ w) → IsUnit (G₀ (φ w)).det → MContDiffAt 2 G₁ (φ w) → IsUnit (G₁ (φ w)).det → corrC (fun x => ρ (φ x)) (fun x => G₀ (φ x)) (fun x => G₁ (φ x)) w = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * corrC ρ G₀ G₁ (φ w) := by
  first | exact @GlobalTheory.GoodTop.corrC_comp_holo | exact GlobalTheory.GoodTop.corrC_comp_holo | (intros; apply GlobalTheory.GoodTop.corrC_comp_holo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTrait
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem GlobalTheory.ThetaMove.ptSec_transl' {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (p x : T ⟶ A) :
    (ptSecT A p).left ≫ (translT A x).left = (ptSecT A (x * p)).left := by
  rw [← Over.comp_left]
  congr 1
  rw [ptSecT, translT, comp_lift, lift_fst, ptSecT, translPt_eq, MonObj.comp_mul, lift_fst_assoc, Category.id_comp,
    lift_snd]

theorem GlobalTheory.ThetaMove.translT_inv {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) :
    (translT A x).left ≫ (translT A x⁻¹).left = 𝟙 _ ∧ (translT A x⁻¹).left ≫ (translT A x).left = 𝟙 _ := by
  constructor
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, inv_mul_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, mul_inv_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]

example (R : Type) [CommRing R] [IsDomain R] (W : Type) [CommRing W] [IsDomain W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] : jFK (R := W) F ≫ jK W = spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
  unfold jFK jK spMap
  rw [← Spec.map_comp]
  rfl

theorem GlobalTheory.ThetaMove.transport_symLift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A), (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left → x' ^ (C.n ^ j) = 1 → ((∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ') → ∃ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ) ∧ ∀ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ → ∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ' ∧ ∀ (σ σ' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j)) (τ τ' : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ' p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ' q z Jt) → IsActOf T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) θ' σ σ' → IsActOf C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) θ τ τ' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ hφ f hf hf1 hf2 w₀ hw₀ x' x hx hx'
  have hPL := C.P.L.isLB
  have hAL := C.A.isLB
  have hGL := T.U.LG.isLB
  have hTL := T.A.isLB
  have hgi : T.U.gen.inv.left ≫ T.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨w, hw, hgw⟩ := GlobalTheory.T.exists_lineBundleIso_restrict_along_section hGL hTL hgi w₀ hw₀
  have h₁ : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α =
      (snd (TFK (R := W) F) T.A.A).left ≫ (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.β := by
    rw [Category.assoc]; exact hf2
  have hT1 := GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 x' x hx
  have hneg := GlobalTheory.T.traitFibreIso_comm_neg C T F f hf1 hf2
  have hinv : f ≫ (translT C.A.A x⁻¹).left = (translT T.A.A x'⁻¹).left ≫ f := by
    calc f ≫ (translT C.A.A x⁻¹).left
        = ((translT T.A.A x'⁻¹).left ≫ (translT T.A.A x').left) ≫ f ≫ (translT C.A.A x⁻¹).left := by
          rw [(translT_inv x').2, Category.id_comp]
      _ = (translT T.A.A x'⁻¹).left ≫ (f ≫ (translT C.A.A x).left) ≫ (translT C.A.A x⁻¹).left := by
          rw [hT1]; simp only [Category.assoc]
      _ = (translT T.A.A x'⁻¹).left ≫ f := by
          rw [Category.assoc, (translT_inv x).1, Category.comp_id]
  have hpt : ∀ i : ℕ, (ptSecT T.A.A (x' ^ i)).left ≫ f = (ptSecT C.A.A (x ^ i)).left := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero, pow_zero, ← inv_mul_cancel x', ← inv_mul_cancel x, ← ptSec_transl', ← ptSec_transl',
        Category.assoc, ← hinv, ← Category.assoc, hx]
    | succ i ih =>
      rw [pow_succ', pow_succ', ← ptSec_transl', ← ptSec_transl', Category.assoc, ← hT1, ← Category.assoc, ih]
  have hpow : ∀ i : ℕ, f ≫ (translT C.A.A (x ^ i)).left = (translT T.A.A (x' ^ i)).left ≫ f :=
    fun i => GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 _ _ (hpt i)
  have hG0 : ((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.G.hom =
      (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    have e1 : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have e2 : (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom = (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F :=
      (Over.w (snd (TFK (R := W) F) T.A.A)).trans (Over.w (fst (TFK (R := W) F) T.A.A)).symm
    have e3 : jFK (R := W) F ≫ jK W = spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
      unfold jFK jK spMap
      rw [← Spec.map_comp]
      rfl
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc T.U.gen.inv.left, e1, ← Category.assoc,
      e2, Category.assoc, e3]
  let JPc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ C.G.left) → C.P.L.L.ι := fun z ψ => (exists_chart hPL (ψ z)).choose
  have gJP : ∀ {Z : Scheme.{0}} (z : Z), Good C.P.L.L z (JPc z) := fun z ψ => (exists_chart hPL (ψ z)).choose_spec
  let JGc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ T.G.left) → T.U.LG.L.ι := fun z ψ => (exists_chart hGL (ψ z)).choose
  have gJG : ∀ {Z : Scheme.{0}} (z : Z), Good T.U.LG.L z (JGc z) := fun z ψ => (exists_chart hGL (ψ z)).choose_spec
  let Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) → ∀ z : Z, ((Z ⟶ C.A.A.left) → C.A.L.ι) →
      ((Z ⟶ T.A.A.left) → T.A.L.ι) → (Z.presheaf.stalk z)ˣ := fun q z JA Jt =>
    tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left q z (JPc z) JA (JGc z) Jt
  have conv : ∀ (σ : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j))
      (τ : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) →
      ∀ (Z : Scheme.{0}) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) (z : Z) JA Jt, Good C.A.L z JA → Good T.A.L z Jt →
        sval τ (q ≫ f) z JA = (Ψ q z JA Jt ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt := by
    intro σ τ hr Z q z JA Jt hJA hJt
    have e := hr Z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) (q ≫ f) q
      rfl (by simp only [Category.assoc]; rw [hf2]) (by rw [Category.assoc, hG0]) z (JPc z) JA (JGc z) Jt (gJP z) hJA
      (gJG z) hJt
    simp only [Category.assoc] at e
    show sval τ (q ≫ f) z JA = ((tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left
      q z (JPc z) JA (JGc z) Jt) ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt
    simp only [tf, hgw, Category.assoc]
    rw [zpow_natCast, mul_pow, mul_pow, inv_pow, Units.val_mul, Units.val_mul]
    calc sval τ (q ≫ f) z JA
        = (((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left))) ^ (C.n ^ j))⁻¹).val *
          ((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ (q ≫ f) z JA) := by
          rw [← _root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.one_mul]
      _ = _ := by rw [e]; ring
  have hs₂ : ∀ p : TFK (R := W) F ⟶ T.A.A, (translT T.A.A p).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (translPt T.A.A p).left := fun p => by rw [← Over.comp_left, translT, lift_snd]
  have hn₂ : (negT T.A.A (TFK (R := W) F)).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left := by rw [← Over.comp_left, negT, lift_snd]
  have hn₃ : (negT T.A.A (TFK (R := W) F)).left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left =
      f ≫ (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left := by
    rw [← Category.assoc, ← hneg, Category.assoc, ← Over.comp_left, negT, lift_snd]
  have hs₃ : (translT T.A.A x').left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left = f ≫ (translPt C.A.A x).left := by
    rw [← Category.assoc, ← hT1, Category.assoc, ← Over.comp_left, translT, lift_snd]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨pt', φ', hφ'⟩, hs'⟩
    have e0 : pt' = x' := hs'.pt_eq
    subst e0
    obtain ⟨u, hu, hvu⟩ := GlobalTheory.T.exists_generator_moved_to_cover_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A x).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A pt').left (translT T.A.A pt').left h₁
      (hs₂ pt') hs₃ ((C.n ^ j : ℕ) : ℤ) φ' hφ'
    obtain ⟨ν', hν', hsym'⟩ := hs'.sym
    obtain ⟨ν, hν, hvν⟩ := GlobalTheory.T.exists_generator_moved_to_cover_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν' hν'
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x, u, hu⟩, ⟨rfl, corr_of_val hAL fun y J hJ => ?_, ν, hν, corr_of_val hAL fun y J hJ => ?_⟩⟩
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ Ψ hpow hx' Hu _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hs'.pow_eq (inv f), val_one, val_one]
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ ν ν' Ψ hinv hneg Hu Hν _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hsym' (inv f), val_one, val_one]
  · rintro ⟨pt, φ, hφ⟩ hs
    have e0 : pt = x := hs.pt_eq
    subst e0
    obtain ⟨u', hu', hvu'⟩ := GlobalTheory.T.exists_generator_moved_to_trait_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A pt).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A x').left (translT T.A.A x').left h₁
      (hs₂ x') hs₃ ((C.n ^ j : ℕ) : ℤ) φ hφ
    obtain ⟨ν, hν, hsym⟩ := hs.sym
    obtain ⟨ν', hν', hvν'⟩ := GlobalTheory.T.exists_generator_moved_to_trait_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν hν
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x', u', hu'⟩, ⟨rfl, corr_of_val hTL fun y J' hJ' => ?_, ν', hν', corr_of_val hTL fun y J' hJ' => ?_⟩, ?_⟩
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hpow hx' Hu _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hs.pow_eq, val_one, val_one]
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ ν ν' Ψ hinv hneg Hu Hν _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hsym, val_one, val_one]
    · intro σ σ' τ τ' hr hr' hact
      exact GlobalTheory.T.thetaGroupAction_compat_fibreIso hAL hTL f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hT1 Hu σ σ' τ τ' (conv σ τ hr) (conv σ' τ' hr') hact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChangeSpansFlagStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_change_spans_flag : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl : Vert.Flag F m) (V : X.Opens) (v : Fin m → Γ(F, V)) (M : Matrix (Fin m) (Fin m) Γ(X, V)), Spans fl V v → M.BlockTriangular id → IsUnit M.det → Spans fl V fun j => ∑ k, M k j • v k := by
  first | exact @GlobalTheory.FlagCell.Spans.mul_upper | exact GlobalTheory.FlagCell.Spans.mul_upper | (intros; apply GlobalTheory.FlagCell.Spans.mul_upper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialLocusRigidifiedBundleClosedSeesaw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivLocus_closed_of_relAmple : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) :=
  GlobalTheory.T.isClosed_trivialLocus_rigidified_bundle

end GlobalTheory.TrivLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAt
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem de_chi_eq {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

theorem fixAt_holds : GlobalTheory.Published.RayClassFieldSt → TwAdm → FixAt := by
  intro hRF hA
  refine AtTw.imp (AtTw.and hA lowAt_holds) fun Fm x hx k p hr hm w _ j H => ?_
  intro ρ hρ hp hL τ hτ
  have hR := ratHyp0_at_point Fm x hx k p hr hm _ H.1.2.2 H.2 j
  have hτ' : ∀ z ∈ (Formalism.L2.Host.embLL0 (Fm.D x k)).fieldRange, τ z = z := by
    rintro _ ⟨y, rfl⟩
    exact hτ y
  have hFB : FixBase p.T p.R.toRealDat j τ :=
    GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField _ _ _ _ _ _ hRF p.T p.R p.cG p.Sx p.nexp (F2 p) p.κ p.v₀ hR.laws hR.core hR.fw hR.tieIn hR.galois
      hR.small.val hR.small.ray hR.small.roots j τ hτ'
  refine ⟨hFB, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := de_chi_eq hρ ((Fm.ex x hx k).nch.twI w) j ((Fm.ex x hx k).nch.sd w) y
    change τ (((ρ.B _ j _).de.chi y : Circle) : ℂ) = _
    rw [hσ]
    refine GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values ρ hρ _ j _ (p.R.C.delAt ((Fm.D x k).ntw.l ((Fm.ex x hx k).nch.twI w))) (hp.delta _ j _) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [hR.small.val.del', hR.small.val.del]
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := (ρ.eG ((Fm.ex x hx k).nch.twI w) j ((Fm.ex x hx k).nch.sd w)).surjective q
    obtain ⟨g, rfl⟩ := (p.R.eG.trans p.cG).surjective y
    have hg := (mem_level_iff hm.2.2 hL _ j _ g).1 hq
    obtain ⟨z, hz⟩ := (level_chi hm.2.2 hρ hL _ j _ ⟨g, hg⟩ hq).2
    change τ ((((ρ.B _ j _).G.P.chi ⟨_, hq⟩ : ℂˣ) : ℂ)) = _
    rw [← hz]
    exact hτ z
  · exact (baseOf_of_realPin hR.core.lev hρ hp _ j _).fix_mu hR.core.lev (hρ.base _ j _) hFB.chi

end GlobalTheory.BigOn.Exp.TwConj
end
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3646
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3643
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3638
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3634
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3648
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3645
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3595
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3642
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3640
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationBundlesCorrespondDeformaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_polarisation_bundles_correspond_deformations : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (e : o₁.A ≅ o₂.A), IsMonHom e.hom → m₁.φ ≫ e.hom.left = m₂.φ → ∀ φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left, IsSquare e.hom.left φ₂ → LBIso o₁.P (o₂.P.pull φ₂) := by
  first | (exact @GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (exact GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (intros; apply GlobalTheory.UPel.HT.PolIsoLift.pol_iso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsKodairaSpencerFormalPointValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperators_kodairaSpencer_formal_point_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (iota : Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) →+* (FractionRing Ω)) (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, iota (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = (algebraMap Ω (FractionRing Ω)) (φ r)) ∧ (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (iota.mapMatrix Θ₁) u' p p' k s)) := by
  first | exact @GlobalTheory.HeatV.heat_values_of_isKS | exact GlobalTheory.HeatV.heat_values_of_isKS | (intros; apply GlobalTheory.HeatV.heat_values_of_isKS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedOfDegDataFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem factor_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G₁ : Over (Sp R₁)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G' U'.LG.L).pull (β₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  intro R _ _ _ hB D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  obtain ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, W, _, _, _, φ, GW, _, _, β, DW, AW, UW,
    hF₀, hD₀, hβ₀, hsq₀, hG₀, hW, hφi, hφl, hβ, hL, hDW, hLam⟩ :=
    GlobalTheory.T.semiabelian_uniformization_linear_action_transfer R hB D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  haveI := hB.2
  have hB₀ : Base R₀ := ⟨hF₀.1, charZero_of_injective_ringHom hF₀.2.1⟩
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β₁, A₁, U₁, hF₁, hD₁, hβ₁, hL₁⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisation_of_trait_unif R₀ hB₀ D₀ G₀ P hG₀ W hW φ hφi hφl GW β DW AW UW hβ hL hDW
  obtain ⟨hF, hD⟩ := GlobalTheory.Mum.FinExtComp.finExt_comp_isPullDeg R R₀ R₁ ρ₀ ρ₁ D.toPre D₀.toPre D₁.toPre hF₀ hF₁ hD₀ hD₁
  obtain ⟨β₁₂, hsq₁, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (spMap ρ₁) G₀ G₁ β₁ hβ₁
  have hQ : (abelian₂ G' U'.LG.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U'.LG.isLB _ _
  have key := hlam P.L.L U₁.LG.L _ (abelian₂ G' U'.LG.L) _ P.L.isLB U₁.LG.isLB hQ hL₁ hLam
  have hsp : spMap (ρ₁.comp ρ₀) = spMap ρ₁ ≫ spMap ρ₀ := by
    simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁.comp ρ₀, D₁, G₁, inferInstance, inferInstance,
    β₁ ≫ β₀, β₁₂ ≫ β₀₂, A₁, U₁, hF, hD, ?_, ?_, ?_⟩
  · rw [hsp]; exact hβ₁.comp hβ₀
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc, hsq₀.1, ← Category.assoc, hsq₁.1, Category.assoc]
    · rw [Category.assoc, hsq₀.2, ← Category.assoc, hsq₁.2, Category.assoc]
  · simpa only [Category.assoc] using key
end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFinrankEqNormPow
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.OActDeg

def endHom {k : Type} [Field k] (X : GlobalTheory.AV.AbVar k) (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) X.X) :
    𝓞 F →+* CategoryTheory.End X where
  toFun c := GlobalTheory.AV.AbVar.Hom.mk (A := X) (B := X) (ρ.act c) (h := ρ.hom c)
  map_one' := by
    apply GlobalTheory.AV.AbVar.hom_ext
    simp [ρ.one]
  map_mul' a b := by
    apply GlobalTheory.AV.AbVar.hom_ext
    change ρ.act (a * b) = ρ.act b ≫ ρ.act a
    rw [mul_comm, ρ.mul]
  map_zero' := by
    apply GlobalTheory.AV.AbVar.hom_ext
    rw [GlobalTheory.AV.AbVar.mk_hom, GlobalTheory.AV.AbVar.zero_hom]
    have h := ρ.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  map_add' a b := by
    apply GlobalTheory.AV.AbVar.hom_ext
    rw [GlobalTheory.AV.AbVar.add_hom, GlobalTheory.AV.AbVar.mk_hom, GlobalTheory.AV.AbVar.mk_hom, GlobalTheory.AV.AbVar.mk_hom, ρ.add]

theorem isFinite_and_finrank_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  intro k _ _ A _ hA F _ _ ρ l d hl hl0 hcard c hc
  let X : GlobalTheory.AV.AbVar k := GlobalTheory.TateHondaBridge.toAbVar A hA
  have h2 := GlobalTheory.abMulN_holds k A X.dim l hA X.smooth hl0
  rw [hcard] at h2
  have hdim : 2 * X.dim = d * Module.finrank ℚ F :=
    (Nat.pow_right_injective hl.two_le h2).symm
  obtain ⟨hiso, hdeg⟩ := GlobalTheory.AV.AbVar.isIsogeny_and_deg_eq_norm_pow k X F (endHom X F ρ) d hdim c hc
  refine ⟨hiso.1, ?_⟩
  classical
  rw [← hdeg]
  unfold GlobalTheory.AV.AbVar.deg
  rw [if_pos hiso]
  rfl

end GlobalTheory.AV.OActDeg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyRepresentableFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogRep

theorem eq_one_iff_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (z : T ⟶ G') :
    z = 1 ↔ z.left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  have e1 : (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
    show (T.hom ≫ η[G'].left) ≫ φ = _
    rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]
  constructor
  · rintro rfl; exact e1
  · intro hz
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hz, e1]
    · rw [Over.w, Over.w]

theorem comp_pow_hom {S : Scheme.{0}} {T H A : Over S} [GrpObj A] (z : T ⟶ H) (f : H ⟶ A) (n : ℕ) :
    z ≫ f ^ n = (z ≫ f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, comp_one]
  | succ n ih => rw [pow_succ, pow_succ, comp_mul, ih]

theorem exists_quot_quasiInv {Y : Scheme.{0}} [IsLocallyNoetherian Y] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀]
    (H : Over Y) [GrpObj H] (i : H ⟶ A₀) (k : ℕ) (hA : IsAbelianScheme A₀) (hi : IsMonHom i) (hm : Mono i)
    (hf : IsFinite H.hom) (he : Etale H.hom) (hk : i ^ k = 1) :
    ∃ (B : Over Y) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧
      IsQuasiInv k ψ ψ' ∧ ∀ (T : Over Y) (x : T ⟶ A₀), x ≫ ψ = 1 ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  obtain ⟨B, gB, q, hB, hqm, hqfin, hqflat, hqsurj, hq⟩ :=
    GlobalTheory.IwLevel.quotGlobal_holds Y A₀ H i hA hi hm hf inferInstance
  have hcB : IsCommMonObj B := hB.comm
  have hker : ∀ (T : Over Y) (x : T ⟶ A₀), x ≫ q = 1 ↔ ∃ z : T ⟶ H, z ≫ i = x := by
    intro T x
    constructor
    · intro h
      have h' : x ≫ q = (1 : T ⟶ A₀) ≫ q := by rw [h, MonObj.one_comp]
      refine ⟨hq.lift x 1 h' ≫ fst H A₀, ?_⟩
      have h1 := hq.lift_fst x 1 h'
      rw [comp_mul, hq.lift_snd, _root_.mul_one] at h1
      rw [Category.assoc, h1]
    · rintro ⟨y, rfl⟩
      have := lift y (1 : T ⟶ A₀) ≫= hq.w
      simpa [comp_mul, ← Category.assoc] using this
  have hK := GlobalTheory.TranslQuotientPow.isMonHom_id_pow A₀ k
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨⟨ψ', hψ', hψ'e⟩, hepi⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Y A₀ B A₀ q ((𝟙 A₀) ^ k)
    hqm hK hqflat hqsurj hqc (fun T x hx => by
      obtain ⟨z, rfl⟩ := (hker T x).1 hx
      rw [GlobalTheory.TranslQuotientPow.comp_id_pow, ← comp_pow_hom, hk, comp_one])
  refine ⟨B, gB, hcB, q, ψ', hB, ⟨hqm, hψ', hψ'e, ?_⟩, hker⟩
  rw [← cancel_epi q, reassoc_of% hψ'e, GlobalTheory.TranslQuotientPow.comp_id_pow q k,
    GlobalTheory.TranslQuotientPow.pow_comp_hom q (𝟙 A₀) k, Category.id_comp]

theorem ker_iff_of_pullbacks {S Y T : Scheme.{0}} {g₀ : Y ⟶ S} {A : Over S} {A₀ : Over Y}
    {φ₀ : A₀.left ⟶ A.left} (h₀ : IsPullback φ₀ A₀.hom A.hom g₀)
    {H : Over Y} {i : H ⟶ A₀} {B : Over Y} [GrpObj B] {ψ : A₀ ⟶ B}
    (hker : ∀ (T' : Over Y) (x : T' ⟶ A₀), x ≫ ψ = 1 ↔ ∃ z : T' ⟶ H, z ≫ i = x)
    {y : T ⟶ Y} {A₁ : Over T} {θ : A₁.left ⟶ A₀.left} (hθ : θ ≫ A₀.hom = A₁.hom ≫ y)
    {B₁ : Over T} [GrpObj B₁] {θ' : B₁.left ⟶ B.left} (hθ' : IsGrpPullback B₁ B y θ') {ψ₁ : A₁ ⟶ B₁}
    (hc : θ ≫ ψ.left = ψ₁.left ≫ θ') (T' : Over T) (g : T' ⟶ A₁) :
    g ≫ ψ₁ = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ θ ≫ φ₀ := by
  have hP : (g.left ≫ θ) ≫ A₀.hom = T'.hom ≫ y := by
    rw [Category.assoc, hθ, ← Category.assoc, Over.w g]
  let P : Over.mk (T'.hom ≫ y) ⟶ A₀ := Over.homMk (g.left ≫ θ) hP
  have e : P ≫ ψ = 1 ↔ (g.left ≫ θ) ≫ ψ.left = T'.hom ≫ y ≫ η[B].left := by
    rw [← Category.assoc T'.hom]
    constructor
    · intro h; exact congrArg Over.Hom.left h
    · intro h; exact Over.OverMorphism.ext h
  rw [eq_one_iff_of_isGrpPullback hθ', Over.comp_left, Category.assoc, ← hc, ← Category.assoc, ← e, hker]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.left, Over.w z, ?_⟩
    have := congrArg Over.Hom.left hz
    rw [Over.comp_left] at this
    rw [← Category.assoc, this]
    rfl
  · rintro ⟨h, hH, hφ⟩
    refine ⟨Over.homMk h hH, Over.OverMorphism.ext ?_⟩
    show h ≫ i.left = g.left ≫ θ
    apply h₀.hom_ext
    · rw [Category.assoc, hφ, Category.assoc]
    · rw [Category.assoc, Over.w i, hH, Category.assoc, hθ, ← Category.assoc, Over.w g]

theorem isogeny_rep : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (B : Over Y.left) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧ IsQuasiInv k ψ ψ' ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsQuasiInv k ψ₁ ψ₁' → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (θ : A₁.left ⟶ A₀.left) (θ' : B₁.left ⟶ B.left), θ ≫ φ₀ = φ₁ ∧ IsGrpPullback A₁ A₀ y θ ∧ IsGrpPullback B₁ B y θ' ∧ θ ≫ ψ.left = ψ₁.left ≫ θ' := by
  intro S _ A _ _ k hA hk0 hk
  obtain ⟨Y, hYf, hYe, hY⟩ := GlobalTheory.T.exists_finite_etale_trivializing_torsion_abelianScheme S A k hA hk0 hk
  refine ⟨Y, hYf, hYe, ?_⟩
  intro A₀ _ _ φ₀ h₀
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  obtain ⟨H, _, i, hi, hm, hHf, hHe, hik, hH⟩ := hY A₀ φ₀ h₀
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀
  obtain ⟨B, gB, cB, ψ, ψ', hB, hq, hker⟩ := exists_quot_quasiInv A₀ H i k hA₀ hi hm hHf hHe hik
  refine ⟨B, gB, cB, ψ, ψ', hB, hq, ?_⟩
  intro T x A₁ _ _ φ₁ B₁ _ _ ψ₁ ψ₁' h₁ hB₁ hq₁
  have hkT : IsUnit (k : Γ(T, ⊤)) := by
    have := hk.map x.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨hψ₁m, hψ₁'m, e₁, e₂⟩ := hq₁
  have hkill : ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ ψ₁ = 1 → g ^ k = 1 := by
    intro T' g hg
    rw [← GlobalTheory.TranslQuotientPow.comp_id_pow, ← e₁, ← Category.assoc, hg, one_comp]
  have hA₁ : IsAbelianScheme A₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₁
  obtain ⟨y, ⟨hyx, hyker⟩, hyu⟩ := hH T x A₁ φ₁ B₁ ψ₁ h₁ hB₁ hψ₁m hkill
  have w : φ₁ ≫ A.hom = (A₁.hom ≫ y) ≫ Y.hom := by rw [h₁.1.w, Category.assoc, hyx]
  let θ := h₀.1.lift φ₁ (A₁.hom ≫ y) w
  have hθφ : θ ≫ φ₀ = φ₁ := h₀.1.lift_fst _ _ _
  have hθs : θ ≫ A₀.hom = A₁.hom ≫ y := h₀.1.lift_snd _ _ _
  have hθ : IsGrpPullback A₁ A₀ y θ := IsGrpPullback.cancel h₀ (h₁.congr hyx.symm hθφ.symm) hθs
  obtain ⟨B₂, _, _, θ₂, ψ₂, ψ₂', hB₂, hθ₂, hq₂, hc₂, -⟩ :=
    GlobalTheory.UPel.HT.ES.pullQuasiInv T Y.left y A₀ B k ψ ψ' A₁ θ hB hq hθ
  obtain ⟨hψ₂f, hψ₂e, hψ₂s⟩ := GlobalTheory.UPel.HT.ES.isFinite_etale_surjective_of_isQuasiInv T A₁ B₂ k ψ₂ ψ₂' hA₁ hB₂ hkT hq₂
  haveI := hψ₂f
  haveI := hψ₂e
  have hk₂ := ker_iff_of_pullbacks h₀.1 hker hθs hθ₂ hc₂
  obtain ⟨β, hβi, hβm, hβ⟩ := GlobalTheory.SameKer.exists_iso_of_sameKer T A₁ B₂ B₁ ψ₂ ψ₁' ψ₁ k hB₁ hkT hq₂.1
    hψ₁'m hψ₁m inferInstance hψ₂s inferInstance e₂ (fun T' g => by rw [hyker, hk₂, hθφ])
  refine ⟨y, ⟨hyx, θ, β.left ≫ θ₂, hθφ, hθ, ?_, ?_⟩, ?_⟩
  · haveI := hβi
    haveI : IsMonHom (asIso β).hom := hβm
    exact ((isGrpPullback_of_iso (asIso β)).comp hθ₂).congr (Category.id_comp _) rfl
  · rw [hc₂, ← hβ, Over.comp_left, Category.assoc]
  · rintro y' ⟨hy'x, θ', θ'', hθ'φ, hθ', hθ'', hc'⟩
    apply hyu
    refine ⟨hy'x, fun T' g => ?_⟩
    rw [ker_iff_of_pullbacks h₀.1 hker hθ'.1.w hθ'' hc', hθ'φ]

end GlobalTheory.UPel.HT.ES.IsogRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfPullbackQuasiInverseIsogenyTrivialAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QuasiInvPull

open GlobalTheory.CechPic in

theorem lbIso_of_pullback_quasiInverseIsogeny_trivial_axes : ∀ (Y : Scheme.{0}) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (Q₁ Q₂ : LB (G2 B).left), IsAbelianScheme B → 0 < k →
    IsUnit (k : Γ(Y, ⊤)) → IsQuasiInv k ψ ψ' → IsAxesTriv B Q₁ → IsAxesTriv B Q₂ →
    LBIso (Q₁.pull (Hecke.sq2 ψ)) (Q₂.pull (Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  intro Y A B _ _ _ _ k ψ ψ' Q₁ Q₂ hB hk _ hq h₁ h₂ hiso
  obtain ⟨hψ, hψ', -, hc⟩ := hq
  haveI := hψ
  haveI := hψ'
  have o₁ : (1 : B ⟶ B) ≫ (𝟙 B) ^ k = 1 := by
    rw [← hc, ← Category.assoc, GlobalTheory.BirigUniq.one_comp_monHom, GlobalTheory.BirigUniq.one_comp_monHom]
  obtain ⟨hL₁, r₁₁, r₁₂⟩ := h₁
  obtain ⟨hL₂, r₂₁, r₂₂⟩ := h₂
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow Y B hB k hk
  let d := cls Q₁ hL₁ - cls Q₂ hL₂
  have z₁₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left (cls Q₁ hL₁) = 0 := (cls_eq_zero_iff (pull_isLB hL₁ _)).2 r₁₁
  have z₁₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left (cls Q₁ hL₁) = 0 := (cls_eq_zero_iff (pull_isLB hL₁ _)).2 r₁₂
  have z₂₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left (cls Q₂ hL₂) = 0 := (cls_eq_zero_iff (pull_isLB hL₂ _)).2 r₂₁
  have z₂₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left (cls Q₂ hL₂) = 0 := (cls_eq_zero_iff (pull_isLB hL₂ _)).2 r₂₂
  have d₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left d = 0 := by simp only [d, map_sub, z₁₁, z₂₁, sub_zero]
  have d₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left d = 0 := by simp only [d, map_sub, z₁₂, z₂₂, sub_zero]
  have dψ : pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left d = 0 := by
    have e : pull (Hecke.sq2 ψ) (cls Q₁ hL₁) = pull (Hecke.sq2 ψ) (cls Q₂ hL₂) :=
      (cls_eq_iff (pull_isLB hL₁ _) (pull_isLB hL₂ _)).2 hiso
    simp only [d, map_sub]
    exact sub_eq_zero.2 e

  have dk : pull (lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k)).left d = 0 := by
    have : lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k) =
        lift (fst B B ≫ ψ') (snd B B ≫ ψ') ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) := by
      rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [this, GlobalTheory.BirigUniq.pull_comp_left, dψ, map_zero]

  have hD : pull (lift (fst B B ≫ (𝟙 B) ^ k) (snd B B)).left d = 0 := by
    refine GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← GlobalTheory.BirigUniq.pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) = lift (1 : B ⟶ B) (𝟙 B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [o₁]
      rw [this, d₁]
    · rw [← GlobalTheory.BirigUniq.pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) =
          lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, dk]

  have hQ : pull (lift (snd B B) (fst B B)).left d = 0 := by
    refine GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← GlobalTheory.BirigUniq.pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (snd B B) (fst B B) = lift (𝟙 B) (1 : B ⟶ B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₂]
    · rw [← GlobalTheory.BirigUniq.pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (snd B B) (fst B B) =
          lift (snd B B) (fst B B) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, GlobalTheory.BirigUniq.pull_comp_left, hD, map_zero]
  have hsw : lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B) = 𝟙 (B ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hd : d = 0 := by
    have H : pull (lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B)).left d = d := by
      rw [hsw, Over.id_left, pull_id]
    rw [GlobalTheory.BirigUniq.pull_comp_left, hQ, map_zero] at H
    exact H.symm
  exact (cls_eq_iff hL₁ hL₂).1 (sub_eq_zero.1 hd)

end GlobalTheory.QuasiInvPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTCount

theorem crysAct_mem_Fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (x : D.O) {h : HdR o₀.A} (hh : h ∈ Fil o₀.A) : crysAct o₀ x h ∈ Fil o₀.A := by
  haveI := o₀.act.hom x
  exact push_mem_Fil (o₀.act.act x) hh

theorem crysAct_intCast {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (n : ℤ) (h : HdR o₀.A) : crysAct o₀ (algebraMap (𝓞 D.F) D.O (n : 𝓞 D.F)) h = (n : k) • h := by
  rw [map_intCast, map_intCast, Int.cast_smul_eq_zsmul]
  rfl

theorem lieZ_le_Fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β →
    ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  intro p _ D R _ b N k _ β s hs o₀
  rw [lieZ, Submodule.span_le]
  rintro z ⟨r, lam, c, y, ⟨x, rfl⟩, hlam, rfl⟩
  set T := crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) with hT

  have hω : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.nm_eq, ← D.tr_eq]; ring
  have hT2 : T (T x) = (D.tr : k) • T x - (D.nm : k) • x := by
    have := congrArg (fun u => crysAct o₀ (algebraMap (𝓞 D.F) D.O u) x) hω
    simp only [map_mul, map_sub, Module.End.mul_apply, LinearMap.sub_apply] at this
    rw [crysAct_intCast, crysAct_intCast] at this
    exact this

  have hρ : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this

  have hy0 : T ((T - ((D.tr : k) - β b.ρ) • 1) x) - β b.ρ • (T - ((D.tr : k) - β b.ρ) • 1) x = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hT2]
    rw [← hρ]
    module
  obtain ⟨w, hw, hyw⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N k β s hs o₀ _ (hy0 ▸ zero_mem _)
  set y := (T - ((D.tr : k) - β b.ρ) • 1) x
  set q := (Fil o₀.A).mkQ
  have key : ∀ c' : 𝓞 D.F, q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = ∑ i, β (b.t i c') • q (w i) := by
    intro c'
    have h1 : crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y - ∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i) ∈ Fil o₀.A := by
      have := crysAct_mem_Fil o₀ (algebraMap (𝓞 D.F) D.O c') hyw
      rwa [map_sub, map_sum] at this
    have e1 : q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = q (∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i)) :=
      (Submodule.Quotient.eq _).2 h1
    rw [e1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    exact (Submodule.Quotient.eq _).2 (hw i c')
  rw [SetLike.mem_coe, ← Submodule.Quotient.mk_eq_zero]
  change q _ = 0
  simp only [map_sum, map_smul, key, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hlam, zero_smul, Finset.sum_const_zero]

end GlobalTheory.HTCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAmpleKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrinThicken

open GlobalTheory.AbDual GlobalTheory.CechPic

theorem evc_comm {S : Scheme.{0}} {X Y : Over S} {M : LB (X ⊗ X).left} (hM : M.IsLB)
    (hc : cls M hM = CechPic.pull (lift (snd X X) (fst X X)).left (cls M hM)) (a b : Y ⟶ X) :
    evc hM a b = evc hM b a := by
  rw [evc, evc]
  conv_lhs => rw [hc]
  rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]

end GlobalTheory.PrinThicken
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedHodgeFiltrationEqOfSameLiftsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftedHodgeFiltration_eq_of_same_lifts : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k))) [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁) (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂), IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ g : HdR A₀ → HdR A₀, (∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) → (∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) → liftFil (epsDP k) h₁ = liftFil (epsDP k) h₂ := by
  first | (exact @GlobalTheory.LiftFilEq.liftFil_eq) | (exact GlobalTheory.LiftFilEq.liftFil_eq) | (intros; apply GlobalTheory.LiftFilEq.liftFil_eq  <;> assumption)
end


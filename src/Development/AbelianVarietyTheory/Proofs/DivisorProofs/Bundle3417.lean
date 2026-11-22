import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3402
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3391
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3396
import Development.AbelianVarietyTheory.Definitions.Divisors.IntLatGEqCanLatOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3393
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivalentIdempotentImageFixedTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EFix

theorem exists_equiv_act_of_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (n : ℕ), 1 ≤ n → IsUnit (n : R) → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A), a ^ n = 1 → a ≫ oA.act F.e = a → ∀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing R)) n p a → ∃ p₁ : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, p₁.y = F.e • p.y ∧ GtPtAct F.o F.e p.g p₁.g ∧ QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p₁ p := by
  intro R _ _ _ hR n hn _ Q D' F A' G' _ _ U' oA oG hS hl a _ hae p hp
  have hAdm : AdmBase R (maximalIdeal R) := ⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩
  haveI : CharZero R := hR.2.2.2
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨q, hqy, hqg⟩ := exists_gtPtAct (F := AlgebraicClosure (FractionRing R)) hL.1.globalFns F.o F.e p
  obtain ⟨E, eG, eA, -, -, eact⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl F.e
  obtain ⟨E', eG', -, -, eh', -⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl (star F.e)
  have hcube := GlobalTheory.Mum.EFixCube.cube_adj_of_oLinear R hAdm D' A' G' U'.toUnifPre hS F.O F.o oA oG hl F.e
  have hfun := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D' A' G' hS U'
  have h2 := (hfun.2 E E' (by rw [eG, eG']; exact hcube)).2 (AlgebraicClosure (FractionRing R))
  have hq := h2.2.2 n hn p q a (by rw [eh', star_star]; exact hqy)
    ((eact (AlgebraicClosure (FractionRing R)) _ _).2 hqg) hp
  rw [eA, hae] at hq
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D' A' G' hS U'
    (AlgebraicClosure (FractionRing R)) n hn
  exact ⟨q, hqy, hqg, (hf.2.2.1 q p).1 (((hf.1 q a).1 hq).symm.trans ((hf.1 p a).1 hp))⟩

end GlobalTheory.Mum.EFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteBasisTangentModuleSmoothCommGroupSchStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_basis_tangentModule_smooth_commGroupScheme : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) := by
  first | exact @GlobalTheory.TanBasis.exists_basis_tanM | exact GlobalTheory.TanBasis.exists_basis_tanM | (intros; apply GlobalTheory.TanBasis.exists_basis_tanM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionFieldMapBasicOpenFormalPointStatement
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
theorem _root_.GlobalTheory.T.exists_fractionField_map_basicOpen_formalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left), x' ≫ t.G.hom = spMap φ → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∃ iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω), ∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r) := by
  first | exact @GlobalTheory.HeatV.fracIotaBasicOpen | exact GlobalTheory.HeatV.fracIotaBasicOpen | (intros; apply GlobalTheory.HeatV.fracIotaBasicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointAbelianVarietyThroughFormalPoiStatement
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
theorem _root_.GlobalTheory.T.exists_genericPoint_abelianVariety_through_formalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) ∧ ξ ≫ P.A.A.hom = spMap ψ ∧ ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' ∧ ∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0 := by
  first | exact @GlobalTheory.UnifGenPoint.main | exact GlobalTheory.UnifGenPoint.main | (intros; apply GlobalTheory.UnifGenPoint.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionCoverStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glued_lineBundleSection_cover : ∀ {X : Scheme.{0}} (M : LB X), M.IsLB → ∀ (V : X.Opens) {J : Type} (W : J → X.Opens) (j : J → M.ι) (F : ∀ i, Γ(X, W i)), ⨆ i, W i = V → (∀ i, W i ≤ M.U (j i)) → (∀ i i', rsT (F i) (W i ⊓ W i') = rsT (M.g (j i) (j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i')) → ∃ t : ∀ c, Γ(X, M.U c ⊓ V), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ V) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ V) * rsT (t c') (M.U c ⊓ M.U c' ⊓ V)) ∧ ∀ i, rsT (t (j i)) (W i) = F i := by
  first | exact @GlobalTheory.GlueOver.exists_glue | exact GlobalTheory.GlueOver.exists_glue | (intros; apply GlobalTheory.GlueOver.exists_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsThetaShiftTriple
section
set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralFamTriple

variable {R : Type} [CommRing R] [IsDomain R]

def Rel (Q : DegPre R) {k : ℕ} {β : Q.X} (σ : Q.SecB k β)
    (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))) (r : R) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι),
    Good Q.P.L z J → sval σ (x ≫ (DegPre.prB Q (FractionRing R)).left) z J =
      gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * sval s x z J

theorem gs_zero {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) : gs f z ⊤ (0 : Γ(Y, ⊤)) = 0 := by
  rw [gs_eq f z ⊤ trivial, map_zero, map_zero]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem rel_scale {Q : DegPre R} {k : ℕ} {β : Q.X} {σ : Q.SecB k β}
    {s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))} {r : R} (h : Rel Q σ s r) (a : R) :
    Rel Q (DVR.SecOps.secScale (Out.scal Q.P.A.hom a) σ) s (a * r) := by
  intro Z x z J hJ
  rw [sval_secScale _ _ _ _ hJ, h Z x z J hJ, ← _root_.mul_assoc, map_mul, gs_mul _ z ⊤ trivial]
  refine congrArg (· * _) (congrArg (· * _) ?_)
  have e : (x ≫ (DegPre.prB Q (FractionRing R)).left) ≫ Q.P.A.hom = x ≫ (DegPre.BF Q (FractionRing R)).hom := by
    rw [Category.assoc, Over.w]
  rw [← e]
  exact gs_pull _ Q.P.A.hom z ⊤ trivial _

theorem rel_cast {Q : DegPre R} {k : ℕ} {F : Fam Q (FractionRing R) k} {a b : Q.X} (h : a = b) (σ : Q.SecB k b)
    (e : Q.SecB k b = Q.SecB k a) {r : R} (H : Rel Q σ (F.s b) r) : Rel Q (cast e σ) (F.s a) r := by
  subst h
  simpa only [cast_eq] using H

theorem isUnit_gs {Q : DegPre R} {r : R} (hr : r ≠ 0) {Z : Scheme.{0}} (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) :
    IsUnit (gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have e : x ≫ (DegPre.BF Q (FractionRing R)).hom =
      (x ≫ (fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [← Over.w (fst (TF (R := R) (FractionRing R)) Q.P.A)]
    simp only [Category.assoc]
    rfl
  rw [e]
  set q := x ≫ (fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)
  rw [← gs_pull q (jK R) z ⊤ (Set.mem_univ _), gs_eq q z (jK R ⁻¹ᵁ ⊤) (Set.mem_univ _)]
  have n := congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  have u : IsUnit (algebraMap R (FractionRing R) r) := by
    have : algebraMap R (FractionRing R) r ≠ 0 := fun h0 =>
      hr (IsFractionRing.injective R (FractionRing R) (by rw [h0, map_zero]))
    exact this.isUnit
  have u' : IsUnit ((jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    rw [show jK R = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) from rfl, ← n]; exact u.map _
  exact (u'.map _).map _

theorem shiftEq_of_rel (Q : DegPre R) (k : ℕ) (F : Fam Q (FractionRing R) k) (mu α : Q.X) (r : R) (σ : Q.SecB k α)
    (σ₁ : Q.SecB k (α + k • mu)) (h₀ : Rel Q σ (F.s α) r) (h₁ : Rel Q σ₁ (F.s (α + k • mu)) r) :
    ShiftEq Q k mu α σ σ₁ 0 σ₁ := by
  intro u hu hc z J hJ
  have fe := (secRel_iff Q.P.isLB _ _ (F.s (α + k • mu)) _ _ (F.s α) (DegPre.trF Q (FractionRing R) mu).left _ _ u).1
    (F.fe mu α u hu hc) _ (𝟙 _) z J hJ
  have a₁ := h₁ _ (𝟙 _) z J hJ
  have a₀ := h₀ _ (DegPre.trF Q (FractionRing R) mu).left z J hJ
  have w : (DegPre.trF Q (FractionRing R) mu).left ≫ (DegPre.BF Q (FractionRing R)).hom =
      (DegPre.BF Q (FractionRing R)).hom := Over.w _
  simp only [Category.id_comp] at a₁ fe
  rw [w] at a₀
  have z0 : Out.scal (DegPre.BF Q (FractionRing R)).hom (0 : R) = 0 := by simp [Out.scal]
  rw [Over.comp_left, a₀, a₁, fe, z0, gs_zero, zero_mul, add_zero]
  ring

theorem exists_triple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (Dd : DegData R (maximalIdeal R)) (k : ℕ), 1 ≤ k → ∀ (mu mu' α : Dd.toPre.X), ∃ (σ : Dd.toPre.SecB k α) (σ₁ : Dd.toPre.SecB k (α + k • mu)) (σ₂ : Dd.toPre.SecB k (α + k • mu + k • mu')) (e : Dd.toPre.SecB k (α + k • mu + k • mu') = Dd.toPre.SecB k (α + k • (mu + mu'))), ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ ∧ ShiftEq Dd.toPre k mu' (α + k • mu) σ₁ σ₂ 0 σ₂ ∧ ShiftEq Dd.toPre k (mu + mu') α σ (cast e σ₂) 0 (cast e σ₂) ∧ ∃ (z : (DegPre.BF Dd.toPre (FractionRing R)).left) (J : ((DegPre.BF Dd.toPre (FractionRing R)).left ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J ∧ IsUnit (sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J) := by
  intro R _ _ _ _ _ Dd k hk mu mu' α
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.FamFree.exists_sec_ne_zero (D := Dd.toPre) (F := FractionRing R) GlobalTheory.CMClaims.secTwist hk α
  obtain ⟨F, hFα, -⟩ := GlobalTheory.FamFree.exists_fam_single GlobalTheory.CMClaims.laws.globalFns Dd.tau_bimult hk α s₀
  obtain ⟨r₀, hr₀, σ₀, h₀⟩ := GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre R Dd.toPre k α (F.s α)
  obtain ⟨r₁, hr₁, σ₁, h₁⟩ := GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre R Dd.toPre k (α + k • mu) (F.s (α + k • mu))
  obtain ⟨r₂, hr₂, σ₂, h₂⟩ := GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre R Dd.toPre k (α + k • (mu + mu')) (F.s (α + k • (mu + mu')))
  have g₀ := rel_scale (Q := Dd.toPre) (σ := σ₀) h₀ (r₁ * r₂)
  have g₁ := rel_scale (Q := Dd.toPre) (σ := σ₁) h₁ (r₀ * r₂)
  have g₂ := rel_scale (Q := Dd.toPre) (σ := σ₂) h₂ (r₀ * r₁)
  rw [show r₁ * r₂ * r₀ = r₀ * r₁ * r₂ by ring] at g₀
  rw [show r₀ * r₂ * r₁ = r₀ * r₁ * r₂ by ring] at g₁
  have hX : α + k • mu + k • mu' = α + k • (mu + mu') := by rw [smul_add, add_assoc]
  have e : Dd.toPre.SecB k (α + k • mu + k • mu') = Dd.toPre.SecB k (α + k • (mu + mu')) := by rw [hX]
  have g₂' := rel_cast (F := F) hX _ e.symm g₂
  refine ⟨_, _, cast e.symm (DVR.SecOps.secScale (Out.scal Dd.toPre.P.A.hom (r₀ * r₁)) σ₂), e,
    shiftEq_of_rel Dd.toPre k F mu α _ _ _ g₀ g₁,
    shiftEq_of_rel Dd.toPre k F mu' (α + k • mu) _ _ _ g₁ g₂', ?_, ?_⟩
  · rw [cast_cast, cast_eq]
    exact shiftEq_of_rel Dd.toPre k F (mu + mu') α _ _ _ g₀ g₂
  · obtain ⟨z, J, hJ, hu⟩ := GlobalTheory.T.exists_unit_value_translated_bundleSection R Dd.toPre k α (mu + mu') (F.s α) (by rw [hFα]; exact hs₀)
    refine ⟨z, J, hJ, ?_⟩
    rw [Over.comp_left, g₀ _ _ z J hJ]
    exact (isUnit_gs (mul_ne_zero (mul_ne_zero hr₀ hr₁) hr₂) _ z).mul hu

end GlobalTheory.IntegralFamTriple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLieBasisOfIsLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocalBasis

theorem exists_isLieBasis_of_isLocalRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B]
    [IsCommMonObj B], Smooth B.hom → ∃ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y := by
  intro R _ _ B _ _ hs
  haveI := hs
  obtain ⟨C⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_chart B
  obtain ⟨g, hg, n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_lieBasis_away C (IsLocalRing.maximalIdeal R)
  have hu : IsUnit g := by
    by_contra h
    exact hg ((IsLocalRing.mem_maximalIdeal g).2 h)
  let L := Localization.Away g
  let f' : L →+* R := IsLocalization.Away.lift (g := RingHom.id R) g hu
  have hf' : f'.comp (algebraMap R L) = RingHom.id R := RingHom.ext fun r => IsLocalization.Away.lift_eq (g := RingHom.id R) g hu r
  let G' := ReciprocityTheory.ChartRestriction.G.Chart.Gs B g
  have hpb : IsGrpPullback G' B (ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (pullback.fst B.hom _) :=
    isGrpPullback_pullback B _
  have hcomp : spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L = 𝟙 (Sp R) := by
    simp only [spMap, ReciprocityTheory.ChartRestriction.G.Chart.fB]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf']
    exact Spec.map_id _
  let φ' : B.left ⟶ G'.left := pullback.lift (𝟙 _) (B.hom ≫ spMap f') (by rw [Category.assoc, hcomp]; simp)
  have hφ : φ' ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hw : φ' ≫ G'.hom = B.hom ≫ spMap f' := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl B).hom := inferInstanceAs (IsMonHom (𝟙 B))
  have hid : IsGrpPullback B B (𝟙 (Sp R)) (𝟙 B.left) := (isGrpPullback_of_iso (Iso.refl B)).congr rfl rfl
  have hn : IsGrpPullback B B (spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (φ' ≫ pullback.fst _ _) :=
    hid.congr hcomp.symm hφ.symm
  have hB : IsGrpPullback B G' (spMap f') φ' := hpb.cancel hn hw
  have hs' : Smooth G'.hom := by
    show Smooth (pullback.snd B.hom _)
    infer_instance
  obtain ⟨v', hv', -⟩ := GlobalTheory.exists_isLieBasis_baseChange L R f' G' B φ' hB hs' n v hv
  exact ⟨n, v', hv'⟩

end GlobalTheory.LieLocalBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatum_abelianLocus_point : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing B] (f : A →+* B) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)), 1 ≤ g → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsOpen (abLocus G) → L.IsSymmetric → PolOnAb G L.L → IsLieBasis y → NzFib σ → Set.range (spMap f) ⊆ abLocus G → ∃ (x : KeyIn B) (hg : x.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) := by
  first | exact @GlobalTheory.KeyDatumAb.exists_keyOn | exact GlobalTheory.KeyDatumAb.exists_keyOn | (intros; apply GlobalTheory.KeyDatumAb.exists_keyOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.AbLevel

theorem torsRat_of_isGrpPullback {R O : Type} [CommRing R] [IsDomain R] [CommRing O] [IsDomain O] (ρ : R →+* O)
    (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {A : Over (Sp O)} [GrpObj A] {π : A.left ⟶ G.left}
    (hπ : IsGrpPullback A G (spMap ρ) π) {n : ℕ} (h : TorsRat G n) : TorsRat A n := by
  intro K _ _ κ x hx
  have hj : Function.Injective ((algebraMap O (FractionRing O)).comp ρ) :=
    (IsFractionRing.injective O (FractionRing O)).comp hρ
  let i : FractionRing R →+* FractionRing O := IsFractionRing.lift hj
  have hsq : spMap i ≫ jK R = jK O ≫ spMap ρ := by
    show spMap i ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap O (FractionRing O)) ≫ spMap ρ
    rw [← spMap_comp, ← spMap_comp]
    have hi : ∀ r, i (algebraMap R (FractionRing R) r) = algebraMap O (FractionRing O) (ρ r) := fun r =>
      IsFractionRing.lift_algebraMap (K := FractionRing R) hj r
    exact congrArg spMap (RingHom.ext hi)
  let x0 := GlobalTheory.ObjPull.pushEquiv hπ _ x
  have hx0 : x0 ^ n = 1 := by simp only [x0, ← map_pow, hx, map_one]
  have hT : spMap (κ.comp i) ≫ jK R = (Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ := by
    show _ = (spMap κ ≫ jK O) ≫ spMap ρ
    rw [spMap_comp, Category.assoc, hsq, Category.assoc]
  let e : Over.mk (spMap (κ.comp i) ≫ jK R) ⟶ Over.mk ((Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
  obtain ⟨y, hy⟩ := h K (κ.comp i) (e ≫ x0) (by rw [← MonObj.comp_pow, hx0, MonObj.comp_one])
  have hy' : x.left ≫ π = spMap κ ≫ spMap i ≫ y.left := by
    have e₁ : x.left ≫ π = (e ≫ x0).left := (Category.id_comp _).symm
    exact e₁.trans (hy.trans ((congrArg (· ≫ y.left) (spMap_comp i κ)).trans (Category.assoc _ _ _)))
  have hz : (spMap i ≫ y.left) ≫ G.hom = jK O ≫ spMap ρ := by
    rw [Category.assoc, Over.w y]
    exact hsq
  refine ⟨Over.homMk (hπ.1.lift _ (jK O) hz) (hπ.1.lift_snd _ _ _), hπ.1.hom_ext ?_ ?_⟩
  · show x.left ≫ π = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ π
    rw [Category.assoc, hπ.1.lift_fst, hy']
  · show x.left ≫ A.hom = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ A.hom
    rw [Category.assoc, hπ.1.lift_snd]
    exact Over.w x

theorem exists_factor {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {H : Over T} [GrpObj H]
    {f : S' ⟶ S} {t : T ⟶ S'} {u : T ⟶ S} (hu : t ≫ f = u) {π : A.left ⟶ G.left} {π₂ : (A ⊗ A).left ⟶ (G ⊗ G).left}
    (hπ : IsGrpPullback A G f π) (sπ : IsSquare π π₂) {a : H.left ⟶ G.left} {a₂ : (H ⊗ H).left ⟶ (G ⊗ G).left}
    (ha : IsGrpPullback H G u a) (sa : IsSquare a a₂) :
    ∃ (ψ : H.left ⟶ A.left) (ψ₂ : (H ⊗ H).left ⟶ (A ⊗ A).left), IsGrpPullback H A t ψ ∧ IsSquare ψ ψ₂ ∧ a₂ = ψ₂ ≫ π₂ := by
  let ψ := hπ.1.lift a (H.hom ≫ t) (by rw [Category.assoc, hu]; exact ha.1.w)
  have hψ : ψ ≫ π = a := hπ.1.lift_fst _ _ _
  have hpb : IsGrpPullback H A t ψ := hπ.cancel (ha.congr hu.symm hψ.symm) (hπ.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  exact ⟨ψ, _, hpb, sψ, GlobalTheory.LamPull.isSquare_unique sa (hψ ▸ AbPol.isSquare_comp sψ sπ)⟩

theorem sameFib_factor {S₁ S₂ S₁' S₂' T : Scheme.{0}} {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {P₁ : LB (G2 G₁).left}
    {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {P₂ : LB (G2 G₂).left} (h₁ : P₁.IsLB) (h₂ : P₂.IsLB)
    {A₁ : Over S₁'} [GrpObj A₁] [IsCommMonObj A₁] {A₂ : Over S₂'} [GrpObj A₂] [IsCommMonObj A₂]
    {f₁ : S₁' ⟶ S₁} {t₁ : T ⟶ S₁'} {u₁ : T ⟶ S₁} (e₁ : t₁ ≫ f₁ = u₁)
    {f₂ : S₂' ⟶ S₂} {t₂ : T ⟶ S₂'} {u₂ : T ⟶ S₂} (e₂ : t₂ ≫ f₂ = u₂)
    {π₁ : A₁.left ⟶ G₁.left} {q₁ : (G2 A₁).left ⟶ (G2 G₁).left} (p₁ : IsGrpPullback A₁ G₁ f₁ π₁) (s₁ : IsSquare π₁ q₁)
    {π₂ : A₂.left ⟶ G₂.left} {q₂ : (G2 A₂).left ⟶ (G2 G₂).left} (p₂ : IsGrpPullback A₂ G₂ f₂ π₂) (s₂ : IsSquare π₂ q₂)
    (h : SameFib G₁ P₁ u₁ G₂ P₂ u₂) : SameFib A₁ (P₁.pull q₁) t₁ A₂ (P₂.pull q₂) t₂ := by
  obtain ⟨H, _, _, a, a₂, a', a₂', ha, sa, ha', sa', e⟩ := h
  obtain ⟨ψ, ψ₂, hψ, sψ, rfl⟩ := exists_factor e₁ p₁ s₁ ha sa
  obtain ⟨χ, χ₂, hχ, sχ, rfl⟩ := exists_factor e₂ p₂ s₂ ha' sa'
  refine ⟨H, inferInstance, inferInstance, ψ, ψ₂, χ, χ₂, hψ, sψ, hχ, sχ, ?_⟩
  have c := (CechPic.cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).2 e
  rw [← CechPic.cls_eq_iff (pull_isLB (pull_isLB h₁ _) _) (pull_isLB (pull_isLB h₂ _) _),
    CechPic.cls_pull (pull_isLB h₁ _), CechPic.cls_pull (pull_isLB h₂ _), CechPic.cls_pull h₁, CechPic.cls_pull h₂,
    ← CechPic.pull_comp, ← CechPic.pull_comp]
  rwa [CechPic.cls_pull h₁, CechPic.cls_pull h₂] at c

theorem lbIso_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {N : LB Z} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    {a : Y ⟶ X} {b : Z ⟶ Y} (e : LBIso M (L.pull a)) (e' : LBIso N (M.pull b)) : LBIso N (L.pull (b ≫ a)) := by
  have c := (CechPic.cls_eq_iff hM (pull_isLB hL _)).2 e
  have c' := (CechPic.cls_eq_iff hN (pull_isLB hM _)).2 e'
  rw [← CechPic.cls_eq_iff hN (pull_isLB hL _), c', CechPic.cls_pull hM, c, CechPic.cls_pull hL, CechPic.cls_pull hL,
    CechPic.pull_comp]

theorem siegPB_trans {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {u : SiegPre h n ζ s} {c : SiegPre h n ζ s'} {c' : SiegPre h n ζ s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : SiegPB c' c f') (m : SiegPB c u f) : SiegPB c' u (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩ := m'
  exact ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, AbPol.isSquare_comp hs' hs, lbIso_comp u.isLB c.isLB c'.isLB hw hw', fun a =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))⟩

theorem exists_level : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → TorsRat G₁ n → ∀ (K : Type) [Field K] (κ : Localization.Away (∏ k, C.t k) →+* K) (x₀ : Sp K ⟶ F.X), x₀ ≫ F.s = spMap ((κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) → SameFib F.univ.A F.univ.P x₀ G₁ P (spMap (κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))))) → ∃ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal ∧ (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) ∧ ∀ yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X, SiegPB c F.univ yU → yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) → spMap κ ≫ yU = x₀ := by
  intro g n φ hn hodd F C G₁ _ _ P hM hab hT K _ κ x₀ hx₀ hsf
  obtain ⟨A, _, _, π₀, π₂, hπ, sπ, hA, hP⟩ := AbPol.exists_isPPol_away g n φ hn C G₁ P hM hab
  have hCN := hM.1
  have hPG := hM.2.2.2.1.1
  let t := ∏ k, C.t k
  let O := Localization.Away t
  have ht0 : t ≠ 0 := fun h0 => by
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := O) t).map κ
    have : algebraMap C.R O t = 0 := (congrArg (algebraMap C.R O) h0).trans (map_zero _)
    rw [this, map_zero] at hu
    exact not_isUnit_zero hu
  haveI := hCN.1
  haveI := hCN.2.1
  have hle : Submonoid.powers t ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  haveI : IsDomain O := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Submonoid.powers t) _ inferInstance
  haveI : IsIntegrallyClosed O := isIntegrallyClosed_of_isLocalization O (Submonoid.powers t) hle
  have hTA : TorsRat A n := torsRat_of_isGrpPullback _ (IsLocalization.injective O hle) hπ hT
  let b : cycAway n →+* O := (algebraMap C.R O).comp C.b
  let c₀ : SiegPre g n (zetaAway n) (spMap (κ.comp b)) := GlobalTheory.LowChart.siegPull F.univ x₀ _ hx₀
  have pb₀ : SiegPB c₀ F.univ x₀ := GlobalTheory.LowChart.siegPB_siegPull _ _ _ _
  have hs₀ : SameFib c₀.A c₀.P (𝟙 _) A (P.pull π₂) (spMap κ) :=
    sameFib_factor F.univ.isLB hPG (Category.id_comp x₀) (spMap_comp _ _).symm
      (Pdiv.PullbackComparison.isGrpPullback x₀ F.univ.A) (Pdiv.PullbackComparison.isSquare x₀ F.univ.A) hπ sπ hsf
  obtain ⟨c, hc, hcc, a, a₂, ha, sa, ea⟩ := GlobalTheory.LevSpread.level_spreads n hn hodd O b A (P.pull π₂) hA hP hTA g K κ c₀
    (GlobalTheory.LowChart.principal_siegPull _ _ _ _ F.princ) hs₀
  refine ⟨c, hc, ⟨a ≫ π₀, a₂ ≫ π₂, (ha.comp hπ).congr (Category.id_comp _) rfl, AbPol.isSquare_comp sa sπ,
    lbIso_comp hPG (pull_isLB hPG _) c.isLB (GlobalTheory.lbIso_refl (pull_isLB hPG _)) ea⟩, fun yU hy hys => ?_⟩
  refine F.inj K _ _ _ c₀ ?_ (siegPB_trans hcc hy) pb₀
  rw [Category.assoc, hys, hx₀, ← spMap_comp, RingHom.comp_assoc]

end GlobalTheory.TChart.AbLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionExtendBasicOpenStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleSection_extend_basicOpen : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (M : LB X), M.IsLB → ∀ (f : Γ(X, ⊤)) (t : ∀ c, Γ(X, M.U c ⊓ X.basicOpen f)), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ X.basicOpen f) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ X.basicOpen f) * rsT (t c') (M.U c ⊓ M.U c' ⊓ X.basicOpen f)) → ∃ (N : ℕ) (s : LB.Sec M), ∀ c, rsT (s.f c) (M.U c ⊓ X.basicOpen f) = rsT f (M.U c ⊓ X.basicOpen f) ^ N * t c := by
  first | exact @GlobalTheory.SecAff.sec_extend_basicOpen | exact GlobalTheory.SecAff.sec_extend_basicOpen | (intros; apply GlobalTheory.SecAff.sec_extend_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismProjSpaceBasepointFreeSectionsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_projSpace_basepointFreeSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → x 0 ≠ 0 → ∃ (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  first | exact @GlobalTheory.HSAmp.GenMap.toProj_gens | exact GlobalTheory.HSAmp.GenMap.toProj_gens | (intros; apply GlobalTheory.HSAmp.GenMap.toProj_gens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerMulGlobalFunctionStatement
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
theorem _root_.GlobalTheory.T.exists_section_power_mul_global_function : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (c : Γ(X, ⊤)), ∃ σ'' : SecM (𝟙 X) L k, ∀ j, σ''.f j = resTop _ c * σ.f j := by
  first | exact @GlobalTheory.SecSmul.exists_smul | exact GlobalTheory.SecSmul.exists_smul | (intros; apply GlobalTheory.SecSmul.exists_smul <;> assumption)
end


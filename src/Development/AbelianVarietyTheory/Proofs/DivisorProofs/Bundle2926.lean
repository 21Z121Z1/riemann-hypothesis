import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelRelAmpleAndPrincipalAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2824
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePowerIsoMinimalSiegelCompactification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HodgeMin

open GlobalTheory.CechPic

theorem hodge_pow_iso_pull_pow_of_minimal_compactification : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), MinAt5 F z i OZ → Geo.Tor.IsNormalScheme S → IsProjOver (π ≫ z) → Dense (Set.range j) → j ≫ π = i → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsGrpPullback F.univ.A G j e → ∃ a N : ℕ, 1 ≤ a ∧ 1 ≤ N ∧ LBIso (lbPow (hodge G g) N) (lbPow (OZ.pull π) a) := by
  intro g n F Z z i OZ S π j _ G _ e hM hS hp hj hji hG hsm he
  obtain ⟨o', _, β, S', s', U, c, π', G', _, e', _, N, ⟨-, hz, -, hiz, -, hO, -⟩,
    ⟨-, -, -, hS', -, _, _, hU, -, -, _, _⟩, ⟨hG', hsm', he'⟩, hN, hiso⟩ := hM
  have := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver hp
  have : QuasiSeparated π := .of_comp π z
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian π'
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  have : AlgebraicGeometry.IsNoetherian S := {}
  have hd : Dense (⇑(c ≫ j) '' {x | (((c ≫ j) ≫ π ≫ z) x).asIdeal = ⊥}) := by
    refine (DenseRange.dense_image hj j.continuous F.isReduced_and_dense.2).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := c.surjective x
    refine ⟨y, ?_, by simp⟩
    rw [Category.assoc, reassoc_of% hji, hiz]
    exact hx
  obtain ⟨W, p, p', H, _, α, α', _, _, hw, h₁, h₂⟩ := exists_common_cover z π π' (GlobalTheory.IsNormalScheme.pred S') (c ≫ j) U.ι
    (by rw [Category.assoc, hji, hU]) hd hG hG' ((isGrpPullback_pullback F.univ.A c).comp he) he'
  have := hG.separated
  have := hG'.separated
  have v₁ := GlobalTheory.LieVB.isVB_omega G g
  have v₂ := GlobalTheory.LieVB.isVB_omega G' g
  have l₁ : (hodge G g).IsLB := v₁.isLB_det
  have l₂ : (hodge G' g).IsLB := v₂.isLB_det
  have l₃ : (hodge H g).IsLB := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h₁ v₁).isLB_det
  have e₁ := (cls_eq_iff (pull_isLB l₁ p) l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₁ v₁)
  have e₂ := (cls_eq_iff (pull_isLB l₂ p') l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₂ v₂)
  have e₃ := (cls_eq_iff (pull_isLB hO π') (isLB_lbPow l₂ N)).2 hiso
  rw [cls_pull l₁] at e₁
  rw [cls_pull l₂] at e₂
  rw [cls_pull hO, cls_lbPow l₂] at e₃
  obtain ⟨d, hd, h⟩ := exists_nsmul_eq_zero hS p (N • cls _ l₁ - pull π (cls _ hO)) (by
    rw [map_sub, map_nsmul, ← pull_comp, hw, pull_comp, e₃, map_nsmul, e₁, e₂, sub_self])
  refine ⟨d, d * N, hd, Nat.mul_pos hd hN,
    (cls_eq_iff (isLB_lbPow l₁ _) (isLB_lbPow (pull_isLB hO π) _)).1 ?_⟩
  rw [cls_lbPow l₁, cls_lbPow (pull_isLB hO π), cls_pull hO, mul_smul, ← sub_eq_zero, ← smul_sub, h]

end GlobalTheory.HodgeMin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateDifferenceSectionStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_difference_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) (x y : S ⟶ Hs P' x0 hu), ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) := by
  first | exact @GlobalTheory.FinPartAt.exists_mul | exact GlobalTheory.FinPartAt.exists_mul | (intros; apply GlobalTheory.FinPartAt.exists_mul <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateGluedSectionStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_glued_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (κ : (Sp (FractionRing R) ⟶ t.G.left) → Rˣ) (b : P'.Bˣ), P'.Gl κ b → ∀ (S : Over (Sp O)) (x y z : S ⟶ Hs P' x0 hu), z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) → z ≫ chi P' x0 hu b = (x ≫ chi P' x0 hu b) * (y ≫ chi P' x0 hu b) := by
  first | exact @GlobalTheory.FinPartAt.chi_mul | exact GlobalTheory.FinPartAt.chi_mul | (intros; apply GlobalTheory.FinPartAt.chi_mul <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapPowEqOneStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_map_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π), aH P' x0 hu hg.1 ^ q = 1 := by
  first | exact @GlobalTheory.FinPartAt.aH_pow_eq_one | exact GlobalTheory.FinPartAt.aH_pow_eq_one | (intros; apply GlobalTheory.FinPartAt.aH_pow_eq_one <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFiniteStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_scheme_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)), IsFinite (Hs P' x0 hu).hom := by
  first | exact @GlobalTheory.FinPartAt.hs_isFinite | exact GlobalTheory.FinPartAt.hs_isFinite | (intros; apply GlobalTheory.FinPartAt.hs_isFinite <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFlatStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_scheme_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)), Flat (Hs P' x0 hu).hom := by
  first | exact @GlobalTheory.FinPartAt.flat_main | exact GlobalTheory.FinPartAt.flat_main | (intros; apply GlobalTheory.FinPartAt.flat_main <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateUnitTorsionPointStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_unit_torsion_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (b : P'.Bˣ) (tt : P.T), (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ t.G.left), P'.At x0 w β → ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w → algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) → ∀ (w : specO 𝓞_ℂ_[p] 𝓞_ℂ_[p] ⟶ Hs P' x0 hu) (z : GlobalTheory.ChTor.Pts P.A.A), z.left ≫ P.gen = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (w ≫ aH P' x0 hu hg.1).left → algebraMap 𝓞_ℂ_[p] ℂ_[p] (unitOf (w ≫ chi P' x0 hu b) : 𝓞_ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  first | exact @GlobalTheory.FinPartAt.unitOf_chi_eq_weil | exact GlobalTheory.FinPartAt.unitOf_chi_eq_weil | (intros; apply GlobalTheory.FinPartAt.unitOf_chi_eq_weil <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
open GlobalTheory.CxForm GlobalTheory.ChartGlue

namespace GlobalTheory.LineForm.TopInt

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_add (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
  unfold HolAtlas.loc; split_ifs
  · rfl
  · exact (add_zero 0).symm

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) (v : V n) : A.loc (c • α) i v = c • A.loc α i v := by
  unfold HolAtlas.loc; split_ifs
  · rfl
  · exact (smul_zero c).symm

theorem dens_add (x y : Alt n) : dens (x + y) = dens x + dens y := by
  simp only [dens, map_add, Finsupp.add_apply, add_div]

theorem dens_smul (c : ℂ) (x : Alt n) : dens (c • x) = c * dens x := by
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem reDens_add (α β : A.Fld) (i : A.ι) (v : V n) :
    A.reDens (α + β) i v = A.reDens α i v + A.reDens β i v := by
  simp only [HolAtlas.reDens, loc_add, dens_add, Complex.add_re]

theorem reDens_smul (t : ℝ) (α : A.Fld) (i : A.ι) (v : V n) :
    A.reDens ((t : ℂ) • α) i v = t * A.reDens α i v := by
  simp only [HolAtlas.reDens, loc_smul, dens_smul, Complex.re_ofReal_mul]

variable [MeasurableSpace M]

def G (r : A.ι → V n → ℝ) : Measure M := glueMeas A.e fun i y => ENNReal.ofReal (r i (A.e i y))

def Good (r : A.ι → V n → ℝ) : Prop :=
  (∀ i, ContinuousOn (r i) (A.e i).target) ∧
  ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
    r i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y)

theorem part_eq (γ : A.Fld) (ε : ℤˣ) (r : A.ι → V n → ℝ) (h : ∀ i v, ((ε : ℤ) : ℝ) * A.reDens γ i v = r i v) :
    A.part γ ε = G A r := by
  simp only [HolAtlas.part, G]
  congr 1
  funext i y
  rw [← h]
  rfl

theorem good_lin {α : A.Fld} (hα : A.IsForm α) (c : ℝ) : Good A fun i v => c * A.reDens α i v :=
  ⟨fun i => continuousOn_const.mul (A.continuousOn_reDens hα i),
    fun i j y hi hj => by simp only [A.reDens_compat hα i j y hi hj]; ring⟩

theorem isJacobianCompatibleDensity_linearCombination_realDensity {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (c d : ℝ) :
    Good A fun i v => c * A.reDens α i v + d * A.reDens β i v :=
  ⟨fun i => (continuousOn_const.mul (A.continuousOn_reDens hα i)).add
      (continuousOn_const.mul (A.continuousOn_reDens hβ i)),
    fun i j y hi hj => by simp only [A.reDens_compat hα i j y hi hj, A.reDens_compat hβ i j y hi hj]; ring⟩

theorem glueMeas_mono [BorelSpace M] {ρ ρ' : A.ι → M → ℝ≥0∞} (h : ∀ i y, ρ i y ≤ ρ' i y) :
    glueMeas A.e ρ ≤ glueMeas A.e ρ' := by
  unfold glueMeas
  exact iSup_mono fun i => Measure.le_iff.2 fun S hS => by
    rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
    exact lintegral_mono fun v => h i _

variable [BorelSpace M] [SecondCountableTopology M]

theorem aem {r : A.ι → V n → ℝ} (hr : Good A r) (i : A.ι) (S : Set M) :
    AEMeasurable (fun v => ENNReal.ofReal (r i (A.e i ((A.e i).symm v))))
      (volume.restrict ((A.e i).target ∩ (A.e i).symm ⁻¹' S)) :=
  (HolAtlas.aemeasurable_ofReal_chart (A.e i) (r i) (hr.1 i)).mono_measure
    (Measure.restrict_mono (inter_subset_inter_right _ (preimage_mono (subset_univ S))) le_rfl)

theorem G_add {r₁ r₂ : A.ι → V n → ℝ} (h₁ : Good A r₁) (h₂ : Good A r₂) :
    glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y))) = G A r₁ + G A r₂ := by
  ext S hS
  rw [Measure.add_apply]
  exact glueMeas_add_of_compat_on A.e A.holo A.cover hS _ _
    (fun i j y _ hi hj => A.ofReal_compat r₁ h₁.2 i j y hi hj)
    (fun i j y _ hi hj => A.ofReal_compat r₂ h₂.2 i j y hi hj) (fun i => aem A h₁ i S)

theorem holAtlasGluedDensityMeasure_add_three {r₁ r₂ r₃ : A.ι → V n → ℝ} (h₁ : Good A r₁) (h₂ : Good A r₂) (h₃ : Good A r₃) :
    glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)) +
      ENNReal.ofReal (r₃ i (A.e i y))) = G A r₁ + G A r₂ + G A r₃ := by
  ext S hS
  have c₁ := A.ofReal_compat r₁ h₁.2
  have c₂ := A.ofReal_compat r₂ h₂.2
  have c₃ := A.ofReal_compat r₃ h₃.2
  rw [Measure.add_apply, Measure.add_apply,
    glueMeas_add_of_compat_on A.e A.holo A.cover hS
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i y => ENNReal.ofReal (r₃ i (A.e i y)))
      (fun i j y _ hi hj => by rw [c₁ i j y hi hj, c₂ i j y hi hj, mul_add])
      (fun i j y _ hi hj => c₃ i j y hi hj)
      (fun i => (aem A h₁ i S).add (aem A h₂ i S)),
    glueMeas_add_of_compat_on A.e A.holo A.cover hS
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) (fun i y => ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i j y _ hi hj => c₁ i j y hi hj) (fun i j y _ hi hj => c₂ i j y hi hj)
      (fun i => aem A h₁ i S)]
  rfl

theorem G_smul {r : A.ι → V n → ℝ} (h : Good A r) {c : ℝ} (hc : 0 ≤ c) :
    G A (fun i v => c * r i v) = ENNReal.ofReal c • G A r := by
  have hc' : Good A (fun i v => c * r i v) :=
    ⟨fun i => continuousOn_const.mul (h.1 i), fun i j y hi hj => by simp only [h.2 i j y hi hj]; ring⟩
  refine ext_of_cover (fun i => (A.e i).source) (fun i => (A.e i).open_source) A.cover fun i S hS hSi => ?_
  rw [Measure.smul_apply, G, G, glueMeas_apply _ _ A.holo (fun i j y hi hj => A.ofReal_compat (fun i v => c * r i v) hc'.2 i j y hi hj) i hS hSi,
    glueMeas_apply _ _ A.holo (fun i j y hi hj => A.ofReal_compat _ h.2 i j y hi hj) i hS hSi,
    chartMeas_apply_of_subset _ _ hS hSi, chartMeas_apply_of_subset _ _ hS hSi, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun v => ?_
  rw [ENNReal.ofReal_mul hc]

theorem part_finite [CompactSpace M] {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) : IsFiniteMeasure (A.part α ε) := by
  have h := good_lin A hα ((ε : ℤ) : ℝ)
  have e : A.part α ε = G A (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) := part_eq A α ε _ fun _ _ => rfl
  have fin : G A (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) univ ≠ ∞ :=
    GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn A.e A.cover A.holo (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) h.1 h.2
  refine ⟨?_⟩
  rw [e]
  exact lt_top_iff_ne_top.2 fin

theorem part_add_le {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (ε : ℤˣ) :
    A.part (α + β) ε ≤ A.part α ε + A.part β ε := by
  rw [part_eq A (α + β) ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v + ((ε : ℤ) : ℝ) * A.reDens β i v)
      fun i v => by rw [reDens_add, mul_add],
    part_eq A α ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    part_eq A β ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens β i v) fun _ _ => rfl,
    ← G_add A (good_lin A hα _) (good_lin A hβ _)]
  exact glueMeas_mono A fun i y => ENNReal.ofReal_add_le

theorem part_balance {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.part (α + β) 1 + A.part α (-1) + A.part β (-1) = A.part (α + β) (-1) + A.part α 1 + A.part β 1 := by
  rw [part_eq A (α + β) 1 (fun i v => 1 * A.reDens α i v + 1 * A.reDens β i v)
      fun i v => by simp [reDens_add],
    part_eq A α (-1) (fun i v => (-1) * A.reDens α i v + 0 * A.reDens β i v) fun i v => by simp,
    part_eq A β (-1) (fun i v => 0 * A.reDens α i v + (-1) * A.reDens β i v) fun i v => by simp,
    part_eq A (α + β) (-1) (fun i v => (-1) * A.reDens α i v + (-1) * A.reDens β i v)
      fun i v => by simp [reDens_add]; ring,
    part_eq A α 1 (fun i v => 1 * A.reDens α i v + 0 * A.reDens β i v) fun i v => by simp,
    part_eq A β 1 (fun i v => 0 * A.reDens α i v + 1 * A.reDens β i v) fun i v => by simp,
    ← holAtlasGluedDensityMeasure_add_three A (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _),
    ← holAtlasGluedDensityMeasure_add_three A (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _)]
  congr 1
  funext i y
  have := HolAtlas.ofReal_posNeg (A.reDens α i (A.e i y)) (-A.reDens β i (A.e i y))
  convert this using 3 <;> ring_nf

theorem part_smul_nonneg {α : A.Fld} (hα : A.IsForm α) {t : ℝ} (ht : 0 ≤ t) (ε : ℤˣ) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal t • A.part α ε := by
  rw [part_eq A ((t : ℂ) • α) ε (fun i v => t * (((ε : ℤ) : ℝ) * A.reDens α i v))
      fun i v => by rw [reDens_smul]; ring,
    part_eq A α ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    G_smul A (good_lin A hα _) ht]

theorem part_smul_nonpos {α : A.Fld} (hα : A.IsForm α) {t : ℝ} (ht : t ≤ 0) (ε : ℤˣ) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal (-t) • A.part α (-ε) := by
  rw [part_eq A ((t : ℂ) • α) ε (fun i v => (-t) * ((((-ε : ℤˣ) : ℤ) : ℝ) * A.reDens α i v))
      fun i v => by rw [reDens_smul, Units.val_neg, Int.cast_neg]; ring,
    part_eq A α (-ε) (fun i v => (((-ε : ℤˣ) : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    G_smul A (good_lin A hα _) (neg_nonneg.2 ht)]

theorem part_congr {α β : A.Fld} (h : ∀ x, dens (α x) = dens (β x)) (ε : ℤˣ) : A.part α ε = A.part β ε := by
  simp only [HolAtlas.part]
  congr 1
  funext i y
  congr 3
  unfold HolAtlas.loc
  split_ifs
  · exact h _
  · rfl

end GlobalTheory.LineForm.TopInt

namespace GlobalTheory.LineForm

open GlobalTheory.LineForm.TopInt

theorem wInt_props : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    (∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, IsFiniteMeasure (A.part α ε)) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), A.IsForm α → A.IsForm β → (∀ ε : ℤˣ, Integrable g (A.part α ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part β ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β) ∧
    (∀ (g : M → ℝ) (t : ℝ) (α : A.Fld), A.IsForm α → wInt A g ((t : ℂ) • α) = t * wInt A g α) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), (∀ x, dens (α x) = dens (β x)) → wInt A g α = wInt A g β) := by
  intro M _ _ _ _ _ _ n A
  refine ⟨fun α hα ε => part_finite A hα ε, fun g α β hα hβ ga gb => ?_, fun g t α hα => ?_,
    fun g α β h => by simp only [wInt, part_congr A h]⟩
  · have gs : ∀ ε : ℤˣ, Integrable g (A.part (α + β) ε) := fun ε =>
      ((ga ε).add_measure (gb ε)).mono_measure (part_add_le A hα hβ ε)
    refine ⟨gs, ?_⟩
    have key := congrArg (fun μ : Measure M => ∫ y, g y ∂μ) (part_balance A hα hβ)
    rw [integral_add_measure (((gs 1).add_measure (ga (-1)))) (gb (-1)),
      integral_add_measure (gs 1) (ga (-1)),
      integral_add_measure (((gs (-1)).add_measure (ga 1))) (gb 1),
      integral_add_measure (gs (-1)) (ga 1)] at key
    simp only [wInt]
    linarith
  · rcases le_total 0 t with ht | ht
    · simp only [wInt, part_smul_nonneg A hα ht, integral_smul_measure, ENNReal.toReal_ofReal ht, smul_eq_mul]
      ring
    · simp only [wInt, part_smul_nonpos A hα ht, integral_smul_measure, ENNReal.toReal_ofReal (neg_nonneg.2 ht),
        smul_eq_mul, neg_neg]
      ring

end GlobalTheory.LineForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormChartChangeCoeffIdealPowStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d → (∀ m, MvPolynomial.coeff m F ∈ I ^ e) → ∀ i j, C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) ∧ C.ρ e i i * C.ev e i F = C.ev e i F ∧ rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ d * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ev e j F) := by
  first | exact @GlobalTheory.FormalAlg.Charts.ev_change | exact GlobalTheory.FormalAlg.Charts.ev_change | (intros; apply GlobalTheory.FormalAlg.Charts.ev_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormPowersLinearStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_form_powers_linear : ∀ (D : ℕ) (F : MvPolynomial (Fin 5) ℝ), F.IsHomogeneous D →
    ∃ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D := by
  first | exact @GlobalTheory.IntLinPow.homog_eq_sum_pow_intLin | exact GlobalTheory.IntLinPow.homog_eq_sum_pow_intLin | (intros; apply GlobalTheory.IntLinPow.homog_eq_sum_pow_intLin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousLineBaseDifferenceStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_line_base_difference : ∀ (d : ℕ) (a b : ℤ), ∃ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d ∧
    onLine d a b - onBase d a b = (X 0 - X 4) * (X 0 - X 3) * K := by
  first | exact @GlobalTheory.CovTest.SwapLine.onLine_sub_onBase_factor | exact GlobalTheory.CovTest.SwapLine.onLine_sub_onBase_factor | (intros; apply GlobalTheory.CovTest.SwapLine.onLine_sub_onBase_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypSOfBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SymDescentAlgClosed

theorem hypS_of_baseChange : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A : PolAV (Sp K)) (B : PolAV (Sp Ω)) (b : B.A.left ⟶ A.A.left), IsGrpPullback B.A A.A (spMap j) b → LBIso B.L (A.L.pull b) → (letI := B.isAb.comm; GlobalTheory.ZH.HypS B.A B.L) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  intro K Ω _ _ _ _ j A B b h hb hS
  letI := B.isAb.comm
  letI := A.isAb.comm
  obtain ⟨w, wd, hw, hwd, hs, hp, ha⟩ := hS
  obtain ⟨w₀, -, e⟩ := GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero K Ω j A.A A.A B.A B.A b b A.isAb A.isAb h h w hw
  obtain ⟨wd₀, -, ed⟩ := GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero K Ω j A.A A.A B.A B.A b b A.isAb A.isAb h h wd hwd
  exact GlobalTheory.SymLevelDescent.hypS_descend j A.isAb h A.isLB B.isLB hb e ed hw hwd hs hp ha

end GlobalTheory.SymDescentAlgClosed
end


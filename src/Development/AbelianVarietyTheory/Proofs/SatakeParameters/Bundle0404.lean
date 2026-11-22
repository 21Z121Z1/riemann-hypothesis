import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0402
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0088
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0398
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0400
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0399
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0403
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0384
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0300

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicSardShiftedFunctionsRegularZerosStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicSard_shifted_functions_regularZeros : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ φ : Fin d → Γ(X, U), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ c ∉ E, ∀ (z : CxPts p (RingHom.id ℂ)) (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
        (∀ j, CxPts.evHom hz (φ j) + c j = 0) →
        RingHom.ker (CxPts.evHom hz) ≤
          Ideal.span (Set.range fun j => φ j + ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (c j)) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2 := by
  first | (exact @GlobalTheory.AlgSard.main) | (exact GlobalTheory.AlgSard.main) | (intros; apply GlobalTheory.AlgSard.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechComparisonDegreeZeroAlternatingPullbackStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechComparison_degreeZero_alternatingPullback : ∀ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V)
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
    (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (0 + 1)))
    (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (0 + 1))),
    y.1 = (cechAbPull f τ hτ φ).term (0 + 1) x.1 →
    cechAbHEquivH' hc' hG 0 (cechClass _ 0 y) =
      SheafPull.pull f φ 0 (homOfLE hV) (cechAbHEquivH' hc hF 0 (cechClass _ 0 x)) := by
  first | (exact @GlobalTheory.cechAbPull_degZero) | (exact GlobalTheory.cechAbPull_degZero) | (intros; apply GlobalTheory.cechAbPull_degZero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOrthogonalInvariantProjection
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory.PD.XCover

theorem mem_germ_range_of_mem_rB : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (y : Z.functionField), y ∈ rB ℂ Z.functionField (crd φ) I → ∃ f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i), (Z.presheaf.germ _ (genericPoint Z) h).hom f = y := by
  intro d Z _ p _ inst hinst φ _ _ hgen I hI h y hy
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  have hsc : ∀ r : ℂ, algebraMap ℂ Z.functionField r = (Z.presheaf.germ ⊤ (genericPoint Z) trivial).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) := by
    subst hinst; intro r; rfl
  set U : Z.Opens := I.inf fun i => φ ⁻¹ᵁ chart d i with hU
  have hUa : IsAffineOpen U := (GlobalTheory.T.projective_chart_affine_cover d Z φ).2 I hI
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Z U hUa
  have halg : ∀ b, algebraMap Γ(Z, U) Z.functionField b = (Z.presheaf.germ U (genericPoint Z) h).hom b := fun _ => rfl
  haveI : IsIntegrallyClosed Γ(Z, U) := by
    have hs := p.smooth_appLE (U := ⊤) (isAffineOpen_top _) hUa (by simp)
    letI := (p.appLE ⊤ U (by simp)).hom.toAlgebra
    haveI : Algebra.Smooth Γ(Sp ℂ, ⊤) Γ(Z, U) := hs
    let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    haveI : IsDomain Γ(Sp ℂ, ⊤) := e.injective.isDomain (e : Γ(Sp ℂ, ⊤) →+* ℂ)
    haveI : IsIntegrallyClosed Γ(Sp ℂ, ⊤) := IsIntegrallyClosed.of_equiv e.symm
    exact isIntegrallyClosed_of_smooth Γ(Sp ℂ, ⊤) Γ(Z, U)
  have hgerm : ∀ a ∈ rA ℂ (crd φ) I, ∃ g : Γ(Z, U),
      (Z.presheaf.germ U (genericPoint Z) h).hom g = ((a : fld φ) : Z.functionField) := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi, j, rfl⟩ := hx
      have hle : U ≤ φ ⁻¹ᵁ chart d i := Finset.inf_le hi
      refine ⟨Z.presheaf.map (homOfLE hle).op (φ.app (chart d i) (ratioSec d i j)), ?_⟩
      rw [Z.presheaf.germ_res_apply]
      have hr := (GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div d Z φ 0 i j (hgen 0) (hgen i)).2
      simp only [IntermediateField.coe_div, crd_val]
      rw [← hr, rat, dif_pos (hgen i)]
    | algebraMap r =>
      refine ⟨Z.presheaf.map (homOfLE le_top).op (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), ?_⟩
      rw [Z.presheaf.germ_res_apply]
      exact (hsc r).symm
    | add x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      exact ⟨g + g', by rw [map_add, hg, hg']; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      exact ⟨g * g', by rw [map_mul, hg, hg']; rfl⟩
  have hy' : IsIntegral (rA ℂ (crd φ) I) y := hy
  have hB : IsIntegral Γ(Z, U) y := by
    obtain ⟨q, hq, hqy⟩ := hy'
    have hl : q.map (algebraMap (rA ℂ (crd φ) I) Z.functionField) ∈
        Polynomial.lifts (algebraMap Γ(Z, U) Z.functionField) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨g, hg⟩ := hgerm _ (q.coeff n).2
      exact ⟨g, by rw [halg, hg]; rfl⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hq.map _)
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map, hqy]
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hB
  exact ⟨b, hb⟩

end GlobalTheory.PD.XCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermChartInterIntegralCoordinateRatiosStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericGerm_chartInter_integral_coordinateRatios : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i)), (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I := by
  first | (exact @GlobalTheory.PD.XCover.germ_mem_rB) | (exact GlobalTheory.PD.XCover.germ_mem_rB) | (intros; apply GlobalTheory.PD.XCover.germ_mem_rB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModuleCubePullHomTermCommCechDifferentialStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential : ∀ {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
    {σ : R →+* S} {τ : κ → ι} {A : Cube.{0} ι R} {B : Cube.{0} κ S}
    (ψ : Cube.PullHom σ τ A B) (p : ℕ) (x : Cube.Term A p),
    ψ.term (p + 1) (Cube.d A p x) = Cube.d B p (ψ.term p x) := by
  first | (exact @GlobalTheory.Cube.PullHom.term_d) | (exact GlobalTheory.Cube.PullHom.term_d) | (intros; apply GlobalTheory.Cube.PullHom.term_d  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootLinesWeightBoundOfFree
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open GlobalTheory.RoadU

namespace GlobalTheory.Row9

theorem coreAll_of_rowStarCore : Inputs → GlobalTheory.RoadW.RowStarCore → CoreAll :=
  fun hI hR => GlobalTheory.RoadU.coreAll_of_core hI (GlobalTheory.RoadW.core_of_rowStarCore hR)

end GlobalTheory.Row9
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceCechCochainFractionEqSumFibreStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_cechCochain_fraction_eq_sum_fibre : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (exact GlobalTheory.PD.trF_locCoch_eq_finsum_fib) | (intros; apply GlobalTheory.PD.trF_locCoch_eq_finsum_fib  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsAtConstructedPointOverTrueC
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_bpt : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (K : Ctx) (β : BPt K), β.Is (positionOf HasPart) → ModelsAt β.D β.O := by
  intro h1 h2 K β hβ
  have key : ∀ O : Obj β.X.toD7, ofObj O = β.c.O → ModelsAt β.X.toD7 O := by
    refine positionOf_ind (P := HasPart) (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ModelsAt X.toD7 O) ?_ hβ
    intro K B f T w Z c hc O hO
    obtain ⟨b⟩ := hc
    have b' : Part w Z (ofObj O) := hO ▸ b
    exact GlobalTheory.T.tuplesHaveLocalModels_of_standardColumnObjects h1 h2 B f T w Z O b'
  have hm := key (β.Y.obj β.p) (by rw [ofObj_obj]; exact β.hY)
  exact GlobalTheory.T.tuplesLocalModels_of_otherDivisionLatticesHeights β.X.toD7 (β.Y.obj β.p) (nPrime β.p.L) β.p.ht hm

end GlobalTheory.Svd
end


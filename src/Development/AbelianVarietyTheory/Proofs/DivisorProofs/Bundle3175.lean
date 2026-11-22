import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3120
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PSpaceDeg

theorem ringKrullDim_eq_one (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ringKrullDim k = 1 := by
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := ℤ) (B := k)
    (algebraMap ℤ k).injective_int]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem isArithVar (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    IsArithVar (PSpace.str k D) D :=
  ProjModel.isArithVar_pspace k (ringKrullDim_eq_one k) D

theorem injective_ringHom {k : Type} [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (ψ : k →+* ℂ) : Function.Injective ψ := by
  refine (RingHom.injective_iff_ker_eq_bot ψ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  rw [RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)

def ringHomEquiv (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] [Field K]
    [Algebra k K] [IsFractionRing k K] : (k →+* ℂ) ≃ (K →+* ℂ) where
  toFun ψ := IsFractionRing.lift (injective_ringHom ψ)
  invFun φ := φ.comp (algebraMap k K)
  left_inv ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom ψ) x
  right_inv φ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors k) (RingHom.ext fun x => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom (φ.comp (algebraMap k K))) x

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem finrank_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    [Field K] [Algebra k K] [IsFractionRing k K] [CharZero K] :
    Module.finrank ℚ K = Module.finrank ℤ k ∧ FiniteDimensional ℚ K := by
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  haveI : @IsScalarTower ℤ ℚ K Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance
  let b := Module.Free.chooseBasis ℤ k
  let b' := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  exact ⟨(Module.finrank_eq_card_basis b').trans (Module.finrank_eq_card_basis b).symm,
    Module.Finite.of_basis b'⟩

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem card_ringHom (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  haveI : CharZero (FractionRing k) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
  obtain ⟨h1, h2⟩ := finrank_fractionRing k (FractionRing k)
  haveI : NumberField (FractionRing k) := ⟨⟩
  rw [Nat.card_congr (ringHomEquiv k (FractionRing k)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card, h1]

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

open Set
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)

theorem exists_stdChart (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) :
    ∃ (c : AlgChart (PSpace.str k N) σ N) (i : (ProjSpace.hermitianTwistingSheaf k N).B.ι),
      c.e.source = ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) ∧ c.e.target = Set.univ ∧
      c.e.source ⊆ ptsIn (PSpace.str k N) σ ((ProjSpace.hermitianTwistingSheaf k N).B.U i) ∧
      ∀ v, ((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  obtain ⟨c, h₁, h₂, h₃⟩ := StdProjChart.exists_of_bijective (p := PSpace.str k N) σ
    (ProjSpace.isAffineOpen_chart k N 0) _ (StdProjChart.bijective_ratio k N 0)
  refine ⟨c, (0 : Fin (N + 1)), h₁, h₂, h₁.le, fun v => ?_⟩
  have hv : c.e.symm v ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) :=
    h₁ ▸ c.e.map_target (h₂ ▸ trivial)
  have h := Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N)
    (ProjSpace.coord k N) (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) (0 : Fin (N + 1))
    (c.e.symm v)
  refine h.trans ?_
  have h0 : ev (PSpace.str k N) σ (ProjSpace.chart k N 0) (ProjSpace.ratio k N 0 0)
      (c.e.symm v) = 1 := by
    simp only [ProjSpace.ratio, ProjSpace.ratioOn_self]
    rw [ev_eq hv, map_one]
  have key : ∑ a : Fin (N + 1), ‖ev (PSpace.str k N) σ (ProjSpace.chart k N 0)
      (ProjSpace.ratio k N 0 a) (c.e.symm v)‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
    rw [Fin.sum_univ_succ, h0, EuclideanSpace.norm_sq_eq]
    simp only [Fin.succAbove_zero] at h₃
    simp only [h₃, norm_one, one_pow]
  rw [← key]
  simp [Matrix.one_apply, ev]

theorem chern_mass_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (N : ℕ) (σ : k →+* ℂ) :
    ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N 1 Set.univ = 1 ∧
      ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N (-1) Set.univ = 0 := by
  have hA := isArithVar k N
  have hproj : IsProjOver (PSpace.str k N) := hA.isProjOver
  haveI : IsIntegral (PSpace k N) := ProjSpace.isIntegral_of_isDomain k N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).IsCInf := (ProjSpace.hermitianTwistingSheaf k N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf k N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := exists_stdChart k σ N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace k N) ∈ ProjSpace.chart k N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace k N)).mem_open_set_iff (ProjSpace.chart k N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := ChernNull.chernPart_over_closed hA ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ
    (ProjSpace.chart k N 0).isOpen.isClosed_compl (by simpa using hgen) σ ((ProjSpace.hermitianTwistingSheaf k N).φ σ) 1
  have hcX : (ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0))ᶜ =
      {y : CxPts (PSpace.str k N) σ | y.1 (IsLocalRing.closedPoint ℂ) ∈
        ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ} := by
    ext y
    simp [mem_ptsIn]
  rw [← hcX, ← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (lintegral_fubiniStudy_density_eq_one N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, FSDet.det_fubiniStudy_hess N v]
  simp

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem degree_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) := by
  have hσ : ∀ σ : k →+* ℂ, ((ProjSpace.hermitianTwistingSheaf k D).φ σ).chernInt D Set.univ (fun _ => 1) = 1 := by
    intro σ
    obtain ⟨h1, h0⟩ := chern_mass_hermitian_O_one_projective k D σ
    rw [GdegPullProof.chernInt_one, h1, h0]
    simp
  haveI : Finite (k →+* ℂ) := by
    haveI : CharZero (FractionRing k) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
    haveI : FiniteDimensional ℚ (FractionRing k) := (finrank_fractionRing k (FractionRing k)).2
    haveI : NumberField (FractionRing k) := ⟨⟩
    exact Finite.of_equiv _ (ringHomEquiv k (FractionRing k)).symm
  haveI := Fintype.ofFinite (k →+* ℂ)
  simp only [gdeg, chInt, hσ]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

theorem main : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ),
    IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧
      Nat.card (k →+* ℂ) = Module.finrank ℤ k :=
  fun k _ _ _ _ D => ⟨isArithVar k D, degree_hermitian_O_one_projective k D, card_ringHom k⟩

end GlobalTheory.PSpaceDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNorms
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem upAtPrime_groups_values_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (u : SmFn p) (a b : ℤ), (upperParabolic P u).H a b = P.H a b ∧ (∀ f, NV (upperParabolic P u) a b f = NV P a b f) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), val (upperParabolic P u) a b σ y f = val P a b σ y f * (Real.exp (-(a * u.u σ y) / 2) : ℝ) ∧ (upperParabolic P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(a * u.u σ y) / 2) := by
  intro k _ X _ p P u a b
  have key : ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      Real.exp (-(a * ((upperParabolic P u).L.φ σ).φ (pick ((upperParabolic P u).L.φ σ).isLB y) y + b * ((upperParabolic P u).A.φ σ).φ (pick ((upperParabolic P u).A.φ σ).isLB y) y) / 2)
        = Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)
          * Real.exp (-(a * u.u σ y) / 2) := by
    intro σ y
    rw [← Real.exp_add]
    congr 1
    show -(a * ((P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + u.u σ y) + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 = _
    ring
  refine ⟨rfl, fun f => rfl, fun σ y f => ⟨?_, ?_⟩⟩
  · show ratVal _ y * ((Real.exp _ : ℝ) : ℂ) = ratVal _ y * ((Real.exp _ : ℝ) : ℂ) * _
    rw [key σ y, Complex.ofReal_mul, mul_assoc]
    rfl
  · show ‖ratVal _ y‖ * Real.exp _ = ‖ratVal _ y‖ * Real.exp _ * _
    rw [key σ y, mul_assoc]
    rfl

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackEqReducedIntersectionNumbeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDegree_pullback_eq_reducedIntersectionNumber : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∀ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ p) 1 → z ≫ w = redι Z ≫ ratFibre.fst p → IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) → ∀ M : LB X, M.IsLB → ratDeg (w ≫ p) (M.pull w) = interNumRed ℚ Z ![M.pull (ratFibre.fst p)] := by
  first | exact @GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed | exact GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed | (intros; apply GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.TorsLift

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem gtTors_toT {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (g : GtPtF D F) (h : k • g = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k (GlobalTheory.FieldRestrictionTest.toT g) := by
  obtain ⟨gs, h0, hs, hl⟩ := (GlobalTheory.TorusExt.isNsmul_iff_eq k g (k • g)).2 rfl
  refine ⟨GlobalTheory.FieldRestrictionTest.toT (k • g),
    ⟨fun i => GlobalTheory.FieldRestrictionTest.toT (gs i), h0, fun i => hs i, congrArg GlobalTheory.FieldRestrictionTest.toT hl⟩, ?_⟩
  exact (GlobalTheory.FieldRestrictionTest.isZero_toT _).2 ((GlobalTheory.TorusExt.isZero_iff_eq _).2 h)

theorem inj (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hR : GlobalTheory.Mum.Base V)
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (D : DegData V (maximalIdeal V))
    (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (k : ℕ) (hk : 1 ≤ k) (N : Over (Sp V))
    (g₀ : GtPt D.toPre N) (x₀ : N ⟶ G) (hfin : IsFinite N.hom) (hg₀ : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k g₀)
    (huniv : ∀ (T : Over (Sp V)) (g : GtPt D.toPre T), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g)
    (htors : x₀ ^ k = 1) (hform : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre x₀ g₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (n n' : TF (R := V) F ⟶ N)
    (h : n.left ≫ x₀.left = n'.left ≫ x₀.left) : n = n' := by
  have hB := D.tau_bimult
  haveI : IsNoetherianRing V := hR.1.1
  have : CharZero V := hR.2
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hR.1 D A G hG U F k hk
  have key : ∀ m : TF (R := V) F ⟶ N, ∃ q : GtPtF D.toPre F, GtPt.IsPullF F m.left g₀ q ∧
      ∃ hq : k • q = GlobalTheory.TorusExt.iota hB F 0,
        (f (GlobalTheory.TorusExt.qkMk hB 0 q hq)).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = m.left ≫ x₀.left := by
    intro m
    obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF m g₀
    obtain ⟨h0, hn, hz⟩ := hg₀
    obtain ⟨h0', hh0'⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF m h0
    have hk' : k • q = GlobalTheory.TorusExt.iota hB F 0 := by
      rw [map_zero, ← (GlobalTheory.TorusExt.isNsmul_iff_eq k q h0').1 (GlobalTheory.FieldRestrictionTest.isNsmul_restrict hq hh0' hn)]
      exact (GlobalTheory.TorusExt.isZero_iff_eq _).1 (GlobalTheory.FieldRestrictionTest.isZero_restrict hh0' hz)
    obtain ⟨a, ha, hqa⟩ := GlobalTheory.ToricTorsionUnif.generic V hR G hG D A U k hk N g₀ x₀ hfin htors hform F m.left
      (Over.w m) (GlobalTheory.TorusExt.qkMk hB 0 q hk') rfl hq
    exact ⟨q, hq, hk', by rw [← (hf.1 _ a).1 hqa]; exact ha⟩
  obtain ⟨q, hq, hk1, e1⟩ := key n
  obtain ⟨q', hq', hk2, e2⟩ := key n'
  have hff : f (GlobalTheory.TorusExt.qkMk hB 0 q hk1) = f (GlobalTheory.TorusExt.qkMk hB 0 q' hk2) := by
    rw [← cancel_mono U.gen.inv]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, e1, h, e2]
    · exact (Over.w (f (GlobalTheory.TorusExt.qkMk hB 0 q hk1) ≫ U.gen.inv)).trans
        (Over.w (f (GlobalTheory.TorusExt.qkMk hB 0 q' hk2) ≫ U.gen.inv)).symm
  obtain ⟨z, hz1, hz2⟩ := (GlobalTheory.TorusExt.equiv_iff hB _ _).1 ((hf.2.2.1 _ _).1 hff)
  have hz : z = 0 := by
    have h1 : k • z = 0 := by
      have := hz1.symm
      simpa using this
    have h2 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact h1
    exact (smul_eq_zero.1 h2).resolve_left (by omega)
  have hqq : q' = q := by
    have := hz2
    simpa [hz] using this
  subst hqq
  have ht : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k (GlobalTheory.FieldRestrictionTest.toT q') :=
    GlobalTheory.TorsionFormCompare.tors_of_isPull n hq hg₀
  obtain ⟨_, _, hu⟩ := huniv _ _ ht
  exact (hu n hq).trans (hu n' hq').symm

theorem lift : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A) (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N), xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ x.left → p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → ∃ (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), h ^ N = 1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors N g ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g ∧ IntTerm.Ext U.toUnifPre x h ∧ GtPt.IsPullF (AlgebraicClosure (FractionRing V)) (toUnit (TF (R := V) (AlgebraicClosure (FractionRing V)))).left g p.g := by
  intro V _ _ _ hV D A G _ _ hG U N hN x xb p hxb hy hp
  have : CharZero V := hV.2.2.2
  haveI : IsNoetherianRing V := hV.1
  have hR : GlobalTheory.Mum.Base V := ⟨admissibleBase_of_completeNormalLocalCharZero hV, hV.2.2.2⟩
  obtain ⟨M, g₀, x₀, hfin, -, hg₀, huniv, hx₀, hform⟩ :=
    GlobalTheory.ToricTorsionUnif.exists_torsion_toG V hR G D A U N hN
  have hB := D.tau_bimult
  have hkg : N • p.g = 0 := by rw [GlobalTheory.TorusExt.qk_nsmul hB p, hy, map_zero]
  obtain ⟨nb, hnb, -⟩ := huniv _ _ (gtTors_toT p.g hkg)
  obtain ⟨a, ha, hqa⟩ := GlobalTheory.ToricTorsionUnif.generic V hR G hG D A U N hN M g₀ x₀ hfin hx₀ hform
    (AlgebraicClosure (FractionRing V)) nb.left (Over.w nb) p hy hnb
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) (admissibleBase_of_completeNormalLocalCharZero hV) D A G hG U
    (AlgebraicClosure (FractionRing V)) N hN
  have hax : a = xb := ((hf.1 p a).1 hqa).trans ((hf.1 p xb).1 hp).symm
  have hnx : nb.left ≫ x₀.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫
      x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) := by
    rw [← ha, hax, hxb, Category.assoc]
  have hfix : ∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V),
      spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left := by
    intro σ
    have hσ : spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => σ.commutes r
    let n' : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ M :=
      Over.homMk (spMap σ.toAlgHom.toRingHom ≫ nb.left) (by
        rw [Category.assoc, Over.w nb]
        show spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jK V = _
        rw [reassoc_of% hσ]; rfl)
    have e := inj V hR G hG D A U N hN M g₀ x₀ hfin hg₀ huniv hx₀ hform (AlgebraicClosure (FractionRing V)) n' nb
      (by
        show (spMap σ.toAlgHom.toRingHom ≫ nb.left) ≫ x₀.left = _
        rw [Category.assoc, hnx, reassoc_of% hσ])
    exact congrArg (·.left) e
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_invariant_point_descends_to_section V hV.2.1 M hfin nb hfix
  obtain ⟨g, hg⟩ := GlobalTheory.ConstLie.exists_isPull s g₀
  refine ⟨s ≫ x₀, g, ?_, GlobalTheory.TorsionFormCompare.tors_of_isPull s hg hg₀,
    (GlobalTheory.TorsionFormCompare.formalEq_iff _ _ _).2 (((GlobalTheory.TorsionFormCompare.formalEq_iff _ _ _).1 hform).pull s hg),
    ?_, ?_⟩
  · rw [← MonObj.comp_pow, hx₀, MonObj.comp_one]
  · show x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = (toUnit (TF (R := V) (FractionRing V)) ≫ s ≫ x₀).left
    apply GlobalTheory.OnePoint.point_ext (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))
    rw [← hnx, hs, Over.comp_left, Over.comp_left, Over.comp_left]
    simp only [← Category.assoc]
    congr 2
    have e1 : ∀ X : Over (Sp V), (toUnit X).left = X.hom := fun X => by simp
    rw [e1, e1]
    show jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) ≫ jK V
    rw [← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (AlgebraicClosure (FractionRing V)))) g
    have h2 := GlobalTheory.FlatTors.TorsMapExists.isPullF_trans hg hq
    rw [← Over.comp_left, ← hs] at h2
    rwa [GlobalTheory.FieldRestrictionTest.isPullF_unique h2 hnb] at hq

end GlobalTheory.Poinc.TorsLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedPullbackInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refinesPolarised_pullback_injective : ∀ {V V₀ V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₀] [IsDomain V₀] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ₀ : V →+* V₀) (D₀ : DegPre V₀) (e₀ : D₀.X ≃+ Q.X), Function.Injective ρ₀ → Refines Q ρ₀ D₀ e₀ → ∀ (ρ : V₀ →+* V₁) (D₁ : DegPre V₁) (hD : IsPullDeg ρ D₀ D₁), Function.Injective ρ → Refines Q (ρ.comp ρ₀) D₁ (hD.xe.trans e₀) := by
  first | exact @GlobalTheory.RefPull.refines_pull | exact GlobalTheory.RefPull.refines_pull | (intros; apply GlobalTheory.RefPull.refines_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIdeStatement
section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ), kerIdeal ((relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) := by
  first | exact @GlobalTheory.PDiv.kerIdeal_relFrob_le_frobKerIdeal | exact GlobalTheory.PDiv.kerIdeal_relFrob_le_frobKerIdeal | (intros; apply GlobalTheory.PDiv.kerIdeal_relFrob_le_frobKerIdeal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_condition_descends_galois_cover : ∀ (O : Type) [Ring O] (star : O → O) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (act : OActN O A) (act₀ : OActN O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ c, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (star c))).left)) → ∀ c, LBIso (P₀.pull (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left) (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left) := by
  first | exact @GlobalTheory.RosatiDescent.lbIso_act_descent | exact GlobalTheory.RosatiDescent.lbIso_act_descent | (intros; apply GlobalTheory.RosatiDescent.lbIso_act_descent; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem loc_continuousOn_holo : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField), f ∈ P.H a b → ∀ i j, ContinuousOn (ratVal (q := p) (σ := σ) (P.loc a b f i j)) (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) ∧ ∀ (D : ℕ) (c : AlgChart p σ D), DifferentiableOn ℂ (fun v => ratVal (P.loc a b f i j) (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j))) := by
  intro k _ X _ p P a b σ f hf i j
  have key : ∀ y ∈ ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j), ∃ (W : X.Opens) (hW : genericPoint X ∈ W)
      (g : Γ(X, W)), y ∈ ptsIn p σ W ∧ P.loc a b f i j = fnOf W hW g := by
    intro y hy
    have hr : RegAt (under y) (P.loc a b f i j) := hf _ i j (mem_ptsIn.1 hy.1) (mem_ptsIn.1 hy.2)
    obtain ⟨W, hx, g, e⟩ := hr.exists_fnOf
    exact ⟨W, gen_mem hx, g, mem_ptsIn.2 hx, e.symm⟩
  refine ⟨fun y hy => ?_, fun D c => ?_⟩
  · obtain ⟨W, hW, g, hy', e⟩ := key y hy
    have hc : ContinuousAt (ratVal (q := p) (σ := σ) (P.loc a b f i j)) y := by
      refine ((continuousOn_ev (p := p) (σ := σ) g).continuousAt ((isOpen_ptsIn W).mem_nhds hy')).congr ?_
      filter_upwards [(isOpen_ptsIn W).mem_nhds hy'] with z hz
      rw [e, ratVal_fnOf hz]
    exact hc.continuousWithinAt
  · intro v hv
    obtain ⟨W, hW, g, hy', e⟩ := key _ hv.2
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W) :=
      c.e.isOpen_inter_preimage_symm (isOpen_ptsIn W)
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W := ⟨hv.1, hy'⟩
    have hd := (c.holo W g).differentiableAt (hO.mem_nhds hm)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hO.mem_nhds hm] with w hw
    rw [e, ratVal_fnOf hw.2]
    rfl

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointEqAdicSumTermsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValue_integralPoint_eq_adicSum_terms : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))) (g' : GtPtF D.toPre (FractionRing V)) (l : FractionRing V), l ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g → IntTerm.Ext U.toUnifPre x h → GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.FrRel U.toUnifPre w₀ x e h l → ∃ w : Frm D.toPre (FractionRing V) 1 g'.b, w.IsGen ∧ IntTerm.IntFrm D.toPre g.b w l ∧ IntTerm.Lies U.toUnifPre w₀ g' w x e := by
  first | exact @GlobalTheory.Poinc.IntEval.eval_at_integral | exact GlobalTheory.Poinc.IntEval.eval_at_integral | (intros; apply GlobalTheory.Poinc.IntEval.eval_at_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsAdjointNefSeparateEtaleFibreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_adjointNef_separate_etaleFibre : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)], IsProjOver p → IsProjOver (f ≫ p) → 1 ≤ n → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (K : CanonLB (f ≫ p) n) (N : LB W) (hN : N.IsLB) (N' B : LB M) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : Sp ℂ ⟶ W) (U : W.Opens), IsNef ℂ N → IsBig ℂ N → IsNef ℂ (N.pull f) → IsBig ℂ (N.pull f) → IsNef ℂ N' → (n + 1).choose 2 < m → cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN' → x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → Etale (f ∣_ U) → (∀ (Z : Closeds W) (e : ℕ), IsIrreducible (Z : Set W) → Set.range x ⊆ Z → 1 ≤ e → topologicalKrullDim (Z : Set W) = e → 0 < interNumRed ℂ Z fun _ : Fin e => N) → ∀ (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M)), Function.Injective z → (∀ j, z j ≫ f = x) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 (f ≫ p) (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) → a = 0 := by
  first | exact @GlobalTheory.EtaleSep.sections_separate_fibre | exact GlobalTheory.EtaleSep.sections_separate_fibre | (intros; apply GlobalTheory.EtaleSep.sections_separate_fibre <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumExpPotentialUniformBound
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantEqOfFirstColumnsChangeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_eq_of_firstColumns_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x' y : Frame X.Ψ r)
    (τ : X.Ψ) (C : Matrix (Fin X.p0) (Fin X.p0) ℂ), C.det ≠ 0 → (X.gramPos y τ).det ≠ 0 →
    (∀ a : Fin X.p0, col (mat x' τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, C c a • col (mat y τ) (Fin.castLE X.p0_le c)) →
    ∀ v : Fin r → ℂ, X.maj x' τ v = X.maj y τ v := by
  first | exact @GlobalTheory.MajCols.maj_eq_of_cols | exact GlobalTheory.MajCols.maj_eq_of_cols | (intros; apply GlobalTheory.MajCols.maj_eq_of_cols <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogPeriodChowlaSelberg
section
noncomputable section

namespace GlobalTheory.MeanPeriodClosed

open NumberField Formalism.BasicNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (brN br_meanLogOm_eq br_b_spec absNorm_inv_mul_different natAbs_discr_eq
  discr_K discriminant_mod_four br_sqrt_sq br_finrank_K br_finrank_E)

theorem two_log_brN (D : D7) :
    (2 / (Module.finrank ℚ D.host.E : ℝ)) * Real.log (brN D) =
      Real.log D.host.rdE - Real.log (Real.sqrt (D.host.d : ℝ)) := by
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hdK : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
    discr_K D.host.K D.host.d (discriminant_mod_four D) _ (br_sqrt_sq D) (br_finrank_K D)
  have h1 := absNorm_inv_mul_different D.host.K D.host.E D.host.conj D.host.𝔟 (br_b_spec D)
  have h2 := natAbs_discr_eq D.host.K D.host.E D.host.d hdK
  set A : ℝ := (Ideal.absNorm (differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)) : ℝ) with hA
  have hsq : brN D ^ 2 = A := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    simp only [Rat.cast_pow, Rat.cast_natCast] at this
    rw [hA, ← this]
    rfl
  set m : ℕ := Module.finrank D.host.K D.host.E with hm
  have hE : Module.finrank ℚ D.host.E = 2 * m := br_finrank_E D
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := Module.finrank_pos
    exact_mod_cast this.ne'
  have hdisc : |(NumberField.discr D.host.E : ℝ)| = A * (D.host.d : ℝ) ^ m := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at this
    rw [hA, ← this]
  have hdisc0 : |(NumberField.discr D.host.E : ℝ)| ≠ 0 := by
    simpa using NumberField.discr_ne_zero D.host.E
  have hA0 : A ≠ 0 := fun h => hdisc0 (by rw [hdisc, h, zero_mul])
  have hlogA : 2 * Real.log (brN D) = Real.log A := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have hrd : Real.log D.host.rdE =
      (Real.log A + (m : ℝ) * Real.log D.host.d) / (2 * (m : ℝ)) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [Real.log_rpow (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)), hdisc,
      Real.log_mul hA0 (pow_ne_zero _ hd0.ne'), Real.log_pow, hE]
    push_cast
    field_simp
  rw [hrd, Real.log_sqrt hd0.le, hE]
  push_cast
  field_simp
  linear_combination hlogA

theorem meanPeriodAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc δ := by
  intro M _ hM τ
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ,
      0 < Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have e := br_meanLogOm_eq D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M hM.1 τ hpos
  have hN := two_log_brN D
  show Formalism.MainNotions.TaylorLogMetric.meanLogOm D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M τ = Formalism.MainNotions.TaylorLogMetric.logOmVal D
  rw [e, GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.logOmVal_eq]
  have hmean' : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area
      (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / Real.pi)) / (Module.finrank ℚ M : ℝ) =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt D.host.d) -
        Formalism.MainNotions.TaylorLogMetric.logDerivativeAtOne D := hmean
  rw [hmean']
  have hd0 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hr0 : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)) _
  rw [Real.log_div (by positivity) hd0.ne', Real.log_div (by positivity) hr0.ne']
  rw [neg_mul, hN]
  ring

theorem meanPeriod : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod :=
  fun D cc δ hcc hδ => meanPeriodAt D cc δ hcc hδ

end GlobalTheory.MeanPeriodClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLinearSystemConeAlgebraIffCoeffStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_linearSystemConeAlgebra_iff_coeff : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (p : Polynomial Ω), p ∈ coneAlg ev ↔ ∀ d : ℕ, p.coeff d ∈ ((LinearMap.range ev) ^ d : Submodule K Ω) := by
  first | exact @GlobalTheory.DegCmp.mem_coneAlg_iff_coeff | exact GlobalTheory.DegCmp.mem_coneAlg_iff_coeff | (intros; apply GlobalTheory.DegCmp.mem_coneAlg_iff_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
section
noncomputable section

open NumberField

namespace GlobalTheory.WeilUnitaryTransport

def ratPair (F : Type) [Field F] [NumberField F] (κ : Type) :
    AddSubgroup ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :=
  ((AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).prodMap
    (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ)).range

theorem mem_ratPair_iff {F : Type} [Field F] [NumberField F] {κ : Type}
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    w ∈ ratPair F κ ↔ ∃ y z : κ → F,
      w = (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) := by
  constructor
  · rintro ⟨⟨y, z⟩, rfl⟩
    exact ⟨y, z, rfl⟩
  · rintro ⟨y, z, rfl⟩
    exact ⟨(y, z), rfl⟩

end GlobalTheory.WeilUnitaryTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E}

def actLin (p : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB) : Matrix α β E ≃ₗ[R] Matrix α β E where
  toFun x := GlobalTheory.WeilM.actAB c p x
  invFun x := (((p.1⁻¹ : GlobalTheory.WeilM.UG c JA) : GL α E) : Matrix α α E) * x *
    (((p.2⁻¹ : GlobalTheory.WeilM.UG c JB) : GL β E) : Matrix β β E)ᵀ
  map_add' x y := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_smul, Matrix.smul_mul]
  left_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  right_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.mul_one]

end Gen

variable (F : Type) [Field F] [NumberField F]

def finE {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F := fun i => (0, y i)

def finE2 {κ : Type} (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (finE F m.1, finE F m.2)

def infE {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), 0)

def mixedSpaceVecPairAsAdeles {κ : Type} (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (infE F v.1, infE F v.2)

def slice {κ : Type} (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), y i)

def schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * f (z + v.1)

variable {F}

theorem dot_infE {κ : Type} [Fintype κ] (x : κ → AdeleRing (𝓞 F) F) (z : κ → mixedEmbedding.mixedSpace F) :
    x ⬝ᵥ infE F z = infE F (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ⬝ᵥ infE F z := by
  simp only [dotProduct, infE]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Prod.ext ?_ ?_
  · show (x i).1 * _ = _ * _
    rw [RingEquiv.symm_apply_apply]
  · show (x i).2 * 0 = (0 : FiniteAdeleRing (𝓞 F) F) * 0
    rw [mul_zero, mul_zero]

theorem pureA_schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (schrInf F ψ v f) g = GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) (GlobalTheory.WeilM.pureA F f g) := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  rw [dot_infE x v.2, mul_assoc]
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + v.1 =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + infE F v.1) i).1 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + v.1 i =
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v.1 i))
    rw [map_add, RingEquiv.apply_symm_apply]
  have h2 : (fun i => (x i).2) = fun i => ((x + infE F v.1) i).2 := by
    funext i
    show (x i).2 = (x i).2 + 0
    rw [add_zero]
  rw [h1, h2]

theorem slice_schr (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    slice F (GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) Φ) y = schrInf F ψ v (slice F Φ y) := by
  funext z
  simp only [slice, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  congr 2
  · congr 1
    refine (dot_infE _ v.2).trans ?_
    congr 2
    funext i
    exact RingEquiv.apply_symm_apply _ _
  · funext i
    refine Prod.ext ?_ ?_
    · exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm
    · exact add_zero _

theorem pureA_add {κ : Type} (f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (f + f') g = GlobalTheory.WeilM.pureA F f g + GlobalTheory.WeilM.pureA F f' g := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, Pi.add_apply, add_mul]

theorem pureA_smul {κ : Type} (a : ℂ) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (a • f) g = a • GlobalTheory.WeilM.pureA F f g := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem exists_schwartz_slice {κ : Type} [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ z, s z = slice F Φ y z := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g y • f, fun z => ?_⟩
    simp only [SchwartzMap.smul_apply, smul_eq_mul, slice, GlobalTheory.WeilM.pureA, RingEquiv.apply_symm_apply]
    exact mul_comm _ _
  | zero => exact ⟨0, fun z => rfl⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hx'
    exact ⟨s + s', fun z => by rw [SchwartzMap.add_apply, hs, hs']; rfl⟩
  | smul a x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨a • s, fun z => by rw [SchwartzMap.smul_apply, hs]; rfl⟩

end GlobalTheory.WeilAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LawsFieldChange

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem goodOf_comp (σ' : c'.F →+* ℂ) :
    (goodOf c' σ').comp (incF c c' hle) = goodOf c (σ'.comp (incF c c' hle)) := by
  have h : GoodEmb c' σ' ↔ GoodEmb c (σ'.comp (incF c c' hle)) := Iff.rfl
  unfold goodOf
  by_cases hg : GoodEmb c' σ'
  · rw [if_pos hg, if_pos (h.1 hg)]
  · rw [if_neg hg, if_neg (fun h' => hg (h.2 h'))]
    rfl

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem modelWt_unfBC (σ' : c'.F →+* ℂ) (G : WTZ E) :
    modelWt (unfBC hle U σ') G = modelWt (U (σ'.comp (incF c c' hle))) G := by
  have hr : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  unfold modelWt
  rw [hr]
  rfl

theorem petAt_unfBC (σ' : c'.F →+* ℂ) (x : ℝ) {D : D7} (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (μ : Measure (AutQ V)) (G : WTZ E)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    petAt (unfBC hle U σ') x V dict μ G (rulBC hle f) = petAt (U (σ'.comp (incF c c' hle))) x V dict μ G f := by
  have hrd := (rulBC_cusp E H Dw l Xo c c' hle r U a n f hf).1 σ'
  unfold petAt
  rw [hrd, modelWt_unfBC hle U σ' G]
  rfl

end

theorem laws_fieldChange : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f : cuspW Xo c U (wtZ a n), ∃ h : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n), ∀ σ : c'.F →+* ℂ, normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ ⟨_, h⟩ = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ.comp (incF c c' hle)) f := by
  intro D j H Dw l Xo c c' hle U dict hL
  refine ⟨?_, ?_⟩
  · exact
      { inR := hL.inR
        host := hL.host
        dat := hL.dat
        levA := hL.levA
        unf := fun σ' hσ' => GlobalTheory.OneMapAll.isUnf_unfExt hle σ' (fun _ => rfl) (hL.unf (σ'.comp (incF c c' hle)) hσ')
        chiTriv := fun σ' hσ' a n hd k γ hγ => by
          rw [laU_unfBC hle U σ' a n]
          exact hL.chiTriv (σ'.comp (incF c c' hle)) hσ' a n hd k γ hγ
        dictU := fun σ' hσ' => hL.dictU (σ'.comp (incF c c' hle)) hσ'
        modelW := fun σ' hσ' => hL.modelW (σ'.comp (incF c c' hle)) hσ' }
  · intro a n _ f
    have hf : (f : Rul Xo c) ∈ cusp Xo c U a n := (cuspW_wtZ (U := U) a n).le f.2
    have hsec : (f : Rul Xo c) ∈ sec Xo c a n := cusp_le_sec _ _ _ _ _ hf
    have hmem : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n) := by
      rw [cuspW_wtZ]
      exact (rulBC_cusp _ H Dw l Xo c c' hle D.R.r U a n _ hsec).2.2 hf
    refine ⟨hmem, fun σ' => ?_⟩
    have e1 : normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ'
        ⟨_, hmem⟩ = petAt (unfBC hle U (goodOf c' σ')) (xiR D) (D.sp.W j) (dict ((goodOf c' σ').comp (incF c c' hle)))
          (muQ1 (D.sp.W j)) (wtZ a n) (rulBC hle (f : Rul Xo c)) := rfl
    have e2 : normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ'.comp (incF c c' hle)) f =
        petAt (U (goodOf c (σ'.comp (incF c c' hle)))) (xiR D) (D.sp.W j) (dict (goodOf c (σ'.comp (incF c c' hle))))
          (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) := rfl
    rw [e1, e2, petAt_unfBC hle U (goodOf c' σ') _ _ _ _ _ hsec]
    have key : ∀ τ τ' : c.F →+* ℂ, τ = τ' →
        petAt (U τ) (xiR D) (D.sp.W j) (dict τ) (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) =
        petAt (U τ') (xiR D) (D.sp.W j) (dict τ') (muQ1 (D.sp.W j)) (wtZ a n) (f : Rul Xo c) := by
      rintro τ _ rfl; rfl
    exact key _ _ (goodOf_comp hle σ')

end GlobalTheory.LawsFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitPlaceStabilizerFixesLatticeVacuum
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem nonSplit_fixes_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (H : Geo.Tor.Host D.host.E) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ f, IsThetaFunO ψ V W f → IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) f → ∀ v ε (k : GA D W), GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.SuppPl ε W k → (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = f ∧ (V.rank ≠ 0 → mu k = 1) := by
  intro D ψ θ V W χV χW om hP mu hmu _ ΛV ΛW hV hW f hf hvac v ε k hv hk hst
  obtain ⟨uV, uW⟩ := hP.unr v ε hv
  refine ⟨?_, fun _ => ?_⟩
  · have h1 : GlobalTheory.WeilParts.SuppPl ε V 1 := fun i j => by
      rw [GlobalTheory.FinWeilO.mt_one, sub_self, Matrix.zero_apply, mul_zero]
    refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hP.weil.std V W ΛV ΛW hV hW χV χW om hP.eta hP.weil v ε hv uV uW 1 k h1 hk
      (fun u => ?_) f hf fun u hu => ?_
    · rw [GlobalTheory.InertVac.mem_latO_place_iff hv.1, GlobalTheory.InertVac.mem_latO_place_iff hv.1, ← hst,
        ← GlobalTheory.FinWeilO.actO_smul, (GlobalTheory.InertVac.actO_injective 1 k).eq_iff]
    · obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
      have h1 : 2 • (a • u) = u := by
        rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.InertVac.placeIdem_smul_eq hv.1 hu]
      have h2 := hvac.1 (a • u)
        (GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
      rwa [h1] at h2
  · obtain ⟨x, hx, -, xs, x1, x2⟩ := GlobalTheory.VacInert.exists_unit_root hv W k hk
    rw [hmu.2 k x hx, uV x xs x1 x2, Circle.coe_one]

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPairRealPointsSmulAdelicVacuumDetPow
section
noncomputable section

open NumberField MeasureTheory
open scoped Classical ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem vacuum_smul_realA : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
    (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
    ∀ g ∈ GinfC X.A, X.om (g, 1) X.vac = (∏ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det ^ P.n τ) • X.vac := by
  intro D cc δ t0 Q P X hX hb g hg
  have hW := hX.2.weil
  have hθ := hX.2.inf
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  have cart : ∀ (V : HSp D), V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    have : gramAt D V τ = 1 := by rw [gramAt, hV, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [this]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hmt1 : Formalism.L2.Theta.mt X.B 1 = 1 := by simp [Formalism.L2.Theta.mt]
  have hc1 : ∀ τ, compAt X.θ τ (Formalism.L2.Theta.mt X.B 1) = 1 := fun τ => by
    rw [hmt1, compAt, Matrix.map_one _ (by simp) (by simp)]
  have hA0 : ∀ τ, (gramAt D X.A τ).det ≠ 0 := fun τ => by
    rw [gramAt, hX.1.gramA, Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]; exact one_ne_zero
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.A hA0 g hg
  have hy : IsDetRoot X.B 1 1 := by simp [IsDetRoot]
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D X.ψ hW.std X.A X.B X.θ hθ X.χA X.χB X.om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) (fun _ => 1)
    (cart X.A hX.1.gramA) (cart X.B hX.1.gramB) g hg 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
    (fun τ => by rw [one_mul, mul_one]) x 1 hx hy X.vac hX.2.vac_theta hX.2.vac_fock]
  congr 1
  let c : D.what₂.Tau → ℤ := fun τ => -((P.n τ : ℤ) + P.d)
  have hν : ∀ τ, HasInfExp D (X.χB * (η ^ X.B.rank)⁻¹) τ ((c τ : ℤ) : ℚ) := by
    intro τ
    have := GlobalTheory.VacuumCharacter.hasInfExp_twist (hb τ) (e2 τ) X.B.rank
    convert this using 1
    rw [X.rkB]
    simp only [c]
    push_cast
    ring
  rw [Circle.coe_mul, Circle.coe_inv, hxv _ c hν, map_one, Circle.coe_one, mul_one, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨p, hp, hd⟩ := GlobalTheory.VacuumCharacter.detPlus_one (n := X.A.rank) (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)
    (by simp)
  obtain ⟨d1, -⟩ := hd (compAt X.θ τ (Formalism.L2.Theta.mt X.A g⁻¹)) (compAt X.θ τ (Formalism.L2.Theta.mt X.B 1))
    (by rw [one_mul, mul_one])
  have hpd : p = P.d := by
    have : (p : ℂ) = X.B.rank := by
      rw [Matrix.trace_one, Fintype.card_fin] at hp
      linear_combination -hp / 2
    exact_mod_cast this.trans (congrArg (Nat.cast) X.rkB)
  have e1' : ((1 / 2 : ℂ) • (1 + 1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ) * 1 + (1 / 2 : ℂ) • (1 - 1)) = 1 := by
    rw [mul_one]; module
  have inv : (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det * (compAt X.θ τ (Formalism.L2.Theta.mt X.A g⁻¹)).det = 1 := by
    rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [d1, hc1, e1', Matrix.det_one, one_pow, one_mul, hpd, eq_inv_of_mul_eq_one_right inv]
  simp only [c]
  rw [zpow_neg, inv_inv, zpow_add₀ g0, zpow_natCast, zpow_natCast, inv_pow]
  field_simp

end GlobalTheory.NormDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumExpPotentialUniformBoundStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitSum_exp_potential_uniform_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ s : ℝ, 0 < s → (∃ I : ℝ≥0∞, I < ⊤ ∧ ∀ x1 : Frame X.Ψ r, IsOrth X x1 → ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x1 z))) ∂muF X x1 ≤ I) → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x → ∑' γ : X.Γ, ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))) ≤ C := by
  first | exact @GlobalTheory.OrbitSum.orbitSum_le | exact GlobalTheory.OrbitSum.orbitSum_le | (intros; apply GlobalTheory.OrbitSum.orbitSum_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodLatticeActionOfFiniteOrderAutomorphismStatement
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLattice_action_of_finiteOrder_automorphism : ∀ (E : Type) [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ), IsMonHom θ → 0 < N → (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A → (∀ a, act.act a ≫ θ = θ ≫ act.act a) → 0 < n → ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧ (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  first | exact @GlobalTheory.periodLattice_of_finiteOrder | exact GlobalTheory.periodLattice_of_finiteOrder | (intros; apply GlobalTheory.periodLattice_of_finiteOrder <;> assumption)
end


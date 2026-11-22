import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0774
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0772
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0680
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0464
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import GroundTheory.GlobalFields.TateThesis.AdelicChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0137

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealLieChartKernelOperatorAtOne
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW Topology

namespace GlobalTheory.JSW.KerDeriv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

def rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := rmul
      map_add' := fun y z => ContinuousLinearMap.ext fun x => Matrix.mul_add (Matrix.of x) (Matrix.of y) (Matrix.of z)
      map_smul' := fun c y => ContinuousLinearMap.ext fun x => Matrix.mul_smul (Matrix.of x) c (Matrix.of y) }

omit [IsTotallyComplex E] in
theorem norm_rmul_le (y : Lie E a) : ‖rmul y‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ :=
  (rmulL (E := E) (a := a)).le_opNorm y

omit [IsTotallyComplex E] in
theorem norm_mul_le (x y : Lie E a) :
    ‖toL (Matrix.of x * Matrix.of y)‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ * ‖x‖ :=
  (rmulL (E := E) (a := a)).le_opNorm₂ y x

omit [IsTotallyComplex E] in

theorem eventually_inv_bdd :
    ∀ᶠ Y in 𝓝 (oneL E a), Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < ‖oneL E a‖ + 1 := by
  have hc : ContinuousAt (fun Y : Lie E a => toL (Matrix.of Y)⁻¹) (oneL E a) := by
    have h := continuousAt_matrix_inv (1 : Matrix (Fin a) (Fin a) (Cinf E)) (by
      rw [Matrix.det_one]
      exact NormedRing.inverse_continuousAt (1 : (Cinf E)ˣ))
    exact h
  have h1 : toL (Matrix.of (oneL E a))⁻¹ = oneL E a := by simp
  have h0 : ‖toL (Matrix.of (oneL E a))⁻¹‖ < ‖oneL E a‖ + 1 := by rw [h1]; exact lt_add_one _
  have h2 := hc.norm.eventually (gt_mem_nhds h0)
  exact Filter.Eventually.and (isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)) h2

theorem norm_chart_le (φ : GA E a → ℂ) (g : GA E a) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (Y : Lie E a) :
    ‖chart φ g Y‖ ≤ max C 0 := by
  unfold chart
  split_ifs
  · exact le_max_of_le_left (hC _)
  · simp

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have h := ContinuousOn.measurable_piecewise (hφ g).continuousOn (continuousOn_const (c := (0 : ℂ)))
    isOpen_invSet.measurableSet
  convert h using 1
  funext Y
  by_cases hY : Y ∈ invSet E a
  · rw [Set.piecewise_eq_of_mem _ _ _ hY]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hY]
    have hY' : ¬ IsUnit (Matrix.of Y) := hY
    simp [chart, hY']

theorem hasFDerivAt_chart_kerOp_of_bound {X : Type} [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) (φ : Sm E a) (hφ : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C)
    (hD : ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖)
    (g : GA E a) :
    HasFDerivAt (chart (kerOp ν k γ φ.1) g)
      (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) := by
  obtain ⟨hkm, hγm, hint⟩ := hk
  obtain ⟨Cφ, hCφ⟩ := hφ
  obtain ⟨CD, hCD⟩ := hD
  set M := ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ with hM
  set B := ‖oneL E a‖ + 1 with hB
  have hM0 : 0 ≤ M := norm_nonneg _
  have hB0 : 0 ≤ B := by positivity
  set s : Set (Lie E a) := {Y | Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < B} with hs_def
  have hs : s ∈ 𝓝 (oneL E a) := eventually_inv_bdd
  set F : Lie E a → X → ℂ := fun Y x => k x * chart φ.1 g (rmul (toL (γ x).val) Y) with hF
  set F' : Lie E a → X → (Lie E a →L[ℝ] ℂ) := fun Y x =>
    k x • (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)).comp (rmul (toL (γ x).val)) with hF'
  have hγL : Measurable fun x => toL (γ x).val := hγm
  have heq : chart (kerOp ν k γ φ.1) g =ᶠ[𝓝 (oneL E a)] fun Y => ∫ x, F Y x ∂ν := by
    filter_upwards [isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)] with Y hY
    obtain ⟨u, hu⟩ := hY
    have hY' : Y = toL u.val := hu.symm
    subst hY'
    rw [chart_val]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change k x * φ.1 (g * infGL E a u * infGL E a (γ x)) = k x * chart φ.1 g (rmul (toL (γ x).val) (toL u.val))
    rw [mul_assoc, ← map_mul, ← chart_val φ.1 g (u * γ x)]
    rfl
  have e1 : ∀ x, rmul (toL (γ x).val) (oneL E a) = toL (γ x).val := fun x => one_mul (γ x).val
  have hF'1 : F' (oneL E a) =
      fun x => k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) := by
    funext x; simp only [hF', e1]
  refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
  rw [← hF'1]

  have hmeasF : ∀ Y, AEStronglyMeasurable (F Y) ν := fun Y => by
    refine (hkm.aestronglyMeasurable).mul ?_
    refine ((measurable_chart φ.2 g).comp ?_).aestronglyMeasurable
    exact ((rmulL (E := E) (a := a)).flip Y).continuous.measurable.comp hγL
  have hmeasF' : AEStronglyMeasurable (F' (oneL E a)) ν := by
    rw [hF'1]
    refine hkm.aestronglyMeasurable.smul ?_
    exact (ContinuousLinearMap.compL ℝ (Lie E a) (Lie E a) ℂ).aestronglyMeasurable_comp₂
      ((measurable_fderiv ℝ (chart φ.1 g)).comp hγL).aestronglyMeasurable
      ((rmulL (E := E) (a := a)).continuous.measurable.comp hγL).aestronglyMeasurable

  have hint0 : Integrable (F (oneL E a)) ν := by
    refine Integrable.mono' ((hint 0).mul_const (max Cφ 0)) (hmeasF _) (ae_of_all _ fun x => ?_)
    simp only [hF, norm_mul, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_chart_le φ.1 g hCφ _) (norm_nonneg _)

  set K := max CD 0 * M * B * M with hK
  have hbound : ∀ᵐ x ∂ν, ∀ Y ∈ s, ‖F' Y x‖ ≤ ‖k x‖ * height (γ x) ^ 2 * K := by
    refine ae_of_all _ fun x Y hY => ?_
    have hu : IsUnit (Matrix.of Y) := hY.1
    set y := hu.unit * γ x with hy
    have hyv : rmul (toL (γ x).val) Y = toL y.val := by
      rw [hy, Units.val_mul, IsUnit.unit_spec]; rfl
    have hyi : toL (y⁻¹).val = toL (Matrix.of (toL (γ x)⁻¹.val) * Matrix.of (toL (hu.unit⁻¹).val)) := by
      rw [hy, _root_.mul_inv_rev, Units.val_mul]; rfl
    have hui : ‖toL (hu.unit⁻¹).val‖ ≤ B := by
      rw [Matrix.coe_units_inv, IsUnit.unit_spec]; exact hY.2.le
    have hg1 : ‖toL (γ x).val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x)⁻¹.val)]
    have hg2 : ‖toL (γ x)⁻¹.val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x).val)]
    have hL : ‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ ≤ max CD 0 * (M * B * height (γ x)) := by
      rw [hyv]
      refine (hCD g y).trans ?_
      have h1 : ‖toL (y⁻¹).val‖ ≤ M * B * height (γ x) := by
        rw [hyi]
        refine (norm_mul_le _ _).trans ?_
        gcongr
      calc CD * ‖toL (y⁻¹).val‖ ≤ max CD 0 * ‖toL (y⁻¹).val‖ := by gcongr; exact le_max_left _ _
        _ ≤ _ := by gcongr
    have hR : ‖rmul (toL (γ x).val)‖ ≤ M * height (γ x) := (norm_rmul_le _).trans (mul_le_mul_of_nonneg_left hg1 hM0)
    calc ‖F' Y x‖ ≤ ‖k x‖ * (‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ * ‖rmul (toL (γ x).val)‖) := by
          simp only [hF', norm_smul]
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖k x‖ * ((max CD 0 * (M * B * height (γ x))) * (M * height (γ x))) := by
          have hh0 : 0 ≤ height (γ x) := (norm_nonneg _).trans hg1
          gcongr
      _ = ‖k x‖ * height (γ x) ^ 2 * K := by rw [hK]; ring
  have hdiff : ∀ᵐ x ∂ν, ∀ Y ∈ s, HasFDerivAt (F · x) (F' Y x) Y := by
    refine ae_of_all _ fun x Y hY => ?_
    have hmem : rmul (toL (γ x).val) Y ∈ invSet E a := IsUnit.mul hY.1 (γ x).isUnit
    have h1 : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y))
        (rmul (toL (γ x).val) Y) :=
      ((contDiffAt_chart φ.2 g hmem).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp Y (rmul (toL (γ x).val)).hasFDerivAt).const_mul (k x)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs (Filter.Eventually.of_forall hmeasF) hint0 hmeasF'
    hbound ((hint 2).mul_const K) hdiff

end GlobalTheory.JSW.KerDeriv

namespace GlobalTheory.JSW

theorem hasFDerivAt_chart_kerOp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type)
    [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      HasFDerivAt (chart (kerOp ν k γ φ.1) g)
        (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) :=
  fun E _ _ _ a _ _ ν k γ hk φ hφ hL g =>
    KerDeriv.hasFDerivAt_chart_kerOp_of_bound ν k γ hk φ hφ (GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives E a φ hL) g

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficients
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem hyodo_mat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)), IsRat r σ → (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) → (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) → (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) → (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) = (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) → ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) = ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  intro l _ P AI T n _ _ K r σ Q hσ hQ c hcr hcc hcoc hdR
  obtain ⟨ω, W, hW, hω, hcoef⟩ := GlobalTheory.T.exists_continuous_coords_unramified_frobenius l r hσ.pos
  obtain ⟨ρ₀, p, hρc, hpK, hint, hc₀⟩ := GlobalTheory.T.exists_rational_form_unramified_restrictionScalars l n K r σ ω W hσ hW hω hcoef
  obtain ⟨c₀, hc₀c, hpc⟩ := hc₀ c hcr hcc
  have hcoc₀ := GlobalTheory.T.cocycle_restrictionScalars_rational_coords l n K r σ ρ₀ p c c₀ hint hpc hcoc
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.T.periodMatrix_restrictionScalars_blockDiagonal l P n K r σ Q ρ₀ p hQ hpK hint
  have hsst : IsSst P (repOf ρ₀) :=
    GlobalTheory.T.isSemistable_of_invertible_periodMatrix_semistableRing l P AI T (n × Fin r) K (n × Fin r → ℚ_[l]) (Pi.basisFun ℚ_[l] _) (repOf ρ₀) Q₀
      (fun g => by rw [toMatrix_repOf]; exact hQ₀ g)
  obtain ⟨β, hβ⟩ := GlobalTheory.T.deRham_trivial_rational_cocycle_restrictionScalars l P n K r σ ρ₀ p c c₀ hpK hint hpc hdR
  obtain ⟨bd, hbd⟩ := GlobalTheory.T.coboundary_tmul_of_column_deRham l P K _ ρ₀ c₀ β hβ
  have hcontρ : ∀ v : n × Fin r → ℚ_[l], Continuous fun g => repOf ρ₀ g v := by
    intro v
    simp only [repOf_apply]
    refine continuous_pi fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => (hρc i j).mul continuous_const
  obtain ⟨bs, hbs⟩ := GlobalTheory.T.hyodo_statement l P AI T K (n × Fin r → ℚ_[l]) (repOf ρ₀) hcontρ hsst c₀ hc₀c
    hcoc₀ ⟨bd, hbd⟩
  obtain ⟨β', hβ'⟩ := GlobalTheory.T.coboundary_semistableTensor_columns l P K _ ρ₀ c₀ bs hbs
  exact GlobalTheory.T.coboundary_restrictionScalars_block_zero l P n K r hσ.pos σ ρ₀ p c c₀ β' hpK hint hpc hβ'

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorThroughFrameEvalFinitePoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.InertTransfer

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem tOne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : TrivOutside {v} (1 : GAf L n) := by
  intro v' _
  show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v') = 1
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem tMul {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {v} y) : TrivOutside {v} (x * y) := by
  intro v' hv'
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1
  rw [Units.val_mul, Matrix.map_mul, hx v' hv', hy v' hv', Matrix.one_mul]

private theorem tInv {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : GAf L n}
    (hx : TrivOutside {v} x) : TrivOutside {v} x⁻¹ := by
  intro v' hv'
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v' hv', Matrix.mul_one] at e

def trivSub (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v} x}
  mul_mem' := fun hx hy => tMul hx hy
  one_mem' := tOne v
  inv_mem' := fun hx => tInv hx

theorem heckeVec_frame_eval : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (D : InertDatum L n v w) (U0 : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w n → ∀ p : locU n w →* Formalism.UG.GU D.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ y, D.loc y = b⁻¹ * cLoc w (F.j y) * b) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU D.σw n), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U0, NG.rt L n κ f = f) → ∀ (lam : W →ₗ[ℂ] ℂ) (φ : UA L n → ℂ), (∀ g, φ (F.j g) = lam (f g)) → ∀ g, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU D.σw n).comap p) (fun x => h (p x)) φ (F.j g) = lam (heckeFunI L n U0 D h f g) := by
  intro L _ _ _ n F v w hwv D U0 hU0 b hb p hp hloc h hh W _ _ f hf lam φ hφ g
  have hvw : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hwv
  let T : Subgroup (GAf L n) := trivSub v
  let ψ : T →* locU n w :=
    { toFun := fun t => ⟨F.j t, GlobalTheory.T.trivOutside_place_mem_definiteUnitaryLocalPoints L n F v w hwv t t.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hψv : ∀ t : T, ((ψ t : locU n w) : UA L n) = F.j t := fun t => rfl
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := F.onto y.1 (Subgroup.mem_inf.1 y.2).1
    have hxl : F.j x ∈ locU n w := hx ▸ y.2
    have ht : TrivOutside {v} x := hvw ▸ GlobalTheory.UnramDict.trivOutside F hxl
    exact ⟨⟨x, ht⟩, Subtype.ext hx⟩
  set K' : Subgroup (locU n w) := (Formalism.UG.KU D.σw n).comap p with hK'
  have hiff : ∀ t : T, ψ t ∈ K' ↔ (t : GAf L n) ∈ U0 := by
    intro t
    rw [Subgroup.mem_comap, GlobalTheory.T.integralFrame_conj_unitaryIntegral_iff_GL_integral L n w D.σw b hb p hp (ψ t), hψv,
      GlobalTheory.T.localComponent_mem_maxCompactGL_iff_mem_maxCompact L n F w t (GlobalTheory.T.trivOutside_place_mem_definiteUnitaryLocalPoints L n F v w hwv t t.2), hU0 t t.2]
  have hRi : ∀ (a : Formalism.UG.GU D.σw n) (c : Formalism.UG.KU D.σw n), h (a * c) = h a :=
    fun a c => by simpa using hh.1 1 c a
  have haK : ∀ x, ∀ k ∈ K', h (p (x * k)) = h (p x) := by
    intro x k hk
    rw [map_mul]
    exact hRi (p x) ⟨p k, hk⟩
  have hfinU := Formalism.UG.P.finite_support_cosets (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified D.unram n) hh.2
  let e : locU n w ⧸ K' → Formalism.UG.GU D.σw n ⧸ Formalism.UG.KU D.σw n := fun d => (p d.out : _)
  have he : Function.Injective e := by
    intro d d' hdd
    have h1 := QuotientGroup.eq.1 hdd
    rw [← map_inv, ← map_mul] at h1
    rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d']
    exact QuotientGroup.eq.2 h1
  have heq : ∀ d : locU n w ⧸ K', h (p d.out) = h (e d).out := by
    intro d
    have hk : (p d.out)⁻¹ * (e d).out ∈ Formalism.UG.KU D.σw n :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (e d)).symm
    have := hRi (p d.out) ⟨_, hk⟩
    rw [← this]
    congr 1
    group
  have hsupp : (Function.support fun d : locU n w ⧸ K' => h (p d.out)).Finite := by
    refine (hfinU.preimage he.injOn).subset ?_
    intro d hd
    show h (e d).out ≠ 0
    rw [← heq]; exact hd
  have hβ : ∀ x, ∀ u ∈ U0, f (g * (x * u)) = f (g * x) := by
    intro x u hu
    have := congrFun (hf u hu) (g * x)
    rw [← mul_assoc]; exact this
  have hφ' : ∀ t : T, φ (F.j g * ((ψ t : locU n w) : UA L n)) = lam (f (g * t)) := by
    intro t
    rw [hψv, ← map_mul]; exact hφ _
  have key := GlobalTheory.T.cosetSum_transfer_along_surjection_preimage U0 K' T ψ hsurj hiff (fun x => h (p x))
    (fun d => φ (F.j g * (d : UA L n))) (fun x => f (g * x)) lam haK hsupp hβ hφ'
  have hv : ∀ x (hx : TrivOutside {v} x), D.hval h (D.loc x) = h (p (ψ ⟨x, hx⟩)) := by
    intro x hx
    have e1 : D.loc x = (p (ψ ⟨x, hx⟩)).val := by rw [hloc, hp]; rfl
    rw [InertDatum.hval, dif_pos (e1 ▸ (p (ψ ⟨x, hx⟩)).2)]
    congr 1
    exact Subtype.ext e1

  have hL : GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) K' (fun x => h (p x)) φ (F.j g) =
      ∑ᶠ d : locU n w ⧸ K', h (p d.out) * φ (F.j g * (d.out : UA L n)) := by
    unfold GlobalTheory.LFun.heckeVec
    have hfin' : (Function.support fun c : locU n w ⧸ K' =>
        (fun x => h (p x)) c.out • ((RU L n).comp (locU n w).subtype) c.out φ).Finite :=
      hsupp.subset fun c hc h0 => hc (by simp only [h0, zero_smul])
    change (Pi.evalAddMonoidHom (fun _ : UA L n => ℂ) (F.j g))
      (∑ᶠ c : locU n w ⧸ K', (fun x => h (p x)) c.out • ((RU L n).comp (locU n w).subtype) c.out φ) = _
    rw [AddMonoidHom.map_finsum _ hfin']
    rfl
  rw [hL, key]
  congr 1
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  split_ifs with h1 h2 h2
  · rw [hv h2.choose h2.choose_spec.2]
    rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

end GlobalTheory.InertTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfJacquetMin
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacMinCusp

open GlobalTheory.SmGL.CuspMax Matrix
open scoped TensorProduct

theorem blk_two_stdSum {a b n : ℕ} (h : a + b = n) (i : Fin n) :
    blk (two (stdSum h)) i = decide (a ≤ (i : ℕ)) := by
  obtain ⟨x, rfl⟩ := (stdSum h).surjective i
  rcases x with x | x
  · rw [← two_false, blk_apply]; simp [x.2]
  · rw [← two_true, blk_apply]; simp

theorem blk_two_stdSum_lt {a b n : ℕ} (h : a + b = n) (i j : Fin n) :
    blk (two (stdSum h)) i < blk (two (stdSum h)) j ↔ (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : a ≤ (i : ℕ) <;> by_cases h2 : a ≤ (j : ℕ) <;> simp [h1, h2] <;> omega

theorem mem_unipRad_two_iff {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) {g : GL (Fin n) R} :
    g ∈ unipRad R (two (stdSum h)) ↔ ∀ i j : Fin n, ¬ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) →
      (g : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [mem_unipRad_iff_entries]
  simp only [blk_two_stdSum_lt]

end GlobalTheory.JacMinCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace GlobalTheory.TypeVec

def rtHom (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : GAf L n →* Module.End ℂ (GAf L n → ℂ) where
  toFun h := Formalism.L2.NG.rt L n h
  map_one' := by
    apply LinearMap.ext; intro f; funext g
    simp [Formalism.L2.NG.rt]
  map_mul' a b := by
    apply LinearMap.ext; intro f; funext g
    simp [Formalism.L2.NG.rt, mul_assoc]

def IsLiftAt {L : Type} [Field L] [NumberField L] [IsCMField L] {g : ℕ} [Fact g.Prime] {n : ℕ} (s : SplitPlace L)
    (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)) (y : GL (Fin n) ℤ_[g]) (x : GAf L n) : Prop :=
  TrivOutside {s.v} (x : GA L n) ∧ s.loc n x = Matrix.GeneralLinearGroup.map j.toRingHom (GlobalTheory.GLp.inc g n y)

attribute [local instance] GlobalTheory.TypeRec.factG

def KFix (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E)
    (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E))
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A) : Submodule ℂ A :=
  ⨅ (k : Fin 2) (v : D.nd.PlG k) (y : (GlobalTheory.GLp.red (D.host.g k) D.R.r).ker) (x : GAf D.host.E D.R.r)
    (_ : IsLiftAt (s k v) (j k v) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) x), LinearMap.ker (ρA x - LinearMap.id)

end GlobalTheory.TypeVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStandardAdelicAddCharGlobalAdelicCharStatement
section
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardAdelicAddChar_global_adelicChar : ∀ (E : Type) [Field E] [NumberField E], GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) := by
  first | exact @GlobalTheory.StdCharStd.stdPsi_adelicChar | exact GlobalTheory.StdCharStd.stdPsi_adelicChar | (intros; apply GlobalTheory.StdCharStd.stdPsi_adelicChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleRefineTensor
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem isSubquotient_jac_refine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (jac E π) := by
  intro k _ _ _ _ n s d e V _ _ π hπ X _ _ ρ _ hsub t d' e' Y _ _ ρ' hρ'
  refine ⟨refinePlace e e', ?_⟩
  refine isSubquotient_of_comp (flatHom fun a b => GL (Fin (d' a b)) k) (flatHom_surjective _) ?_
  obtain ⟨φR⟩ := GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested s t (fun a b => GL (Fin (d' a b)) k) Y ρ'
  obtain ⟨φT⟩ := GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized k s d t d' e' X ρ
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s n d e t d' e' V π
  have h1 : IsSubquotient (piTensor fun a => piTensor (ρ' a)) (piTensor fun a => jac (e' a) (ρ a)) :=
    GlobalTheory.piTensor_isSubquotient_of_forall _ _ _ _ _ _ hρ'
  have h3 := GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi k s d t d' e' _ _ (piTensor ρ) (jac e π) (isSmooth_jac e hπ) hsub
  exact (isSubquotient_of_equiv φR).trans (h1.trans ((isSubquotient_of_equiv φT.symm).trans
    (h3.trans (isSubquotient_of_equiv φS.symm))))

end GlobalTheory.JacStages
end


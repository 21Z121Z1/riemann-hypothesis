import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound
import Formalism.FlagUnipotentLattices.Bundle0010
import Formalism.FlagUnipotentLattices.FlagUnipotentLatticeOfRel
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ExistsTowerOfLocalSetting
import Formalism.FormalDegreeBessel.Bundle0002

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDefs
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

structure CSize (X : CData) where
  tau1 : X.I.GA → ℝ
  I0 : Set X.I.GA
  str : ∀ J : ℕ, Composition J → Set X.I.GA
  tau : ∀ (J : ℕ) (c : Composition J), X.I.GA → Fin c.length → ℝ
  kap : ∀ J : ℕ, Composition J → ℝ

def cn_Y (X : CData) : ℝ := Formalism.HermitianLatticeCounting.S7.Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b

def cn_tauS (X : CData) (C₁ : ℝ) : ℝ := cn_Y X ^ (-(C₁ * (X.qq : ℝ)))

def CSize.Mod {X : CData} (S : CSize X) (C₁ : ℝ) : Set X.I.GA := {x | cn_tauS X C₁ ≤ S.tau1 x}

def CSize.Strata {X : CData} (S : CSize X) : Prop :=
  Measurable S.tau1 ∧ (∀ J c, MeasurableSet (S.str J c)) ∧ (∀ J c, Measurable (S.tau J c)) ∧
    (∀ x, x ∈ S.I0 ∨ ∃ J, 1 ≤ J ∧ J ≤ X.qq ∧ ∃ c, x ∈ S.str J c) ∧ (∀ x ∈ S.I0, S.tau1 x = 1 / 2) ∧
    (∀ x, 0 < S.tau1 x ∧ S.tau1 x ≤ 1 / 2) ∧
    ∀ J c, ∀ x ∈ S.str J c, ∀ a, S.tau1 x ≤ S.tau J c x a

theorem CSize.measurableSet_Mod {X : CData} (S : CSize X) (h : S.Strata) (C₁ : ℝ) : MeasurableSet (S.Mod C₁) :=
  measurableSet_le measurable_const h.1

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentTranslateMeasurable
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Grp

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin (2 * r + k + 1) → Bool}
  {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}

theorem discrete_series_isometry (hσ : IsDSHpk k r ε lam σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (v : H) :
    ‖σ a v‖ = ‖v‖ := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have := hDS.2.2.1.2.1 _ (cayley_conj_mem_diagonal_model hP ha).1 v
  simpa only [(cayley_conj_mem_diagonal_model hP ha).2] using this

theorem discrete_series_inner (hσ : IsDSHpk k r ε lam σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (x y : H) :
    ⟪σ a x, σ a y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ a : H →ₗ[ℂ] H) (discrete_series_isometry hσ ha)).inner_map_map x y

theorem discrete_series_continuousOn (hσ : IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have h1 := hDS.2.2.1.2.2 v
  have hc : Continuous fun x : Mat k r => P * x * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h2 := h1.comp hc.continuousOn (fun a ha => (cayley_conj_mem_diagonal_model hP ha).1)
  refine h2.congr fun a ha => ?_
  simp only [Function.comp, (cayley_conj_mem_diagonal_model hP ha).2]

theorem isClosed_unitary_group (k r : ℕ) : IsClosed (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  have hc : Continuous fun g : Mat k r => gᴴ * Formalism.QuantumDeterminants.Hpk k r * g :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const

end Grp

namespace BData

variable (X : BData)

def EFix : Prop :=
  ∀ y : X.H, ∫ x, X.e (Matrix.of x) * ⟪y, X.σ (Matrix.of x) X.w⟫_ℂ ∂X.μG = ⟪y, X.w⟫_ℂ

def E2 (g y : Mat X.k X.r) : ℂ := (fdegH X.μG X.σ X.w : ℂ) * star ⟪X.σ g X.w, X.σ y X.w⟫_ℂ

variable {X}

theorem idempotent_translate_left (hX : X.Hyp) {g y : Mat X.k X.r} (hg : g ∈ X.G) (hy : y ∈ X.G) : X.E2 g (g * y) = X.e y := by
  show (fdegH X.μG X.σ X.w : ℂ) * star ⟪X.σ g X.w, X.σ (g * y) X.w⟫_ℂ =
    (fdegH X.μG X.σ X.w : ℂ) * star ⟪X.w, X.σ y X.w⟫_ℂ
  rw [discrete_series_map_mul hX.2.1 hg hy, ContinuousLinearMap.comp_apply, discrete_series_inner hX.2.1 hg]

theorem meas_orbit (hX : X.Hyp) (v : X.H) : AEStronglyMeasurable (fun y => X.σ (Matrix.of y) v) X.μG := by
  have hc : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt X.k X.r => X.σ (Matrix.of y) v) {y | Matrix.of y ∈ X.G} :=
    discrete_series_continuousOn hX.2.1 v
  have hm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt X.k X.r | Matrix.of y ∈ X.G} :=
    (show IsClosed {y : Formalism.QuantumDeterminants.Mt X.k X.r | Matrix.of y ∈ X.G} from isClosed_unitary_group X.k X.r).measurableSet
  have := hc.aestronglyMeasurable (μ := X.μG) hm
  have hae : ∀ᵐ y ∂X.μG, y ∈ {y : Formalism.QuantumDeterminants.Mt X.k X.r | Matrix.of y ∈ X.G} := ae_mem hX
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at this

theorem meas_Φ (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ) {x : Mat X.k X.r} (hx : x ∈ X.G) :
    AEStronglyMeasurable (fun y => X.Φ B χ (x * Matrix.of y)) X.μG :=
  hχ.2.2.1.comp_measurePreserving (mp_left hX hx)

theorem idempotent_translate_measurable (hX : X.Hyp) (g : Mat X.k X.r) : AEStronglyMeasurable (fun y => X.E2 g (Matrix.of y)) X.μG := by
  unfold E2
  refine AEStronglyMeasurable.const_mul ?_ _
  exact Complex.continuous_conj.comp_aestronglyMeasurable (aestronglyMeasurable_const.inner (meas_orbit hX X.w))

theorem subst (hX : X.Hyp) (B : X.H → X.Vp) (χ : Mat X.k X.r → ℝ) (x : Mat X.k X.r) {g : Mat X.k X.r}
    (hg : g ∈ X.G) :
    (fun y => X.E2 g (Matrix.of (Formalism.QuantumDeterminants.lmulM g y)) • X.Φ B χ (x * Matrix.of (Formalism.QuantumDeterminants.lmulM g y))) =ᵐ[X.μG]
      fun y => X.e (Matrix.of y) • X.Φ B χ (x * g * Matrix.of y) := by
  filter_upwards [ae_mem hX] with y hy
  have e1 : Matrix.of (Formalism.QuantumDeterminants.lmulM g y) = g * Matrix.of y := rfl
  rw [e1, idempotent_translate_left hX hg hy, Matrix.mul_assoc]

theorem meas_F (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ) {x : Mat X.k X.r}
    (hx : x ∈ X.G) (g : Mat X.k X.r) :
    AEStronglyMeasurable (fun y => X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)) X.μG :=
  (idempotent_translate_measurable hX g).smul (meas_Φ hX hχ hx)

theorem integrable_F (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ) (he : X.ConvolutionKernelIntegrable)
    {x g : Mat X.k X.r} (hx : x ∈ X.G) (hg : g ∈ X.G) :
    Integrable (fun y => X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)) X.μG := by
  have h1 : Integrable (fun y => X.e (Matrix.of y) • X.Φ B χ (x * g * Matrix.of y)) X.μG :=
    integrable_conv hX hχ he (unitary_group_mul_mem hx hg)
  have h2 := h1.congr (subst hX B χ x hg).symm
  exact ((mp_left hX hg).integrable_comp (meas_F hX hχ hx g)).1 h2

theorem integral_F (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ)
    {x g : Mat X.k X.r} (hx : x ∈ X.G) (hg : g ∈ X.G) :
    ∫ y, X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y) ∂X.μG =
      ∫ y, X.e (Matrix.of y) • X.Φ B χ (x * g * Matrix.of y) ∂X.μG := by
  rw [← integral_congr_ae (subst hX B χ x hg)]
  have hmp := mp_left hX hg
  have hm : AEStronglyMeasurable (fun y => X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y))
      (X.μG.map (Formalism.QuantumDeterminants.lmulM g)) := by rw [hmp.map_eq]; exact meas_F hX hχ hx g
  have := integral_map hmp.measurable.aemeasurable hm
  rw [hmp.map_eq] at this
  exact this

theorem integral_normF (hX : X.Hyp) {B : X.H → X.Vp} {χ : Mat X.k X.r → ℝ} (hχ : X.IsCut B χ)
    {x g : Mat X.k X.r} (hx : x ∈ X.G) (hg : g ∈ X.G) :
    ∫ y, ‖X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)‖ ∂X.μG =
      ∫ y, ‖X.e (Matrix.of y) • X.Φ B χ (x * g * Matrix.of y)‖ ∂X.μG := by
  rw [← integral_congr_ae ((subst hX B χ x hg).mono fun y hy => congrArg norm hy)]
  have hmp := mp_left hX hg
  have hm : AEStronglyMeasurable (fun y => ‖X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)‖)
      (X.μG.map (Formalism.QuantumDeterminants.lmulM g)) := by rw [hmp.map_eq]; exact (meas_F hX hχ hx g).norm
  have := integral_map hmp.measurable.aemeasurable hm
  rw [hmp.map_eq] at this
  exact this

theorem idempotent_convolution_self (hf : X.EFix) (y : Mat X.k X.r) :
    ∫ g, X.e (Matrix.of g) * X.E2 (Matrix.of g) y ∂X.μG = X.e y := by
  have h1 : ∀ g : Formalism.QuantumDeterminants.Mt X.k X.r, X.e (Matrix.of g) * X.E2 (Matrix.of g) y =
      (fdegH X.μG X.σ X.w : ℂ) * (X.e (Matrix.of g) * ⟪X.σ y X.w, X.σ (Matrix.of g) X.w⟫_ℂ) := by
    intro g
    unfold E2
    rw [show star ⟪X.σ (Matrix.of g) X.w, X.σ y X.w⟫_ℂ = ⟪X.σ y X.w, X.σ (Matrix.of g) X.w⟫_ℂ from
      inner_conj_symm _ _]
    ring
  simp only [h1]
  rw [integral_const_mul, hf (X.σ y X.w)]
  show (fdegH X.μG X.σ X.w : ℂ) * ⟪X.σ y X.w, X.w⟫_ℂ = (fdegH X.μG X.σ X.w : ℂ) * star ⟪X.w, X.σ y X.w⟫_ℂ
  rw [show star ⟪X.w, X.σ y X.w⟫_ℂ = ⟪X.σ y X.w, X.w⟫_ℂ from inner_conj_symm _ _]

theorem idem_of (hX : X.Hyp) {B : X.H → X.Vp} (he : X.ConvolutionKernelIntegrable) (hf : X.EFix) : X.IdemStep B := by
  intro χ hχ x hx
  have : SigmaFinite X.μG := hX.2.2.2.2.1.1
  obtain ⟨M, hM⟩ := hχ.2.2.2.1
  set f : Formalism.QuantumDeterminants.Mt X.k X.r → Formalism.QuantumDeterminants.Mt X.k X.r → X.Vp := fun g y =>
    (X.e (Matrix.of g) * X.E2 (Matrix.of g) (Matrix.of y)) • X.Φ B χ (x * Matrix.of y) with hfdef

  have hmeas : AEStronglyMeasurable (Function.uncurry f) (X.μG.prod X.μG) := by
    have m1 : AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r => X.e (Matrix.of p.1))
        (X.μG.prod X.μG) := he.aestronglyMeasurable.comp_fst
    have m2 : AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r =>
        X.E2 (Matrix.of p.1) (Matrix.of p.2)) (X.μG.prod X.μG) := by
      unfold E2
      refine AEStronglyMeasurable.const_mul ?_ _
      exact Complex.continuous_conj.comp_aestronglyMeasurable
        ((meas_orbit hX X.w).comp_fst.inner (meas_orbit hX X.w).comp_snd)
    have m3 : AEStronglyMeasurable (fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r =>
        X.Φ B χ (x * Matrix.of p.2)) (X.μG.prod X.μG) := (meas_Φ hX hχ hx).comp_snd
    exact (m1.mul m2).smul m3
  have hbound : ∀ g : Mat X.k X.r, g ∈ X.G →
      ∫ y, ‖X.E2 g (Matrix.of y) • X.Φ B χ (x * Matrix.of y)‖ ∂X.μG ≤ M * ∫ y, ‖X.e (Matrix.of y)‖ ∂X.μG := by
    intro g hg
    rw [integral_normF hX hχ hx hg, ← integral_const_mul]
    refine integral_mono_ae (integrable_conv hX hχ he (unitary_group_mul_mem hx hg)).norm (he.norm.const_mul M) ?_
    filter_upwards [ae_mem hX] with y hy
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _ (unitary_group_mul_mem (unitary_group_mul_mem hx hg) hy)) (norm_nonneg _)
  have hint : Integrable (Function.uncurry f) (X.μG.prod X.μG) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · filter_upwards [ae_mem hX] with g hg
      have := (integrable_F hX hχ he hx hg).smul (X.e (Matrix.of g))
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [Function.uncurry, hfdef, Pi.smul_apply, smul_smul]
    · refine Integrable.mono' (he.norm.mul_const (M * ∫ y, ‖X.e (Matrix.of y)‖ ∂X.μG))
        hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_mem hX] with g hg
      have e1 : ∀ y, ‖Function.uncurry f (g, y)‖ =
          ‖X.e (Matrix.of g)‖ * ‖X.E2 (Matrix.of g) (Matrix.of y) • X.Φ B χ (x * Matrix.of y)‖ := by
        intro y
        simp only [Function.uncurry, hfdef, mul_smul, norm_smul]
      simp only [e1]
      rw [integral_const_mul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (integral_nonneg fun y => norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hbound _ hg) (norm_nonneg _)

  have s1 : rconv X.μG X.e (X.Wf B χ) x = ∫ g, ∫ y, f g y ∂X.μG ∂X.μG := by
    unfold rconv
    refine integral_congr_ae ?_
    filter_upwards [ae_mem hX] with g hg
    have : X.Wf B χ (x * Matrix.of g) = ∫ y, X.E2 (Matrix.of g) (Matrix.of y) • X.Φ B χ (x * Matrix.of y) ∂X.μG := by
      rw [integral_F hX hχ hx hg]
      rfl
    rw [this, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hfdef, mul_smul]
  rw [s1, integral_integral_swap hint]
  unfold Wf rconv
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hfdef]
  rw [integral_smul_const, idempotent_convolution_self hf]

end BData

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionChange
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exp_lie_algebra_mem_unitary (k r : ℕ) (X : CayleySignature.Mat k r) (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  obtain ⟨-, hH2, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
  set Hm := Formalism.QuantumDeterminants.Hpk k r with hHm
  set Y : CayleySignature.Mat k r := (t : ℂ) • X with hYdef
  have hY : Yᴴ * Hm + Hm * Y = 0 := by
    have h1 : Yᴴ = (t : ℂ) • Xᴴ := by simp [hYdef, Matrix.conjTranspose_smul]
    have h2 : Xᴴ * Hm + Hm * X = 0 := hX
    rw [h1, hYdef, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h2, smul_zero]
  have hinv : Hm⁻¹ = Hm := Matrix.inv_eq_right_inv hH2
  have hYh : Yᴴ = Hm * (-Y) * Hm⁻¹ := by
    rw [hinv]
    have h1 : Yᴴ * Hm = -(Hm * Y) := eq_neg_of_add_eq_zero_left hY
    calc Yᴴ = Yᴴ * (Hm * Hm) := by rw [hH2, Matrix.mul_one]
      _ = (Yᴴ * Hm) * Hm := by rw [Matrix.mul_assoc]
      _ = Hm * (-Y) * Hm := by rw [h1, Matrix.mul_neg]
  have hu : IsUnit Hm := ⟨⟨Hm, Hm, hH2, hH2⟩, rfl⟩
  have hdet : IsUnit (NormedSpace.exp Y).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp Y)
  show (NormedSpace.exp Y)ᴴ * Hm * NormedSpace.exp Y = Hm
  rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hu, hinv, Matrix.exp_neg]
  calc Hm * (NormedSpace.exp Y)⁻¹ * Hm * Hm * NormedSpace.exp Y
      = Hm * (NormedSpace.exp Y)⁻¹ * (Hm * Hm) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = Hm * ((NormedSpace.exp Y)⁻¹ * NormedSpace.exp Y) := by rw [hH2, Matrix.mul_one, Matrix.mul_assoc]
    _ = Hm := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

theorem mat_mul_mem_UH_Hpk {k r : ℕ} {g h : CayleySignature.Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hh : h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : g * h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = Formalism.QuantumDeterminants.Hpk k r
  calc (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hg', hh']

section Move

variable {k r : ℕ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
  [InnerProductSpace ℂ H']

theorem intertwiner_symm_apply (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x))
    (g : CayleySignature.Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (x' : H') :
    σ g (U.symm x') = U.symm (σ' g x') := by
  apply U.injective
  rw [hU g hg, U.apply_symm_apply, U.apply_symm_apply]

theorem smooth_vectors_intertwiner_symm (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x))
    {x' : H'} (hx : x' ∈ smoothVecs (k := k) (r := r) σ') : U.symm x' ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨Uo, F, hO, hmem, hF, hEq⟩ := hx g₀ hg₀
  refine ⟨Uo, fun g => U.symm (F g), hO, hmem, ?_, fun g hg hin => ?_⟩
  · exact ((U.symm.contDiff).restrict_scalars ℝ).comp_contDiffOn hF
  · have h1 : σ' g x' = F g := hEq g hg hin
    show σ g (U.symm x') = U.symm (F g)
    rw [intertwiner_symm_apply σ σ' U hU g hin, h1]

theorem deriv_isometry_symm_zero (U : H ≃ₗᵢ[ℂ] H') (f : ℝ → H') :
    deriv (fun t => U.symm (f t)) 0 = U.symm (deriv f 0) := by
  let e : H' ≃L[ℝ] H :=
    { toLinearEquiv := U.symm.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := U.symm.continuous
      continuous_invFun := U.continuous }
  have he : ∀ y, e y = U.symm y := fun y => rfl
  by_cases hd : DifferentiableAt ℝ f 0
  · exact ((e : H' →L[ℝ] H).hasFDerivAt.comp_hasDerivAt 0 hd.hasDerivAt).deriv
  · have hd' : ¬ DifferentiableAt ℝ (fun t => U.symm (f t)) 0 := fun h =>
      hd ((e.comp_differentiableAt_iff (f := f) (x := 0)).1 h)
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', map_zero]

theorem derivative_word_intertwiner_symm (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x))
    (w : List (CayleySignature.Mat k r)) (hw : ∀ X ∈ w, InLieHpk k r X) (x' : H') :
    dsigW (k := k) (r := r) σ w (U.symm x') = U.symm (dsigW (k := k) (r := r) σ' w x') := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    have ihw := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    show dsig σ X (dsigW σ w (U.symm x')) = U.symm (dsig σ' X (dsigW σ' w x'))
    rw [ihw]
    unfold dsig
    rw [← deriv_isometry_symm_zero U]
    congr 1
    funext t
    exact intertwiner_symm_apply σ σ' U hU _ (exp_lie_algebra_mem_unitary k r X (hw X List.mem_cons_self) t) _

theorem bessel_map_transport_sigma (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x))
    {Vp : Type} [NormedAddCommGroup Vp] [NormedSpace ℂ Vp] (z : Fin (2 * r + k + 1) → ℂ) (ψ : CayleySignature.Mat k r → ℂ)
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)) (B : H → Vp) (N : ℕ)
    (hB : IsBesselMapSm z ψ σ π B) (hO : HasOrdLe k r N σ B) (hne : ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) :
    IsBesselMapSm z ψ σ' π (fun x' => B (U.symm x')) ∧ HasOrdLe k r N σ' (fun x' => B (U.symm x')) ∧
      ∃ x' ∈ smoothVecs (k := k) (r := r) σ', B (U.symm x') ≠ 0 := by
  have hs := fun {x' : H'} (hx : x' ∈ smoothVecs (k := k) (r := r) σ') => smooth_vectors_intertwiner_symm σ σ' U hU hx
  obtain ⟨b1, b2, b3, C, Ws, hWs, hbd⟩ := hB
  have hsum : ∀ (Ws : List (List (CayleySignature.Mat k r))), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) → ∀ v' : H',
      (Ws.map fun w => ‖dsigW (k := k) (r := r) σ w (U.symm v')‖) =
        (Ws.map fun w => ‖dsigW (k := k) (r := r) σ' w v'‖) := by
    intro Ws hWs v'
    refine List.map_congr_left fun w hw => ?_
    rw [derivative_word_intertwiner_symm σ σ' U hU w (hWs w hw), U.symm.norm_map]
  refine ⟨⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, C, Ws, hWs, fun v hv => ?_⟩, ?_, ?_⟩
  · show B (U.symm (v + w)) = _
    rw [map_add]; exact b1 _ (hs hv) _ (hs hw)
  · show B (U.symm (c • v)) = _
    rw [map_smul]; exact b2 c _ (hs hv)
  · show B (U.symm (σ' (h * m) v)) = _
    rw [← intertwiner_symm_apply σ σ' U hU _ (mat_mul_mem_UH_Hpk hh.1 hm.1)]
    exact b3 h hh m hm _ (hs hv)
  · rw [← hsum Ws hWs v]; exact hbd _ (hs hv)
  · obtain ⟨C', Ws', hW', hbd'⟩ := hO
    refine ⟨C', Ws', hW', fun v hv => ?_⟩
    rw [← hsum Ws' (fun w hw => (hW' w hw).2) v]; exact hbd' _ (hs hv)
  · obtain ⟨x, hx, hxne⟩ := hne
    refine ⟨U x, ?_, by rwa [U.symm_apply_apply]⟩
    have := smooth_vectors_intertwiner_symm σ' σ U.symm (fun g hg x' => (intertwiner_symm_apply σ σ' U hU g hg x').symm) hx
    simpa using this

theorem bessel_map_transport_pi (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) {Vp Vp' : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [NormedAddCommGroup Vp'] [InnerProductSpace ℂ Vp'] (z : Fin (2 * r + k + 1) → ℂ) (ψ : CayleySignature.Mat k r → ℂ)
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)) (π' : CayleySignature.Mat k r → (Vp' →L[ℂ] Vp')) (A : Vp ≃ₗᵢ[ℂ] Vp')
    (hA : ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, A (π h x) = π' h (A x)) (B : H → Vp) (N : ℕ)
    (hB : IsBesselMapSm z ψ σ π B) (hO : HasOrdLe k r N σ B) (hne : ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) :
    IsBesselMapSm z ψ σ π' (fun x => A (B x)) ∧ HasOrdLe k r N σ (fun x => A (B x)) ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, A (B x) ≠ 0 := by
  obtain ⟨b1, b2, b3, C, Ws, hWs, hbd⟩ := hB
  refine ⟨⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, C, Ws, hWs, fun v hv => ?_⟩, ?_, ?_⟩
  · show A (B (v + w)) = _
    rw [b1 v hv w hw, map_add]
  · show A (B (c • v)) = _
    rw [b2 c v hv, map_smul]
  · show A (B (σ (h * m) v)) = _
    rw [b3 h hh m hm v hv, map_smul, hA h hh]
  · show ‖A (B v)‖ ≤ _
    rw [A.norm_map]; exact hbd v hv
  · obtain ⟨C', Ws', hW', hbd'⟩ := hO
    exact ⟨C', Ws', hW', fun v hv => by
      show ‖A (B v)‖ ≤ _
      rw [A.norm_map]; exact hbd' v hv⟩
  · obtain ⟨x, hx, hxne⟩ := hne
    exact ⟨x, hx, fun h => hxne (A.injective (by rw [h, map_zero]))⟩

end Move

def DiscreteSeriesUniqueUpToUnitaryEquiv : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ →
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')),
    IsDSHpk k r ε lam σ' →
  ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x)

def HighestWeightUnique : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.IsHCParam u →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ (Vp' : Type) [NormedAddCommGroup Vp'] [InnerProductSpace ℂ Vp'] [FiniteDimensional ℂ Vp']
    (π' : CayleySignature.Mat k r → (Vp' →L[ℂ] Vp')), IsHCTypeW k r z u π' →
  ∃ A : Vp ≃ₗᵢ[ℂ] Vp', ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, A (π h x) = π' h (A x)

def PositionChange : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), Formalism.QuantumDeterminants.IsHCParam u →
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) →
  ∀ (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.inWb k r z' → 0 < Formalism.QuantumDeterminants.Tz k r z' → (∀ a, c' a ≠ 0) → (∃ g', IsFrameW k r z' g') →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ (B : H → Vp) (N : ℕ), IsBesselMapSm z (psiGen k r z c) σ π B → HasOrdLe k r N σ B →
    (∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) →
  ∃ (π' : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z' u π' ∧
    ∃ B' : H → Vp, IsBesselMapSm z' (psiGen k r z' c') σ π' B' ∧ HasOrdLe k r N σ B' ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, B' x ≠ 0

theorem local_transport_of_position_change (hD : DiscreteSeriesUniqueUpToUnitaryEquiv) (hC : HighestWeightUnique) (hP : PositionChange) : LocalTransport := by
  intro k r u v b hu hl hsome z c hz hT hc H _ _ _ σ hσ Vp _ _ _ π hπ
  obtain ⟨z0, c0, hz0, hT0, hc0, H0, i1, i2, i3, σ0, hσ0, Vp0, j1, j2, j3, π0, hπ0, B0, hB0, hO0, hne0⟩ := hsome
  obtain ⟨π1, hπ1, B1, hB1, hO1, hne1⟩ :=
    hP k r u v b hu hl z0 z c0 c hz0 hT0 hc0 hz hT hc ⟨hπ.choose, hπ.choose_spec.1⟩ H0 σ0 hσ0 Vp0 π0 hπ0 B0 _ hB0 hO0 hne0
  obtain ⟨U, hU⟩ := hD k r _ _ hl H0 σ0 hσ0 H σ hσ
  obtain ⟨hB2, hO2, hne2⟩ := bessel_map_transport_sigma σ0 σ U hU z _ π1 B1 _ hB1 hO1 hne1
  obtain ⟨A, hA⟩ := hC k r z u hz hT hu Vp0 π1 hπ1 Vp π hπ
  obtain ⟨hB3, hO3, hne3⟩ := bessel_map_transport_pi σ z _ π1 π A hA _ _ hB2 hO2 hne2
  exact ⟨_, hB3, hO3, hne3⟩

theorem ordered_at_ranks_of_position_change (D : D7) (X : ThetaX D) (C : ℝ) (h3 : PointsLemma D X) (h4 : Step4 D X) (hD : DiscreteSeriesUniqueUpToUnitaryEquiv)
    (hC : HighestWeightUnique) (hP : PositionChange) : OrderedAtRanks D C :=
  ordered_at_ranks_of_tower_hyp D X C h3 h4 (local_transport_of_position_change hD hC hP)

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnimodF
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def RepA (X : CData) : Prop :=
  (∀ g h, X.R (g * h) = X.R g ∘L X.R h) ∧ X.R 1 = 1 ∧ (∀ g (F : X.L2), ‖X.R g F‖ = ‖F‖) ∧
    ∀ F : X.L2, Continuous fun g => X.R g F

def UnimodF (X : CData) : Prop := X.μf.IsMulRightInvariant

end Formalism.MainNotions.LeviCoordinates

end
end


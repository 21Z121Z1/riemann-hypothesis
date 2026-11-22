import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFinitePlaneMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformHeckeEigenvalue
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspidality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvalues

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalZetaOfAnnulusFunction
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel
open Ad3 Ad3.LFS GlobalTheory.CompanionTheory.LFDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LFDual.ZRho

section Compact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isCompact_modulus_le (R : ℝ) : IsCompact {x : F | (modulus x : ℝ) ≤ R} := by
  have hq : (1 : ℝ) < (residueCard F : ℝ) := by exact_mod_cast one_lt_residueCard (K := F)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R hq
  have hO : IsCompact (𝒪[F] : Set F) := IsNonarchimedeanLocalField.isCompact_closedBall F 1
  set u : Fˣ := unifUnit F ^ (k : ℤ) with hu
  have hI : IsCompact ((fun y : F => y * ((u⁻¹ : Fˣ) : F)) '' (𝒪[F] : Set F)) :=
    hO.image (continuous_id.mul continuous_const)
  have hmod : Continuous fun x : F => (modulus x : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  refine hI.of_isClosed_subset (isClosed_le hmod continuous_const) ?_
  intro x hx
  refine ⟨x * (u : F), ?_, by simp⟩
  have hmu : (modulus (u : F) : ℝ) = ((residueCard F : ℝ) ^ k)⁻¹ := by
    rw [modulus_of_ne_zero u.ne_zero, hu, ord_unifUnit_zpow]
    push_cast
    rw [_root_.zpow_neg, zpow_natCast]
  have hx' : (modulus x : ℝ) ≤ R := hx
  have hpos : (0 : ℝ) < (residueCard F : ℝ) ^ k := by positivity
  apply (modulus_le_one_iff).1
  rw [modulus_mul, ← NNReal.coe_le_coe]
  push_cast
  rw [hmu, ← div_eq_mul_inv, div_le_one hpos]
  exact hx'.trans hk.le

theorem isCompact_shell {r : ℝ} (hr : 0 < r) (R : ℝ) :
    IsCompact {τ : Fˣ | r ≤ (modulus (τ : F) : ℝ) ∧ (modulus (τ : F) : ℝ) ≤ R} := by
  have hmod : Continuous fun x : F => (modulus x : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  have hK : IsCompact {x : F | r ≤ (modulus x : ℝ) ∧ (modulus x : ℝ) ≤ R} :=
    (isCompact_modulus_le R).of_isClosed_subset
      ((isClosed_le continuous_const hmod).inter (isClosed_le hmod continuous_const))
      fun x hx => hx.2
  have hsub : {x : F | r ≤ (modulus x : ℝ) ∧ (modulus x : ℝ) ≤ R} ⊆ Set.range (Units.val : Fˣ → F) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := hx.1
      simp at this
      linarith
    exact ⟨Units.mk0 x hx0, rfl⟩
  exact ((isOpenEmbedding_units_val (K := F)).isInducing.isCompact_preimage_iff hsub).2 hK

theorem continuous_mp (z : ℂ) : Continuous fun τ : Fˣ => mp τ z := by
  have hm : Continuous fun τ : Fˣ => (((modulus (τ : F) : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  exact hm.cpow continuous_const fun τ =>
    Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast modulus_pos τ.ne_zero)

end Compact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem continuous_Atau {f : F → ℂ} {c : Fˣ →* ℂˣ} (hf : Continuous f) (hc : IsUnit1 c) (s lam : ℂ) :
    Continuous (Atau f c s lam) := by
  unfold Atau
  exact ((hf.comp Units.continuous_val).mul
    (Units.continuous_val.comp hc.1.inv)).mul (continuous_mp _)

theorem integrable_and_integral_Atau : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (f : F → ℂ) (c : Fˣ →* ℂˣ), Continuous f → (∃ r R : ℝ, 0 < r ∧ ∀ x, f x ≠ 0 → r ≤ (modulus x : ℝ) ∧ (modulus x : ℝ) ≤ R) → IsUnit1 c → ∀ s lam : ℂ, Integrable (Atau f c s lam) (rho F) ∧ ∫ τ, Atau f c s lam τ ∂rho F = kq F * localZeta f c⁻¹ (1 - s - lam) := by
  intro F _ _ _ _ _ _ f c hf ⟨r, R, hr, hsupp⟩ hc s lam
  have hmodc : Continuous fun τ : Fˣ => (modulus (τ : F) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val)
  set k : ℝ := ((multHaarConst F).toReal)⁻¹ with hk
  have hk0 : 0 ≤ k := inv_nonneg.2 ENNReal.toReal_nonneg
  set g : Fˣ → ENNReal := fun τ => ENNReal.ofReal (k * (modulus (τ : F) : ℝ) ^ 2) with hg
  have hgm : Measurable g := (continuous_const.mul (hmodc.pow 2)).measurable.ennreal_ofReal
  have hglt : ∀ᵐ τ ∂multHaar F, g τ < ⊤ := Eventually.of_forall fun τ => ENNReal.ofReal_lt_top
  have hgr : ∀ τ, (g τ).toReal = k * (modulus (τ : F) : ℝ) ^ 2 := fun τ =>
    ENNReal.toReal_ofReal (by positivity)
  have hA := continuous_Atau hf hc s lam
  have hcont : Continuous fun τ : Fˣ => (g τ).toReal • Atau f c s lam τ := by
    simp only [hgr]
    exact (continuous_const.mul (hmodc.pow 2)).smul hA
  have hcs : HasCompactSupport fun τ : Fˣ => (g τ).toReal • Atau f c s lam τ := by
    refine HasCompactSupport.intro (isCompact_shell hr R) fun τ hτ => ?_
    have h0 : f (τ : F) = 0 := by
      by_contra h
      exact hτ (hsupp _ h)
    simp [Atau, h0]
  have hsm : Integrable (fun τ : Fˣ => (g τ).toReal • Atau f c s lam τ) (multHaar F) :=
    hcont.integrable_of_hasCompactSupport hcs
  refine ⟨(integrable_withDensity_iff_integrable_smul' hgm hglt).2 hsm, ?_⟩
  have hrho : rho F = (multHaar F).withDensity g := rfl
  rw [hrho, integral_withDensity_eq_integral_toReal_smul hgm hglt, localZeta, kq,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  have hm0 : (((modulus (τ : F) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero τ.ne_zero
  have hpow : (((modulus (τ : F) : ℝ)) : ℂ) ^ (1 - s - lam) =
      (((modulus (τ : F) : ℝ)) : ℂ) ^ 2 * mp τ (-s - 1 - lam) := by
    rw [mp, ← Complex.cpow_ofNat, ← Complex.cpow_add _ _ hm0]
    congr 1
    push_cast
    ring
  simp only [hgr, Atau, hpow, MonoidHom.inv_apply, Complex.real_smul]
  rw [hk]
  push_cast
  ring

end GlobalTheory.CompanionTheory.LFDual.ZRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerZetaIntegralBoundaryRelation
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem integrableOn_band_w {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd}
    {H : G2 → ℂ} (c : HeckeCharacter ℚ) (hS : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) (s : ℂ)
    (hmb : MeasurableSet band) :
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ band) μ := by
  obtain ⟨C, hC⟩ := hH.bdd
  have hmF : MeasurableSet (𝓕 ∩ band) := hS.meas.inter hmb
  refine Measure.integrableOn_of_bounded (M := C * (2 : ℝ) ^ |s.re|) hS.vol.ne
    (measurable_w hH c s).aestronglyMeasurable ?_
  refine (ae_restrict_iff' hmF).2 (Eventually.of_forall fun g hg => ?_)
  obtain ⟨h1, h2⟩ := hg.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hp : (Dt g) ^ s.re ≤ (2 : ℝ) ^ |s.re| :=
    (Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self _)).trans
      (Real.rpow_le_rpow (Dt_pos g).le h2.le (abs_nonneg _))
  rw [norm_mul, norm_mul, norm_cdet, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
  exact mul_le_mul (hC g) hp (Real.rpow_nonneg (Dt_pos g).le _) hC0

theorem cpow_half (s : ℂ) : (((1 / 2 : ℝ)) : ℂ) ^ s = 2 ^ (-s) := by
  have h2 : (2 : ℂ).arg ≠ Real.pi := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_pos.ne
  rw [show (((1 / 2 : ℝ)) : ℂ) = (2 : ℂ)⁻¹ by push_cast; norm_num, Complex.inv_cpow _ _ h2,
    Complex.cpow_neg]

theorem Jl_shift : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ →
    GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s * (1 - 2 ^ (-s)) = GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s * 2 ^ (-s) := by
  intro μ 𝓕 mK 𝓓 H c hG hS hH hc s hI
  set w : G2 → ℂ := fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s with hw
  obtain ⟨-, hr, hT⟩ := hG μ 𝓕 mK 𝓓 hS
  obtain ⟨z, hz2, hzc⟩ := hr (1 / 2) (by norm_num)
  have hzc' := hzc c hc
  have hm1 : MeasurableSet {g : G2 | Dt g < 1} := measurableSet_lt measurable_Dt measurable_const
  have hm2 : MeasurableSet {g : G2 | Dt g < 2} := measurableSet_lt measurable_Dt measurable_const
  have hmb : MeasurableSet band :=
    (measurableSet_le measurable_const measurable_Dt).inter hm2
  have hwm : Measurable w := measurable_w hH c s
  have hset : {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} = {g : G2 | Dt g < 1} := rfl
  have hFm : Measurable (Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w) :=
    hwm.indicator hm1
  have hFl : LInv (Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w) :=
    linv_ind (linv_w hH c s) _
  have hinv : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) ∂μ =
      ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w g ∂μ :=
    (hT (fun g : G2 => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hFm hFl
  have hpt : ∀ g : G2, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) =
      2 ^ (-s) * Set.indicator {g : G2 | Dt g < 2} w g := by
    intro g
    have hD : Dt (dg2 z z * g) = 1 / 2 * Dt g := by rw [Dt_dg, hz2]
    have hwg : w (dg2 z z * g) = 2 ^ (-s) * w g := by
      simp only [hw]
      rw [hH.cen z g, cdet_dg c z hzc' g, cpow_dg, hz2, cpow_half]
      ring
    by_cases h : Dt g < 2
    · have h' : dg2 z z * g ∈ {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} := by
        simp only [Set.mem_setOf_eq, Set.mem_Iio, hD]; linarith
      rw [Set.indicator_of_mem h', Set.indicator_of_mem (show g ∈ {g : G2 | Dt g < 2} from h), hwg]
    · have h' : dg2 z z * g ∉ {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} := by
        simp only [Set.mem_setOf_eq, Set.mem_Iio, hD]; linarith
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (show g ∉ {g : G2 | Dt g < 2} from h),
        mul_zero]
  have e1 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) ∂μ =
      2 ^ (-s) * ∫ g in 𝓕 ∩ {g : G2 | Dt g < 2}, w g ∂μ := by
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_indicator hm2]
  have e2 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w g ∂μ =
      GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
    rw [hset, setIntegral_indicator hm1]
    rfl
  have hun : 𝓕 ∩ {g : G2 | Dt g < 2} = (𝓕 ∩ {g : G2 | Dt g < 1}) ∪ (𝓕 ∩ band) := by
    ext g
    simp only [band, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : Dt g < 1
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, not_lt.1 h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, -, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨h1, h2⟩
  have hdis : Disjoint (𝓕 ∩ {g : G2 | Dt g < 1}) (𝓕 ∩ band) := by
    refine Set.disjoint_left.2 fun g hg hb => ?_
    have h1 : Dt g < 1 := hg.2
    have h2 : 1 ≤ Dt g := hb.2.1
    linarith
  have e3 : ∫ g in 𝓕 ∩ {g : G2 | Dt g < 2}, w g ∂μ =
      GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s + GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s := by
    rw [hun, setIntegral_union hdis (hS.meas.inter hmb) hI (integrableOn_band_w c hS hH s hmb)]
    rfl
  have key : 2 ^ (-s) * (GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s + GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s) =
      GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
    rw [← e3, ← e1, hinv, e2]
  linear_combination -key

end GlobalTheory.CompanionTheory.RSZeta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapEqOne
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open PositivityTheory.Rg.Rsw.Em
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AlgStab

section Gen
variable {R : Type} [CommRing R] {a n : ℕ}

private noncomputable def twoSide [TopologicalSpace R] [IsTopologicalRing R] (h hi : Matrix (Fin a) (Fin a) R)
    (g gi : Matrix (Fin n) (Fin n) R) (h1 : h * hi = 1) (h2 : hi * h = 1) (g1 : g * gi = 1) (g2 : gi * g = 1) :
    Matrix (Fin a) (Fin n) R ≃ₜ Matrix (Fin a) (Fin n) R where
  toFun X := h * X * g
  invFun X := hi * X * gi
  left_inv X := by
    show hi * (h * X * g) * gi = X
    rw [Matrix.mul_assoc h, ← Matrix.mul_assoc hi, h2, Matrix.one_mul, Matrix.mul_assoc, g1, Matrix.mul_one]
  right_inv X := by
    show h * (hi * X * gi) * g = X
    rw [Matrix.mul_assoc hi, ← Matrix.mul_assoc h, h1, Matrix.one_mul, Matrix.mul_assoc, g2, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private theorem map_inv {S : Type} [CommRing S] (f : R →+* S) {x y : Matrix (Fin a) (Fin a) R} (h : x * y = 1) :
    x.map f * y.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_eq_one {S : Type} [CommRing S] (f : R →+* S) {e : R} (he : f e = 0) {x : Matrix (Fin a) (Fin a) R}
    (h : e • (x - 1) = x - 1) : x.map f = 1 := by
  have h0 : (x - 1).map f = 0 := by
    rw [← h]
    ext i j
    simp [he]
  rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)] at h0
  exact sub_eq_zero.1 h0

private noncomputable def famEquiv {T : Type} [Fintype T] (h hi : T → Matrix (Fin a) (Fin a) ℂ) (g gi : T → Matrix (Fin n) (Fin n) ℂ)
    (h1 : ∀ τ, h τ * hi τ = 1) (h2 : ∀ τ, hi τ * h τ = 1) (g1 : ∀ τ, g τ * gi τ = 1) (g2 : ∀ τ, gi τ * g τ = 1) :
    (T → Fin a → Fin n → ℂ) ≃L[ℝ] (T → Fin a → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X τ => (h τ * Matrix.of (X τ) * g τ : Matrix (Fin a) (Fin n) ℂ)
      invFun := fun X τ => (hi τ * Matrix.of (X τ) * gi τ : Matrix (Fin a) (Fin n) ℂ)
      map_add' := fun X Y => by
        funext τ
        show h τ * (Matrix.of (X τ) + Matrix.of (Y τ)) * g τ = h τ * Matrix.of (X τ) * g τ + h τ * Matrix.of (Y τ) * g τ
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        funext τ
        show h τ * (c • Matrix.of (X τ)) * g τ = c • (h τ * Matrix.of (X τ) * g τ)
        rw [Matrix.mul_smul, Matrix.smul_mul]
      left_inv := fun X => funext fun τ => (twoSide (h τ) (hi τ) (g τ) (gi τ) (h1 τ) (h2 τ) (g1 τ) (g2 τ)).left_inv (Matrix.of (X τ))
      right_inv := fun X => funext fun τ => (twoSide (h τ) (hi τ) (g τ) (gi τ) (h1 τ) (h2 τ) (g1 τ) (g2 τ)).right_inv (Matrix.of (X τ)) }

end Gen

private theorem schw {D : D7} (θ : InfFam D) {a n : ℕ} (h : GL (Fin a) (AE D)) (g : GL (Fin n) (AE D)) {Φ : Mx D a n → ℂ}
    (hΦ : Φ ∈ schwartzA θ a n) : (fun X => Φ (mm (mm h.1 X) g.1)) ∈ schwartzA θ a n := by
  induction hΦ using Submodule.span_induction with
  | zero => exact Submodule.zero_mem _
  | add f₁ f₂ _ _ i₁ i₂ => exact Submodule.add_mem _ i₁ i₂
  | smul c f _ i => exact Submodule.smul_mem _ c i
  | mem Φ hm =>
    obtain ⟨f, k, hk, rfl⟩ := hm
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := by first | infer_instance | exact GlobalTheory.AdelicU.isTopologicalRing_tens | exact isTopologicalRing_tens
    let ρ : D.what₂.Tau → (AE D →+* ℂ) := fun τ => (θ τ).comp (infPart D)
    let L := famEquiv (fun τ => h.1.map (ρ τ)) (fun τ => h.2.map (ρ τ)) (fun τ => g.1.map (ρ τ)) (fun τ => g.2.map (ρ τ))
      (fun τ => map_inv _ h.3) (fun τ => map_inv _ h.4) (fun τ => map_inv _ g.3) (fun τ => map_inv _ g.4)
    let H := twoSide (h.1.map (finPart D)) (h.2.map (finPart D)) (g.1.map (finPart D)) (g.2.map (finPart D))
      (map_inv _ h.3) (map_inv _ h.4) (map_inv _ g.3) (map_inv _ g.4)
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun y => k (H y),
      ⟨hk.1.comp_continuous H.continuous, hk.2.comp_homeomorph H⟩, ?_⟩
    funext X
    have e1 : (fun τ i j => compAt θ τ (mm (mm h.1 X) g.1) i j) = L (fun τ i j => compAt θ τ X i j) := by
      funext τ
      show (h.1 * X * g.1).map (ρ τ) = h.1.map (ρ τ) * X.map (ρ τ) * g.1.map (ρ τ)
      rw [Matrix.map_mul, Matrix.map_mul]
    have e2 : (fun i j => finPart D (mm (mm h.1 X) g.1 i j)) = H (fun i j => finPart D (X i j)) := by
      show (h.1 * X * g.1).map (finPart D) = h.1.map (finPart D) * X.map (finPart D) * g.1.map (finPart D)
      rw [Matrix.map_mul, Matrix.map_mul]
    show f (fun τ i j => compAt θ τ (mm (mm h.1 X) g.1) i j) * k (fun i j => finPart D (mm (mm h.1 X) g.1 i j)) = _
    rw [e1, e2]
    rfl

end GlobalTheory.CompanionTheory.AlgStab

open GlobalTheory.CompanionTheory.AlgStab in
theorem GlobalTheory.CompanionTheory.AlgStab.algStab : IdemEx → AlgStab := by
  intro _ D θ _ a n S e he h g hh hg Φ hΦ hG hC
  refine ⟨schw θ h g hΦ, fun X => ?_, ?_⟩
  · have hI : IntOff S (mm (mm h.1 X) g.1) ↔ IntOff S X := by
      refine forall_congr' fun v => forall_congr' fun hv => ?_
      have h0 : cv D v e = 0 := by rw [he.2 v, if_neg hv]
      have : (h.1 * X * g.1).map (cv D v) = X.map (cv D v) := by
        rw [Matrix.map_mul, Matrix.map_mul, map_eq_one _ h0 hh, map_eq_one _ h0 hg, Matrix.one_mul, Matrix.mul_one]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      rw [show cv D v (mm (mm h.1 X) g.1 i j) = cv D v (X i j) from congrFun (congrFun this i) j]
    have hs : e • mm (mm h.1 X) g.1 = mm (mm h.1 (e • X)) g.1 := by
      show e • (h.1 * X * g.1) = h.1 * (e • X) * g.1
      rw [Matrix.mul_smul, Matrix.smul_mul]
    have := hG (mm (mm h.1 X) g.1)
    by_cases hX : IntOff S X
    · rw [if_pos (hI.2 hX), hs] at this
      rw [if_pos hX]
      exact this
    · rw [if_neg (fun c => hX (hI.1 c))] at this
      rw [if_neg hX]
      exact this
  · haveI : IsTopologicalRing (AE D) := by first | infer_instance | exact GlobalTheory.AdelicU.isTopologicalRing_tens | exact isTopologicalRing_tens
    exact hC.comp_homeomorph (twoSide h.1 h.2 g.1 g.2 h.3 h.4 g.3 g.4)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePointOfNonvanishingCoordsStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiprojective_point_of_nonvanishing_coords : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ), (∀ k, z ⟨k, c k⟩ ≠ 0) →
  IsUnder (GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z) z ∧ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.isUnder_ptMP | exact GlobalTheory.CompanionTheory.MPSmooth.isUnder_ptMP | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.isUnder_ptMP <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformHeckeEigenvalueStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_hecke_eigenvalue : Ad3.R.C1 → Ad3.R.U1 := by
  first | exact @GlobalTheory.CompanionTheory.WhitU.eq_zero_of_eigen | exact GlobalTheory.CompanionTheory.WhitU.eq_zero_of_eigen | (intros; apply GlobalTheory.CompanionTheory.WhitU.eq_zero_of_eigen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductorStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_conductor : Ad3.R.B0 → Ad3.R.F0b := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftConductor.f0b | exact GlobalTheory.CompanionTheory.NewformLiftConductor.f0b | (intros; apply GlobalTheory.CompanionTheory.NewformLiftConductor.f0b <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspFormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_cusp_form : Ad3.R.B0 → Ad3.R.ConstantTermVanishingAlt := by
  first | exact @GlobalTheory.CompanionTheory.LiftCusp.lift_cuspidal | exact GlobalTheory.CompanionTheory.LiftCusp.lift_cuspidal | (intros; apply GlobalTheory.CompanionTheory.LiftCusp.lift_cuspidal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspidalityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_cuspidality : Ad3.R.F6 := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6 | exact GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6 | (intros; apply GlobalTheory.CompanionTheory.NewformLiftCuspidality.f6 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistenceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_existence : Ad3.R.B0 → Ad3.R.F0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | exact GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergQ.f0 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficientsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_fourier_coefficients : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.U2 → Ad3.R.G0 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F2 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.F4 := by
  first | exact @GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq | exact GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq | (intros; apply GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvaluesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_hecke_eigenvalues : Ad3.R.B0 → Ad3.R.C0 → Ad3.R.C1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.AutomorphicLevelEquivariance → Ad3.R.HeckeSumLocalTranslates → Ad3.R.F3 := by
  first | exact @GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift | exact GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift | (intros; apply GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacterStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_level_character : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | exact GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance <;> assumption)
end


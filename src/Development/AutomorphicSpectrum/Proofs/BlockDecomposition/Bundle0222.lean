import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0209
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0210
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0211
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0212
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjGelfValOfIsHerm
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem amat_map_conj {n : ℕ} (l : Fin n → ℂ) :
    (Formalism.REAL.Amat l).map (starRingEnd ℂ) = Formalism.REAL.Amat (fun a => conj (l a)) := by
  ext a b
  simp only [Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply]
  split_ifs <;> simp

theorem conj_gelfVal {n : ℕ} (c : Fin n → ℂ) (m : ℕ) :
    conj (GlobalTheory.Dec.gelfVal c m) = GlobalTheory.Dec.gelfVal (fun a => conj (c a)) m := by
  have h : ((Formalism.REAL.Amat fun a => c a + ((n : ℂ) - 1) / 2) ^ m).map (starRingEnd ℂ) =
      (Formalism.REAL.Amat fun a => conj (c a) + ((n : ℂ) - 1) / 2) ^ m := by
    rw [Matrix.map_pow, amat_map_conj]
    congr 2
    funext a
    simp [map_ofNat]
  simp only [GlobalTheory.Dec.gelfVal, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← h]
  rfl

theorem prod_one_sub_ne_zero {n : ℕ} (l : Fin n → ℂ) :
    (∏ a, (1 - PowerSeries.C (l a) * PowerSeries.X) : PowerSeries ℂ) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun a _ h => ?_
  have := congrArg PowerSeries.constantCoeff h
  simp at this

theorem gser_comp_perm {n : ℕ} (c : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    gser (fun a => c (σ a)) = gser c := by
  have h1 := gser_mul_prod n (fun a => c (σ a))
  have h2 := gser_mul_prod n c
  beta_reduce at h1
  have e1 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) :=
    Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X))
  have e2 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) : PowerSeries ℂ) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) :=
    Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X))
  rw [e1, e2] at h1
  have hP : (∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) ≠ 0 :=
    prod_one_sub_ne_zero _
  have h3 : (1 - PowerSeries.X * gser (fun a => c (σ a))) = 1 - PowerSeries.X * gser c :=
    mul_right_cancel₀ hP (h1.trans h2.symm)
  have h4 : PowerSeries.X * gser (fun a => c (σ a)) = PowerSeries.X * gser c := sub_right_injective h3
  exact mul_left_cancel₀ PowerSeries.X_ne_zero h4

theorem gelfVal_comp_perm {n : ℕ} (c : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    GlobalTheory.Dec.gelfVal (fun a => c (σ a)) m = GlobalTheory.Dec.gelfVal c m := by
  have h := congrArg (PowerSeries.coeff m) (gser_comp_perm c σ)
  simpa [gser] using h

theorem conj_gelfVal_of_isHerm : ∀ (n : ℕ) (χ : Inf n), IsHerm χ → ∀ (s : Bool) (m : ℕ),
    conj (GlobalTheory.Dec.gelfVal (χ s) m) = GlobalTheory.Dec.gelfVal (fun a => - χ (!s) a) m := by
  intro n χ hχ s m
  obtain ⟨σ, hσ⟩ := hχ
  rw [conj_gelfVal]
  cases s
  · simp only [Bool.not_false]
    rw [← gelfVal_comp_perm (fun a => conj (χ false a)) σ]
    congr 1
    funext a
    simp [hσ a]
  · simp only [Bool.not_true]
    rw [← gelfVal_comp_perm (fun a => -χ false a) σ]
    congr 1
    funext a
    simp [hσ a]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOneParamDifferentiableStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_one_param_differentiable : ∀ {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Φ : ℝ → 𝔸), Continuous Φ → Φ 0 = 1 → (∀ s t, Φ (s + t) = Φ s * Φ t) → ∃ B, HasDerivAt Φ B 0 := by
  first | exact @GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | exact GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | (intros; apply GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousTranslatedIntegrand
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinThetaC

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  have hinv : Continuous fun a : IdeleGroup k ↦ ((a⁻¹ : IdeleGroup k) : 𝔸[k]) :=
    Units.continuous_val.comp continuous_inv
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j ↦ ?_
    by_cases hij : i = j
    · subst hij
      simpa [Function.comp_def, scalC, Matrix.scalar_apply] using
        (Units.continuous_val : Continuous fun a : IdeleGroup k ↦ (a : 𝔸[k]))
    · simpa [Function.comp_def, scalC, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
        using continuous_const
  · refine continuous_matrix fun i j ↦ ?_
    by_cases hij : i = j
    · subst hij
      simpa [Function.comp_def, scalC, Matrix.scalar_apply] using hinv
    · simpa [Function.comp_def, scalC, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
        using continuous_const

theorem thetaC_ltr (A h : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    thetaC (ltr A F) h = thetaC F (A * h) := by
  simp only [thetaC, ltr, Units.val_mul, Matrix.mulVec_mulVec]

theorem continuous_thetaC {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) :
    Continuous (thetaC F : GL ι 𝔸[k] → ℂ) := by
  refine continuous_iff_continuousAt.2 fun h₀ ↦ ?_
  obtain ⟨C, hC, hh₀⟩ := exists_compact_mem_nhds h₀
  obtain ⟨u, hu, hFu⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF hC
  have hcont : ContinuousOn (thetaC F : GL ι 𝔸[k] → ℂ) C := by
    refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hFu h hh ξ
    refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
    exact Units.continuous_val.matrix_mulVec continuous_const
  exact hcont.continuousAt hh₀

noncomputable def translatedIntegrand (w : InfinitePlace k) (Ψ : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (p : {r : ℝ // 0 < r} × GL ι 𝔸[k]) (u : normOneSubgroup k) : ℂ :=
  thetaC Ψ (p.2 * scalC (moduleSection w p.1 * (u : IdeleGroup k))) *
    (ω.toIdele (u : IdeleGroup k) : ℂ)

theorem continuous_translatedIntegrand (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) :
    Continuous (Function.uncurry (translatedIntegrand w Ψ ω)) := by
  have hu : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      (x.2 : IdeleGroup k) := continuous_subtype_val.comp continuous_snd
  have hs : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      moduleSection w x.1.1 :=
    (continuous_moduleSection w).comp (continuous_fst.comp continuous_fst)
  have hg : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      x.1.2 := continuous_snd.comp continuous_fst
  exact ((continuous_thetaC hΨ).comp (hg.mul (continuous_scalC.comp (hs.mul hu)))).mul
    (continuous_subtype_val.comp (ω.continuous_toIdele.comp hu))

theorem continuous_thetaCInt_ltr {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) :
    Continuous fun p : {r : ℝ // 0 < r} × GL ι 𝔸[k] ↦ thetaCInt w (ltr p.2 Ψ) ω p.1 := by
  have h := GlobalTheory.CompanionTheory.EisRk1Theta.continuous_setIntegral_of_continuous_uncurry (normOneMeasure k)
    (isCompact_closure_normOneFundamentalDomain k)
    (normOneMeasure_normOneFundamentalDomain_lt_top k) (continuous_translatedIntegrand w hΨ ω)
  refine h.congr fun p ↦ ?_
  simp only [thetaCInt, thetaC_ltr, translatedIntegrand]

end GlobalTheory.CompanionTheory.EpsteinThetaC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformConvolutionStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosh_transform_convolution : ∀ (g g' : ℝ → ℝ) (T T' : ℝ) (c : ℂ), IsBump g T → IsBump g' T' → coshT g c * coshT g' c = coshT (gconv g g') c := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT | exact GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT | (intros; apply GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverSystemCechPullNaturalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_system_cech_pull_natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  first | exact @GlobalTheory.CompanionTheory.CechLerayPull.cechHEquiv_pull | exact GlobalTheory.CompanionTheory.CechLerayPull.cechHEquiv_pull | (intros; apply GlobalTheory.CompanionTheory.CechLerayPull.cechHEquiv_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFactsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_domain_facts : PositivityTheory.RgBcC.Fc.DenseD := by
  first | exact @GlobalTheory.CompanionTheory.DenseCpt.denseD | exact GlobalTheory.CompanionTheory.DenseCpt.denseD | (intros; apply GlobalTheory.CompanionTheory.DenseCpt.denseD <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivIntegralCompactSupportStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deriv_integral_compact_support : ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (ρ : ℝ → Mat n → ℝ), Sm ρ → ∀ (K : Set (G n)), IsCompact K → ∀ (s₀ ε : ℝ), 0 < ε → (∀ s ∈ Metric.ball s₀ ε, ∀ y : G n, y ∉ K → ρ s y.val = 0) → HasDerivAt (fun s => ∫ y : G n, ρ s y.val ∂μ) (∫ y : G n, dt ρ s₀ y.val ∂μ) s₀ := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.IntDeriv.hasDerivAt_integral_compact | exact GlobalTheory.CompanionTheory.WaveSpd.IntDeriv.hasDerivAt_integral_compact | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.IntDeriv.hasDerivAt_integral_compact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeAsRightWordsStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_as_right_words : ∀ (n : ℕ) (L : List (Idx n)), ∃ (m : ℕ) (c : Fin m → Mat n → ℝ) (w : Fin m → List (Idx n)),
    (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
      ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | exact GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | (intros; apply GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityPointwiseEstimateStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.energy_density_pointwise_estimate : ∀ {W ι : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι] (w v : W) (Y : ι → W) (L : ι → ℝ) (A : W →L[ℝ] W) (C₁ C c φ : ℝ), 0 ≤ C₁ → C₁ * (1 + Fintype.card ι) ≤ C → c ≤ 0 → 0 ≤ φ → (∀ p, |L p| ≤ C₁) → c * C * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2) + φ * (2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ) - (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ ≤ (‖A‖ + 1) * (φ * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2)) := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq | exact GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityTimeDerivativeStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.energy_density_time_derivative : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (u : ℝ → Mat n → W), Sm u → ∀ (s : ℝ), ∀ y ∈ GLs n, HasDerivAt (fun r => dens u r y) (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ + 2 * ⟪dt u s y, u s y⟫_ℝ) s := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens | exact GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDividedPowersOnReductions
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

theorem mem_span_pow_of_factorial_mul_eq {S : Type} [CommRing S] (hS : R.TF S) {l : ℕ}
    (hl : l.Prime) (n : ℕ) {x : S} (hx : x ∈ Ideal.span {(l : S) ^ n}) {k : ℕ} (hk : k ≠ 0)
    {y : S} (e : (k.factorial : S) * y = x ^ k) : y ∈ Ideal.span {(l : S) ^ n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton'.1 hx
  haveI := Fact.mk hl
  obtain ⟨v, m, hlm, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd k.factorial_ne_zero l hl.ne_one
  have hv : v < k := by
    have h1 : v ≤ padicValNat l k.factorial :=
      (padicValNat_dvd_iff_le k.factorial_ne_zero).1 ⟨m, hm⟩
    have h2 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := l) hk
    have h3 : 1 ≤ l - 1 := Nat.le_sub_of_add_le hl.two_le
    nlinarith
  obtain ⟨t, ht⟩ : ∃ t, n * k = n + v + t := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    refine ⟨n * k' - v, ?_⟩
    have : v ≤ n * k' := by nlinarith [Nat.lt_succ_iff.1 hv]
    rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one]
    omega
  have hfac : (k.factorial : S) = (l : S) ^ v * (m : S) := by rw [hm]; push_cast; rfl
  have e2 : (l : S) ^ v * ((m : S) * y) = (l : S) ^ v * ((l : S) ^ n * ((l : S) ^ t * x' ^ k)) := by
    rw [← mul_assoc, ← hfac, e, mul_pow, ← pow_mul, ht, pow_add, pow_add]
    ring
  have hr : (l : S) ^ v ∈ nonZeroDivisors S := pow_mem (hS l hl.ne_zero) v
  have e3 : (m : S) * y = (l : S) ^ n * ((l : S) ^ t * x' ^ k) := by
    have h0 : (l : S) ^ v * ((m : S) * y - (l : S) ^ n * ((l : S) ^ t * x' ^ k)) = 0 := by
      rw [mul_sub, e2, sub_self]
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hr) _ (by rwa [mul_comm] at h0))
  have hc : IsCoprime (m : ℤ) ((l : ℤ) ^ n) := by
    apply IsCoprime.pow_right
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hl).2 hlm).symm
  obtain ⟨a, b, hab⟩ := hc
  have hab' : (a : S) * (m : S) + (b : S) * (l : S) ^ n = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → S) hab
  have hy : y = ((a : S) * ((l : S) ^ t * x' ^ k) + (b : S) * y) * (l : S) ^ n := by
    calc y = ((a : S) * (m : S) + (b : S) * (l : S) ^ n) * y := by rw [hab', one_mul]
      _ = (a : S) * ((m : S) * y) + (b : S) * (l : S) ^ n * y := by ring
      _ = _ := by rw [e3]; ring
  rw [hy]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_dividedPowers_map_mkAcr {l : ℕ} [hl : Fact l.Prime] (A : PAlg l) (n : ℕ)
    (I : Ideal A.Acr0) (hI : R.PdI I) (K : Ideal (A.Acr n)) (hK : K = I.map (A.mkAcr n)) :
    ∃ δ : DividedPowers K, R.IsPd (A.mkAcr n) I δ := by
  subst hK
  exact GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient A.acris_torsion_free I
    (Ideal.span {(l : A.Acr0) ^ n}) hI
    fun x _ hx k hk y e => mem_span_pow_of_factorial_mul_eq A.acris_torsion_free hl.out n hx hk e

theorem exists_dividedPowers_fil_pfil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ),
    (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧
      ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := by
  intro l _ A n
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.filtration_divided_power_structures A
  exact ⟨exists_dividedPowers_map_mkAcr A n _ p1 _ (h1 n 1),
    exists_dividedPowers_map_mkAcr A n _ p2 _ (h2 n)⟩

end GlobalTheory.CompanionTheory.PerfFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.KUFactsU

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem iwGL_entries {n : ℕ} {x : GL (Fin n) L} (hx : x ∈ IwGL L n) (i j : Fin n) :
    (x : Matrix (Fin n) (Fin n) L) i j ∈ intL L := by
  have hk := (Subgroup.mem_iInf.1 hx) (Fin.last n)
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hk
  have hmem : (Pi.single j 1 : Fin n → L) ∈ latK L n (Fin.last n) := by
    intro l
    simp only [Fin.val_last, l.isLt, if_true]
    by_cases hl : l = j
    · subst hl
      simp
    · simp [Pi.single_apply, hl]
  have h2 : (Matrix.GeneralLinearGroup.toLin : GL (Fin n) L ≃* _).toMonoidHom x •
      (Pi.single j 1 : Fin n → L) ∈ latK L n (Fin.last n) := by
    rw [← hk]
    exact Set.smul_mem_smul_set hmem
  have h3 := h2 i
  simp only [Fin.val_last, i.isLt, if_true] at h3
  show (x : Matrix (Fin n) (Fin n) L) i j ∈ Valued.v.integer
  rw [Valuation.mem_integer_iff]
  convert h3 using 2
  simp [Units.smul_def, Matrix.GeneralLinearGroup.toLin, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem iwU_le_KU (σ : L →+* L) (n : ℕ) : IwU σ n ≤ KU σ n := by
  intro x hx
  have hx' : (x : GL (Fin n) L) ∈ IwGL L n := Subgroup.mem_subgroupOf.1 hx
  have hxi : ((x : GL (Fin n) L))⁻¹ ∈ IwGL L n := inv_mem hx'
  have hmem : x ∈ ((KU σ n : Subgroup (GU σ n)) : Set (GU σ n)) := by
    rw [GlobalTheory.LFun.IntPtsUnitary.coe_KU, Set.mem_preimage, GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    exact ⟨fun i j => iwGL_entries hx' i j, fun i j => iwGL_entries hxi i j⟩
  exact hmem

theorem ordL_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (d : ℤ) : ordL (ϖ ^ d) = d := by
  have h1 : Valued.v (ϖ ^ d) =
      ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_neg, smul_eq_mul, mul_one]
  have hne : Valued.v (ϖ ^ d) ≠ 0 := by
    rw [h1]
    exact WithZero.coe_ne_zero
  unfold ordL
  rw [dif_neg hne]
  have key : WithZero.unzero hne = Multiplicative.ofAdd (-d) :=
    WithZero.coe_injective (by rw [WithZero.coe_unzero, h1])
  rw [key, toAdd_ofAdd, neg_neg]

def expo (n : ℕ) (i : Fin n) : ℤ := (n : ℤ) - 1 - 2 * (i.val : ℤ)

def tGL {ϖ : L} (h0 : ϖ ≠ 0) (n : ℕ) : GL (Fin n) L where
  val := Matrix.diagonal fun i => ϖ ^ expo n i
  inv := Matrix.diagonal fun i => ϖ ^ (-expo n i)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ h0]; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ h0]; simp

theorem tGL_mem {ϖ : L} (h0 : ϖ ≠ 0) {σ : L →+* L} (hσ : σ ϖ = ϖ) (n : ℕ) : tGL h0 n ∈ GU σ n := by
  show cT σ ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n *
    ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antiJ L n
  have hc : cT σ ((tGL h0 n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => ϖ ^ expo n i := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [cT, tGL, map_zpow₀, hσ]
    · simp [cT, tGL, hab, Ne.symm hab]
  rw [hc]
  ext a b
  simp only [tGL, Matrix.diagonal_mul, Matrix.mul_diagonal, antiJ]
  split_ifs with hab
  · have he : expo n a + expo n b = 0 := by
      unfold expo
      omega
    rw [mul_one, ← zpow_add₀ h0, he, zpow_zero]
  · simp

theorem exists_strictDom {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ t : GU σ n, IsDiagM (t : GL (Fin n) L) ∧ IsStrictDom (t : GL (Fin n) L) := by
  obtain ⟨-, -, hσ, hϖ, -⟩ := h
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨⟨tGL h0 n, tGL_mem h0 hσ n⟩, fun i j hij => ?_, fun i j hij => ?_⟩
  · show (Matrix.diagonal fun i => ϖ ^ expo n i) i j = 0
    exact Matrix.diagonal_apply_ne _ hij
  · show ordL ((Matrix.diagonal fun i => ϖ ^ expo n i) j j) <
      ordL ((Matrix.diagonal fun i => ϖ ^ expo n i) i i)
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ordL_zpow hϖ, ordL_zpow hϖ]
    unfold expo
    have hlt : (i : ℕ) < j := hij
    omega

theorem kuFacts : PositivityTheory.SphericalProduct.KUFacts := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  exact ⟨ho, hc, iwU_le_KU σ n, exists_strictDom h n⟩

end GlobalTheory.CompanionTheory.KUFactsU

end
end


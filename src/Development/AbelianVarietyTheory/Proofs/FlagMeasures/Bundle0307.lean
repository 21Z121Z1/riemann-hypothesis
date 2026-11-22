import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0297
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandOperatorExtension
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbSumFibreEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0292
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptotic
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric

noncomputable section

namespace GlobalTheory.GaugeSubLoc

variable {n : ℕ} {ε : Fin n → Bool}

theorem eventually_bounds {S : Set (Formalism.REAL.UJ ε)} {d : ℕ} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) {θ : ℝ} (hθ : 1 < θ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0,
      μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ ρ} ≤
        ENNReal.ofReal (θ * ρ ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∧
      ENNReal.ofReal (ρ ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
        ENNReal.ofReal θ * μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ ρ} := by
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have h0 : ω ≠ 0 := (measure_ball_pos _ 0 one_pos).ne'
  have ht : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hθ' : 1 < ENNReal.ofReal θ := by simpa using hθ
  have h1 : ω < ENNReal.ofReal θ * ω := by
    conv_lhs => rw [← one_mul ω]
    exact ENNReal.mul_lt_mul_left h0 ht hθ'
  have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal θ) hμ.2.2 (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [hμ.2.2.eventually (gt_mem_nhds h1), h2.eventually (lt_mem_nhds h1),
    self_mem_nhdsWithin] with ρ a1 a2 a3
  have hρ : (0 : ℝ) < ρ := a3
  have hp : ENNReal.ofReal (ρ ^ d) ≠ 0 := by simpa using pow_pos hρ d
  constructor
  · rw [ENNReal.div_lt_iff (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)] at a1
    rw [ENNReal.ofReal_mul (by linarith), mul_right_comm]
    exact a1.le
  · rw [← mul_div_assoc, ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)] at a2
    rw [mul_comm]
    exact a2.le

open scoped Matrix.Norms.Frobenius in
theorem norm_mul_bounds {θ : ℝ} (hθ : 1 < θ) (g Z : Matrix (Fin n) (Fin n) ℂ)
    (hg : ‖g - 1‖ < 1 - θ⁻¹) : ‖g * Z‖ ≤ θ * ‖Z‖ ∧ ‖Z‖ ≤ θ * ‖g * Z‖ := by
  have h1 : ‖g * Z - Z‖ ≤ (1 - θ⁻¹) * ‖Z‖ := by
    have : g * Z - Z = (g - 1) * Z := by rw [Matrix.sub_mul, Matrix.one_mul]
    rw [this]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hg.le (norm_nonneg _))
  have h2 := abs_le.1 ((abs_norm_sub_norm_le (g * Z) Z).trans h1)
  have h3 : θ⁻¹ * θ = 1 := inv_mul_cancel₀ (by linarith)
  have h4 : 0 < θ⁻¹ := inv_pos.2 (by linarith)
  have h5 := norm_nonneg Z
  have h6 : 2 - θ⁻¹ ≤ θ := by nlinarith [sq_nonneg (θ - 1)]
  constructor
  · nlinarith
  · have : θ⁻¹ * ‖Z‖ ≤ ‖g * Z‖ := by linarith
    calc ‖Z‖ = θ * (θ⁻¹ * ‖Z‖) := by rw [← mul_assoc, mul_comm θ, h3, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by linarith)

open scoped Matrix.Norms.Frobenius in
theorem density_bounds {S : Set (Formalism.REAL.UJ ε)} {d : ℕ} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) (ψ : Formalism.REAL.UJ ε → EuclideanSpace ℝ (Fin d)) (hψ : Continuous ψ)
    {s : ℝ} (hs : 0 < s)
    (h2 : ∀ g h : Formalism.REAL.UJ ε, g ∈ S → h ∈ S → ‖uMat g - 1‖ < s → ‖uMat h - 1‖ < s →
      ‖uMat g - uMat h‖ ≤ 2 * ‖ψ g - ψ h‖)
    (hlip : ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ g h : Formalism.REAL.UJ ε, g ∈ S → h ∈ S →
      ‖uMat g - 1‖ < δ → ‖uMat h - 1‖ < δ →
      ‖ψ g - ψ h‖ ≤ ‖uMat g - uMat h‖ ∧ ‖uMat g - uMat h‖ ≤ κ * ‖ψ g - ψ h‖)
    (hsurj : ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < ρ →
      ∃ g ∈ S, ‖uMat g - 1‖ < δ ∧ ψ g = x)
    (κ : ℝ) (hκ : 1 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ → ∀ᶠ r : ℝ in 𝓝[>] 0,
      (μ.restrict {g | ‖uMat g - 1‖ < s}).map ψ (closedBall x r) ≤
        ENNReal.ofReal κ * volume (closedBall x r) ∧
      volume (closedBall x r) ≤
        ENNReal.ofReal κ * (μ.restrict {g | ‖uMat g - 1‖ < s}).map ψ (closedBall x r) := by
  obtain ⟨θ, hθκ, hθ⟩ : ∃ θ : ℝ, θ ^ (2 * d + 1) < κ ∧ 1 < θ := by
    have : Tendsto (fun θ : ℝ => θ ^ (2 * d + 1)) (𝓝[>] 1) (𝓝 1) := by
      have : ContinuousAt (fun θ : ℝ => θ ^ (2 * d + 1)) 1 := by fun_prop
      simpa using this.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    exact ((this.eventually (gt_mem_nhds hκ)).and self_mem_nhdsWithin).exists
  have hθ0 : 0 < θ := by linarith
  obtain ⟨δ₁, hδ₁, hl⟩ := hlip θ hθ
  have hη : 0 < 1 - θ⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hθ)
  obtain ⟨ρ, hρ, hsu⟩ := hsurj (min (min δ₁ s) (1 - θ⁻¹)) (lt_min (lt_min hδ₁ hs) hη)
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨g, hgS, hg, rfl⟩ := hsu x hx
  rw [lt_min_iff] at hg
  obtain ⟨hg1, hg3⟩ := hg
  have hgs : ‖uMat g - 1‖ < s := hg1.trans_le (min_le_right _ _)
  have hgδ : ‖uMat g - 1‖ < δ₁ := hg1.trans_le (min_le_left _ _)
  have hae : ∀ᵐ h ∂μ, h ∈ S := hμ.1
  have htr : ∀ t : ℝ, μ {h | ‖uMat (g⁻¹ * h) - 1‖ ≤ t} =
      μ {k | Real.sqrt (Formalism.REAL.hs (uMat k - 1)) ≤ t} := by
    intro t
    conv_lhs => rw [← hμ.2.1 g hgS]
    rw [(measurableEmbedding_mulLeft g).map_apply]
    congr 1
    ext k
    simp [GlobalTheory.GaugeConst.sqrt_hs]
  have hZ : ∀ h : Formalism.REAL.UJ ε, uMat g * (uMat (g⁻¹ * h) - 1) = uMat h - uMat g := by
    intro h
    rw [Matrix.mul_sub, ← uMat_mul, mul_inv_cancel_left, Matrix.mul_one]
  have htri : ∀ h : Formalism.REAL.UJ ε, ‖uMat h - 1‖ ≤ ‖uMat h - uMat g‖ + ‖uMat g - 1‖ := fun h =>
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  filter_upwards [(GlobalTheory.GaugeConst.tendsto_mul_nhdsGT (pow_pos hθ0 2)).eventually (eventually_bounds hμ hθ),
    (GlobalTheory.GaugeConst.tendsto_mul_nhdsGT (inv_pos.2 hθ0)).eventually (eventually_bounds hμ hθ),
    Ioo_mem_nhdsGT (half_pos (sub_pos.2 hg1))] with r a1 a2 a3
  obtain ⟨hr, hr'⟩ := a3
  have hm1 := min_le_left δ₁ s
  have hm2 := min_le_right δ₁ s
  rw [Measure.map_apply hψ.measurable measurableSet_closedBall,
    Measure.restrict_apply (hψ.measurable measurableSet_closedBall),
    Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin]
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  constructor
  · have hsub : μ (ψ ⁻¹' closedBall (ψ g) r ∩ {g | ‖uMat g - 1‖ < s}) ≤
        μ {h | ‖uMat (g⁻¹ * h) - 1‖ ≤ θ ^ 2 * r} := by
      refine measure_mono_ae ?_
      filter_upwards [hae] with h hS hh
      obtain ⟨b1, b2⟩ := hh
      have b1' : ‖ψ h - ψ g‖ ≤ r := mem_closedBall_iff_norm.1 b1
      have b3 := h2 h g hS hgS b2 hgs
      have b4 := (hl h g hS hgS (by linarith [htri h]) hgδ).2
      have b5 := (norm_mul_bounds hθ (uMat g) (uMat (g⁻¹ * h) - 1) hg3).2
      rw [hZ] at b5
      change ‖uMat (g⁻¹ * h) - 1‖ ≤ θ ^ 2 * r
      calc _ ≤ θ * (θ * r) := b5.trans (mul_le_mul_of_nonneg_left
            (b4.trans (mul_le_mul_of_nonneg_left b1' hθ0.le)) hθ0.le)
        _ = _ := by ring
    rw [htr] at hsub
    refine (hsub.trans a1.1).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    calc θ * (θ ^ 2 * r) ^ d = θ ^ (2 * d + 1) * r ^ d := by ring
      _ ≤ _ := by gcongr
  · have hsub : μ {h | ‖uMat (g⁻¹ * h) - 1‖ ≤ θ⁻¹ * r} ≤
        μ (ψ ⁻¹' closedBall (ψ g) r ∩ {g | ‖uMat g - 1‖ < s}) := by
      refine measure_mono_ae ?_
      filter_upwards [hae] with h hS hh
      have hh' : ‖uMat (g⁻¹ * h) - 1‖ ≤ θ⁻¹ * r := hh
      have b5 := (norm_mul_bounds hθ (uMat g) (uMat (g⁻¹ * h) - 1) hg3).1
      rw [hZ] at b5
      have b6 : ‖uMat h - uMat g‖ ≤ r := by
        refine b5.trans ((mul_le_mul_of_nonneg_left hh' hθ0.le).trans_eq ?_)
        field_simp
      have b4 := (hl h g hS hgS (by linarith [htri h]) hgδ).1
      exact ⟨mem_closedBall_iff_norm.2 (b4.trans b6), show ‖uMat h - 1‖ < s by linarith [htri h]⟩
    rw [htr] at hsub
    have e : ENNReal.ofReal (r ^ d) = ENNReal.ofReal (θ ^ d) * ENNReal.ofReal ((θ⁻¹ * r) ^ d) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_inv_cancel_left₀ hθ0.ne']
    rw [e, mul_assoc]
    refine (mul_le_mul_right a2.2 _).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    gcongr
    calc θ ^ d * θ = θ ^ (d + 1) := by ring
      _ ≤ θ ^ (2 * d + 1) := pow_le_pow_right₀ hθ.le (by omega)
      _ ≤ _ := hθκ.le

open scoped Matrix.Norms.Frobenius in

theorem gauge_local_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub {g | uMat g - 1 ∈ A} d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ (∀ μ', IsGaugeSub {g | uMat g - 1 ∈ A} d μ' → μ' = μ) ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ r₀ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | Formalism.REAL.hs (uMat g - 1) < r₁}, φ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re / r) ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t, φ t)) := by
  intro n ε A d E hA hE hV μ hμ
  obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.isRiemannianHaarOnSubgroup_sigmaFinite_unique n ε (algSub ε A hA) (isClosed_algSub A hA) d μ hμ
  refine ⟨a1, a2, a3, ?_⟩
  have hlip := GlobalTheory.T.unitarySubgroupChart_almost_isometric_near_one n ε A d E hA hE hV
  have hsurj := GlobalTheory.T.unitarySubgroupChart_surjective_near_origin n ε A d E hA hE hV
  simp only [GlobalTheory.GaugeConst.sqrt_hs] at hlip hsurj
  set ψ : Formalism.REAL.UJ ε → EuclideanSpace ℝ (Fin d) :=
    fun g => WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) with hψdef
  have hψ : Continuous ψ := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => Complex.continuous_re.comp ?_)
    exact (((GlobalTheory.GaugeConst.continuous_uMat ε).sub continuous_const).matrix_mul
      continuous_const).matrix_trace
  obtain ⟨δ, hδ, h2⟩ := hlip 2 one_lt_two
  obtain ⟨s₀, ⟨hs1, -⟩, hs2, hs3⟩ :=
    ((eventually_bounds hμ one_lt_two).and (Ioo_mem_nhdsGT hδ)).exists
  refine ⟨s₀ ^ 2, by positivity, fun r₁ hr₁ hr₁' φ hφ hφc => ?_⟩
  have hs : 0 < Real.sqrt r₁ := Real.sqrt_pos.2 hr₁
  have hs' : Real.sqrt r₁ ≤ s₀ := Real.sqrt_le_iff.2 ⟨hs2.le, hr₁'⟩
  have hset : {g : Formalism.REAL.UJ ε | Formalism.REAL.hs (uMat g - 1) < r₁} =
      {g | ‖uMat g - 1‖ < Real.sqrt r₁} := by
    ext g
    simp only [Set.mem_ofPred_eq, ← GlobalTheory.GaugeConst.sqrt_hs]
    exact (Real.sqrt_lt_sqrt_iff_of_pos hr₁).symm
  rw [hset]
  have hfin : IsFiniteMeasure (μ.restrict {g | ‖uMat g - 1‖ < Real.sqrt r₁}) := by
    refine isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top ?_ (le_trans (measure_mono ?_) hs1))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · intro g hg
      simp only [Set.mem_ofPred_eq, GlobalTheory.GaugeConst.sqrt_hs] at hg ⊢
      linarith
  have hd := density_bounds hμ ψ hψ hs
    (fun g h hg hh b1 b2 => (h2 g h hg hh (by linarith) (by linarith)).2) hlip hsurj
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hΦ : Continuous (fun x : EuclideanSpace ℝ (Fin d) => φ (e x)) := hφ.comp e.continuous
  have hv := GlobalTheory.T.tendsto_rescaled_integral_of_ball_density_bounds d _ inferInstance hd (fun x => φ (e x)) hΦ
    (hφc.comp_homeomorph e.toHomeomorph)
  have hI : ∫ x : EuclideanSpace ℝ (Fin d), φ (e x) = ∫ t, φ t :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp' φ
  rw [hI] at hv
  refine hv.congr fun r => ?_
  rw [integral_map (f := fun x => φ (e (r⁻¹ • x))) hψ.aemeasurable (hΦ.comp (continuous_const_smul r⁻¹)).aestronglyMeasurable]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  refine congrArg φ (funext fun i => ?_)
  simp [e, hψdef, div_eq_inv_mul]

end GlobalTheory.GaugeSubLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandOperatorExtensionStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f ∧ ∀ (k : ℕ) (z : ℂ), ‖z‖ = 1 → ∀ g ∈ SUset ε, gelf ε k f (z • g) = z ^ m * (((m : ℂ) / n) ^ (k + 1) * n * f' g + ∑ j ∈ range (k + 1), ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) * gelfS ε j f' g) := by
  first | exact @GlobalTheory.GelfCentral.gelf_central | exact GlobalTheory.GelfCentral.gelf_central | (intros; apply GlobalTheory.GelfCentral.gelf_central <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesStableUnderVectorStabilizer
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.StabSet

open GlobalTheory.Mass Formalism.HermitianLatticesTheory GlobalTheory.Mass.RowMean

theorem main : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (M₀ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)) (ψ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u) → ℝ≥0∞), (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u)) (M : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)), ψ (s • M) = ψ M) → GlobalTheory.Mass.Stable (GlobalTheory.RowsOrb.Gz X u) {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} ∧ ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L)) = ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L) := by
  intro D X u M₀ ψ hψ
  have hU : ∀ v, v ∈ GlobalTheory.RowsOrb.Ub X u ↔ GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) v = 0 :=
    fun v => GlobalTheory.RowsOrb.mem_Ub X u v
  have hπ : ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)),
      GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) =
        resZ (GlobalTheory.RowsOrb.hb X) hU g • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L :=
    fun g L => StabSplit.latIn_smul (GlobalTheory.RowsOrb.hb X) (GlobalTheory.RowsOrb.Ub X u) g.1 (smul_compl _ hU g) L
  have hY : Stable (isom (GlobalTheory.RowsOrb.hU X u)) (genus (GlobalTheory.RowsOrb.hU X u) M₀) :=
    Transp.genus_stable (R := 𝓞 D.host.E) (K := D.host.E) (V := GlobalTheory.RowsOrb.Ub X u) (h := GlobalTheory.RowsOrb.hU X u) M₀
  refine ⟨?_, fun g L => by rw [hπ]; exact hψ _ _⟩
  rintro g L ⟨h1, h2, h3, h4⟩
  have H := Formalism.HermitianLatticesTheory.isomAct (𝓞 D.host.E) D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) g.1.1 g.1.2 L
  refine ⟨H.2.2.2.2.2 h1, H.2.2.2.1.2 h2, fun t => ?_, ?_⟩
  · have hg : g.1.1 (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u := g.2
    have hs : g.1.1.symm (t • GlobalTheory.RowsOrb.zb X u) = t • GlobalTheory.RowsOrb.zb X u :=
      g.1.1.symm_apply_eq.2 (by rw [map_smul, hg])
    change t • GlobalTheory.RowsOrb.zb X u ∈ Formalism.HermitianLatticesTheory.gmap (g.1.1 : GlobalTheory.RowsOrb.Wb X ≃ₗ[D.host.E] GlobalTheory.RowsOrb.Wb X) L ↔ _
    rw [isomAct_mem_gmap, hs, h3]
  · let s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u) := resZ (GlobalTheory.RowsOrb.hb X) hU g
    have k : s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀ := hY s _ h4
    have e : GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) = s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L := hπ g L
    exact Eq.mpr (congrArg (fun N => N ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀) e) k

end GlobalTheory.RowsOrb.StabSet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrincipleStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_local_global_principle : ∀ (D : D7) (Z : LocDat D), (∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → {p | lattice₂ D Z.M p Λ₁ ≠ lattice₂ D Z.M p Λ₂}.Finite ∧ ((∀ p, lattice₂ D Z.M p Λ₁ = lattice₂ D Z.M p Λ₂) → Λ₁ = Λ₂)) ∧ ∀ (Λ₀ : LV D), Submodule.IsLattice D.host.E Λ₀ → ∀ Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p), (∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤) → {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite → ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ = Lp p := by
  first | exact @GlobalTheory.Unfold.LatLoc.lattices_local_global | exact GlobalTheory.Unfold.LatLoc.lattices_local_global | (intros; apply GlobalTheory.Unfold.LatLoc.lattices_local_global <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerLatticeIdentificationCompatOfGraphEqStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerLatticeIdentification_compat_of_graph_eq : ∀ (D : D7) (T T' : D.host.E) (F₀ B : LFlag (VS D) D.R.rS T) (P₁ P₂ B' : LFlag (VS D) D.R.rS T') (Λ : LV D) (ψ₀ ψ₁ β : GV D), ψ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ψ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (Xsp F₀).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp F₀).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp P₁).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (Xsp P₂).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₀ Λ)).2.2 = (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₁ Λ)).2.2 → β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (Xsp P₁).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp P₂ → (∀ l ∈ Lrep Λ F₀, (ψ₁⁻¹ * ψ₀) l - l ∈ Xsp F₀) → (∀ x' ∈ Lrep Λ P₁, (ψ₁⁻¹ * ψ₀) x' - β x' ∈ Xsp P₂) → IotaCompat Λ F₀ P₁ P₂ β (gS D) := by
  first | exact @GlobalTheory.iotaCompat_of_graph_eq | exact GlobalTheory.iotaCompat_of_graph_eq | (intros; apply GlobalTheory.iotaCompat_of_graph_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEq
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.LsubG

variable {D : D7}

theorem exists_proj (X : Submodule D.host.E (VS D).V) :
    ∃ Q : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ X, Q x = 0) ∧ (∀ v, v - Q v ∈ X) ∧ ∀ v, Q (Q v) = Q v := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl X
  have hC' : IsCompl C X := hC.symm
  refine ⟨C.projection X hC', fun x hx => (Submodule.projection_apply_eq_zero_iff hC').2 hx, fun v => ?_, fun v => ?_⟩
  · rw [← Submodule.projection_eq_self_sub_projection hC']
    exact Submodule.projection_apply_mem _ _
  · exact Submodule.projection_apply_of_mem_left hC' (Submodule.projection_apply_mem _ _)

def endP (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
  Fintype.linearCombination (D.s.atP p).Ep (fun i => baseChange₂ D p (Q ((VS D).frame i)))

theorem bcP_endP (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    endP p Q (baseChange₂ D p x) = baseChange₂ D p (Q x) := by
  rw [endP, Fintype.linearCombination_apply]
  conv_rhs => rw [← (VS D).frame.sum_repr x]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, baseChange_smul₂]
  rfl

theorem endP_latP (Z : LocDat D) (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) (Λ : LV D) {y : Vp D p}
    (hy : y ∈ lattice₂ D Z.M p Λ) : endP p Q y ∈ lattice₂ D Z.M p (Λ.map (Q.restrictScalars (𝓞 D.host.E))) := by
  refine Submodule.span_induction (p := fun y _ => endP p Q y ∈ lattice₂ D Z.M p (Λ.map (Q.restrictScalars (𝓞 D.host.E))))
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨x, hx, rfl⟩
    rw [bcP_endP]
    exact Submodule.subset_span ⟨Q x, Submodule.mem_map_of_mem hx, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have e : endP p Q (c • a) = c • endP p Q a := by
      rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ c ha

theorem localLattice_mono' (Z : LocDat D) (p : PlF D) {Λ Λ' : LV D} (h : Λ ≤ Λ') : lattice₂ D Z.M p Λ ≤ lattice₂ D Z.M p Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_of_local (Z : LocDat D) (Γ : LV D) (hΓ : Submodule.IsLattice D.host.E Γ) (x : (VS D).V)
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Γ) : x ∈ Γ := by
  have r := ((GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Γ) (LatLoc.isLattice_map _ _ hΓ)).1
    (LatLoc.cE D x)).2 (fun p => by rw [← LatLoc.baseChange_eq, ← LatLoc.localLattice_eq]; exact h p)
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.1 r
  have : y = x := (LatLoc.cE D).injective hxy
  exact this ▸ hy

theorem herm_smul_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (c : E) (u w : V) : H.h u (c • w) = M.L.cj c * H.h u w := by
  rw [H.h_herm (c • w) u, H.h_smul_left, map_mul, ← H.h_herm w u]

theorem herm_span_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (u : V) (S : Set V) (hS : ∀ s ∈ S, H.h u s = 0) :
    ∀ w ∈ Submodule.span E S, H.h u w = 0 := by
  intro w hw
  refine Submodule.span_induction (p := fun w _ => H.h u w = 0) hS ?_ ?_ ?_ hw
  · rw [H.h_herm 0 u, H.h_zero_left, map_zero]
  · intro a b _ _ ha hb
    rw [H.h_herm (a + b) u, H.h_add_left, map_add, ← H.h_herm a u, ← H.h_herm b u, ha, hb, add_zero]
  · intro c a _ ha
    rw [herm_smul_right, ha, mul_zero]

theorem X_iso {T : D.host.E} (G : LFlag (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ Xsp G) :
    x ∈ orth (VS D) (Xsp G) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y hy
  have hgen : ∀ b, (VS D).hT y (G.fl.e b) = 0 := by
    intro b
    refine Submodule.span_induction (p := fun y _ => (VS D).hT y (G.fl.e b) = 0) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨a, rfl⟩; exact G.fl.e_iso a b
    · simp
    · intro a c _ _ ha hc; simp [ha, hc]
    · intro c a _ ha; simp [ha]
  refine Submodule.span_induction (p := fun x _ => (VS D).hT y x = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩; exact hgen b
  · simp
  · intro a c _ _ ha hc; simp [ha, hc]
  · intro c a _ ha; simp [ha]

example (Λ : LV D) (h : Submodule.IsLattice D.host.E Λ) : Λ.FG ∧ Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ :=
  ⟨h.fg, h.span_eq_top⟩

set_option maxHeartbeats 1000000 in
theorem lsub_le (Z : LocDat D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
    (f : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p)
    (hf : ∀ p, f p = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) (Λ₁ Λ₂ : LV D)
    (h₂ : Submodule.IsLattice D.host.E Λ₂)
    (hL : ∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (f p) ⊆ (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (f p)) :
    Lsub Λ₁ G ≤ Lsub Λ₂ G := by
  obtain ⟨Q, hQX, hQv, hQQ⟩ := exists_proj (Xsp G)
  set Γ : LV D := Λ₂ ⊔ Λ₂.map (Q.restrictScalars (𝓞 D.host.E)) with hΓdef
  have hΓ : Submodule.IsLattice D.host.E Γ :=
    ⟨h₂.fg.sup (h₂.fg.map _), eq_top_iff.2 (h₂.span_eq_top.symm.le.trans (Submodule.span_mono (show (Λ₂ : Set (VS D).V) ⊆ Γ from fun z hz => Submodule.mem_sup_left hz)))⟩
  intro v hv
  have hvo : v ∈ orth (VS D) (Xsp G) := hv.2
  obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 hv.1
  have hlo : l ∈ orth (VS D) (Xsp G) := hl.2
  have hloc : ∀ p, baseChange₂ D p (Q (l + x)) ∈ lattice₂ D Z.M p Γ := by
    intro p
    have hXQ : ∀ w ∈ (locH Z p).X (f p), endP p Q w = 0 := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => endP p Q w = 0) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨a, rfl⟩
        rw [hf p]
        simp only
        rw [map_smul, bcP_endP, hQX _ (Submodule.subset_span ⟨a, by simp [frame, FlagG.fvec]⟩), map_zero, smul_zero]
      · exact map_zero _
      · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
      · intro c a _ ha; rw [map_smul, ha, smul_zero]
    have hperp : baseChange₂ D p l ∈ (locH Z p).perp ((locH Z p).X (f p)) := by
      intro w hw
      refine herm_span_right (locH Z p) (baseChange₂ D p l) _ ?_ w hw
      rintro _ ⟨a, rfl⟩
      rw [hf p]
      simp only
      rw [herm_smul_right]
      have e0 : (locH Z p).h (baseChange₂ D p l) (baseChange₂ D p (frame G a.castSucc)) = 0 := by
        show LocFacts₂ Z.M p (baseChange₂ D p l) (baseChange₂ D p (frame G a.castSucc)) = 0
        rw [baseChangeAt_form Z.M p (Z.hcj p), brS]
        have hmem : frame G a.castSucc ∈ Xsp G := Submodule.subset_span ⟨a, by simp [frame, FlagG.fvec]⟩
        have := hlo
        simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this
        rw [this _ hmem, map_zero]
      rw [e0, mul_zero]
    obtain ⟨y, hy, hyw⟩ := hL p ⟨⟨baseChange₂ D p l, hperp⟩, Submodule.subset_span ⟨l, hl.1, rfl⟩, rfl⟩
    have hdiff : ((y : Vp D p) - baseChange₂ D p l) ∈ (locH Z p).X (f p) := by
      have := (Submodule.Quotient.eq _).1 hyw
      simpa using this
    have e : endP p Q (baseChange₂ D p l) = endP p Q y := by
      have := hXQ _ hdiff
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    rw [← bcP_endP, map_add, map_add, e, bcP_endP p Q x, hQX x hx, map_zero, add_zero]
    exact localLattice_mono' Z p (le_sup_right : Λ₂.map (Q.restrictScalars (𝓞 D.host.E)) ≤ Γ) (endP_latP Z p Q Λ₂ hy)
  have hmem : Q (l + x) ∈ Γ := mem_of_local Z Γ hΓ _ hloc
  obtain ⟨a, ha, b', hb', hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hb'
  have hQab : Q a + Q b = Q (l + x) := by
    have := congrArg Q hab
    simp only [LinearMap.restrictScalars_apply, map_add, hQQ] at this
    rw [map_add Q l x]
    exact this
  have h2 : Q (l + x - (a + b)) = 0 := by
    rw [map_sub Q, map_add Q a b, hQab, sub_self]
  have hc : l + x - (a + b) ∈ Xsp G := by
    have h1 := hQv (l + x - (a + b))
    rw [h2, sub_zero] at h1
    exact h1
  have hco : a + b ∈ orth (VS D) (Xsp G) := by
    have : a + b = (l + x) - (l + x - (a + b)) := by abel
    rw [this]
    exact Submodule.sub_mem _ hvo (X_iso G hc)
  refine ⟨Submodule.mem_sup.2 ⟨a + b, ⟨Submodule.add_mem _ ha hb, hco⟩, l + x - (a + b), hc, by abel⟩, hvo⟩

theorem lsub_eq_of_local : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := by
  intro D Z T G Fr hFr Λ₁ Λ₂ h₁ h₂ hL
  exact le_antisymm
    (lsub_le Z G (fun p => (Fr p).f) hFr Λ₁ Λ₂ h₂ fun p => (hL p).le)
    (lsub_le Z G (fun p => (Fr p).f) hFr Λ₂ Λ₁ h₁ fun p => (hL p).ge)

end GlobalTheory.Unfold.LsubG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsComplHermitianOrthogonalOfTotallyPositiveStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompl_hermitianOrthogonal_of_totallyPositive : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), (∀ x ∈ orth S U, x ≠ 0 → 0 < Algebra.trace ℚ E (S.hT x x)) → IsCompl U (orth S U) := by
  first | exact @GlobalTheory.isCompl_orth_of_definite | exact GlobalTheory.isCompl_orth_of_definite | (intros; apply GlobalTheory.isCompl_orth_of_definite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegersStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V), Submodule.IsLattice K Λ → ∀ W : Submodule K V, Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.isLattice_comap_subtype_ringOfIntegers | exact GlobalTheory.isLattice_comap_subtype_ringOfIntegers | (intros; apply GlobalTheory.isLattice_comap_subtype_ringOfIntegers <;> assumption)
end


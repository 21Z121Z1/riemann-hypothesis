import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverse
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (hs)

noncomputable section

namespace GlobalTheory.LeviIso.RadLoc

section
open scoped Matrix.Norms.Frobenius

theorem hs_eq_norm_sq {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : hs M = ‖M‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp [hs]

theorem hs_inv_compare {j : ℕ} (x : Matrix (Fin j) (Fin j) ℂ) (hx : x.det ≠ 0) {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (h : hs (x⁻¹ - 1) ≤ (1 - a) ^ 2) :
    a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1) := by
  simp only [hs_eq_norm_sq] at *
  have e : (x⁻¹ - 1) + (x - 1) = -((x⁻¹ - 1) * (x - 1)) := by
    rw [sub_mul, mul_sub, Matrix.nonsing_inv_mul _ (Ne.isUnit hx)]
    simp
    abel
  have h1 : ‖(x⁻¹ - 1) + (x - 1)‖ ≤ ‖x⁻¹ - 1‖ * ‖x - 1‖ := by
    rw [e, norm_neg]; exact norm_mul_le _ _
  have h2 : ‖x⁻¹ - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x - 1)
  have h3 : ‖x - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x⁻¹ - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x⁻¹ - 1)
  have hA := norm_nonneg (x - 1)
  have hB := norm_nonneg (x⁻¹ - 1)
  generalize ‖x - 1‖ = A at *
  generalize ‖x⁻¹ - 1‖ = B at *
  have h4 : B ≤ 1 - a := (sq_le_sq₀ hB (by linarith)).1 h
  have h5 : B * A ≤ (1 - a) * A := mul_le_mul_of_nonneg_right h4 hA
  rw [← mul_pow, ← mul_pow, sq_le_sq₀ (by positivity) hB, sq_le_sq₀ (by positivity) hA]
  constructor
  · linarith
  · have h6 : a * B ≤ a * ((2 - a) * A) := mul_le_mul_of_nonneg_left (by linarith) ha.le
    nlinarith [mul_nonneg (sq_nonneg (1 - a)) hA]

end

theorem hs_nonneg {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : 0 ≤ hs M := by
  unfold hs; positivity

theorem continuous_hs {j : ℕ} : Continuous (hs : Matrix (Fin j) (Fin j) ℂ → ℝ) := by
  unfold hs; fun_prop

def unitBallAt (j : ℕ) (s : ℝ) : Set (Fin j → Fin j → ℂ) := {x | hs (Matrix.of x - 1) ≤ s ^ 2}

theorem measurableSet_unitBallAt (j : ℕ) (s : ℝ) : MeasurableSet (unitBallAt j s) := by
  refine (isClosed_le (continuous_hs.comp ?_) continuous_const).measurableSet
  exact (continuous_id (X := Matrix (Fin j) (Fin j) ℂ)).sub continuous_const

theorem volume_unitBallAt (j : ℕ) {s : ℝ} (hs0 : 0 < s) :
    volume (unitBallAt j s) = ENNReal.ofReal (s ^ (2 * j ^ 2)) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  have hd : Module.finrank ℝ (EuclideanSpace ℂ (Fin j × Fin j)) = 2 * j ^ 2 := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin j × Fin j → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring
  set e := PoissonV.coords (Fin j) (Fin j) with he
  rw [← (PoissonV.measurePreserving_coords (Fin j) (Fin j)).measure_preimage
    (measurableSet_unitBallAt j s).nullMeasurableSet, ← he]
  have h1 : e ⁻¹' unitBallAt j s =
      Metric.closedBall (e.symm (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ))) s := by
    ext z
    rw [mem_closedBall_iff_norm, ← sq_le_sq₀ (norm_nonneg _) hs0.le, ← PoissonV.norm_sq_coords, ← he,
      map_sub, e.apply_symm_apply]
    rfl
  rw [h1, Measure.addHaar_closedBall _ _ hs0.le, hd]
  congr 1
  rw [← hd]
  have h := (stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin j × Fin j))).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem exists_subset {j : ℕ} {P : (Fin j → Fin j → ℂ) → Prop}
    (h : ∀ᶠ x in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)), P x) :
    ∃ δ > 0, ∀ s, 0 ≤ s → s < δ → ∀ x ∈ unitBallAt j s, P x := by
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun s hs0 hsδ x hx => H (lt_of_le_of_lt ?_ hsδ)⟩
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hs0]
  intro r
  rw [pi_norm_le_iff_of_nonneg hs0]
  intro c
  rw [← sq_le_sq₀ (norm_nonneg _) hs0]
  refine le_trans ?_ hx
  unfold hs
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_univ r))
  exact Finset.single_le_sum (f := fun c => ‖(Matrix.of x - 1) r c‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ c)

theorem eventually_good (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ x : Fin j → Fin j → ℂ in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)),
      (a ≤ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ∧ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (Matrix.of x - 1) ≤ hs ((Matrix.of x)⁻¹ - 1) ∧
      a ^ 2 * hs ((Matrix.of x)⁻¹ - 1) ≤ hs (Matrix.of x - 1) := by
  show ∀ᶠ x : Matrix (Fin j) (Fin j) ℂ in nhds 1,
      (a ≤ (‖x.det‖ ^ 2)⁻¹ ^ j ∧ (‖x.det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1)
  have hdet : Continuous fun x : Matrix (Fin j) (Fin j) ℂ => x.det := continuous_id.matrix_det
  have h1 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => (‖x.det‖ ^ 2)⁻¹ ^ j) 1 :=
    (((hdet.norm.pow 2).continuousAt).inv₀ (by simp)).pow j
  have h2 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => hs (x⁻¹ - 1)) 1 := by
    refine continuous_hs.continuousAt.comp (ContinuousAt.sub (continuousAt_matrix_inv _ ?_) continuousAt_const)
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (by simp)
  have h3 := h1.eventually (lt_mem_nhds (a := a) (by simpa using ha1))
  have h4 := h1.eventually (gt_mem_nhds (a := a⁻¹) (by simpa using (one_lt_inv₀ ha).2 ha1))
  have h5 := h2.eventually (gt_mem_nhds (a := (1 - a) ^ 2) (by
    have : 0 < 1 - a := by linarith
    simpa [hs] using pow_pos this 2))
  have h6 := (hdet.continuousAt (x := 1)).eventually_ne (y := 0) (by simp)
  filter_upwards [h3, h4, h5, h6] with x x3 x4 x5 x6
  exact ⟨⟨x3.le, x4.le⟩, hs_inv_compare x x6 ha ha1 x5.le⟩

theorem sandwich (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) ≤
        (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ∧
      (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ≤
      ENNReal.ofReal (a⁻¹ ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  obtain ⟨δ, hδ, H⟩ := exists_subset (eventually_good j ha ha1)
  filter_upwards [Ioo_mem_nhdsGT (mul_pos ha hδ)] with r ⟨hr, hrδ⟩
  have h2 : (0 : ℝ) < √2 := by positivity
  have h21 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have h22 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : r < δ := by nlinarith
  have hr2 : a * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) (by nlinarith)
  have hr3 : a⁻¹ * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) ?_
    rwa [inv_mul_lt_iff₀ ha]
  have hrd : ENNReal.ofReal (r ^ (2 * j ^ 2)) ≠ 0 := by
    simpa using pow_pos hr _
  have hvol : ∀ b : ℝ, 0 < b → ENNReal.ofReal (2 ^ (j ^ 2)) * (ENNReal.ofReal b *
      volume (unitBallAt j (b * r / √2))) = ENNReal.ofReal (b ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) * ENNReal.ofReal (r ^ (2 * j ^ 2)) := by
    intro b hb
    rw [volume_unitBallAt j (by positivity), mul_right_comm, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [div_pow, pow_mul √2, h22, mul_pow]
    field_simp
    ring
  constructor
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hrd) (Or.inl ENNReal.ofReal_ne_top), ← hvol a ha,
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans ?_ (measure_mono (s := unitBallAt j (a * r / √2)) fun x hx => ?_)
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr2 x hx).1.1
    · have h3 := (H _ (by positivity) hr2 x hx).2.2
      have h4 : hs (Matrix.of x - 1) ≤ a ^ 2 * r ^ 2 / 2 := by
        have : hs (Matrix.of x - 1) ≤ (a * r / √2) ^ 2 := hx
        rwa [div_pow, h22, mul_pow] at this
      have h5 : hs ((Matrix.of x)⁻¹ - 1) ≤ r ^ 2 / 2 :=
        le_of_mul_le_mul_left (a := a ^ 2) (by linarith) (by positivity)
      have h6 : a ^ 2 * r ^ 2 ≤ r ^ 2 := mul_le_of_le_one_left (by positivity) (by nlinarith)
      refine Real.sqrt_le_iff.2 ⟨hr.le, by linarith⟩
  · rw [ENNReal.div_le_iff hrd ENNReal.ofReal_ne_top, ← hvol a⁻¹ (by positivity),
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans (measure_mono (t := unitBallAt j (a⁻¹ * r / √2)) fun x hx => ?_) ?_
    · have h1 := (Real.sqrt_le_iff.1 hx).2
      have h0 := hs_nonneg ((Matrix.of x)⁻¹ - 1)
      have h0' := hs_nonneg (Matrix.of x - 1)
      have h3 := (H r hr.le hr1 x (show hs (Matrix.of x - 1) ≤ r ^ 2 by linarith)).2.1
      have h6 : a ^ 2 * hs (Matrix.of x - 1) ≤ hs (Matrix.of x - 1) :=
        mul_le_of_le_one_left h0' (by nlinarith)
      show hs (Matrix.of x - 1) ≤ (a⁻¹ * r / √2) ^ 2
      rw [div_pow, h22, mul_pow, inv_pow, le_div_iff₀ (by norm_num), le_inv_mul_iff₀ (by positivity)]
      linarith
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr3 x hx).1.2

end GlobalTheory.LeviIso.RadLoc

namespace GlobalTheory.LeviIso

open RadLoc

theorem isRadial_haarLoc (j : ℕ) : IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
    (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  unfold IsRadial
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) with hω
  have hωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hc : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * ω) (nhds 1) (nhds ω) := by
    have : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1))) (nhds 1) (nhds 1) := by
      simpa using ENNReal.tendsto_ofReal ((continuous_pow (2 * j ^ 2 + 1)).tendsto (1 : ℝ))
    simpa using ENNReal.Tendsto.mul_const this (Or.inl one_ne_zero)
  have hi : Filter.Tendsto (fun a : ℝ => a⁻¹) (nhds 1) (nhds 1) := by
    simpa using Filter.Tendsto.inv₀ (Filter.tendsto_id (x := nhds (1 : ℝ))) one_ne_zero
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨a, h1, h2, h3⟩ := (((hc.eventually (lt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_lt_of_le h1 hr.1
  · obtain ⟨a, h1, h2, h3⟩ := ((((hc.comp hi).eventually (gt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_le_of_lt hr.2 h1

end GlobalTheory.LeviIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeSublevelAsymptoticsProd
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Filter Topology
open scoped ENNReal

namespace GlobalTheory.LeviIso

def SublevelLe {X X' : Type} [MeasurableSpace X] [MeasurableSpace X'] (c : ℝ≥0∞) (T : ℝ)
    (μ : Measure X) (q : X → ℝ) (μ' : Measure X') (q' : X' → ℝ) : Prop :=
  ∀ t ≤ T, μ {x | q x ≤ t} ≤ c * μ' {x | q' x ≤ t}

theorem SublevelLe.mono {X X' : Type} [MeasurableSpace X] [MeasurableSpace X'] {c : ℝ≥0∞}
    {T T' : ℝ} {μ : Measure X} {q : X → ℝ} {μ' : Measure X'} {q' : X' → ℝ}
    (h : SublevelLe c T μ q μ' q') (hT : T' ≤ T) : SublevelLe c T' μ q μ' q' :=
  fun t ht => h t (ht.trans hT)

theorem SublevelLe.prod {X X' Y Y' : Type} [MeasurableSpace X] [MeasurableSpace X']
    [MeasurableSpace Y] [MeasurableSpace Y'] {c : ℝ≥0∞} {T : ℝ}
    {μ : Measure X} {q : X → ℝ} {μ' : Measure X'} {q' : X' → ℝ}
    {ν : Measure Y} {p : Y → ℝ} {ν' : Measure Y'} {p' : Y' → ℝ}
    [SFinite μ] [SFinite μ'] [SFinite ν] [SFinite ν'] (hc : c ≠ ⊤)
    (hq : Measurable q) (hq' : Measurable q') (hp : Measurable p) (hp' : Measurable p')
    (hq0 : ∀ x, 0 ≤ q' x) (hp0 : ∀ y, 0 ≤ p y)
    (h1 : SublevelLe c T μ q μ' q') (h2 : SublevelLe c T ν p ν' p') :
    SublevelLe (c * c) T (μ.prod ν) (fun z => q z.1 + p z.2) (μ'.prod ν')
      (fun z => q' z.1 + p' z.2) := by
  intro t ht
  have m1 : MeasurableSet {z : X × Y | q z.1 + p z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have m2 : MeasurableSet {z : X' × Y | q' z.1 + p z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have m3 : MeasurableSet {z : X' × Y' | q' z.1 + p' z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have s1 : (μ.prod ν) {z : X × Y | q z.1 + p z.2 ≤ t}
      ≤ c * (μ'.prod ν) {z : X' × Y | q' z.1 + p z.2 ≤ t} := by
    rw [Measure.prod_apply_symm m1, Measure.prod_apply_symm m2, ← lintegral_const_mul' _ _ hc]
    refine lintegral_mono fun y => ?_
    have := h1 (t - p y) (by linarith [hp0 y])
    simpa only [Set.preimage_setOf_eq, le_sub_iff_add_le] using this
  have s2 : (μ'.prod ν) {z : X' × Y | q' z.1 + p z.2 ≤ t}
      ≤ c * (μ'.prod ν') {z : X' × Y' | q' z.1 + p' z.2 ≤ t} := by
    rw [Measure.prod_apply m2, Measure.prod_apply m3, ← lintegral_const_mul' _ _ hc]
    refine lintegral_mono fun x => ?_
    have := h2 (t - q' x) (by linarith [hq0 x])
    simpa only [Set.preimage_setOf_eq, le_sub_iff_add_le'] using this
  calc _ ≤ _ := s1
    _ ≤ c * (c * _) := by gcongr
    _ = _ := by rw [mul_assoc]

theorem volume_norm_sq_le (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ r ^ 2}
      = ENNReal.ofReal (r ^ d) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have : {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ r ^ 2} = Metric.closedBall 0 r := by
    ext u
    simp [sq_le_sq₀ (norm_nonneg u) hr]
  rw [this, Measure.addHaar_closedBall _ _ hr]
  simp

theorem setOf_sqrt_le {X : Type} (q : X → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    {x | √(q x) ≤ r} = {x | q x ≤ r ^ 2} := by
  ext x
  simp [Real.sqrt_le_left hr, Real.sqrt_le_iff, hr]

theorem volume_prod_norm_sq_le (d e : ℕ) (t : ℝ) :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod
      (volume : Measure (EuclideanSpace ℝ (Fin e)))) {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ t}
      = volume {u : EuclideanSpace ℝ (Fin (d + e)) | ‖u‖ ^ 2 ≤ t} := by
  let f : WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d + e)) :=
    ((stdOrthonormalBasis ℝ _).reindex (finCongr (by
      rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]; simp))).repr
  have h := f.measurePreserving.comp (WithLp.volume_preserving_toLp _ _)
  rw [← h.measure_preimage (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet]
  congr 1
  ext z
  simp [WithLp.prod_norm_sq_eq_of_L2]

theorem exists_one_lt_mul_mul_lt {a b : ℝ≥0∞} (h : a < b) :
    ∃ c : ℝ≥0∞, 1 < c ∧ c ≠ ⊤ ∧ c * c * a < b := by
  have ha : a ≠ ⊤ := h.ne_top
  have t1 : Tendsto (fun c : ℝ≥0∞ => c * c * a) (𝓝 1) (𝓝 (1 * 1 * a)) :=
    ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.mul tendsto_id (by simp) tendsto_id (by simp)) (Or.inr ha)
  simp only [one_mul] at t1
  have e1 := t1.eventually (gt_mem_nhds h)
  have e2 : ∀ᶠ c : ℝ≥0∞ in 𝓝 1, c < ⊤ := gt_mem_nhds (by simp)
  haveI : (𝓝[>] (1 : ℝ≥0∞)).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, by simp⟩
  obtain ⟨c, ⟨h1, h2⟩, h3⟩ := (((e1.and e2).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ≥0∞)) (a := 1))).exists
  exact ⟨c, h3, h2.ne, h1⟩

theorem IsRadial.sublevelLe {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℝ} {d : ℕ}
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (h : IsRadial μ q d) {c : ℝ≥0∞} (hc : 1 < c)
    (hc' : c ≠ ⊤) :
    ∃ T > 0, SublevelLe c T μ q volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) ∧
      SublevelLe c T volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) μ q := by
  unfold IsRadial at h
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ω0 : ω ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have ωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hlt : ω < c * ω := by
    simpa using ENNReal.mul_lt_mul_left ω0 ωt hc
  have e1 := h.eventually (gt_mem_nhds hlt)
  have e2 := (ENNReal.Tendsto.const_mul (a := c) h (Or.inl ω0)).eventually (lt_mem_nhds hlt)
  have e3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ {x | √(q x) ≤ r} ≤ c * (ENNReal.ofReal (r ^ d) * ω) ∧
      ENNReal.ofReal (r ^ d) * ω ≤ c * μ {x | √(q x) ≤ r} := by
    filter_upwards [e1, e2, self_mem_nhdsWithin] with r h1 h2 hr
    have hr' : (0 : ℝ) < r := hr
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    constructor
    · have := (ENNReal.div_le_iff n0 ENNReal.ofReal_ne_top).1 h1.le
      calc _ ≤ _ := this
        _ = _ := by ring
    · rw [← mul_div_assoc] at h2
      have := (ENNReal.le_div_iff_mul_le (Or.inl n0) (Or.inl ENNReal.ofReal_ne_top)).1 h2.le
      rwa [mul_comm] at this
  have tg : Tendsto (fun r : ℝ => μ {x | √(q x) ≤ r}) (𝓝[>] 0) (𝓝 (μ {x | √(q x) ≤ 0})) := by
    have hI : {x | √(q x) ≤ 0} = ⋂ r > (0 : ℝ), {x | √(q x) ≤ r} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h r hr => h.trans hr.le, fun h => le_of_forall_gt_imp_ge_of_dense h⟩
    rw [hI]
    refine tendsto_measure_biInter_gt (s := fun r : ℝ => {x | √(q x) ≤ r})
      (fun r _ => (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet)
      (fun i j _ hij x hx => le_trans hx hij) ?_
    obtain ⟨r, h1, h2⟩ := (e3.and self_mem_nhdsWithin).exists
    exact ⟨r, h2, ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hc' (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ωt)) h1.1⟩
  have th : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ d) * ω) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ d) * ω)) :=
    ENNReal.Tendsto.mul_const
      (((ENNReal.continuous_ofReal.comp (continuous_pow d)).tendsto 0).mono_left
        nhdsWithin_le_nhds) (Or.inr ωt)
  have z1 := le_of_tendsto_of_tendsto tg (ENNReal.Tendsto.const_mul (a := c) th (Or.inr hc'))
    (e3.mono fun r h => h.1)
  have z2 := le_of_tendsto_of_tendsto th (ENNReal.Tendsto.const_mul (a := c) tg (Or.inr hc'))
    (e3.mono fun r h => h.2)
  obtain ⟨δ, hδ, hs⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 e3
  have hδ' : (0 : ℝ) < δ := hδ
  have key : ∀ r, 0 ≤ r → r ≤ δ → μ {x | √(q x) ≤ r} ≤ c * (ENNReal.ofReal (r ^ d) * ω) ∧
      ENNReal.ofReal (r ^ d) * ω ≤ c * μ {x | √(q x) ≤ r} := by
    intro r h0 h1
    rcases h0.eq_or_lt with rfl | h0
    · exact ⟨z1, z2⟩
    · exact hs ⟨h0, h1⟩
  have key2 : ∀ t ≤ δ ^ 2,
      μ {x | q x ≤ t} ≤ c * volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} ∧
      volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} ≤ c * μ {x | q x ≤ t} := by
    intro t ht
    rcases lt_or_ge t 0 with h0 | h0
    · have a1 : {x | q x ≤ t} = ∅ := by
        ext x; simp; linarith [hq0 x]
      have a2 : {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} = ∅ := by
        ext x; simp; nlinarith [sq_nonneg ‖x‖]
      simp [a1, a2]
    · have := key (√t) (Real.sqrt_nonneg _) (Real.sqrt_le_iff.2 ⟨hδ'.le, ht⟩)
      rw [← volume_norm_sq_le d (Real.sqrt_nonneg _), setOf_sqrt_le q (Real.sqrt_nonneg _),
        Real.sq_sqrt h0] at this
      exact this
  exact ⟨δ ^ 2, by positivity, fun t ht => (key2 t ht).1, fun t ht => (key2 t ht).2⟩

theorem isRadial_of_sublevelLe {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℝ} {d : ℕ}
    (h : ∀ c : ℝ≥0∞, 1 < c → c ≠ ⊤ → ∃ T > 0,
      SublevelLe (c * c) T μ q volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) ∧
      SublevelLe (c * c) T volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) μ q) :
    IsRadial μ q d := by
  unfold IsRadial
  have hv := fun r => volume_norm_sq_le d (r := r)
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ev : ∀ T > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r ^ 2 ≤ T := by
    intro T hT
    filter_upwards [Ioc_mem_nhdsGT (Real.sqrt_pos.2 hT)] with r hr
    exact ⟨hr.1, (Real.le_sqrt hr.1.le hT.le).1 hr.2⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨c, c1, c2, c3⟩ := exists_one_lt_mul_mul_lt ha
    obtain ⟨T, hT, -, h2⟩ := h c c1 c2
    filter_upwards [ev T hT] with r ⟨hr, hrT⟩
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have := h2 _ hrT
    rw [hv r hr.le, ← setOf_sqrt_le q hr.le, mul_comm,
      ← ENNReal.le_div_iff_mul_le (Or.inl n0) (Or.inl ENNReal.ofReal_ne_top),
      mul_div_assoc] at this
    by_contra hn
    have h3 : c * c * (μ {x | √(q x) ≤ r} / ENNReal.ofReal (r ^ d)) ≤ c * c * a := by
      gcongr; exact not_lt.1 hn
    exact absurd (c3.trans_le (this.trans h3)) (lt_irrefl _)
  · obtain ⟨c, c1, c2, c3⟩ := exists_one_lt_mul_mul_lt ha
    obtain ⟨T, hT, h1, -⟩ := h c c1 c2
    filter_upwards [ev T hT] with r ⟨hr, hrT⟩
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have := h1 _ hrT
    rw [hv r hr.le, ← setOf_sqrt_le q hr.le] at this
    refine lt_of_le_of_lt ?_ c3
    rw [ENNReal.div_le_iff n0 ENNReal.ofReal_ne_top]
    calc _ ≤ _ := this
      _ = _ := by ring

theorem isRadial_prod : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (q : X → ℝ) (p : Y → ℝ) (d e : ℕ), Measurable q → Measurable p → (∀ x, 0 ≤ q x) → (∀ y, 0 ≤ p y) → IsRadial μ q d → IsRadial ν p e → IsRadial (μ.prod ν) (fun z => q z.1 + p z.2) (d + e) := by
  intro X Y _ _ μ ν _ _ q p d e hq hp hq0 hp0 h1 h2
  refine isRadial_of_sublevelLe fun c c1 c2 => ?_
  obtain ⟨T, hT, a1, a2⟩ := h1.sublevelLe hq hq0 c1 c2
  obtain ⟨T', hT', b1, b2⟩ := h2.sublevelLe hp hp0 c1 c2
  refine ⟨min T T', lt_min hT hT', fun t ht => ?_, fun t ht => ?_⟩
  · have := SublevelLe.prod c2 hq (by fun_prop) hp (by fun_prop) (fun _ => by positivity) hp0
      (a1.mono (min_le_left _ _)) (b1.mono (min_le_right _ _)) t ht
    rwa [volume_prod_norm_sq_le] at this
  · have := SublevelLe.prod c2 (by fun_prop) hq (by fun_prop) hp hq0 (fun _ => by positivity)
      (a2.mono (min_le_left _ _)) (b2.mono (min_le_right _ _)) t ht
    rwa [volume_prod_norm_sq_le] at this

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvLeSizeQAboveOrthogonalSaturated
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Count.PerpSize

open GlobalTheory.Count.PerpStep

theorem inv_le_sizeQ_perp : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → ∀ N, perpIn I x R < N → N ≤ lamX I x → hi⁻¹ ≤ sizeQ (bas I) (frm I x) N (perpIn I x R) := by
  intro I x R hi hR hhi hL N hPN hNA
  obtain ⟨-, hA, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨htc, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  obtain ⟨-, -, -, hm⟩ := GlobalTheory.Count.PerpStep.main I x
  obtain ⟨N', n1, n2, n3, n4⟩ := nd_sat (bas I) (frm I x) hX hA hNA
  obtain ⟨sP, rP, ppR, -, -⟩ := hm R R hR hR le_rfl
  obtain ⟨sS, rS, ppN, -, -⟩ := hm N' N' n2 n2 le_rfl
  have hPN' : perpIn I x R ≤ N' := hPN.le.trans n1
  obtain ⟨-, -, -, hle, hq⟩ := hm _ N' sP n2 hPN'
  rw [ppR] at hle hq
  have hfg : ∀ {M}, M ≤ lamX I x → M.FG := fun h => Submodule.FG.of_le hA h
  have hR0 : R ≠ ⊥ := by
    intro e
    have h1 : perpIn I x N' = R := by
      rw [e] at hle ⊢
      exact le_bot_iff.1 hle
    rw [h1] at ppN
    exact (lt_of_lt_of_le hPN n1).ne ppN
  rw [htQ_eq _ _ hX _ _ (hfg hR.1) (sat_mono _ _ sS hle hR.1),
    htQ_eq _ _ hX _ _ (hfg n2.1) (sat_mono _ _ sP hPN' n2.1), ← Real.exp_neg] at hq
  have hq' := Real.exp_injective hq
  obtain ⟨l0, lb⟩ := largest_bound (bas I) (frm I x) hX (hfg hR.1) hR0 hle
  have hd := rk_lt (bas I) (frm I x) hX hA sP hPN hNA
  have r1 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg hR.1)).2.1
  have r2 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sP.1)).2.1
  have r3 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sS.1)).2.1
  have r4 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg n2.1)).2.1
  have hrk : rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R =
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N := by
    rw [← n3, r1, r2, r3, r4, ← mul_add, ← mul_add, rP, rS]
  have hrk' : (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') =
      (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hrk
    push_cast at h
    linarith
  rw [hrk'] at lb
  rw [log_sizeQ (bas I) (frm I x) hX hA sP hPN hNA, ← Real.log_le_iff_le_exp (inv_pos.2 hhi),
    le_div_iff₀ (sub_pos.2 hd), Real.log_inv]
  have h4 := Real.log_le_log l0 hL
  have h5 := mul_le_mul_of_nonneg_right h4 (sub_pos.2 hd).le
  linarith

end GlobalTheory.Count.PerpSize
end


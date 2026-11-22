import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AExact
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace ChartNormSquare

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem continuousOn_source_of {E : Type*} [TopologicalSpace E] (e : OpenPartialHomeomorph Y (V n))
    (f : Y → E) (h : ContinuousOn (f ∘ e.symm) e.target) : ContinuousOn f e.source := by
  refine (h.comp e.continuousOn e.mapsTo).congr ?_
  intro y hy
  simp [Function.comp, e.left_inv hy]

theorem nsq_eq_chart (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) (hF : A.IsSec la F)
    (i : ι) (y : Y) (hy : y ∈ (A.chart i).source) :
    A.nsq la F y = ‖F i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold nsq
  have hj : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
  have htr := hF.2 i (A.pick y) y (Set.mem_univ _) hy hj
  have hph := A.ph_trans la i (A.pick y) y hy hj
  have hg := A.g_ne la i (A.pick y) y hy hj
  have hgp : 0 < ‖A.g la i (A.pick y) y‖ ^ 2 := by positivity
  have he : Real.exp (-(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2))) =
      ‖A.g la i (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la i y) := by
    rw [show -(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2)) =
      -A.ph la i y + Real.log (‖A.g la i (A.pick y) y‖ ^ 2) by ring, Real.exp_add,
      Real.exp_log hgp]
    ring
  rw [hph, he, htr, norm_mul, mul_pow]
  ring

theorem continuous_nsq (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ)
    (hF : A.IsSec la F) : Continuous (A.nsq la F) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hs : (A.chart (A.pick y)).source ∈ 𝓝 y :=
    (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hFc : ContinuousOn (F (A.pick y)) (A.chart (A.pick y)).source := by
    apply continuousOn_source_of
    have := (hF.1 (A.pick y)).continuousOn
    simpa using this
  have hph : ContinuousOn (A.ph la (A.pick y)) (A.chart (A.pick y)).source :=
    continuousOn_source_of _ _ ((A.smooth_ph la (A.pick y)).continuousOn)
  have hc : ContinuousOn (fun x => ‖F (A.pick y) x‖ ^ 2 * Real.exp (-A.ph la (A.pick y) x))
      (A.chart (A.pick y)).source :=
    (hFc.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  refine (hc.continuousAt hs).congr ?_
  filter_upwards [hs] with x hx
  exact (nsq_eq_chart A la F hF _ x hx).symm

theorem nsq_nonneg (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) (y : Y) :
    0 ≤ A.nsq la F y := by
  unfold nsq; positivity

theorem sqn_nonneg {N : ℕ} (A : WeightedAtlas n Y ι La) (la : La) (w : Fin N → ι → Y → ℂ)
    (y : Y) : 0 ≤ A.sqn la w y :=
  Finset.sum_nonneg fun k _ => nsq_nonneg A la (w k) y

end ChartNormSquare

universe u

namespace ChartNormSquare

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

end ChartNormSquare

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeA
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal

noncomputable section

def apraW (d : ℕ) (ε τ : ℝ) (t : ℝ) : ℝ≥0∞ :=
  if t < ε then ENNReal.ofReal ((max (t ^ 2) τ) ^ (-(d : ℝ))) else 0

lemma apraW_meas (d : ℕ) (ε τ : ℝ) : Measurable (apraW d ε τ) := by
  unfold apraW
  refine Measurable.ite measurableSet_Iio ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp
    (((measurable_id.pow_const 2).max measurable_const).pow_const _)

lemma apraW_anti (d : ℕ) (ε : ℝ) {τ τ' : ℝ} (hτ : 0 < τ) (h : τ ≤ τ') (t : ℝ) :
    apraW d ε τ' t ≤ apraW d ε τ t := by
  unfold apraW
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (lt_max_of_lt_right hτ)
      (max_le_max le_rfl h) (neg_nonpos.mpr (Nat.cast_nonneg d)))
  · exact le_rfl

lemma apra_slice (d k : ℕ) (hMVd : MVStatement d) (ε τ : ℝ) (u : V d × V k → ℂ)
    (hu : DifferentiableOn ℂ u (ball (0 : V d) ε ×ˢ ball (0 : V k) ε)) (ζ : V k)
    (hζ : ζ ∈ ball (0 : V k) ε) :
    ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) * ∫⁻ x : V d, apraW d ε τ ‖x‖ ≤
      ∫⁻ x in ball (0 : V d) ε,
        ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  have hdiff : DifferentiableOn ℂ (fun x : V d => u (x, ζ)) (ball 0 ε) :=
    hu.comp (differentiableOn_id.prodMk (differentiableOn_const ζ)) (fun x hx => ⟨hx, hζ⟩)
  have h := hMVd ε (fun x => u (x, ζ)) (apraW d ε τ) hdiff (apraW_meas d ε τ)
    (fun t ht => by simp [apraW, not_lt.mpr ht])
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun x => ?_
  by_cases hx : ‖x‖ < ε
  · have hx' : x ∈ ball (0 : V d) ε := mem_ball_zero_iff.mpr hx
    simp only [apraW, if_pos hx, Set.indicator_of_mem hx']
    rw [ENNReal.ofReal_mul (by positivity)]
  · have hx' : x ∉ ball (0 : V d) ε := fun h => hx (mem_ball_zero_iff.mp h)
    simp [apraW, hx]

lemma apra_base (k : ℕ) (hMVk : MVStatement k) (ε : ℝ) (g : V k → ℂ)
    (hg : DifferentiableOn ℂ g (ball 0 ε)) :
    ENNReal.ofReal (‖g 0‖ ^ 2) * volume (ball (0 : V k) ε) ≤
      ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖g ζ‖ ^ 2) := by
  have h := hMVk ε g (fun t => if t < ε then 1 else 0) hg
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)
    (fun t ht => by simp [not_lt.mpr ht])
  have e1 : ∫⁻ y : V k, (fun t : ℝ => if t < ε then (1 : ℝ≥0∞) else 0) ‖y‖ =
      volume (ball (0 : V k) ε) := by
    rw [← lintegral_indicator_one measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : ‖y‖ < ε <;> simp [hy, Set.indicator]
  have e2 : ∫⁻ y : V k, ENNReal.ofReal (‖g y‖ ^ 2) *
      (fun t : ℝ => if t < ε then (1 : ℝ≥0∞) else 0) ‖y‖ =
      ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖g ζ‖ ^ 2) := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : ‖y‖ < ε <;> simp [hy, Set.indicator]
  rw [e1, e2] at h
  exact h

lemma apra_blow (d : ℕ) (hd : 1 ≤ d) (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) :
    ⨆ n : ℕ, ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ = ⊤ := by
  have : Nontrivial (V d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  set f : ℕ → V d → ℝ≥0∞ := fun n x => apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ with hf
  have hmeas : ∀ n, Measurable (f n) := fun n => (apraW_meas _ _ _).comp measurable_norm
  have hmono : Monotone f := by
    intro m n hmn x
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    show apraW d ε (1 / ((m : ℝ) + 1)) ‖x‖ ≤ apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖
    exact apraW_anti d ε h2 h1 _
  rw [← lintegral_iSup hmeas hmono]
  set g : V d → ℝ≥0∞ := fun x => ENNReal.ofReal ‖x‖ ^ (-2 * (d : ℝ)) with hg
  have hpt : ∀ x : V d, x ≠ 0 → (ball (0 : V d) ε).indicator g x ≤ ⨆ n, f n x := by
    intro x hx0
    by_cases hx : ‖x‖ < ε
    · rw [Set.indicator_of_mem (mem_ball_zero_iff.mpr hx)]
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (pow_pos hpos 2)
      refine le_trans ?_ (le_iSup _ n)
      simp only [hf, hg, apraW, if_pos hx]
      rw [max_eq_left hn.le, ENNReal.ofReal_rpow_of_pos hpos, ← Real.rpow_natCast,
        ← Real.rpow_mul hpos.le]
      apply le_of_eq
      congr 2
      push_cast
      ring
    · rw [Set.indicator_of_notMem (fun h => hx (mem_ball_zero_iff.mp h))]
      exact bot_le
  have hae : ∀ᵐ x ∂(volume : Measure (V d)), (ball (0 : V d) ε).indicator g x ≤ ⨆ n, f n x := by
    have h0 : ∀ᵐ x ∂(volume : Measure (V d)), x ∉ ({0} : Set (V d)) :=
      measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
    filter_upwards [h0] with x hx using hpt x (by simpa using hx)
  have hT : ∫⁻ y in ball (0 : V d) 1, g y = ⊤ :=
    not_lt_top_iff.mp (fun h => lt_irrefl _ ((hMVI hd d).1 h))
  have hdn : -2 * (d : ℝ) ≤ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hpt2 : ∀ y : V d, g y ≤ (ball (0 : V d) ε).indicator g y + ENNReal.ofReal ε ^ (-2 * (d : ℝ)) := by
    intro y
    by_cases hy : y ∈ ball (0 : V d) ε
    · rw [Set.indicator_of_mem hy]
      exact le_self_add
    · rw [Set.indicator_of_notMem hy, zero_add]
      have : ε ≤ ‖y‖ := by simpa [mem_ball_zero_iff] using hy
      simp only [hg]
      rw [ENNReal.ofReal_rpow_of_pos (hε.trans_le this), ENNReal.ofReal_rpow_of_pos hε]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hε this hdn)
  have hc : ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [ENNReal.rpow_eq_top_iff, hε]) measure_ball_lt_top.ne
  have hle : ∫⁻ y in ball (0 : V d) 1, g y ≤ (∫⁻ y, (ball (0 : V d) ε).indicator g y) +
      ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) := by
    calc ∫⁻ y in ball (0 : V d) 1, g y
        ≤ ∫⁻ y in ball (0 : V d) 1, ((ball (0 : V d) ε).indicator g y +
            ENNReal.ofReal ε ^ (-2 * (d : ℝ))) := lintegral_mono fun y => hpt2 y
      _ = (∫⁻ y in ball (0 : V d) 1, (ball (0 : V d) ε).indicator g y) +
            ENNReal.ofReal ε ^ (-2 * (d : ℝ)) * volume (ball (0 : V d) 1) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ _ := add_le_add (setLIntegral_le_lintegral _ _) le_rfl
  have hind : ∫⁻ y, (ball (0 : V d) ε).indicator g y = ⊤ := by
    by_contra hne
    exact (ENNReal.add_ne_top.2 ⟨hne, hc⟩) (eq_top_iff.2 (hT ▸ hle))
  exact eq_top_iff.2 (hind ▸ lintegral_mono_ae hae)

theorem ap_prod_blowup (d k : ℕ) (hd : 1 ≤ d) (hMVd : MVStatement d) (hMVk : MVStatement k)
    (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) (M : ℝ) :
    ∃ τ0 : ℝ, 0 < τ0 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → ∀ u : V d × V k → ℂ,
      DifferentiableOn ℂ u (Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε) →
      ENNReal.ofReal (M * ‖u 0‖ ^ 2) ≤
        ∫⁻ z in Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε,
          ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  have hvol : volume (ball (0 : V k) ε) ≠ 0 := (measure_ball_pos volume (0 : V k) hε).ne'
  have hsup : ⨆ n : ℕ, volume (ball (0 : V k) ε) *
      ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ = ⊤ := by
    rw [← ENNReal.mul_iSup, apra_blow d hd hMVI ε hε, ENNReal.mul_top hvol]
  have hlt : ENNReal.ofReal M < ⨆ n : ℕ, volume (ball (0 : V k) ε) *
      ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ := by
    rw [hsup]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun τ hτ hτ0 u hu => ?_⟩
  have hIτ : ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ ≤ ∫⁻ x : V d, apraW d ε τ ‖x‖ :=
    lintegral_mono fun x => apraW_anti d ε hτ hτ0 _
  have hslice : ∀ ζ ∈ ball (0 : V k) ε,
      ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) * ∫⁻ x : V d, apraW d ε τ ‖x‖ ≤
        ∫⁻ x in ball (0 : V d) ε,
          ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) :=
    fun ζ hζ => apra_slice d k hMVd ε τ u hu ζ hζ
  have hbase := apra_base k hMVk ε (fun ζ => u (0, ζ))
    (hu.comp ((differentiableOn_const (0 : V d)).prodMk differentiableOn_id)
      (fun ζ hζ => ⟨mem_ball_self hε, hζ⟩))
  have hmeasF : AEMeasurable
      (fun z : V d × V k => ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))))
      ((volume.restrict (ball (0 : V d) ε)).prod (volume.restrict (ball (0 : V k) ε))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hu' : AEMeasurable u (volume.restrict (ball (0 : V d) ε ×ˢ ball (0 : V k) ε)) :=
      hu.continuousOn.aemeasurable (measurableSet_ball.prod measurableSet_ball)
    exact ((hu'.norm.pow_const 2).mul (((measurable_fst.norm.pow_const 2).max
      measurable_const).pow_const _).aemeasurable).ennreal_ofReal
  have hfub : ∫⁻ z in ball (0 : V d) ε ×ˢ ball (0 : V k) ε,
      ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) =
      ∫⁻ ζ in ball (0 : V k) ε, ∫⁻ x in ball (0 : V d) ε,
        ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hmeasF]
  rw [hfub]
  calc ENNReal.ofReal (M * ‖u 0‖ ^ 2)
      = ENNReal.ofReal (‖u (0, 0)‖ ^ 2) * ENNReal.ofReal M := by
        rw [ENNReal.ofReal_mul' (by positivity), mul_comm]
        rfl
    _ ≤ ENNReal.ofReal (‖u (0, 0)‖ ^ 2) *
          (volume (ball (0 : V k) ε) * ∫⁻ x : V d, apraW d ε τ ‖x‖) :=
        mul_le_mul' le_rfl (hn.le.trans (mul_le_mul' le_rfl hIτ))
    _ = (ENNReal.ofReal (‖u (0, 0)‖ ^ 2) * volume (ball (0 : V k) ε)) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := (mul_assoc _ _ _).symm
    _ ≤ (∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖u (0, ζ)‖ ^ 2)) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := mul_le_mul' hbase le_rfl
    _ ≤ ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := lintegral_mul_const_le _ _
    _ ≤ _ := setLIntegral_mono' measurableSet_ball hslice

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeW
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

structure APGeom (A : WeightedAtlas n Y ι La) (la : La) (d m : ℕ) (r r' : ℝ) (B : Fin m → Set Y)
    (π : Fin m → Y → EuclideanSpace ℂ (Fin d)) (f : Fin m → ι → Y → ℂ) : Prop where
  r_pos : 0 < r
  r_lt : r < r'
  isOpen : ∀ a, IsOpen (B a)
  disj : Pairwise (Function.onFun Disjoint B)
  holo : ∀ a i, DifferentiableOn ℂ (π a ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' B a)
  lt_r' : ∀ a, ∀ y ∈ B a, ‖π a y‖ < r'
  proper : ∀ a (K : Set (EuclideanSpace ℂ (Fin d))), IsCompact K → K ⊆ Metric.ball 0 r' →
    IsCompact (B a ∩ π a ⁻¹' K)
  sec : ∀ a, A.IsSecOn (A.kap + la) (B a) (f a)

def apBump {m d : ℕ} (B : Fin m → Set Y) (π : Fin m → Y → EuclideanSpace ℂ (Fin d)) (r : ℝ)
    (Φ : ℝ → ℝ) (y : Y) : ℝ :=
  ∑ a, (B a).indicator (fun x => Φ (‖π a x‖ ^ 2 / r ^ 2)) y

def chartCutoffSum {m d : ℕ} (B : Fin m → Set Y) (π : Fin m → Y → EuclideanSpace ℂ (Fin d)) (r : ℝ)
    (χ : ℝ → ℝ) (f : Fin m → ι → Y → ℂ) : ι → Y → ℂ :=
  fun i y => ∑ a, (B a).indicator (fun x => ((χ (‖π a x‖ ^ 2 / r ^ 2) : ℝ) : ℂ) * f a i x) y

def apH {m d : ℕ} (A : WeightedAtlas n Y ι La) (la : La) (B : Fin m → Set Y)
    (π : Fin m → Y → EuclideanSpace ℂ (Fin d)) (r : ℝ) (χ : ℝ → ℝ) (f : Fin m → ι → Y → ℂ)
    (c : ℝ) (y : Y) : ℝ≥0∞ :=
  ∑ a, (B a).indicator (fun x => ENNReal.ofReal (A.nsq (A.kap + la) (f a) x *
    deriv χ (‖π a x‖ ^ 2 / r ^ 2) ^ 2 * (‖π a x‖ ^ 2 / r ^ 2) / c)) y

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourBasic
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem fourBasic_cube_vol (f : ℕ) :
    volume (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1)) = 1 := by
  rw [MeasureTheory.volume_pi_pi]; simp [Real.volume_Ioc]

theorem fourBasic_norm_exp {f : ℕ} (ν : Fin f → ℤ) (x b : Fin f → ℝ) :
    ‖Complex.exp (-2 * Real.pi * Complex.I *
        ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I))‖ =
      Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) := by
  have hsplit : (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) =
      ((∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) + ((∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have harg : -2 * Real.pi * Complex.I *
        (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) =
      ((2 * Real.pi * ∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) +
        ((-2 * Real.pi * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * Complex.I := by
    rw [hsplit]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * ∑ k, (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq
  rw [harg, Complex.norm_exp]
  congr 1
  simp

theorem four_bound (f : ℕ) : FOURBoundStatement f := by
  intro h b ν C hC
  have hint_r : ‖fourCoeff h b ν‖ ≤ C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) := by
    unfold fourCoeff
    have : IsFiniteMeasure
        (volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1))) :=
      ⟨by rw [Measure.restrict_apply_univ, fourBasic_cube_vol]; exact ENNReal.one_lt_top⟩
    have hle := norm_integral_le_of_norm_le_const
      (μ := volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1)))
      (f := fun x : Fin f → ℝ => h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) *
        Complex.exp (-2 * Real.pi * Complex.I *
          ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)))
      (C := C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k))
      (ae_of_all _ fun x => by
        rw [norm_mul, fourBasic_norm_exp]
        exact mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le)
    simpa [Measure.real, Measure.restrict_apply_univ, fourBasic_cube_vol] using hle
  have h1 : Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) *
      Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) = 1 := by
    rw [← Real.exp_add]
    rw [show 2 * Real.pi * ∑ k, (ν k : ℝ) * b k + -2 * Real.pi * ∑ k, (ν k : ℝ) * b k = 0 by ring]
    exact Real.exp_zero
  calc ‖fourCoeff h b ν‖ * Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k)
      ≤ C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) *
          Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) :=
        mul_le_mul_of_nonneg_right hint_r (Real.exp_pos _).le
    _ = C := by rw [mul_assoc, h1, mul_one]

theorem four_sign (f : ℕ) (hI : FOURIndepStatement f) (hB : FOURBoundStatement f) :
    FOURSignStatement f := by
  intro Ω h b0 κ C E hΩ hpre hd hper hray hgrowth ν hne
  by_contra hneg0
  have hneg := not_le.mp hneg0
  obtain ⟨S0, hS0⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * b0 k := ⟨_, rfl⟩
  obtain ⟨Sκ, hSκ⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * κ k := ⟨_, rfl⟩
  rw [← hSκ] at hneg
  have hb0 : b0 ∈ Ω := by simpa using hray 0 le_rfl
  have hsum : ∀ t : ℝ, ∑ k, (ν k : ℝ) * (b0 + t • κ) k = S0 + t * Sκ := by
    intro t
    rw [hS0, hSκ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -2 * Real.pi * Sκ := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβ]; nlinarith [mul_pos Real.pi_pos (neg_pos.mpr hneg)]
  have hK : 0 < ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0) :=
    mul_pos (norm_pos_iff.mpr hne) (Real.exp_pos _)
  have hle : ∀ t : ℝ, 0 ≤ t → ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0) ≤
      C * ((1 + t) ^ E * Real.exp (-β * t)) := by
    intro t ht
    have hcoef := hI Ω h hΩ hpre hd hper b0 hb0 (b0 + t • κ) (hray t ht) ν
    have hbd := hB h (b0 + t • κ) ν (C * (1 + t) ^ E) (hgrowth t ht)
    rw [← hcoef, hsum t] at hbd
    have hexp : Real.exp (-2 * Real.pi * (S0 + t * Sκ)) =
        Real.exp (-2 * Real.pi * S0) * Real.exp (β * t) := by
      rw [← Real.exp_add, hβ]; congr 1; ring
    rw [hexp] at hbd
    have h1 : Real.exp (β * t) * Real.exp (-β * t) = 1 := by
      rw [← Real.exp_add, show β * t + -β * t = 0 by ring, Real.exp_zero]
    calc ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0)
        = ‖fourCoeff h b0 ν‖ * (Real.exp (-2 * Real.pi * S0) * Real.exp (β * t)) *
            Real.exp (-β * t) := by
          linear_combination (-(‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0))) * h1
      _ ≤ C * (1 + t) ^ E * Real.exp (-β * t) :=
          mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le
      _ = C * ((1 + t) ^ E * Real.exp (-β * t)) := by ring
  have hlim : Tendsto (fun t : ℝ => C * ((1 + t) ^ E * Real.exp (-β * t))) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero E β hβpos
    have h2 : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
      tendsto_atTop_mono (fun t => le_add_of_nonneg_left zero_le_one) tendsto_id
    have h3 := (h1.comp h2).const_mul (Real.exp β)
    rw [mul_zero] at h3
    have h4 : Tendsto (fun t : ℝ => (1 + t) ^ E * Real.exp (-β * t)) atTop (𝓝 0) := by
      refine h3.congr fun t => ?_
      have he : Real.exp β * Real.exp (-β * (1 + t)) = Real.exp (-β * t) := by
        rw [← Real.exp_add]; congr 1; ring
      show Real.exp β * ((1 + t) ^ E * Real.exp (-β * (1 + t))) = _
      rw [← he]; ring
    have h5 := h4.const_mul C
    rwa [mul_zero] at h5
  have hfin := ge_of_tendsto hlim ((eventually_ge_atTop (0 : ℝ)).mono fun t ht => hle t ht)
  linarith

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GrowSumIndicatorLe
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem grow.{u1, u2} (hC : GROWCountStatement.{u1, u2}) : GROWStatement.{u1, u2} := by
  intro X _ μ Γ _ _ _ _ _ _ D B F ps x' C Sup m hD hB hF hps hinv hm hmv hSup
  set φ : X → ℝ≥0∞ := fun x => ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-ps x)) with hφdef
  have hφ : Measurable φ :=
    ENNReal.measurable_ofReal.comp
      (((hF.norm).pow_const 2).mul (Real.measurable_exp.comp hps.neg))
  have hcount := hC X μ Γ D B φ m hD hB hφ (fun γ x => by simp only [hφdef, hinv]) hm
  have hB2 : ∫⁻ x in B, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (Real.exp Sup) * ∫⁻ x in B, φ x ∂μ := by
    rw [← lintegral_const_mul _ hφ]
    refine setLIntegral_mono ((hφ.const_mul _)) fun x hx => ?_
    rw [hφdef]
    dsimp only
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have h1 : 1 ≤ Real.exp Sup * Real.exp (-ps x) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith [hSup x hx])
    have h2 : 0 ≤ ‖F x‖ ^ 2 := by positivity
    nlinarith
  calc ENNReal.ofReal (‖F x'‖ ^ 2) ≤ C * ∫⁻ x in B, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ := hmv
    _ ≤ C * (ENNReal.ofReal (Real.exp Sup) * (m * ∫⁻ x in D, φ x ∂μ)) := by
        gcongr
        exact hB2.trans (by gcongr)
    _ = C * m * ENNReal.ofReal (Real.exp Sup) * ∫⁻ x in D, φ x ∂μ := by ring

end

end ReciprocityTheory.L2DbarEstimates.Y
end


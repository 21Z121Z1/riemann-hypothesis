import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoOfSqueeze
section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.GaugeProd

def Asym {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → ℝ) (d : ℕ) : Prop :=
  Tendsto (fun r : ℝ => ν {x | Real.sqrt (f x) ≤ r} / ENNReal.ofReal (r ^ d)) (𝓝[>] 0)
    (𝓝 (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))

variable {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

theorem prod_le_right (ν : Measure X) (μ : Measure Y) (lam : Measure Z) [SFinite μ] [SFinite lam]
    {f : X → ℝ} {g : Y → ℝ} {h : Z → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (h0 : ∀ x, 0 ≤ f x) (b : ℝ≥0) {δ : ℝ} (H : ∀ s ≤ δ, μ {y | g y ≤ s} ≤ b * lam {z | h z ≤ s})
    {t : ℝ} (ht : t ≤ δ) :
    ν.prod μ {z | f z.1 + g z.2 ≤ t} ≤ b * ν.prod lam {z | f z.1 + h z.2 ≤ t} := by
  have m1 : MeasurableSet {z : X × Y | f z.1 + g z.2 ≤ t} :=
    measurableSet_le ((hf.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  have m2 : MeasurableSet {z : X × Z | f z.1 + h z.2 ≤ t} :=
    measurableSet_le ((hf.comp measurable_fst).add (hh.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply m1, Measure.prod_apply m2, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun x => ?_
  have e1 : Prod.mk x ⁻¹' {z : X × Y | f z.1 + g z.2 ≤ t} = {y | g y ≤ t - f x} := by
    ext y; simp only [mem_preimage, mem_setOf_eq]; constructor <;> intro <;> linarith
  have e2 : Prod.mk x ⁻¹' {z : X × Z | f z.1 + h z.2 ≤ t} = {y | h y ≤ t - f x} := by
    ext y; simp only [mem_preimage, mem_setOf_eq]; constructor <;> intro <;> linarith
  simp only [e1, e2]
  exact H _ (by linarith [h0 x])

theorem prod_swap_set (ν : Measure X) (μ : Measure Y) [SFinite ν] [SFinite μ]
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) (t : ℝ) :
    ν.prod μ {z | f z.1 + g z.2 ≤ t} = μ.prod ν {z | g z.1 + f z.2 ≤ t} := by
  have m1 : MeasurableSet {z : X × Y | f z.1 + g z.2 ≤ t} :=
    measurableSet_le ((hf.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  rw [← Measure.prod_swap, Measure.map_apply measurable_swap m1]
  congr 1
  ext z
  simp [add_comm]

theorem prod_le_both (ν : Measure X) (μ : Measure Y) (ν' : Measure W) (μ' : Measure Z)
    [SFinite ν] [SFinite μ] [SFinite ν'] [SFinite μ']
    {f : X → ℝ} {g : Y → ℝ} {f' : W → ℝ} {g' : Z → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf' : Measurable f') (hg' : Measurable g')
    (h0 : ∀ x, 0 ≤ f x) (h0' : ∀ x, 0 ≤ g' x) (a b : ℝ≥0) {δ : ℝ}
    (H1 : ∀ s ≤ δ, ν {y | f y ≤ s} ≤ a * ν' {z | f' z ≤ s})
    (H2 : ∀ s ≤ δ, μ {y | g y ≤ s} ≤ b * μ' {z | g' z ≤ s})
    {t : ℝ} (ht : t ≤ δ) :
    ν.prod μ {z | f z.1 + g z.2 ≤ t} ≤ b * a * ν'.prod μ' {z | f' z.1 + g' z.2 ≤ t} := by
  refine (prod_le_right ν μ μ' hf hg hg' h0 b H2 ht).trans ?_
  rw [mul_assoc, prod_swap_set ν μ' hf hg', prod_swap_set ν' μ' hf' hg']
  gcongr
  exact prod_le_right μ' ν ν' hg' hf hf' h0' a H1 ht

theorem le_of_pos (ν : Measure X) (lam : Measure Z) {f : X → ℝ} {g : Z → ℝ} (hg : Measurable g)
    (h0 : ∀ x, 0 ≤ f x) (a : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (hfin : lam {z | g z ≤ δ} ≠ ⊤)
    (H : ∀ s, 0 < s → s ≤ δ → ν {y | f y ≤ s} ≤ a * lam {z | g z ≤ s}) :
    ∀ s ≤ δ, ν {y | f y ≤ s} ≤ a * lam {z | g z ≤ s} := by
  intro s hs
  rcases lt_trichotomy s 0 with h | h | h
  · have : {y | f y ≤ s} = ∅ := by
      ext y; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]; linarith [h0 y]
    simp [this]
  · subst h
    have T := tendsto_measure_biInter_gt (μ := lam) (s := fun r : ℝ => {z | g z ≤ r}) (a := 0)
      (fun r _ => (measurableSet_le hg measurable_const).nullMeasurableSet)
      (fun i j _ hij z hz => le_trans hz hij) ⟨δ, hδ, hfin⟩
    have e : (⋂ r > (0 : ℝ), {z | g z ≤ r}) = {z | g z ≤ 0} := by
      ext z
      simp only [mem_iInter, mem_setOf_eq]
      exact ⟨fun h => le_of_forall_gt_imp_ge_of_dense fun r hr => h r hr, fun h r hr => h.trans hr.le⟩
    rw [e] at T
    refine ge_of_tendsto (ENNReal.Tendsto.const_mul T (Or.inr ENNReal.coe_ne_top)) ?_
    filter_upwards [Ioc_mem_nhdsGT hδ] with r hr
    exact (measure_mono fun y (hy : f y ≤ 0) => le_trans hy hr.1.le).trans (H r hr.1 hr.2)
  · exact H s h hs

theorem sqrt_set {A : Type*} (f : A → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    {x | Real.sqrt (f x) ≤ r} = {x | f x ≤ r ^ 2} := by
  ext x; simp only [mem_setOf_eq]; exact Real.sqrt_le_left hr

theorem vol_sq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {r : ℝ} (hr : 0 ≤ r) :
    volume {x : E | ‖x‖ ^ 2 ≤ r ^ 2} =
      ENNReal.ofReal (r ^ Module.finrank ℝ E) * volume (Metric.ball (0 : E) 1) := by
  rw [← Measure.addHaar_closedBall volume (0 : E) hr]
  congr 1
  ext x
  simp only [mem_setOf_eq, mem_closedBall_zero_iff]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero

theorem Asym.compare {ν : Measure X} {f : X → ℝ} {d : ℕ} (h : Asym ν f d) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (a : ℝ≥0) (ha : 1 < a) : ∃ δ : ℝ, 0 < δ ∧
      (∀ s ≤ δ, ν {y | f y ≤ s} ≤ a * volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s}) ∧
      (∀ s ≤ δ, volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ≤ a * ν {y | f y ≤ s}) := by
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ω0 : ω ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have ωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have ha' : (1 : ℝ≥0∞) < a := by exact_mod_cast ha
  have lt1 : ω < a * ω := by
    conv_lhs => rw [← one_mul ω]
    exact ENNReal.mul_lt_mul_left ω0 ωt ha'
  have E1 := h.eventually (gt_mem_nhds lt1)
  have E2 := (ENNReal.Tendsto.const_mul (a := (a : ℝ≥0∞)) h (Or.inr ENNReal.coe_ne_top)).eventually
    (lt_mem_nhds lt1)
  obtain ⟨ρ, hρ, hE⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 (E1.and E2)
  have hρ' : (0 : ℝ) < ρ := hρ
  have key : ∀ s, 0 < s → s ≤ ρ ^ 2 →
      ν {y | f y ≤ s} ≤ a * volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ∧
      volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ≤ a * ν {y | f y ≤ s} := by
    intro s hs hsρ
    obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ s = r ^ 2 :=
      ⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
    have hrρ : r ≤ ρ := (pow_le_pow_iff_left₀ hr.le hρ'.le two_ne_zero).1 hsρ
    obtain ⟨e1, e2⟩ := hE ⟨hr, hrρ⟩
    rw [sqrt_set f hr.le] at e1 e2
    have p0 : ENNReal.ofReal (r ^ d) ≠ 0 := by simpa using pow_pos hr d
    rw [vol_sq _ hr.le, finrank_euclideanSpace_fin, ← hω]
    constructor
    · have := (ENNReal.div_le_iff p0 ENNReal.ofReal_ne_top).1 e1.le
      refine this.trans (le_of_eq ?_)
      ring
    · rw [← mul_div_assoc] at e2
      have := (ENNReal.le_div_iff_mul_le (Or.inl p0) (Or.inl ENNReal.ofReal_ne_top)).1 e2.le
      rwa [mul_comm] at this
  have fin1 : volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ ρ ^ 2} ≠ ⊤ := by
    rw [vol_sq _ hρ'.le]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ωt
  refine ⟨ρ ^ 2, by positivity, ?_, ?_⟩
  · exact le_of_pos _ _ (by fun_prop) h0 a (by positivity) fin1 fun s h1 h2 => (key s h1 h2).1
  · refine le_of_pos _ _ hf (fun _ => by positivity) a (by positivity) ?_ fun s h1 h2 => (key s h1 h2).2
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top fin1) (key _ (by positivity) le_rfl).1

theorem vol_prod (d e : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).prod (volume : Measure (EuclideanSpace ℝ (Fin e)))
      {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ r ^ 2} =
      ENNReal.ofReal (r ^ (d + e)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + e))) 1) := by
  let P := WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e))
  have hP : Module.finrank ℝ P = d + e := by
    rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]; simp
  let T : P ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + e)) := ((stdOrthonormalBasis ℝ P).reindex (finCongr hP)).repr
  have m : MeasurableSet {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) |
      ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ r ^ 2} := measurableSet_le (by fun_prop) measurable_const
  have h1 := (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin d))
    (EuclideanSpace ℝ (Fin e))).measure_preimage m.nullMeasurableSet
  have m2 : MeasurableSet {z : EuclideanSpace ℝ (Fin (d + e)) | ‖z‖ ^ 2 ≤ r ^ 2} :=
    measurableSet_le (by fun_prop) measurable_const
  have h2 := T.measurePreserving.measure_preimage m2.nullMeasurableSet
  have h3 := vol_sq (EuclideanSpace ℝ (Fin (d + e))) hr
  rw [finrank_euclideanSpace_fin] at h3
  rw [← h3, ← h2]
  refine h1.symm.trans ?_
  congr 1
  ext z
  simp only [mem_preimage, mem_setOf_eq, LinearIsometryEquiv.norm_map]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem tendsto_of_squeeze {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0∞} {ω : ℝ≥0∞} (hω : ω ≠ ⊤)
    (H : ∀ a : ℝ≥0, 1 < a → ∀ᶠ i in l, F i ≤ a * a * ω ∧ ω ≤ a * a * F i) : Tendsto F l (𝓝 ω) := by
  have C : ∀ u : ℝ≥0∞, u ≠ ⊤ → Tendsto (fun a : ℝ≥0 => (a : ℝ≥0∞) * a * u) (𝓝[>] 1) (𝓝 u) := by
    intro u hu
    have h1 : Tendsto (fun a : ℝ≥0 => ((a * a : ℝ≥0) : ℝ≥0∞)) (𝓝 1) (𝓝 ((1 * 1 : ℝ≥0) : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.comp (continuous_id.mul continuous_id)).tendsto 1
    have h2 := ENNReal.Tendsto.mul_const (b := u) h1 (Or.inr hu)
    simpa using h2.mono_left nhdsWithin_le_nhds
  refine tendsto_order.2 ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨a, h1, h2⟩ := (((C u hu.ne_top).eventually (gt_mem_nhds hu)).and self_mem_nhdsWithin).exists
    filter_upwards [H a h2] with i hi
    by_contra hc
    exact absurd (hi.2.trans (mul_le_mul_right (not_lt.1 hc) _)) (not_le.2 h1)
  · obtain ⟨a, h1, h2⟩ := (((C ω hω).eventually (gt_mem_nhds hu)).and self_mem_nhdsWithin).exists
    filter_upwards [H a h2] with i hi
    exact hi.1.trans_lt h1

theorem Asym.prod {ν : Measure X} {μ : Measure Y} [SFinite ν] [SFinite μ] {f : X → ℝ} {g : Y → ℝ} {d e : ℕ}
    (h₁ : Asym ν f d) (h₂ : Asym μ g e) (hf : Measurable f) (hg : Measurable g)
    (f0 : ∀ x, 0 ≤ f x) (g0 : ∀ y, 0 ≤ g y) : Asym (ν.prod μ) (fun z => f z.1 + g z.2) (d + e) := by
  refine tendsto_of_squeeze measure_ball_lt_top.ne fun a ha => ?_
  obtain ⟨δ₁, p1, A1, B1⟩ := h₁.compare hf f0 a ha
  obtain ⟨δ₂, p2, A2, B2⟩ := h₂.compare hg g0 a ha
  have hδ : 0 < min δ₁ δ₂ := lt_min p1 p2
  filter_upwards [Ioc_mem_nhdsGT (Real.sqrt_pos.2 hδ)] with r hr
  have hr2 : r ^ 2 ≤ min δ₁ δ₂ := (Real.le_sqrt hr.1.le hδ.le).1 hr.2
  have p0 : ENNReal.ofReal (r ^ (d + e)) ≠ 0 := by simpa using pow_pos hr.1 (d + e)
  have U := prod_le_both ν μ volume volume hf hg (by fun_prop) (by fun_prop) f0 (fun _ => by positivity) a a
    (fun s hs => A1 s (hs.trans (min_le_left _ _))) (fun s hs => A2 s (hs.trans (min_le_right _ _))) hr2
  have L := prod_le_both volume volume ν μ (by fun_prop) (by fun_prop) hf hg (fun _ => by positivity) g0 a a
    (fun s hs => B1 s (hs.trans (min_le_left _ _))) (fun s hs => B2 s (hs.trans (min_le_right _ _))) hr2
  rw [vol_prod d e hr.1.le] at U L
  rw [sqrt_set _ hr.1.le]
  constructor
  · refine (ENNReal.div_le_iff p0 ENNReal.ofReal_ne_top).2 (U.trans (le_of_eq ?_))
    ring
  · rw [← mul_div_assoc]
    refine (ENNReal.le_div_iff_mul_le (Or.inl p0) (Or.inl ENNReal.ofReal_ne_top)).2 ?_
    rwa [mul_comm]

end GlobalTheory.GaugeProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumTransversalEqTsumOrbitQuotientGeneral
section
open scoped ENNReal Classical

namespace GlobalTheory

theorem tsum_transversal_eq_tsum_orbitQuotient_general {G X A M : Type} [Group G] [MulAction G X]
    [AddCommMonoid M] [TopologicalSpace M] (ι : A → X) (T : X → Prop)
    (hT : ∀ g : G, ∀ x, T x → T (g • x)) (hι : ∀ a, T (ι a))
    (hsurj : ∀ x, T x → ∃ a, ∃ g : G, g • ι a = x)
    (hinj : ∀ a b, (∃ g : G, g • ι a = ι b) → a = b)
    (φ : X → M) (hφ : ∀ g : G, ∀ x, T x → φ (g • x) = φ x) :
    ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  let c : A → MulAction.orbitRel.Quotient G X := fun a => Quotient.mk (MulAction.orbitRel G X) (ι a)
  have hc : Function.Injective c := by
    intro a b hab
    have h : (MulAction.orbitRel G X) (ι a) (ι b) := Quotient.exact hab
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, hg⟩ := h
    exact (hinj b a ⟨g, hg⟩).symm
  have hout : ∀ a, ∃ g : G, g • ι a = (c a).out := by
    intro a
    have h : (MulAction.orbitRel G X) ((c a).out) (ι a) := Quotient.exact (Quotient.out_eq (c a))
    rw [MulAction.orbitRel_apply] at h
    exact h
  have hsupp : Function.support
      (fun o : MulAction.orbitRel.Quotient G X => if T o.out then φ o.out else 0) ⊆ Set.range c := by
    intro o ho
    have hTo : T o.out := by
      by_contra hn
      exact ho (if_neg hn)
    obtain ⟨a, g, hg⟩ := hsurj _ hTo
    refine ⟨a, ?_⟩
    rw [← Quotient.out_eq o]
    apply Quotient.sound
    have h : (MulAction.orbitRel G X) o.out (ι a) := by
      rw [MulAction.orbitRel_apply]
      exact ⟨g, hg⟩
    exact (MulAction.orbitRel G X).symm h
  rw [← hc.tsum_eq hsupp]
  refine tsum_congr fun a => ?_
  obtain ⟨g, hg⟩ := hout a
  rw [← hg, if_pos (hT g _ (hι a)), hφ g _ (hι a)]

theorem tsum_transversal_eq_tsum_orbitQuotient : ∀ {G X A : Type} [Group G] [MulAction G X] (ι : A → X) (T : X → Prop), (∀ g : G, ∀ x, T x → T (g • x)) → (∀ a, T (ι a)) → (∀ x, T x → ∃ a, ∃ g : G, g • ι a = x) → (∀ a b, (∃ g : G, g • ι a = ι b) → a = b) → (∀ φ : X → ℂ, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0) ∧ ∀ φ : X → ℝ≥0∞, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  intro G X A _ _ ι T hT hι hsurj hinj
  exact ⟨fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ,
    fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentIsometryDefiniteEqOne
section
open Matrix Finset Real

namespace GlobalTheory

open scoped ComplexOrder in

theorem unipotent_isometry_definite_eq_one :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ), c ≠ 0 → Aᴴ * (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * A = c • 1 → (A - 1) ^ m = 0 → A = 1 := by
  intro n m A c hc hA hm

  have hU : Aᴴ * A = 1 := by
    have h1 : c • (Aᴴ * A) = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    exact smul_right_injective _ hc h1
  have hU' : A * Aᴴ = 1 := mul_eq_one_comm.mp hU

  have hcomm : Commute (A - 1)ᴴ (A - 1) := by
    show (A - 1)ᴴ * (A - 1) = (A - 1) * (A - 1)ᴴ
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, hU, hU',
      one_mul, mul_one]
    abel
  have hN : (A - 1) ^ (m + 1) = 0 := by rw [pow_succ, hm, zero_mul]

  have hBh : ((A - 1)ᴴ * (A - 1))ᴴ = (A - 1)ᴴ * (A - 1) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hB : ((A - 1)ᴴ * (A - 1)) ^ (m + 1) = 0 := by
    rw [hcomm.mul_pow, hN, mul_zero]
  have key : ∀ k : ℕ, ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 → (A - 1)ᴴ * (A - 1) = 0 := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro hk
      apply ih
      have h2 : (((A - 1)ᴴ * (A - 1)) ^ (k + 1))ᴴ * ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 := by
        rw [Matrix.conjTranspose_pow, hBh, ← pow_add,
          show k + 1 + (k + 1) = (k + 1 + 1) + k by omega, pow_add, hk, zero_mul]
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h2
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp (key m hB))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
section
open Matrix

namespace GlobalTheory

theorem map_transpose_mul_rev {R : Type} [CommRing R] (s : R →+* R) {l m n : Type} [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) :
    ((A * B).map s)ᵀ = (B.map s)ᵀ * (A.map s)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem unitary_stabiliser_orthogonal_summand :
    ∀ (R : Type) [CommRing R] (s : R →+* R) (N ι κ : Type) [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (J : Matrix N N R) (G : Matrix ι ι R) (G' : Matrix κ κ R) (Q : Matrix N (ι ⊕ κ) R) (Qi : Matrix (ι ⊕ κ) N R), Q * Qi = 1 → Qi * Q = 1 → (Q.map s)ᵀ * J * Q = Matrix.fromBlocks G 0 0 G' → IsUnit G'.det → (∀ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G → ((Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi).map s)ᵀ * J * (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi) = J) ∧ ∀ h : Matrix N N R, (h.map s)ᵀ * J * h = J → (∀ b : κ, h *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b)) → ∃ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G ∧ h = Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi := by
  intro R _ s N ι κ _ _ _ _ _ _ J G G' Q Qi h1 h2 hD hG'
  have h1s : (Qi.map s)ᵀ * (Q.map s)ᵀ = 1 := by
    rw [← map_transpose_mul_rev, h1, Matrix.map_one _ (map_zero s) (map_one s), transpose_one]
  have hblk : ∀ (y : Matrix ι ι R) (c : Matrix κ ι R),
      ((Matrix.fromBlocks y 0 c (1 : Matrix κ κ R)).map s)ᵀ * Matrix.fromBlocks G 0 0 G' *
        Matrix.fromBlocks y 0 c (1 : Matrix κ κ R) =
      Matrix.fromBlocks ((y.map s)ᵀ * G * y + (c.map s)ᵀ * G' * c) ((c.map s)ᵀ * G') (G' * c) G' := by
    intro y c
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero s) (map_one s),
      Matrix.map_zero _ (map_zero s)]
    simp
  refine ⟨fun y hy => ?_, fun h hh hfix => ?_⟩
  · have hb := hblk y 0
    rw [hy] at hb
    simp only [Matrix.mul_zero, add_zero, Matrix.map_zero _ (map_zero s), transpose_zero,
      Matrix.zero_mul] at hb
    rw [map_transpose_mul_rev, map_transpose_mul_rev]
    calc _ = (Qi.map s)ᵀ * (((Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)).map s)ᵀ *
            ((Q.map s)ᵀ * J * Q) * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = (Qi.map s)ᵀ * ((Q.map s)ᵀ * J * Q) * Qi := by rw [hD, hb]
      _ = ((Qi.map s)ᵀ * (Q.map s)ᵀ) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1s, h1, Matrix.one_mul, Matrix.mul_one]
  · set M : Matrix (ι ⊕ κ) (ι ⊕ κ) R := Qi * h * Q with hM
    have hQM : Q * M = h * Q := by
      rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    have hhM : h = Q * M * Qi := by
      rw [hQM, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcol : ∀ x b, M x (Sum.inr b) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R) x (Sum.inr b) := by
      intro x b
      rw [← h2, hM, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact congrFun (hfix b) i
    have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 1 := by
      ext x z
      rcases z with z | z
      · rcases x with x | x <;> rfl
      · rw [hcol]
        rcases x with x | x <;> simp [Matrix.one_apply]
    have hU : (M.map s)ᵀ * Matrix.fromBlocks G 0 0 G' * M = Matrix.fromBlocks G 0 0 G' := by
      rw [← hD]
      calc _ = ((Q * M).map s)ᵀ * J * (Q * M) := by
            rw [map_transpose_mul_rev s Q M]; simp only [Matrix.mul_assoc]
        _ = (Q.map s)ᵀ * ((h.map s)ᵀ * J * h) * Q := by
            rw [hQM, map_transpose_mul_rev]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hh]
    rw [hMb, hblk, Matrix.fromBlocks_inj] at hU
    obtain ⟨ha, -, hc, -⟩ := hU
    have hc0 : M.toBlocks₂₁ = 0 := by
      have := congrArg (G'⁻¹ * ·) hc
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG'] using this
    rw [hc0] at ha hMb
    refine ⟨M.toBlocks₁₁, by simpa using ha, ?_⟩
    rw [← hMb]
    exact hhM

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperUnitriangularMul
section
namespace GlobalTheory.UpperUnitriangularMul

open Matrix

theorem upperUnitriangular_mul {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    {U W : Matrix (Fin N) (Fin N) E}
    (hU : ∀ a b : Fin N, b < a → U a b = (0 : E)) (hU1 : ∀ a : Fin N, U a a = (1 : E))
    (hW : ∀ a b : Fin N, b < a → W a b = (0 : E)) (hW1 : ∀ a : Fin N, W a a = (1 : E)) :
    (∀ a b : Fin N, b < a → (U * W) a b = (0 : E)) ∧ ∀ a : Fin N, (U * W) a a = (1 : E) := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge c a with h | h
    · rw [hU a c h, zero_mul]
    · rw [hW c b (lt_of_lt_of_le hba h), mul_zero]
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU1, hW1, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hU a c h, zero_mul]
      · rw [hW c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.UpperUnitriangularMul
end


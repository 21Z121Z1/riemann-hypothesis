import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddHaarMapSmulOfNormEqOne
section
open MeasureTheory Topology

namespace GlobalTheory

theorem addHaar_map_smul_of_norm_eq_one (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : K) (hc : ‖c‖ = 1) : Measure.map (fun x : V => c • x) μ = μ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  let e : V ≃L[K] V := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc0)
  have he : (fun x : V => c • x) = e := by
    ext x
    simp [e]
  haveI : (Measure.map (fun x : V => c • x) μ).IsAddHaarMeasure := by
    rw [he]
    exact e.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (Measure.map (fun x : V => c • x) μ) μ
  set k := Measure.addHaarScalarFactor (Measure.map (fun x : V => c • x) μ) μ
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  let S : Set V := (fun p : K × V => p.1 • p.2) '' (Metric.sphere (0 : K) 1 ×ˢ C)
  have hS : IsCompact S :=
    ((isCompact_sphere (0 : K) 1).prod hC).image continuous_smul
  have hCS : C ⊆ S := fun x hx => ⟨(1, x), ⟨by simp, hx⟩, by simp⟩
  have hpos : μ S ≠ 0 :=
    ((Measure.measure_pos_of_mem_nhds μ hC0).trans_le (measure_mono hCS)).ne'
  have hfin : μ S ≠ ⊤ := hS.measure_lt_top.ne
  have hpre : (fun x : V => c • x) ⁻¹' S = S := by
    ext x
    constructor
    · rintro ⟨⟨a, y⟩, ⟨ha, hy⟩, h⟩
      refine ⟨(c⁻¹ * a, y), ⟨?_, hy⟩, ?_⟩
      · simp at ha
        simp [ha, hc]
      · simp only at h ⊢
        rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · rintro ⟨⟨a, y⟩, ⟨ha, hy⟩, h⟩
      refine ⟨(c * a, y), ⟨?_, hy⟩, ?_⟩
      · simp at ha
        simp [ha, hc]
      · simp only at h ⊢
        rw [mul_smul, h]
  have hm : Measure.map (fun x : V => c • x) μ S = μ S := by
    rw [Measure.map_apply (continuous_const_smul c).measurable hS.measurableSet, hpre]
  have hk1 : k = 1 := by
    rw [hk, Measure.smul_apply] at hm
    have h1 : (k : ENNReal) * μ S = 1 * μ S := by
      rw [one_mul]
      simpa [ENNReal.smul_def] using hm
    have := (ENNReal.mul_left_inj hpos hfin).1 h1
    exact_mod_cast this
  rw [hk, hk1, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BdIntEqZeroOfPrimitive
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ResRect

noncomputable def bdInt (a b c d : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I))
    + I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I))

def SidesIn (a b c d : ℝ) (B : Set ℂ) : Prop :=
  (∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) ∧ (∀ x ∈ Set.uIcc a b, (x : ℂ) + d * I ∈ B) ∧
  (∀ y ∈ Set.uIcc c d, (b : ℂ) + y * I ∈ B) ∧ (∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B)

theorem int_hor {f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B) {a b c : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) volume a b :=
  (hf.comp (by fun_prop) h).intervalIntegrable

theorem int_ver {f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B) {a c d : ℝ}
    (h : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B) :
    IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume c d :=
  (hf.comp (by fun_prop) h).intervalIntegrable

theorem bdInt_add {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {f g : ℂ → ℂ}
    (hf : ContinuousOn f B) (hg : ContinuousOn g B) :
    bdInt a b c d (fun s => f s + g s) = bdInt a b c d f + bdInt a b c d g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bdInt]
  rw [intervalIntegral.integral_add (int_hor hf h1) (int_hor hg h1),
    intervalIntegral.integral_add (int_hor hf h2) (int_hor hg h2),
    intervalIntegral.integral_add (int_ver hf h3) (int_ver hg h3),
    intervalIntegral.integral_add (int_ver hf h4) (int_ver hg h4)]
  ring

theorem bdInt_sum {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {ι : Type*} (S : Finset ι)
    {f : ι → ℂ → ℂ} (hf : ∀ i ∈ S, ContinuousOn (f i) B) :
    bdInt a b c d (fun s => ∑ i ∈ S, f i s) = ∑ i ∈ S, bdInt a b c d (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [bdInt]
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [bdInt_add h (hf i (Finset.mem_insert_self _ _))
      (continuousOn_finset_sum _ fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

theorem bdInt_congr {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {f g : ℂ → ℂ}
    (hfg : ∀ s ∈ B, f s = g s) : bdInt a b c d f = bdInt a b c d g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bdInt]
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => g (x + c * I)) fun x hx => hfg _ (h1 x hx),
    intervalIntegral.integral_congr (f := fun x : ℝ => f (x + d * I))
      (g := fun x : ℝ => g (x + d * I)) fun x hx => hfg _ (h2 x hx),
    intervalIntegral.integral_congr (f := fun y : ℝ => f (b + y * I))
      (g := fun y : ℝ => g (b + y * I)) fun x hx => hfg _ (h3 x hx),
    intervalIntegral.integral_congr (f := fun y : ℝ => f (a + y * I))
      (g := fun y : ℝ => g (a + y * I)) fun x hx => hfg _ (h4 x hx)]

theorem ftc_hor {F f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B)
    (hF : ∀ s ∈ B, HasDerivAt F (f s) s) {a b c : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) :
    ∫ x : ℝ in a..b, f (x + c * I) = F (b + c * I) - F (a + c * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + c * I))
    (fun x hx => ?_) (int_hor hf h)
  have h1 : HasDerivAt (fun t : ℂ => F (t + c * I)) (f (x + c * I)) (x : ℂ) :=
    HasDerivAt.comp_add_const (x : ℂ) (c * I) (hF _ (h x hx))
  exact h1.comp_ofReal

theorem ftc_ver {F f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B)
    (hF : ∀ s ∈ B, HasDerivAt F (f s) s) {a c d : ℝ}
    (h : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B) :
    I * ∫ y : ℝ in c..d, f (a + y * I) = F (a + d * I) - F (a + c * I) := by
  rw [mul_comm, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => F (a + y * I))
    (fun y hy => ?_) ((int_ver hf h).mul_const I)
  have h0 : HasDerivAt (fun t : ℂ => (a : ℂ) + t * I) I (y : ℂ) := by
    simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (a : ℂ)
  have h1 : HasDerivAt (fun t : ℂ => F (a + t * I)) (f (a + y * I) * I) (y : ℂ) :=
    HasDerivAt.comp (y : ℂ) (hF _ (h y hy)) h0
  exact h1.comp_ofReal

theorem bdInt_eq_zero_of_primitive {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B)
    {F f : ℂ → ℂ} (hf : ContinuousOn f B) (hF : ∀ s ∈ B, HasDerivAt F (f s) s) :
    bdInt a b c d f = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bdInt]
  rw [ftc_hor hf hF h1, ftc_hor hf hF h2, ftc_ver hf hF h3, ftc_ver hf hF h4]
  ring

theorem sidesIn_compl {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) : SidesIn a b c d {p}ᶜ := by
  refine ⟨fun x _ hx => ?_, fun x _ hx => ?_, fun x _ hx => ?_, fun x _ hx => ?_⟩
  · have := congrArg Complex.im (Set.mem_singleton_iff.1 hx); simp at this; linarith
  · have := congrArg Complex.im (Set.mem_singleton_iff.1 hx); simp at this; linarith
  · have := congrArg Complex.re (Set.mem_singleton_iff.1 hx); simp at this; linarith
  · have := congrArg Complex.re (Set.mem_singleton_iff.1 hx); simp at this; linarith

theorem bdInt_sq {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) (k : ℂ) : bdInt a b c d (fun s => k / (s - p) ^ 2) = 0 := by
  refine bdInt_eq_zero_of_primitive (sidesIn_compl h1 h2 h3 h4) (F := fun s => -k * (s - p)⁻¹)
    ?_ fun s hs => ?_
  · exact ContinuousOn.div (by fun_prop) (by fun_prop)
      fun s hs => pow_ne_zero _ (sub_ne_zero.2 hs)
  · have hs' : s - p ≠ 0 := sub_ne_zero.2 hs
    have := (((hasDerivAt_id s).sub_const p).inv hs').const_mul (-k)
    refine this.congr_deriv ?_
    simp only [id]
    ring

theorem bdInt_inv {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) (k : ℂ) : bdInt a b c d (fun s => k / (s - p)) = 2 * Real.pi * I * k := by
  have hc : ∀ B : Set ℂ, (∀ s ∈ B, s - p ≠ 0) → ContinuousOn (fun s => k / (s - p)) B :=
    fun B hB => ContinuousOn.div (by fun_prop) (by fun_prop) hB
  have hc1 := hc {s | s - p ∈ slitPlane} fun s hs => slitPlane_ne_zero hs
  have hc2 := hc {s | -(s - p) ∈ slitPlane} fun s hs => neg_ne_zero.1 (slitPlane_ne_zero hs)
  have hd1 : ∀ s ∈ {s | s - p ∈ slitPlane},
      HasDerivAt (fun s => k * log (s - p)) (k / (s - p)) s := fun s hs => by
    have := (((hasDerivAt_id s).sub_const p).clog hs).const_mul k
    refine this.congr_deriv ?_
    simp only [id]
    ring
  have hd2 : ∀ s ∈ {s | -(s - p) ∈ slitPlane},
      HasDerivAt (fun s => k * log (-(s - p))) (k / (s - p)) s := fun s hs => by
    have := (((hasDerivAt_id s).sub_const p).neg.clog hs).const_mul k
    refine this.congr_deriv ?_
    simp only [id, Pi.neg_apply, neg_div_neg_eq]
    ring
  simp only [bdInt]
  rw [ftc_hor hc1 hd1 (c := c) fun x _ => Or.inr (by simp; linarith),
    ftc_hor hc1 hd1 (c := d) fun x _ => Or.inr (by simp; linarith),
    ftc_ver hc1 hd1 (a := b) fun x _ => Or.inl (by simp; linarith),
    ftc_ver hc2 hd2 (a := a) fun x _ => Or.inl (by simp; linarith)]
  have e1 : log (-((a : ℂ) + d * I - p)) = log ((a : ℂ) + d * I - p) - Real.pi * I := by
    rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos (by simp; linarith)]
    push_cast; ring
  have e2 : log (-((a : ℂ) + c * I - p)) = log ((a : ℂ) + c * I - p) + Real.pi * I := by
    rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg (by simp; linarith)]
    push_cast; ring
  rw [e1, e2]
  ring

theorem residue_rectangle :
    ∀ (f : ℂ → ℂ) (z w : ℂ) (S : Finset ℂ) (r : ℂ → ℂ), z.re < w.re → z.im < w.im → (∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im) → DifferentiableOn ℂ f ((Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im) \ S) → (∀ p ∈ S, ∃ (a : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g p ∧ ∀ᶠ s in nhdsWithin p {p}ᶜ, f s = a / (s - p) ^ 2 + r p / (s - p) + g s) → (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) + I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) = 2 * Real.pi * I * ∑ p ∈ S, r p := by
  classical
  intro f z w S r hre him hS hf hp
  choose! a g hg hfg using hp
  set R : Set ℂ := Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im with hR
  let P : ℂ → ℂ → ℂ := fun p s => a p / (s - p) ^ 2 + r p / (s - p)
  have hP : ∀ p s, s ≠ p → DifferentiableAt ℂ (P p) s := fun p s hs => by
    have hs' : s - p ≠ 0 := sub_ne_zero.2 hs
    have hs2 : (s - p) ^ 2 ≠ 0 := pow_ne_zero _ hs'
    simp only [P]
    fun_prop (disch := assumption)
  let h : ℂ → ℂ := fun s =>
    if s ∈ S then g s s - ∑ q ∈ S.erase s, P q s else f s - ∑ q ∈ S, P q s
  have hopen : ∀ T : Finset ℂ, ∀ s ∉ T, ∀ᶠ t in nhds s, t ∉ T := fun T s hs =>
    T.finite_toSet.isClosed.isOpen_compl.mem_nhds hs
  have hh : DifferentiableOn ℂ h R := by
    intro s hs
    by_cases hsS : s ∈ S
    · have hd : DifferentiableAt ℂ (fun t => g s t - ∑ q ∈ S.erase s, P q t) s :=
        (hg s hsS).differentiableAt.sub
          (DifferentiableAt.fun_sum fun q hq => hP q s (Finset.ne_of_mem_erase hq).symm)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      have e1 := eventually_nhdsWithin_iff.1 (hfg s hsS)
      filter_upwards [e1, hopen (S.erase s) s (Finset.notMem_erase s S)] with t ht1 ht2
      by_cases hts : t = s
      · subst hts
        simp only [h, if_pos hsS]
      · have htS : t ∉ S := fun ht => ht2 (Finset.mem_erase.2 ⟨hts, ht⟩)
        simp only [h, if_neg htS]
        rw [ht1 hts, ← Finset.add_sum_erase S _ hsS]
        simp only [P]
        ring
    · have hd : DifferentiableWithinAt ℂ (fun t => f t - ∑ q ∈ S, P q t) R s := by
        refine DifferentiableWithinAt.sub ?_
          (DifferentiableAt.fun_sum fun q hq => hP q s fun e => hsS (e ▸ hq)).differentiableWithinAt
        refine (hf s ⟨hs, hsS⟩).mono_of_mem_nhdsWithin ?_
        exact inter_mem_nhdsWithin R (hopen S s hsS)
      refine hd.congr_of_eventuallyEq ?_ (by simp only [h, if_neg hsS])
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen S s hsS)] with t ht
      have ht' : t ∉ S := ht
      simp only [h, if_neg ht']
  have hB : SidesIn z.re w.re z.im w.im (R \ S) := by
    rw [SidesIn, Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le]
    refine ⟨fun x hx => ⟨?_, fun hm => ?_⟩, fun x hx => ⟨?_, fun hm => ?_⟩,
      fun x hx => ⟨?_, fun hm => ?_⟩, fun x hx => ⟨?_, fun hm => ?_⟩⟩
    · simp [hR, mem_reProdIm, hx.1, hx.2, him.le]
    · simpa using (hS _ hm).2.2.1
    · simp [hR, mem_reProdIm, hx.1, hx.2, him.le]
    · simpa using (hS _ hm).2.2.2
    · simp [hR, mem_reProdIm, hx.1, hx.2, hre.le]
    · simpa using (hS _ hm).2.1
    · simp [hR, mem_reProdIm, hx.1, hx.2, hre.le]
    · simpa using (hS _ hm).1
  have hPc : ∀ p ∈ S, ContinuousOn (P p) (R \ S) := fun p hp s hs =>
    (hP p s fun e => hs.2 (e ▸ hp)).continuousAt.continuousWithinAt
  have h0 : bdInt z.re w.re z.im w.im h = 0 := by
    have := integral_boundary_rect_eq_zero_of_differentiableOn h z w
      (by rwa [Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le])
    simpa only [smul_eq_mul, bdInt] using this
  change bdInt z.re w.re z.im w.im f = _
  rw [bdInt_congr hB (g := fun s => h s + ∑ q ∈ S, P q s) (fun s hs => by
      have ht' : s ∉ S := hs.2
      simp only [h, if_neg ht']; ring),
    bdInt_add hB (hh.continuousOn.mono Set.diff_subset) (continuousOn_finset_sum _ hPc), h0,
    zero_add, bdInt_sum hB S hPc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hS p hp
  simp only [P]
  rw [bdInt_add (sidesIn_compl h1 h2 h3 h4) (f := fun s => a p / (s - p) ^ 2)
    (g := fun s => r p / (s - p))
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => pow_ne_zero _ (sub_ne_zero.2 hs))
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => sub_ne_zero.2 hs),
    bdInt_sq h1 h2 h3 h4, bdInt_inv h1 h2 h3 h4, zero_add]

end GlobalTheory.ResRect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoeffXMulPart
section
namespace GlobalTheory.PowerSeriesCoeffSum

open MvPowerSeries Finsupp

variable {O : Type} [CommRing O] {a : ℕ}

noncomputable def part (f : MvPowerSeries (Fin a) O) (i : Fin a) : MvPowerSeries (Fin a) O :=
  fun e => if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0

lemma coeff_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (e : Fin a →₀ ℕ) :
    coeff e (part f i) = if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0 := rfl

lemma coeff_X_mul_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if (1 ≤ m i ∧ ∀ j < i, m j = 0) then coeff m f else 0 := by
  rw [X, coeff_monomial_mul, one_mul]
  by_cases h1 : 1 ≤ m i
  · have hle : single i 1 ≤ m := by
      intro k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · simp [single_apply, Ne.symm hk]
    rw [if_pos hle, coeff_part, tsub_add_cancel_of_le hle]
    have : (∀ j < i, (m - single i 1 : Fin a →₀ ℕ) j = 0) ↔ (∀ j < i, m j = 0) := by
      refine forall_congr' fun j => imp_congr_right fun hj => ?_
      have : j ≠ i := ne_of_lt hj
      simp [single_apply, Ne.symm this]
    simp only [this, h1, true_and]
  · have hle : ¬ single i 1 ≤ m := by
      intro h; exact h1 (by simpa using h i)
    simp [hle, h1]

lemma eq_sum (f : MvPowerSeries (Fin a) O) (h0 : coeff 0 f = 0) :
    f = ∑ i, X i * part f i := by
  ext m
  rw [map_sum]
  simp only [coeff_X_mul_part]
  by_cases hm : m = 0
  · subst hm; simp [h0]
  · have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
    set i0 := m.support.min' hne with hi0
    have hi0mem : i0 ∈ m.support := Finset.min'_mem _ _
    have key : ∀ i, (1 ≤ m i ∧ ∀ j < i, m j = 0) ↔ i = i0 := by
      intro i
      constructor
      · rintro ⟨h1, h2⟩
        apply le_antisymm
        · by_contra hlt
          push_neg at hlt
          exact (Finsupp.mem_support_iff.mp hi0mem) (h2 _ hlt)
        · exact Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr (by omega))
      · rintro rfl
        refine ⟨Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi0mem), fun j hj => ?_⟩
        by_contra hj0
        exact absurd (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hj0)) (not_le.mpr hj)
    simp only [key]
    simp

theorem main : ∀ (O : Type) [inst : CommRing O] (a n : ℕ) (f : MvPowerSeries (Fin a) O),
    (∀ (m : Fin a →₀ ℕ), (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m < n →
      (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f = (0 : O)) →
    f ∈ Ideal.span (Set.range MvPowerSeries.X) ^ n := by
  intro O _ a n
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have h0 : coeff 0 f = 0 := hf 0 (by simp)
    rw [eq_sum f h0, pow_succ']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ih _ ?_)
    intro e he
    rw [coeff_part]
    split_ifs
    · apply hf
      rw [map_add, degree_single]; omega
    · rfl

end GlobalTheory.PowerSeriesCoeffSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexRootOfUnityMemRangeOfIsPrimitiveRoot
section
namespace GlobalTheory

theorem complex_rootOfUnity_mem_range_of_isPrimitiveRoot :
    ∀ (K : Type) [Field K] (s : K →+* ℂ) (n : ℕ) (ζ : K), 0 < n → IsPrimitiveRoot ζ n →
      ∀ z : ℂ, z ^ n = 1 → ∃ r : K, s r = z := by
  intro K _ s n ζ hn hζ z hz
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : IsPrimitiveRoot (s ζ) n := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow
section
open Real Filter Asymptotics

namespace GlobalTheory

open Real Filter Asymptotics in

theorem _root_.GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow :
    ∀ a b C : ℝ, ∀ p : ℕ, a < b →
      ∃ x0 : ℝ, ∀ x ≥ x0, C * x ^ a * Real.log x ^ p ≤ x ^ b := by
  intro a b C p hab
  have hlo : (fun x : ℝ => Real.log x ^ (p : ℝ)) =o[atTop] fun x => x ^ (b - a) :=
    isLittleO_log_rpow_rpow_atTop _ (sub_pos.mpr hab)
  have hc : (0 : ℝ) < 1 / (|C| + 1) := by positivity
  have hev := (hlo.bound hc).and (eventually_gt_atTop (0 : ℝ))
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp hev
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨hb, hxpos⟩ := hx0 x hx
  rw [Real.rpow_natCast] at hb
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hxpos a
  have hxba : 0 < x ^ (b - a) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxba] at hb
  have hsplit : x ^ b = x ^ a * x ^ (b - a) := by
    rw [← Real.rpow_add hxpos]; ring_nf
  have h1 : C * Real.log x ^ p ≤ |C| * |Real.log x ^ p| := by
    rw [← abs_mul]; exact le_abs_self _
  have h2 : |C| * |Real.log x ^ p| ≤ x ^ (b - a) := by
    calc |C| * |Real.log x ^ p| ≤ (|C| + 1) * |Real.log x ^ p| := by
          gcongr; linarith
      _ ≤ (|C| + 1) * (1 / (|C| + 1) * x ^ (b - a)) := by gcongr
      _ = x ^ (b - a) := by field_simp
  calc C * x ^ a * Real.log x ^ p = x ^ a * (C * Real.log x ^ p) := by ring
    _ ≤ x ^ a * x ^ (b - a) := by gcongr; linarith
    _ = x ^ b := hsplit.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfPowClose
section
namespace GlobalTheory.EqOneOfPowerClose

open Finset

theorem eq_one_of_pow_close {u : ℂ} (h : ∀ n : ℕ, ‖u ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    u = (1 : ℂ) := by
  have key : ∀ n : ℕ, (n : ℝ) * ‖u - 1‖ ≤ 1 := by
    intro n
    have h1 : ‖∑ k ∈ range n, (u ^ k - 1)‖ ≤ (n : ℝ) / 2 := by
      calc ‖∑ k ∈ range n, (u ^ k - 1)‖ ≤ ∑ k ∈ range n, ‖u ^ k - 1‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ range n, (1 / 2 : ℝ) := sum_le_sum fun k _ => (h k).le
        _ = (n : ℝ) / 2 := by simp; ring
    have h2 : (n : ℂ) = ∑ k ∈ range n, u ^ k - ∑ k ∈ range n, (u ^ k - 1) := by
      rw [sum_sub_distrib]; simp
    have h3 : (n : ℝ) ≤ ‖∑ k ∈ range n, u ^ k‖ + ‖∑ k ∈ range n, (u ^ k - 1)‖ := by
      have := norm_sub_le (∑ k ∈ range n, u ^ k) (∑ k ∈ range n, (u ^ k - 1))
      rw [← h2, Complex.norm_natCast] at this
      exact this
    have h4 : ‖∑ k ∈ range n, u ^ k‖ * ‖u - 1‖ < 1 / 2 := by
      rw [← norm_mul, geom_sum_mul]; exact h n
    have h5 : (n : ℝ) / 2 ≤ ‖∑ k ∈ range n, u ^ k‖ := by linarith
    have h6 := mul_le_mul_of_nonneg_right h5 (norm_nonneg (u - 1))
    linarith
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖u - 1‖)
  rw [div_lt_iff₀ hpos] at hn
  linarith [key n]

end GlobalTheory.EqOneOfPowerClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqXMulShiftAdd
section
namespace GlobalTheory.PowerSeriesShift

noncomputable def shift {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => MvPowerSeries.coeff (Finsupp.single i 1 + m) f

noncomputable def free {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => if m i = 0 then MvPowerSeries.coeff m f else (0 : O)

theorem eq_X_mul_shift_add {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) :
    f = MvPowerSeries.X i * shift i f + free i f := by
  classical
  ext m
  rw [map_add, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases h : m i = 0
  · have h1 : ¬ Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_neg h1, zero_add]
    change _ = if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_pos h]
  · have h1 : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_pos h1, one_mul]
    change _ = MvPowerSeries.coeff (Finsupp.single i 1 + (m - Finsupp.single i 1)) f +
      if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_neg h, add_zero, add_tsub_cancel_of_le h1]

theorem main : (let d1 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ (MvPowerSeries.coeff ((fun₀ | i => (1 : ℕ)) + m) : MvPowerSeries σ O → O) f); let d2 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ if (m : σ → ℕ) i = (0 : ℕ) then (MvPowerSeries.coeff m : MvPowerSeries σ O → O) f else (0 : O)); ∀ {σ O : Type} [inst : CommRing O] (i : σ) (f : MvPowerSeries σ O), f = MvPowerSeries.X i * d1 i f + d2 i f) := by
  intro d1 d2 σ O _ i f
  exact eq_X_mul_shift_add i f

end GlobalTheory.PowerSeriesShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsComapPrime
section
namespace GlobalTheory.ComapPrimeExistence

open NumberField IsDedekindDomain

theorem exists_comap_prime {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (φ : E →+* K) (w : HeightOneSpectrum (RingOfIntegers K)) :
    ∃ Q : HeightOneSpectrum (RingOfIntegers E), ∀ r : RingOfIntegers E,
      r ∈ Q.asIdeal ↔ (RingOfIntegers.mapRingHom φ : RingOfIntegers E → RingOfIntegers K) r ∈ w.asIdeal := by
  have hp := w.isPrime
  refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom φ), Ideal.comap_isPrime _ _, ?_⟩,
    fun r => Ideal.mem_comap⟩
  intro h
  have hn : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hmem : ((Ideal.absNorm w.asIdeal : ℕ) : RingOfIntegers E) ∈
      w.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  rw [h, Ideal.mem_bot] at hmem
  exact hn (Nat.cast_eq_zero.mp hmem)

end GlobalTheory.ComapPrimeExistence
end


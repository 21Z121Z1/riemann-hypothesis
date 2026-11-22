import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0023

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev cj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun q => starRingEnd ℂ (z q)

theorem cj_cj (z : (Σ k, ι k) → ℂ) : cj (cj z) = z := by
  funext q; simp [cj]

theorem cj_nonzero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, cj z ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, by simpa [cj] using hi⟩

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp [mul_assoc]

theorem sameOrbit_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit (cj z) (cj z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => starRingEnd ℂ (c k), fun k => by simpa using hc k, ?_⟩
  funext p
  simp [cj]

theorem cj_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : cj z ∈ mcPts P := by
  refine ⟨cj_nonzero hz.1, fun f hf => ?_⟩
  have h := hz.2 f hf
  have key : eval (cj z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
    rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq,
      map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [map_mul, map_prod, map_pow]
  rw [key, h, map_zero]

theorem log_sub_orbit (A B : HermLine ι) (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := h
  have hP : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  rw [A.smul c z' hc, B.smul c z' hc, ← hab,
    Real.log_mul hP.ne' (A.pos z' hz).ne', Real.log_mul hP.ne' (B.pos z' hz).ne']
  ring

def conjAvg (A : HermLine ι) : HermLine ι where
  a := A.a
  h z := Real.sqrt |A.h z * A.h (cj z)|
  pos z hz := Real.sqrt_pos.2 (abs_pos.2 (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne')
  smul c z hc := by
    have hP : 0 ≤ ∏ k, ‖c k‖ ^ A.a k :=
      Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    have e1 : cj (fun p : Σ k, ι k => c p.1 * z p) =
        fun p => (starRingEnd ℂ (c p.1)) * cj z p := by
      funext p; simp [cj]
    have hc' : ∀ k, starRingEnd ℂ (c k) ≠ 0 := fun k => by simpa using hc k
    rw [e1, A.smul c z hc, A.smul _ (cj z) hc']
    simp only [RCLike.norm_conj]
    rw [show (∏ k, ‖c k‖ ^ A.a k) * A.h z * ((∏ k, ‖c k‖ ^ A.a k) * A.h (cj z)) =
      (∏ k, ‖c k‖ ^ A.a k) ^ 2 * (A.h z * A.h (cj z)) by ring, abs_mul, abs_of_nonneg (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hP]

theorem conjAvg_conj (A : HermLine ι) : IsConjInvariantH (conjAvg A) := fun z => by
  change Real.sqrt |A.h (cj z) * A.h (cj (cj z))| = Real.sqrt |A.h z * A.h (cj z)|
  rw [cj_cj, mul_comm]

theorem conjAvg_log (A : HermLine ι) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((conjAvg A).h z) = (Real.log (A.h z) + Real.log (A.h (cj z))) / 2 := by
  have h1 := A.pos z hz
  have h2 := A.pos _ (cj_nonzero hz)
  change Real.log (Real.sqrt |A.h z * A.h (cj z)|) = _
  rw [abs_of_pos (mul_pos h1 h2), Real.log_sqrt (mul_pos h1 h2).le, Real.log_mul h1.ne' h2.ne']

theorem conjAvg_smooth {A : HermLine ι} (hA : IsSmoothHerm A) : IsSmoothHerm (conjAvg A) := by
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hS
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) := by
    refine contDiff_pi.2 fun q => ?_
    exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ q)
  have hmap : Set.MapsTo (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) S S := fun z hz => cj_nonzero hz
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h (cj z)) S :=
    hA.comp hconj.contDiffOn hmap
  have hprod := hA.mul h2
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.sqrt (A.h z * A.h (cj z))) S :=
    hprod.sqrt fun z hz => (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne'
  refine hs.congr fun z hz => ?_
  change Real.sqrt |A.h z * A.h (cj z)| = _
  rw [abs_of_pos (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz)))]

theorem holoOn_comp {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {g : X → Y} (hg : HoloMap A B g) {V : Set Y}
    {G : Y → ℂ} (hG : B.HoloOn V G) : A.HoloOn (g ⁻¹' V) (G ∘ g) := by
  intro j w hw
  obtain ⟨k, hk⟩ := B.cover (g ((A.chart j).symm w))
  have hw' : w ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (g ⁻¹' (B.chart k).source) := ⟨hw.1, hk⟩
  have h1 := hg.2 j k w hw'
  have h2 : AnalyticAt ℂ (G ∘ (B.chart k).symm) ((B.chart k ∘ g ∘ (A.chart j).symm) w) := by
    refine hG k _ ⟨(B.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (B.chart k).left_inv hk]
    exact hw.2
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (g ∘ (A.chart j).symm) w :=
    hg.1.continuousAt.comp ((A.chart j).continuousAt_symm hw.1)
  filter_upwards [hc ((B.chart k).open_source.mem_nhds hk)] with w' hw''
  have hw3 : g ((A.chart j).symm w') ∈ (B.chart k).source := hw''
  simp only [Function.comp, (B.chart k).left_inv hw3]

def IsLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lift : X → X → (Σ k, ι k) → ℂ) : Prop :=
  (∀ x, IsOpen (U x)) ∧ (∀ x, x ∈ U x) ∧ (∀ x p, A.HoloOn (U x) fun y => lift x y p) ∧
  (∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P) ∧
  (∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)) ∧
  (∀ z ∈ mcPts P, ∃ x, SameOrbit (lift x x) z) ∧
  (∀ x x', SameOrbit (lift x x) (lift x' x') → x = x') ∧
  ∀ x, ∀ p : (k : K) → ι k, (∀ k, lift x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lift x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionForm
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalModel

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem continuousAt_of_chart {E : Type} [TopologicalSpace E] (A : FinHolAtlas e X) (j : Fin A.n) {p : X}
    (hp : p ∈ (A.chart j).source) (f : X → E)
    (h : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j p)) : ContinuousAt f p := by
  have h1 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp (f := A.chart j) h ((A.chart j).continuousAt hp)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hp] with z hz
  simp [(A.chart j).left_inv hz]

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {p : X} (hp : p ∈ U) : ContinuousAt g p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj g ?_
  refine (hg j _ ⟨(A.chart j).map_source hj, ?_⟩).continuousAt
  simpa [(A.chart j).left_inv hj] using hp

theorem continuousAt_of_smoothOn (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) {p : X} (hp : p ∈ U) : ContinuousAt f p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj f ?_
  have hmem : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hp⟩
  exact (hf j).continuousOn.continuousAt
    (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hmem)

theorem zero_set_and_bound : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ (x : X) (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ → Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target → φ.source ⊆ L.U x → (∀ i ∈ S, 1 ≤ μ i) → A.HoloOn φ.source v → (∀ y ∈ φ.source, v y ≠ 0) → (∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i) → (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧ ∃ M : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s → |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
  intro e X _ A L s hL hs x φ S μ v hφ hball hsrc hμ hv hv0 hsv

  have glue : ∀ y ∈ φ.target, ‖s x (φ.symm y)‖ * Real.exp (-L.φ x (φ.symm y)) =
      ‖s (φ.symm y) (φ.symm y)‖ * Real.exp (-L.φ (φ.symm y) (φ.symm y)) := fun y hy =>
    hs.2 x (φ.symm y) (φ.symm y) ⟨hsrc (φ.map_target hy), L.mem_U _⟩
  have hform : ∀ y ∈ φ.target, s x (φ.symm y) = v (φ.symm y) * ∏ i ∈ S, y i ^ μ i := by
    intro y hy
    rw [hsv _ (φ.map_target hy)]
    simp only [φ.right_inv hy]
  have hzero : ∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0) := by
    intro y hy
    have h1 : s (φ.symm y) (φ.symm y) = 0 ↔ s x (φ.symm y) = 0 := by
      have hg := glue y hy
      constructor
      · intro h0
        rw [h0] at hg
        simpa [Real.exp_ne_zero] using hg
      · intro h0
        rw [h0, norm_zero, zero_mul] at hg
        rcases mul_eq_zero.1 hg.symm with h | h
        · exact norm_eq_zero.1 h
        · exact absurd h (Real.exp_ne_zero _)
    change s (φ.symm y) (φ.symm y) = 0 ↔ _
    rw [h1, hform y hy, mul_eq_zero, Finset.prod_eq_zero_iff]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact absurd h (hv0 _ (φ.map_target hy))
      · exact ⟨i, hi, (pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 (hμ i hi))).1 h⟩
    · rintro ⟨i, hi, h⟩
      refine Or.inr ⟨i, hi, ?_⟩
      rw [h]
      exact zero_pow (Nat.one_le_iff_ne_zero.1 (hμ i hi))
  refine ⟨hzero, ?_⟩

  have hcont : ContinuousOn (fun y => -2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) φ.target := by
    intro y hy
    have hp := φ.map_target hy
    have cs : ContinuousAt φ.symm y := φ.continuousAt_symm hy
    have c1 : ContinuousAt (fun y => v (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm) (continuousAt_of_holoOn A hv hp) cs
    have c2 : ContinuousAt (fun y => L.φ x (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm)
        (continuousAt_of_smoothOn A (L.isOpen_U x) (hL.1 x) (hsrc hp)) cs
    have c3 : ContinuousAt (fun y => Real.log ‖v (φ.symm y)‖) y :=
      c1.norm.log (norm_ne_zero_iff.2 (hv0 _ hp))
    exact ((continuousAt_const.mul c3).add (continuousAt_const.mul c2)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin e → ℂ) 2).exists_bound_of_continuousOn
    (hcont.mono hball)
  refine ⟨C + |(∑ i ∈ S, (μ i : ℝ)) * Real.log 4|, fun y hy hnb => ?_⟩
  have hyt := hball hy
  have hnz : ∀ i ∈ S, y i ≠ 0 := fun i hi h0 => hnb ((hzero y hyt).2 ⟨i, hi, h0⟩)
  have hs0 : s (φ.symm y) (φ.symm y) ≠ 0 := hnb
  have hvn : ‖v (φ.symm y)‖ ≠ 0 := norm_ne_zero_iff.2 (hv0 _ (φ.map_target hyt))
  have hlogS : Real.log (∏ i ∈ S, ‖y i‖ ^ μ i) = ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    rw [Real.log_prod (fun i hi => pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))]
    exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _
  have hlog : logNormSec L s (φ.symm y) = Real.log ‖v (φ.symm y)‖ +
      ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ - L.φ x (φ.symm y) := by
    unfold logNormSec
    rw [← glue y hyt, hform y hyt, norm_mul, norm_prod]
    simp only [norm_pow]
    rw [Real.log_mul (mul_ne_zero hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))) (Real.exp_ne_zero _),
      Real.log_mul hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi))), hlogS, Real.log_exp]
    ring
  have hloc : rLoc S μ y = Real.exp 1 + (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 -
      2 * ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    unfold rLoc
    rw [Finset.sum_mul, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn : ‖y i‖ ≠ 0 := norm_ne_zero_iff.2 (hnz i hi)
    rw [Real.log_div (by norm_num) (pow_ne_zero _ hn), Real.log_pow]
    push_cast
    ring
  have hdiff : rW L s (φ.symm y) - rLoc S μ y =
      (-2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) -
        (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 := by
    unfold rW
    rw [hlog, hloc]
    ring
  rw [hdiff]
  have hb := hC y hy
  rw [Real.norm_eq_abs] at hb
  exact (abs_sub _ _).trans (add_le_add hb le_rfl)

end GlobalTheory.CompanionTheory.Ar.PB.LocalModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphere_measure_stereographic_integral : let n : ℂ → Fin 3 → ℝ := (fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)); (∀ f : (Fin 3 → ℝ) → ℝ, Measurable f → (Integrable (fun a : ℂ => f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔ Integrable (fun m : ReciprocityTheory.ChartRestriction.G.AI.S2 => f fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i) ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧ ∫ a : ℂ, f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) = ∫ m : ReciprocityTheory.ChartRestriction.G.AI.S2, f (fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i) ∂ ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧ ∀ a₀ a₁ : ℂ, logSin 1 a₀ a₁ = (1 / 2) * Real.log ((1 - ∑ i, n a₀ i * n a₁ i) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sphere_measure_stereographic_integral | exact GlobalTheory.CompanionTheory.Relay.sphere_measure_stereographic_integral | (intros; apply GlobalTheory.CompanionTheory.Relay.sphere_measure_stereographic_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareParametrizedDensityFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_parametrized_density_formula : ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ (n k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Q.U n → paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z = maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z) ∧ ∀ i < k, ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Q.U n → paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  first | exact @GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula | exact GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula | (intros; apply GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

def fundCo {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : ℝ :=
  f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0

theorem fundCo_sub {N : ℕ} (f g : Fin N → ℝ) (i : Fin N) : fundCo (f - g) i = fundCo f i - fundCo g i := by
  unfold fundCo
  split_ifs <;> simp <;> ring

theorem fundCo_smul {N : ℕ} (c : ℝ) (f : Fin N → ℝ) (i : Fin N) : fundCo (c • f) i = c * fundCo f i := by
  unfold fundCo
  split_ifs <;> simp <;> ring

private theorem abel_range (F B : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ Finset.range M, (F i - F (i + 1)) * ∑ k ∈ Finset.range (i + 1), B k + F M * ∑ k ∈ Finset.range M, B k =
      ∑ k ∈ Finset.range M, F k * B k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => F k * B k), ← ih, Finset.sum_range_succ B M]
    ring

theorem sum_fundCo_mul_sum_Iic {N : ℕ} (f B : Fin N → ℝ) :
    ∑ i, fundCo f i * ∑ k ∈ Finset.Iic i, B k = ∑ k, f k * B k := by
  classical
  let F : ℕ → ℝ := fun j => if h : j < N then f ⟨j, h⟩ else 0
  let B' : ℕ → ℝ := fun j => if h : j < N then B ⟨j, h⟩ else 0
  have hF : ∀ i : Fin N, F i = f i := fun i => by simp [F, i.2]
  have hB : ∀ i : Fin N, B' i = B i := fun i => by simp [B', i.2]
  have hFN : F N = 0 := by simp [F]
  have hco : ∀ i : Fin N, fundCo f i = F i - F (i + 1) := fun i => by
    simp only [fundCo, hF]
    congr 1
  have hI : ∀ i : Fin N, ∑ k ∈ Finset.Iic i, B k = ∑ k ∈ Finset.range ((i : ℕ) + 1), B' k := by
    intro i
    symm
    refine Finset.sum_bij' (fun j hj => (⟨j, by have := Finset.mem_range.1 hj; have := i.2; omega⟩ : Fin N))
      (fun k _ => (k : ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Iic, Fin.le_def]
      have := Finset.mem_range.1 hj
      omega
    · intro k hk
      have : (k : ℕ) ≤ i := Fin.le_def.1 (Finset.mem_Iic.1 hk)
      exact Finset.mem_range.2 (by omega)
    · intro j hj; rfl
    · intro k hk; rfl
    · intro j hj
      have h1 : j < N := by have := Finset.mem_range.1 hj; have := i.2; omega
      simp [B', h1]
  have h := abel_range F B' N
  rw [hFN, zero_mul, add_zero] at h
  simp only [hco, hI]
  rw [Fin.sum_univ_eq_sum_range (fun i => (F i - F (i + 1)) * ∑ k ∈ Finset.range (i + 1), B' k) N, h,
    ← Fin.sum_univ_eq_sum_range (fun k => F k * B' k) N]
  exact Finset.sum_congr rfl fun k _ => by rw [hF, hB]

theorem aeval_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [CommRing S]
    {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) (t : K → S) (x : (Σ k, ι k) → S) :
    aeval (fun p => t p.1 * x p) g = (∏ k, t k ^ a k) * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (t p.1 * x p) ^ m p = (∏ k, t k ^ a k) * ∏ p, x p ^ m p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem isMultiHomog_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι}
    {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k]

theorem aeval_eq_zero_of_mem {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have hc : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMap y).toRingHom = (aeval y).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap])
  have h0 : mConeMap y f = 0 := hf
  have := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0, map_zero] at this
  exact this.symm

theorem hasVal_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (h : HasVal y a s z v) : HasVal y a s (fun p => c p.1 * z p) (v * ∏ k, c k ^ a k) := by
  obtain ⟨dg, dh, g, k', hg, hk, hd, hy, h0, hv⟩ := h
  refine ⟨dg, dh, g, k', hg, hk, hd, hy, ?_, ?_⟩
  · rw [aeval_scale hk]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)) h0
  · rw [aeval_scale hg, aeval_scale hk, hv]
    have e : ∀ k, c k ^ dg k = c k ^ a k * c k ^ dh k := fun k => by
      rw [← zpow_natCast, hd k, zpow_add₀ (hc k), zpow_natCast, mul_comm]
    simp only [e, Finset.prod_mul_distrib]
    ring

theorem isSmoothHerm_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type} [Fintype σ]
    {A : σ → HermLine ι} (hA : ∀ a, IsSmoothHerm (A a)) (n : σ → ℤ) : IsSmoothHerm (combLine A n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (A a).h z ≠ 0 := ((A a).pos z hz).ne'
  have hf := hA a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

end GlobalTheory.CompanionTheory.Ar.Small.Fund
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformisedDegreePolynomialAntisymmetric
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem anSys_proportional : Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j D : ℕ) (S : AnSys D (Ψ × Fin N)), j ≤ N → D = antisymDegree Ψ N → IsUniformised S.A S.open' j S.potH → ∃ v : ℝ, 0 < v ∧ toWt S.degPoly = C v * antisymDelta Ψ N := by
  intro hI Ψ _ _ N j D S hj hD hU
  obtain ⟨hO, hNull, -, -, -⟩ := anSys_open_basics D (Ψ × Fin N) S
  have hInt := AnSys.mIntegrable_potH_and_mInt_eq_degNum hI.convergenceSigned D (Ψ × Fin N) S
  have hmain := GlobalTheory.T.uniformised_potential_integral_formula D S.X S.A Ψ N j S.open' S.th S.ph hj hD hO hNull
    (fun p => (S.sing p).1) (fun p => (S.sing p).2.1) hU (fun w => (hInt w).1)
  obtain ⟨v, hv, hEq⟩ := hmain
  refine ⟨v, hv, ?_⟩
  have hfun : (fun w : Fin D → Ψ × Fin N => mInt S.A (fun i => S.th (w i) + LocPot.ofFun (S.ph (w i))) (fun _ => 1)) = S.degNum :=
    funext fun w => (hInt w).2
  rw [hfun] at hEq
  exact hEq

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightTransformInjectiveLinearStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_transform_injective_linear : (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective | exact GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective <;> assumption)
end


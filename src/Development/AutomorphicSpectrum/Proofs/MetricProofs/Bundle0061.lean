import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemRealStructure
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem pot_holoOn_mono {V W : Set X} {g : X → ℂ} (h : A.HoloOn V g) (hW : W ⊆ V) :
    A.HoloOn W g :=
  fun j w hw => h j w ⟨hw.1, hW hw.2⟩

theorem pot_holoOn_continuousOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hw : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩
  have h1 := (h j _ hw).continuousAt
  have h2 : ContinuousAt (A.chart j) y := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (fun y' => (g ∘ (A.chart j).symm) (A.chart j y')) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(A.chart j).left_inv hy']

theorem pot_holoOn_sub_add {V : Set X} {g₁ g₂ g₃ : X → ℂ} (h₁ : A.HoloOn V g₁)
    (h₂ : A.HoloOn V g₂) (h₃ : A.HoloOn V g₃) :
    A.HoloOn V (fun y => g₁ y - g₂ y + g₃ y) :=
  fun j w hw => ((h₁ j w hw).sub (h₂ j w hw)).add (h₃ j w hw)

theorem pot_holoOn_div {V : Set X} {g₁ g₂ : X → ℂ} (h₁ : A.HoloOn V g₁) (h₂ : A.HoloOn V g₂)
    (hne : ∀ y ∈ V, g₂ y ≠ 0) : A.HoloOn V (fun y => g₁ y / g₂ y) :=
  fun j w hw => (h₁ j w hw).div (h₂ j w hw) (hne _ hw.2)

theorem pot_holoOn_sum_log {K : Type} [Fintype K] {V : Set X} {g : K → X → ℂ} (m : K → ℤ)
    (r : K → ℝ) (h : ∀ k, A.HoloOn V (g k)) (hs : ∀ k, ∀ y ∈ V, g k y ∈ Complex.slitPlane) :
    A.HoloOn V (fun y => ∑ k, (m k : ℂ) * (Complex.log (g k y) + (r k : ℂ))) := by
  intro j w hw
  have : ∀ k, AnalyticAt ℂ (fun z => (m k : ℂ) *
      (Complex.log (g k ((A.chart j).symm z)) + (r k : ℂ))) w := fun k =>
    analyticAt_const.mul ((AnalyticAt.clog (h k j w hw) (hs k _ hw.2)).add analyticAt_const)
  exact Finset.analyticAt_fun_sum _ fun k _ => this k

end Holo

theorem pot_re_sum_log {K : Type} [Fintype K] (m : K → ℤ) (u v : K → ℂ) (hu : ∀ k, u k ≠ 0)
    (hv : ∀ k, v k ≠ 0) :
    (∑ k, (m k : ℂ) * (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ))).re =
      ∑ k, (m k : ℝ) * Real.log ‖u k‖ := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ)).re = Real.log ‖u k‖ := by
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 (hu k)) (norm_ne_zero_iff.2 (hv k))]
    ring
  simp [Complex.mul_re, h1]

theorem pot_log_h_conj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (f : HermLine ι)
    (hf : IsConjInvariantH f) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {a : K → ℂ}
    (ha : ∀ k, a k ≠ 0) :
    Real.log (f.h (fun p => a p.1 * cj z p)) - Real.log (f.h z) =
      ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ := by
  have hP : ∀ k ∈ (Finset.univ : Finset K), ‖a k‖ ^ f.a k ≠ 0 := fun k _ =>
    (zpow_pos (norm_pos_iff.mpr (ha k)) _).ne'
  have hP' : (∏ k, ‖a k‖ ^ f.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 hP
  rw [f.smul a (cj z) ha, show f.h (cj z) = f.h z from hf z,
    Real.log_mul hP' (f.pos z hz).ne', Real.log_prod hP]
  simp [Real.log_zpow]

theorem pot_conj_pluriharmonic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ (f : HermLine ι), IsConjInvariantH f → ∀ (th : LocPot X), (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, Real.log (f.h (lift x y)) - th.φ x y = (G y).re) → ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re := by
  intro K _ ι _ e X _ A P U lift hL c horb hcc hanti f hf th hth x
  obtain ⟨hUo, hUm, hUh, hUpts, hUor, -, -, -⟩ := hL
  choose i hi using (hUpts x x (hUm x)).1
  obtain ⟨V₁, hV₁o, hxV₁, G₁, hG₁, hφ₁⟩ := hth x
  obtain ⟨V₂, hV₂o, hxV₂, G₂, hG₂, hφ₂⟩ := hth (c x)

  have horbit : ∀ y ∈ U x, c y ∈ U (c x) → ∃ a : K → ℂ, (∀ k, a k ≠ 0) ∧
      lift (c x) (c y) = fun p => a p.1 * cj (lift x y) p := fun y hy hcy =>
    sameOrbit_trans (sameOrbit_trans (hUor (c x) (c y) (c y) ⟨hcy, hUm (c y)⟩) (horb y))
      (sameOrbit_cj (hUor y x y ⟨hUm y, hy⟩))

  let b : K → X → ℂ := fun k y =>
    starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩
  let D : K → Set X := fun k => U x ∩ (fun y => lift x y ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hDo : ∀ k, IsOpen (D k) := fun k =>
    (pot_holoOn_continuousOn (hUo x) (hUh x _)).isOpen_inter_preimage (hUo x) isOpen_compl_singleton
  let W₁ : Set X := (U x ∩ c ⁻¹' U (c x)) ∩ ⋂ k, D k
  have hW₁o : IsOpen W₁ :=
    ((hUo x).inter ((hUo (c x)).preimage hcc)).inter (isOpen_iInter_of_finite hDo)
  have hxW₁ : x ∈ W₁ :=
    ⟨⟨hUm x, hUm (c x)⟩, Set.mem_iInter.2 fun k => ⟨hUm x, hi k⟩⟩
  have hden : ∀ y ∈ W₁, ∀ k, lift x y ⟨k, i k⟩ ≠ 0 := fun y hy k =>
    (Set.mem_iInter.1 hy.2 k).2

  have hba : ∀ y ∈ W₁, ∀ a : K → ℂ, lift (c x) (c y) = (fun p => a p.1 * cj (lift x y) p) →
      ∀ k, b k y = starRingEnd ℂ (a k) := fun y hy a ha k => by
    change starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩ = _
    rw [ha]
    simp only [cj, map_mul, Complex.conj_conj]
    exact mul_div_cancel_right₀ _ (hden y hy k)
  have hbne : ∀ y ∈ W₁, ∀ k, b k y ≠ 0 := fun y hy k => by
    obtain ⟨a, ha, hl⟩ := horbit y hy.1.1 hy.1.2
    rw [hba y hy a hl k]
    simpa using ha k
  have hbH : ∀ k, A.HoloOn W₁ (b k) := fun k =>
    pot_holoOn_div
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti (hUh (c x) ⟨k, i k⟩)) fun y hy => hy.1.2)
      (pot_holoOn_mono (hUh x ⟨k, i k⟩) fun y hy => hy.1.1) fun y hy => hden y hy k
  have hqH : ∀ k, A.HoloOn W₁ (fun y => b k y / b k x) := fun k =>
    pot_holoOn_div (hbH k) (fun j w _ => analyticAt_const) fun _ _ => hbne x hxW₁ k
  let B : K → Set X := fun k => W₁ ∩ (fun y => b k y / b k x) ⁻¹' Metric.ball 1 1
  have hBo : ∀ k, IsOpen (B k) := fun k =>
    (pot_holoOn_continuousOn hW₁o (hqH k)).isOpen_inter_preimage hW₁o Metric.isOpen_ball
  let W₂ : Set X := W₁ ∩ ⋂ k, B k
  let V : Set X := (W₂ ∩ V₁) ∩ c ⁻¹' V₂
  have hVo : IsOpen V :=
    ((hW₁o.inter (isOpen_iInter_of_finite hBo)).inter hV₁o).inter (hV₂o.preimage hcc)
  have hVW : V ⊆ W₁ := fun y hy => hy.1.1.1
  have hxV : x ∈ V := by
    refine ⟨⟨⟨hxW₁, Set.mem_iInter.2 fun k => ⟨hxW₁, ?_⟩⟩, hxV₁⟩, hxV₂⟩
    simp [div_self (hbne x hxW₁ k)]
  have hslit : ∀ k, ∀ y ∈ V, b k y / b k x ∈ Complex.slitPlane := fun k y hy => by
    have h1 : b k y / b k x ∈ Metric.ball (1 : ℂ) 1 := (Set.mem_iInter.1 hy.1.1.2 k).2
    have h2 : ‖b k y / b k x - 1‖ < 1 := by simpa [dist_eq_norm] using h1
    simpa using Complex.mem_slitPlane_of_norm_lt_one h2
  refine ⟨V, hVo, hxV,
    fun y => G₁ y - starRingEnd ℂ (G₂ (c y)) +
      ∑ k, (f.a k : ℂ) * (Complex.log (b k y / b k x) + ((Real.log ‖b k x‖ : ℝ) : ℂ)), ?_, ?_⟩
  · refine pot_holoOn_sub_add (pot_holoOn_mono hG₁ fun y hy => hy.1.2)
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti hG₂) fun y hy => hy.2) ?_
    exact pot_holoOn_sum_log f.a _ (fun k => pot_holoOn_mono (hqH k) hVW) fun k => hslit k
  · intro y hy
    have hyW := hVW hy
    obtain ⟨a, ha, hl⟩ := horbit y hyW.1.1 hyW.1.2
    have e₁ := hφ₁ y hy.1.2
    have e₂ := hφ₂ (c y) hy.2
    have e₃ := pot_log_h_conj f hf (hUpts x y hyW.1.1).1 ha
    rw [← hl] at e₃
    have e₄ := pot_re_sum_log f.a (fun k => b k y) (fun k => b k x) (hbne y hyW) (hbne x hxW₁)
    have e₅ : ∑ k, (f.a k : ℝ) * Real.log ‖b k y‖ = ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ :=
      Finset.sum_congr rfl fun k _ => by rw [hba y hyW a hl k, RCLike.norm_conj]
    simp only [Complex.add_re, Complex.sub_re, Complex.conj_re]
    rw [e₄, e₅, ← e₃]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicLiftRealisation
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_comp_of_holoOn {D e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) {V : Set (Fin e → ℂ)}
    {Y : Set X} {g : X → ℂ} (hg : A.HoloOn Y g) {h : (Fin e → ℂ) → X} {z : Fin e → ℂ}
    (hV : V ∈ 𝓝 z) (hc : ContinuousOn h V)
    (ha : ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ h) (V ∩ h ⁻¹' (A.chart k).source)) (hz : h z ∈ Y) :
    AnalyticAt ℂ (g ∘ h) z := by
  obtain ⟨k, hk⟩ := A.cover (h z)
  have hcz : ContinuousAt h z := hc.continuousAt hV
  have h1 : AnalyticAt ℂ (A.chart k ∘ h) z := ha k z ⟨mem_of_mem_nhds hV, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h) z) := by
    refine hg k _ ⟨(A.chart k).map_source hk, ?_⟩
    simpa [Set.mem_preimage, (A.chart k).left_inv hk] using hz
  have h3 : AnalyticAt ℂ ((g ∘ (A.chart k).symm) ∘ (A.chart k ∘ h)) z := h2.comp h1
  refine h3.congr ?_
  filter_upwards [hcz.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with u hu
  simp [(A.chart k).left_inv hu]

theorem ref_pot_along_exact_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (a : σ) (e : ℕ) (V : Set (Fin e → ℂ)) (ΦY : (Fin e → ℂ) → S.X) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (z : Fin e → ℂ), Re.J = ⊤ → Re.deg = 1 → Re.br = ∅ → IsOpen V → z ∈ V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, ∀ x₀, Re.π x₀ = ΦY u → SameOrbit (Re.R.lift x₀ x₀) (zex u)) → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, (S.th a).φ (ΦY z) (ΦY z') = Real.log ((Re.ref a).h (zex z')) + (Hh z').re := by
  intro K _ ι _ D σ S P Re a e V ΦY zex z hJ hdeg hbr hV hzV hana hmc hex
  have hbij : Function.Bijective Re.π := realis_bijective_of_degree_one K ι D σ S P Re hdeg hbr
  set h : (Fin e → ℂ) → Re.R.X := fun u => Function.surjInv hbij.2 (ΦY u) with hdef
  have hπ : ∀ u, Re.π (h u) = ΦY u := fun u => Function.surjInv_eq hbij.2 (ΦY u)
  have hSO : ∀ u ∈ V, SameOrbit (Re.R.lift (h u) (h u)) (zex u) := fun u hu => hex u hu (h u) (hπ u)
  obtain ⟨hc, hch⟩ := holo_of_lift_orbit_top K ι P Re.J D e Re.R V zex h hJ hV hana hmc hSO
  have hVn : V ∈ 𝓝 z := hV.mem_nhds hzV
  have hcz : ContinuousAt h z := hc.continuousAt hVn
  obtain ⟨W, hW, hxW, G, hG, hGeq⟩ := Re.ref_pot a (h z) (Set.mem_univ _)
  have hGh : AnalyticAt ℂ (G ∘ h) z := analyticAt_comp_of_holoOn Re.R.A hG hVn hc hch hxW
  have hxU : h z ∈ Re.R.U (h z) := Re.R.mem_U _

  have hi : ∀ k, ∃ i, zex z ⟨k, i⟩ ≠ 0 := (hmc z hzV).1
  choose i hi using hi
  set c : K → (Fin e → ℂ) → ℂ := fun k u => Re.R.lift (h z) (h u) ⟨k, i k⟩ / zex u ⟨k, i k⟩ with hcdef
  have hcan : ∀ k, AnalyticAt ℂ (c k) z := fun k =>
    AnalyticAt.div (analyticAt_comp_of_holoOn Re.R.A (Re.R.holo (h z) ⟨k, i k⟩) hVn hc hch hxU)
      (hana _ z hzV) (hi k)
  have hcz0 : ∀ k, c k z ≠ 0 := by
    intro k
    obtain ⟨d, hd, hdz⟩ := hSO z hzV
    have : Re.R.lift (h z) (h z) ⟨k, i k⟩ = d k * zex z ⟨k, i k⟩ := congrFun hdz ⟨k, i k⟩
    simp only [hcdef, this]
    exact div_ne_zero (mul_ne_zero (hd k) (hi k)) (hi k)
  have hL : ∀ k, ∃ Lk : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Lk z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖c k z'‖ = (Lk z').re :=
    fun k => log_norm_eventually_eq_re_analyticAt e (c k) z (hcan k) (hcz0 k)
  choose L hLan hLeq using hL
  refine ⟨fun u => (∑ k, (((Re.ref a).a k : ℤ) : ℂ) * L k u) - G (h u), ?_, ?_⟩
  · refine AnalyticAt.sub ?_ hGh
    exact Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul (hLan k)
  · have hne : ∀ᶠ u in 𝓝 z, ∀ k, zex u ⟨k, i k⟩ ≠ 0 :=
      eventually_all.2 fun k => (hana _ z hzV).continuousAt.eventually_ne (hi k)
    filter_upwards [hVn, hne, eventually_all.2 hLeq, hcz.preimage_mem_nhds (hW.mem_nhds hxW),
      hcz.preimage_mem_nhds ((Re.R.isOpen_U (h z)).mem_nhds hxU)] with u huV hune huL huW huU
    have hcompat := Re.R.compat (h z) (h u) (h u) ⟨huU, Re.R.mem_U _⟩
    obtain ⟨d₁, hd₁, e₁⟩ := hcompat
    obtain ⟨d₂, hd₂, e₂⟩ := hSO u huV
    have hlift : Re.R.lift (h z) (h u) = fun p => (d₁ p.1 * d₂ p.1) * zex u p := by
      funext p
      rw [congrFun e₁ p, congrFun e₂ p, mul_assoc]
    have hck : ∀ k, c k u = d₁ k * d₂ k := by
      intro k
      simp only [hcdef, hlift]
      field_simp [hune k]
    have hlift' : Re.R.lift (h z) (h u) = fun p => c p.1 u * zex u p := by
      rw [hlift]; funext p; rw [hck]
    have hcne : ∀ k, c k u ≠ 0 := fun k => by
      rw [hck]; exact mul_ne_zero (hd₁ k) (hd₂ k)
    have hsm := (Re.ref a).smul (fun k => c k u) (zex u) hcne
    have hpos := (Re.ref a).pos (zex u) (hmc u huV).1
    have hlog : Real.log ((Re.ref a).h (Re.R.lift (h z) (h u))) =
        (∑ k, ((Re.ref a).a k : ℝ) * Real.log ‖c k u‖) + Real.log ((Re.ref a).h (zex u)) := by
      rw [hlift', hsm, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ =>
        zpow_ne_zero _ (norm_ne_zero_iff.2 (hcne k))) hpos.ne', Real.log_prod]
      · simp only [Real.log_zpow]
      · exact fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hcne k))
    have hG' : Real.log ((Re.ref a).h (Re.R.lift (h z) (h u))) - (S.th a).φ (ΦY z) (ΦY u) = (G (h u)).re := by
      have := hGeq (h u) huW
      simpa only [potOf, LocPot.pullback, hπ] using this
    have hre : ((∑ k, (((Re.ref a).a k : ℤ) : ℂ) * L k u) - G (h u)).re =
        (∑ k, ((Re.ref a).a k : ℝ) * Real.log ‖c k u‖) - (G (h u)).re := by
      rw [Complex.sub_re, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [huL k]
      simp
    rw [hre]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereNormalized
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

theorem densW (d k i : ℕ) (hi : i < k) (hkd : 2 * k ≤ d + 2) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ)
    (hL : ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)))
    (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y)) (hα : ContDiffAt ℝ 2 α y)
    (hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j))
    (hH : H = hessC α y) (φ : Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ)
    (hφ : ∀ r z, φ r z =
      (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0 : Fin 2 → ℝ) 0 *
          f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0 : Fin 2 → ℝ) 1 *
          f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) +
        (if (r : ℕ) < 2 * k then (0 : ℝ) else 1) * α (Fin.tail (Fin.tail z)))
    (p₀ p₁ : ℂ) :
    maDens φ (Fin.cons p₀ (Fin.cons p₁ y)) = (2 / Real.pi) ^ (d + 2) * (wS p₀ * wS p₁ *
      (L (rename some (aeval ![lin3 (nS p₀), lin3 (nS p₁)]
        (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))) *
          X none ^ (d + 2 - 2 * k))).re) := by
  set uu : Fin (d + 2) → Fin 2 → ℝ := fun r => if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0
  set vv : Fin (d + 2) → ℝ := fun r => if (r : ℕ) < 2 * k then (0 : ℝ) else 1
  have hrow : (fun r => hessC (φ r) (Fin.cons p₀ (Fin.cons p₁ y))) = fun r =>
      blk ((uu r 0 : ℂ) * -(wS p₀ : ℂ)) (blk ((uu r 1 : ℂ) * -(wS p₁ : ℂ))
        ((∑ j, ((uu r 0 * nS p₀ j + uu r 1 * nS p₁ j : ℝ) : ℂ) • T j) + ((vv r : ℝ) : ℂ) • H)) := by
    funext r
    have e : φ r = fun z : Fin (d + 2) → ℂ => uu r 0 * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        uu r 1 * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + vv r * α (Fin.tail (Fin.tail z)) :=
      funext (hφ r)
    rw [e, GlobalTheory.T.complex_hessian_two_point_combination d f α y p₀ p₁ _ _ _ _ (uu r 0) (uu r 1) (vv r) (hfc _) (hfc _) hα (hfh _) (hfh _), ← hH]
    congr 3
    simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hB := GlobalTheory.T.mixed_discriminant_two_row_expansion d T H L hL uu vv (nS p₀) (nS p₁) (-(wS p₀ : ℂ)) (-(wS p₁ : ℂ))
  rw [GlobalTheory.T.word_coefficient_second_derivative d k i hi hkd (nS p₀) (nS p₁)] at hB
  rw [maDens, hrow]
  have hre := congrArg Complex.re hB
  rw [show (((d + 2).factorial : ℕ) : ℂ) = (((d + 2).factorial : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, neg_mul_neg, ← Complex.ofReal_mul, Complex.re_ofReal_mul] at hre
  rw [mul_right_comm, hre]
  ring

theorem densY (d k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d + 2) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ)
    (hL : ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)))
    (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y)) (hα : ContDiffAt ℝ 2 α y)
    (hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j))
    (hH : H = hessC α y) (φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ)
    (hφ : ∀ r z, φ r z = (if (r : ℕ) < 2 * k - 1 then (1 : ℝ) else 0) * f z +
        (if (r : ℕ) < 2 * k - 1 then (0 : ℝ) else 1) * α (Fin.tail z))
    (a : ℂ) :
    maDens φ (Fin.cons a y) = (2 / Real.pi) ^ (d + 1) * (-(wS a) * (2 * (k : ℝ) - 1) *
      (L (rename some (lin3 (nS a) ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k))).re) := by
  set cc : Fin (d + 1) → ℝ := fun r => if (r : ℕ) < 2 * k - 1 then (1 : ℝ) else 0
  set vv : Fin (d + 1) → ℝ := fun r => if (r : ℕ) < 2 * k - 1 then (0 : ℝ) else 1
  have hrow : (fun r => hessC (φ r) (Fin.cons a y)) = fun r =>
      blk ((cc r : ℂ) * -(wS a : ℂ))
        ((∑ j, ((cc r * nS a j : ℝ) : ℂ) • T j) + ((vv r : ℝ) : ℂ) • H) := by
    funext r
    have e : φ r = fun z : Fin (d + 1) → ℂ => cc r * f z + vv r * α (Fin.tail z) := funext (hφ r)
    rw [e, GlobalTheory.T.complex_hessian_block_combination d f α y a _ _ (cc r) (vv r) (hfc _) hα (hfh _), ← hH]
    congr 2
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hB := GlobalTheory.T.mixed_discriminant_one_row_expansion d T H L hL cc vv (nS a) (-(wS a : ℂ))
  rw [GlobalTheory.T.row_product_first_derivative d k hk hkd (nS a)] at hB
  rw [maDens, hrow]
  have hre := congrArg Complex.re hB
  have hR : (-(wS a : ℂ) * L (C (2 * (k : ℝ) - 1) * rename some (lin3 (nS a) ^ (2 * k - 2)) *
      X none ^ (d + 2 - 2 * k))).re = -(wS a) * (2 * (k : ℝ) - 1) *
        (L (rename some (lin3 (nS a) ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k))).re := by
    rw [mul_assoc (C _), C_mul', map_smul, Complex.real_smul, ← Complex.ofReal_neg, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  rw [show (((d + 1).factorial : ℕ) : ℂ) = (((d + 1).factorial : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, hR] at hre
  rw [mul_right_comm, hre]
  ring

theorem fibre_integral_normal : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  intro h d k hk hkd G α y hPD hG2 hα hG1 hGd
  obtain ⟨T, hT⟩ := GlobalTheory.T.xi_potential_hessian_decomposition d G y hPD hG2 hG1 hGd
  obtain ⟨L, hL⟩ := GlobalTheory.T.mixed_discriminant_linear_functional d T (hessC α y)
  set f : (Fin (d + 1) → ℂ) → ℝ := fun z => xiPot (G (Fin.tail z)) (z 0) with hf
  have hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y) := fun a => (hT a).1
  have hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j) := by
    intro a
    rw [(hT a).2]
    ext p q
    refine Fin.cases ?_ (fun p' => ?_) p <;> refine Fin.cases ?_ (fun q' => ?_) q
    · simp [blk, wS]
    · simp [blk]
    · simp [blk]
    · simp [blk, nS, Matrix.sum_apply]
  let ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ L ∘ₗ
    (LinearMap.mulRight ℝ (X none ^ (d + 2 - 2 * k) : MvPolynomial (Option (Fin 3)) ℝ)) ∘ₗ
      (rename some : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Option (Fin 3)) ℝ).toLinearMap
  have hℓ : ∀ p, (L (rename some p * X none ^ (d + 2 - 2 * k))).re = ℓ p := fun p => rfl
  have hword : ∀ i ∈ Finset.range k, (∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) =
      (2 / Real.pi) ^ (d + 2) * (Real.pi ^ 2 * ℓ (diagWordMomentPoly k i)) := by
    intro i hi
    have hik := Finset.mem_range.1 hi
    have hpt : ∀ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y)) =
        (2 / Real.pi) ^ (d + 2) * (logSin 1 p.1 p.2 * (wS p.1 * wS p.2 *
          ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)]
            (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))))) := by
      intro p
      rw [densW d k i hik hkd T _ L hL f α y hfc hα hfh rfl _ ?_ p.1 p.2, hG1, hℓ]
      · ring
      · intro r z
        have hcoef : ∀ c : Fin 2, (if (r : ℕ) = 0 then (![1, -1] : Fin 2 → ℝ) c else if (r : ℕ) = 1 then (![0, 1] : Fin 2 → ℝ) c else if (r : ℕ) < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) = DiagonalFibreFubini.wordCoef i r c := by
          intro c
          simp only [DiagonalFibreFubini.wordCoef]
          split_ifs <;> rfl
        by_cases hr : (r : ℕ) < 2 * k
        · simp only [hr, if_true, hcoef, hf, Fin.tail, Fin.cons_zero, Fin.cons_succ]
          simp
        · simp [hr]
    simp_rw [hpt]
    rw [integral_const_mul, GlobalTheory.T.sphere_pair_log_sine_moment, DiagonalFibreFubini.linProd_word k i hik]
    rfl
  have hY : ∀ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) =
      (2 / Real.pi) ^ (d + 1) * (-(2 * (k : ℝ) - 1)) * (wS a * ℓ (lin3 (nS a) ^ (2 * k - 2))) := by
    intro a
    rw [densY d k hk hkd T _ L hL f α y hfc hα hfh rfl _ ?_ a, hℓ]
    · ring
    · intro r z
      by_cases hr : (r : ℕ) < 2 * k - 1
      · simp [hr, hf]
      · simp [hr]
  have hfib : fibreMomentPoly k = C (-kappa k) * (∑ i, X i ^ 2) ^ (k - 1) := by
    have h2 := h.2.1 k (MvPolynomial (Fin 3) ℝ) X
    rwa [aeval_X_left_apply, MvPolynomial.algebraMap_eq] at h2
  have hpush : pushMomentPoly k = -(∑ i, X i ^ 2) ^ (k - 1) := by
    have h2 := h.2.2.2.1 k hk (MvPolynomial (Fin 3) ℝ) X
    rwa [aeval_X_left_apply] at h2
  rw [Finset.sum_congr rfl hword, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum,
    DiagFibreMoment.sum_diagWordMomentPoly, hfib]
  simp_rw [hY]
  rw [integral_const_mul, GlobalTheory.T.sphere_moment_power]
  have hp : (-(2 * (k : ℝ) - 1)) * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ (2 * k - 2))) =
      -ℓ ((∑ i, X i ^ 2) ^ (k - 1)) := by
    rw [← map_neg, ← hpush, pushMomentPoly, map_smul, smul_eq_mul]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [C_mul', map_smul, smul_eq_mul]
  calc _ = (2 / Real.pi) ^ (d + 1) * (2 / Real.pi) * Real.pi ^ 2 * (-kappa k * ℓ ((∑ i, X i ^ 2) ^ (k - 1))) := by
        rw [pow_succ]; ring
    _ = 2 * kappa k * ((2 / Real.pi) ^ (d + 1) * (Real.pi * (-ℓ ((∑ i, X i ^ 2) ^ (k - 1))))) := by
        field_simp
    _ = _ := by
        rw [← hp]; ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalyticStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_family_analytic : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) τ', IsBlockDiag j (FC.Lc τ ca cb c τ') ∧ (FC.Lc τ ca cb c τ').det ≠ 0) ∧ (∀ τ' r s, AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ) ∧ (∀ L : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L) ∧ (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) τ', IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ')) ∧ ∀ (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ), FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a' → c = c' ∧ a = a' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NullSetImageUnderHoloMapStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.null_set_image_under_holoMap : ∀ (e : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (Z : Set Y), HoloMap B A h → IsNull B Z → IsNull A (h '' Z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.NullImage.isNull_image_of_holoMap | exact GlobalTheory.CompanionTheory.Ar.PB.NullImage.isNull_image_of_holoMap | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.NullImage.isNull_image_of_holoMap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrbitChartTransitionAnalyticStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_chart_transition_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (C₁ C₂ : OrbitChart P e), AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w)) {w | w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariantStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_nonvanishing_orbit_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (z z' : (Σ k, ι k) → ℂ) (p : Ψ × Fin N), SameOrbit z z' → (FC.plk M F b z p ≠ 0 ↔ FC.plk M F b z' p ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOneStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_bijective_degree_one : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), Re.deg = 1 → Re.br = ∅ → Function.Bijective Re.π := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one <;> assumption)
end


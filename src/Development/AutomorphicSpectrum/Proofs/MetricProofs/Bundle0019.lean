import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem log_inv_bounds {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    Real.exp 1 ≤ Real.log (1 / t) ∧ 1 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : Real.exp 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  refine ⟨h1, ?_⟩
  have := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at this

theorem loglog_quot_nonneg {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  obtain ⟨h1, h2⟩ := log_inv_bounds ht hte
  exact div_nonneg (by linarith) (by linarith [Real.exp_pos 1])

theorem epsT_eq_mul (C t : ℝ) :
    epsT C t = C * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) := by
  rw [epsT, mul_div_assoc]

theorem epsT_le_epsT {C C' t : ℝ} (hC : C ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : epsT C t ≤ epsT C' t := by
  rw [epsT_eq_mul, epsT_eq_mul]
  exact mul_le_mul_of_nonneg_right hC (loglog_quot_nonneg ht hte)

theorem mul_epsT_le {C C' t : ℝ} (hC : |C| ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : C * epsT C t ≤ C' * epsT C' t := by
  have hx := loglog_quot_nonneg ht hte
  rw [epsT_eq_mul, epsT_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  have h2 : C ^ 2 ≤ C' ^ 2 := by
    rw [← sq_abs C]
    exact pow_le_pow_left₀ (abs_nonneg C) hC 2
  nlinarith

theorem isPsh_rsmul_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) {ε ε' : ℝ} (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (hε : ε ≤ ε')
    (h : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) :
    IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε') := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hU : (A.chart j).symm y ∈ (th.U x ∩ Set.univ) ∩ Θ.U x := hyU
  have hO1 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' th.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (th.isOpen_U x)
  have hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)
  have hO3 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Set.univ : Set X)) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target isOpen_univ
  have hth2 : ContDiffAt ℝ 2 (th.φ x ∘ (A.chart j).symm) y :=
    ((hth.1 x j).contDiffAt (hO1.mem_nhds ⟨hyt, hU.1.1⟩)).of_le (by norm_cast)
  have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
    ((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)
  have hu2 : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
    ((hu j).contDiffAt (hO3.mem_nhds ⟨hyt, Set.mem_univ _⟩)).of_le (by norm_cast)
  have hP2 : ContDiffAt ℝ 2
      ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y :=
    (hth2.add hu2).add (contDiffAt_const.mul hΘ2)
  have hfun : (th + LocPot.ofFun u + Θ.rsmul ε').φ x ∘ (A.chart j).symm =
      fun z => ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) z +
        (ε' - ε) * (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show th.φ x _ + u _ + ε' * Θ.φ x _ = th.φ x _ + u _ + ε * Θ.φ x _ + (ε' - ε) * Θ.φ x _
    ring
  rw [hfun, levi_add_smul (ε' - ε) hP2 hΘ2 w]
  exact add_nonneg (h x j y ⟨hyt, hyU⟩ w)
    (mul_nonneg (sub_nonneg.2 hε) (hΘp x j y ⟨hyt, hU.2⟩ w))

theorem isRegFamily_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ)
    (C t₀ C' t₁ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hth : IsPotential A th)
    (hs : ∀ y, logNormSec L s y ≤ 0) (hF : IsRegFamily A Θ L s th ph phT C t₀)
    (hC : |C| ≤ C') (ht₁ : 0 < t₁) (ht₁₀ : t₁ ≤ t₀) (hte : t₁ ≤ Real.exp (-Real.exp 1)) :
    IsRegFamily A Θ L s th ph phT C' t₁ := by
  obtain ⟨-, ht₀1, hF⟩ := hF
  have hCC : C ≤ C' := (le_abs_self C).trans hC
  have hr : ∀ y, 0 ≤ rW L s y := fun y => by
    have := hs y
    have := Real.exp_pos 1
    unfold rW
    linarith
  refine ⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF t ht (htt.trans ht₁₀)
  have hte' : t ≤ Real.exp (-Real.exp 1) := htt.trans hte
  have hε := epsT_le_epsT hCC ht hte'
  have hll := (log_inv_bounds ht hte').2
  refine ⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_,
    isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_, fun y hy => ?_,
    fun t' htt' ht' y => ?_⟩
  · have := h4 y
    nlinarith
  · have := h6 y hy hyr
    linarith
  · have := h7 y hy
    have := mul_le_mul_of_nonneg_right hε (hr y)
    linarith
  · have := h8 t' htt' (ht'.trans ht₁₀) y
    have := mul_epsT_le hC (ht.trans_le htt') (ht'.trans hte)
    linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereChartDensityIntegralStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_chart_density_integral : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : Set (Fin e → ℂ)) (Φ : (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (j : Fin A.n), IsParam A V Φ → MeasurableSet B → B ⊆ V → (∀ z ∈ B, Φ z ∈ (A.chart j).source) → (∀ z ∈ B, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ z)) → MeasurableSet ((A.chart j ∘ Φ) '' B) ∧ (IntegrableOn (fun y => g ((A.chart j).symm y) * locDens A P j y) ((A.chart j ∘ Φ) '' B) ↔ IntegrableOn (fun z => g (Φ z) * paramDens P Φ z) B) ∧ ∫ y in (A.chart j ∘ Φ) '' B, g ((A.chart j).symm y) * locDens A P j y = ∫ z in B, g (Φ z) * paramDens P Φ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables | exact GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityDiagonalLeviStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_density_diagonal_levi : ∀ (e : ℕ) (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ), ContDiffAt ℝ 2 φ z → (∀ v, levi φ z v = ∑ q, dd q * ‖(M *ᵥ v) q‖ ^ 2) → maDens (fun _ => φ) z = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (∏ q, dd q) * ‖M.det‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | exact GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_boundary_closed_and_codense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → IsClosed (bdry s) ∧ Dense (bdry s)ᶜ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl | exact GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl | (intros; apply GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecomposition
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.SheetD

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.Tw

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def joinIdx (i : (k : K) → ι k) (j : Fin 2) : (o : Option K) → Tb ι o
  | none => j
  | some k => i k

theorem segre_split (u : (Σ o, Tb ι o) → ℂ) (J : (o : Option K) → Tb ι o) :
    segre u J = segre (basePart₂ u) (fun k => J (some k)) * u ⟨none, J none⟩ := by
  show ∏ o, u ⟨o, J o⟩ = (∏ k, u ⟨some k, J (some k)⟩) * u ⟨none, J none⟩
  rw [Fintype.prod_option, mul_comm]

theorem embL_apply (v : Fin 2 → ℂ) (w : ((k : K) → ι k) → ℂ) (J : (o : Option K) → Tb ι o) :
    embL v w J = w (fun k => J (some k)) * v (J none) := rfl

theorem embL_injective {v : Fin 2 → ℂ} (hv1 : v 1 = 1) :
    Function.Injective (embL v : (((k : K) → ι k) → ℂ) → _) := by
  intro w w' h
  funext i
  have := congrFun h (joinIdx i 1)
  simpa [embL_apply, joinIdx, hv1] using this

theorem glue_oldPart (u : (Σ o, Tb ι o) → ℂ) :
    glue (basePart₂ u) (fun j => u ⟨none, j⟩) = u := by
  funext q
  obtain ⟨o, i⟩ := q
  cases o <;> rfl

theorem oldPart_mem {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : basePart₂ u ∈ mcPts Q := by
  refine ⟨oldPart_ne hu.1, fun f hf => ?_⟩
  have h1 : inc f ∈ twist p Q := Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
  have h2 := hu.2 _ h1
  rw [← glue_oldPart u, eval_inc] at h2
  exact h2

theorem quad_eq_zero {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) :
    u ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * u ⟨none, (1 : Fin 2)⟩ ^ 2 = 0 := by
  have h1 : (quad p : MRing (Tb ι)) ∈ twist p Q :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have h2 := hu.2 _ h1
  rwa [eval_quad] at h2

theorem second_ne_zero {p : ℕ} (hp : p ≠ 0) {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : u ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
  intro h0
  have h1 := quad_eq_zero hu
  rw [h0] at h1
  have h2 : u ⟨none, (0 : Fin 2)⟩ = 0 := by simpa using h1
  obtain ⟨i, hi⟩ := hu.1 none
  refine hi ?_
  have hi' : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
    have : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    exact this i
  rcases hi' with rfl | rfl
  · exact h2
  · exact h0

theorem glue_isSheet {p e : ℕ} {Q : Ideal (MRing ι)}
    {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 ≠ 0) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet Q (pj v Ψ) y w γ) :
    IsSheet (twist p Q) Ψ y (embL v w) (fun y' => glue (γ y') v) := by
  refine ⟨by rw [segre_glue, h.1], ?_⟩
  filter_upwards [h.2] with y' ⟨hd, hm, hΨ⟩
  refine ⟨?_, glue_mem_mcPts hm hv hv1, ?_⟩
  · refine differentiableAt_pi.mpr fun q => ?_
    obtain ⟨o, i⟩ := q
    cases o with
    | none => exact differentiableAt_const _
    | some k => exact differentiableAt_pi.mp hd ⟨k, i⟩
  · rw [segre_glue]; exact hΨ

open Classical in
theorem sheet_of_twist_sheet {p e : ℕ} (hp : p ≠ 0) {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q)
    (k0 : K) {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 = 1) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ' : (Fin e → ℂ) → (Σ o, Tb ι o) → ℂ}
    (h : IsSheet (twist p Q) Ψ y (embL v w) γ') :
    ∃ γ, IsSheet Q (pj v Ψ) y w γ := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hd0, hm0, hΨ0⟩ := h2.self_of_nhds
  have hρ : v 0 ^ 2 = -(p : ℂ) := by
    rw [hv1] at hv
    linear_combination hv
  have hρ0 : v 0 ≠ 0 := by
    intro h0
    rw [h0] at hρ
    have : (p : ℂ) = 0 := by simpa using hρ
    exact hp (by exact_mod_cast this)
  have hb0 := second_ne_zero hp hm0

  have hne : embL v w ≠ 0 := by
    intro h0
    rw [h1, h0, map_zero] at hΨ0
    have := congrFun hΨ0 0
    simp at this
  have hw : w ≠ 0 := by
    intro h0
    exact hne (by rw [h0, map_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hi' : w i ≠ 0 := hi
  have hseg : ∀ j : Fin 2, segre (basePart₂ (γ' y)) i * γ' y ⟨none, j⟩ = w i * v j := by
    intro j
    have := congrFun h1 (joinIdx i j)
    rw [segre_split, embL_apply] at this
    exact this
  have hm : segre (basePart₂ (γ' y)) i ≠ 0 := by
    intro h0
    have := hseg 1
    rw [h0, zero_mul, hv1, mul_one] at this
    exact hi' this.symm
  have hay : γ' y ⟨none, (0 : Fin 2)⟩ = v 0 * γ' y ⟨none, (1 : Fin 2)⟩ := by
    apply mul_left_cancel₀ hm
    have e0 := hseg 0
    have e1 := hseg 1
    rw [hv1, mul_one] at e1
    rw [e0]
    linear_combination (-(v 0)) * e1

  have hcont : ContinuousAt (fun y' => γ' y' ⟨none, (0 : Fin 2)⟩ + v 0 * γ' y' ⟨none, (1 : Fin 2)⟩) y :=
    ((differentiableAt_pi.mp hd0 _).continuousAt).add
      (continuousAt_const.mul (differentiableAt_pi.mp hd0 _).continuousAt)
  have hne2 : γ' y ⟨none, (0 : Fin 2)⟩ + v 0 * γ' y ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
    rw [hay]
    have : v 0 * γ' y ⟨none, (1 : Fin 2)⟩ + v 0 * γ' y ⟨none, (1 : Fin 2)⟩ =
        2 * (v 0 * γ' y ⟨none, (1 : Fin 2)⟩) := by ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hρ0 hb0)
  have hline : ∀ᶠ y' in 𝓝 y, γ' y' ⟨none, (0 : Fin 2)⟩ = v 0 * γ' y' ⟨none, (1 : Fin 2)⟩ := by
    filter_upwards [h2, hcont.eventually_ne hne2] with y' ⟨_, hm', _⟩ hn
    have hq := quad_eq_zero hm'
    have hz : (γ' y' ⟨none, (0 : Fin 2)⟩ - v 0 * γ' y' ⟨none, (1 : Fin 2)⟩) *
        (γ' y' ⟨none, (0 : Fin 2)⟩ + v 0 * γ' y' ⟨none, (1 : Fin 2)⟩) = 0 := by
      linear_combination hq - γ' y' ⟨none, (1 : Fin 2)⟩ ^ 2 * hρ
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hn)

  let c : K → (Fin e → ℂ) → ℂ := fun k y' => if k = k0 then γ' y' ⟨none, (1 : Fin 2)⟩ else 1
  let γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' q => c q.1 y' * basePart₂ (γ' y') q
  have hprod : ∀ y', ∏ k, c k y' = γ' y' ⟨none, (1 : Fin 2)⟩ := by
    intro y'
    simp [c, Finset.prod_ite_eq']
  have hkey : ∀ y', γ' y' ⟨none, (0 : Fin 2)⟩ = v 0 * γ' y' ⟨none, (1 : Fin 2)⟩ →
      embL v (segre (γ y')) = segre (γ' y') := by
    intro y' hl
    funext J
    have hj : γ' y' ⟨none, J none⟩ = γ' y' ⟨none, (1 : Fin 2)⟩ * v (J none) := by
      have hJ : ∀ j : Fin 2, γ' y' ⟨none, j⟩ = γ' y' ⟨none, (1 : Fin 2)⟩ * v j := by
        intro j
        have : j = 0 ∨ j = 1 := by
          have : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
          exact this j
        rcases this with rfl | rfl
        · rw [hl]; ring
        · rw [hv1, mul_one]
      exact hJ _
    have hsm : segre (γ y') = (∏ k, c k y') • segre (basePart₂ (γ' y')) :=
      segre_smul (fun k => c k y') (basePart₂ (γ' y'))
    have hs : segre (γ y') (fun k => J (some k)) =
        γ' y' ⟨none, (1 : Fin 2)⟩ * segre (basePart₂ (γ' y')) (fun k => J (some k)) := by
      rw [hsm, hprod]
      rfl
    rw [embL_apply, segre_split, hj, hs]
    ring
  refine ⟨γ, embL_injective hv1 ?_, ?_⟩
  · rw [hkey y hay, h1]
  · filter_upwards [h2, hline] with y' ⟨hd, hm', hΨ'⟩ hl
    refine ⟨?_, ?_, ?_⟩
    · refine differentiableAt_pi.mpr fun q => ?_
      have hc : DifferentiableAt ℂ (c q.1) y' := by
        by_cases hk : q.1 = k0
        · simp only [c, hk, if_true]
          exact differentiableAt_pi.mp hd _
        · simp only [c, hk, if_false]
          exact differentiableAt_const _
      exact hc.mul (differentiableAt_pi.mp hd _)
    · refine mcPts_smul hQ (fun k => c k y') (fun k => ?_) (oldPart_mem hm')
      by_cases hk : k = k0
      · simpa [c, hk] using second_ne_zero hp hm'
      · simp [c, hk]
    · show Ψ (embL v (segre (γ y'))) = _
      rw [hkey y' hl]
      exact hΨ'

theorem density_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L' : Fin e → HermLine (Tb ι)) (A' : HermLine (Tb ι)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (v : Fin 2 → ℂ), p ≠ 0 → IsArithVar Q (e + 1) → IsArithVar (twist p Q) (e + 1) → IsGoodProj (twist p Q) Ψ → (∀ j, IsSmoothHerm (L' j)) → IsSmoothHerm A' → IsSectionOn (twist p Q) A' (inc s) → (v = vPlus p ∨ v = vMinus p) → (∀ j, ∀ z ∈ mcPts Q, (L' j).h (glue z v) = (L j).h z) → (∀ z ∈ mcPts Q, A'.h (glue z v) = A.h z) → ∀ᵐ y, ∀ w, sheetDensity (twist p Q) Ψ (pot L') (logNorm A' (inc s)) y (embL v w) = sheetDensity Q (pj v Ψ) (pot L) (logNorm A s) y w := by
  intro K _ ι _ p Q e Ψ L' A' L A s v hp hQ hT hΨ hL' hA' hs hv hLh hAh
  have hv1 : v 1 = 1 := by
    rcases hv with rfl | rfl <;> simp [vPlus, vMinus]
  have hvq : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0 := by
    rcases hv with rfl | rfl
    · exact vPlus_root p
    · exact vMinus_root p
  obtain ⟨k0⟩ := hQ.1
  have hQh : IsMultiHomogIdeal Q := hQ.2.1.2.1
  filter_upwards [sheetIndep (Option K) (Tb ι) (twist p Q) e Ψ L' A' (inc s) hT hΨ hL' hA' hs] with y hind
  intro w
  by_cases hγ : ∃ γ, IsSheet Q (pj v Ψ) y w γ
  · have hg := hγ.choose_spec
    have hg1 := glue_isSheet hvq (by rw [hv1]; exact one_ne_zero) hg
    have hex : ∃ γ', IsSheet (twist p Q) Ψ y (embL v w) γ' := ⟨_, hg1⟩
    unfold sheetDensity
    rw [dif_pos hex, dif_pos hγ, hind _ _ _ hex.choose_spec hg1]
    have hlog : logNorm A' (inc s) (glue (hγ.choose y) v) = logNorm A s (hγ.choose y) := by
      rw [logNorm, logNorm, eval_inc, hAh _ hg.2.self_of_nhds.2.1]
    have hma : maDensity (fun j y' => pot L' j (glue (hγ.choose y') v)) y =
        maDensity (fun j y' => pot L j (hγ.choose y')) y := by
      refine maDensity_congr_of_eventuallyEq fun j => ?_
      filter_upwards [hg.2] with y' ⟨_, hm, _⟩
      simp only [pot, hLh j _ hm]
    rw [hlog, hma]
  · have hno : ¬ ∃ γ', IsSheet (twist p Q) Ψ y (embL v w) γ' := fun ⟨γ', h⟩ =>
      hγ (sheet_of_twist_sheet hp hQh k0 hvq hv1 h)
    unfold sheetDensity
    rw [dif_neg hno, dif_neg hγ]

end GlobalTheory.CompanionTheory.Ar.Tw.SheetD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xi_potential_hessian_decomposition : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → ∃ T : Fin 3 → Matrix (Fin d) (Fin d) ℂ, ∀ a : ℂ, ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧ hessC (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) = Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (-(((1 + ‖a‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => ∑ i, (((fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)) a i : ℝ) : ℂ) * T i p' q') q) p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition | exact GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition | (intros; apply GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition <;> assumption)
end


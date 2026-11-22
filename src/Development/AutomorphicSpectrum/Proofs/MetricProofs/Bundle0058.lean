import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareIntersectionPullbackStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_square_intersection_pullback : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2), (∀ (L : Fin (d + 2) → HermLine ι) (L' : Fin (d + 2) → HermLine Q.ιW) (N : HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 0) (Q.v 0) (L j) (L' j)) → IsSmoothHerm N → II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc L' N) = (N.a (Q.κ 1 k₀) : ℝ) * II K ι P (d + 2) L) ∧ ∀ (L : Fin (d + 3) → HermLine ι) (L' : Fin (d + 3) → HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 1) (Q.v 1) (L j) (L' j)) → II Q.KW Q.ιW Q.PW (d + 3) L' = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback | exact GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback | (intros; apply GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartFlagAnalyticMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_gram_comp_basePoint :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (τ' : Ψ) (Un : Set (Fin d → ℂ)) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s) → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ' (bp w) r s) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM l τ' Un bp hU hbp han hmem r t
  have hre := contDiffOn_comp_of_analytic_in_charts _ _ _ BM.Rb.A Un bp _ _ hU hbp han hmem
    (BM.G_smooth l τ' r t).1
  have him := contDiffOn_comp_of_analytic_in_charts _ _ _ BM.Rb.A Un bp _ _ hU hbp han hmem
    (BM.G_smooth l τ' r t).2
  have h1 := Complex.ofRealCLM.contDiff.comp_contDiffOn hre
  have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn him
  have h3 := h1.add (h2.mul (contDiffOn_const (c := Complex.I)))
  refine h3.congr ?_
  intro w _
  simp [Complex.re_add_im]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CardPIdxEqChoose
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept

variable {Ψ : Type} {N j : ℕ}

theorem stepOf_val' (N j : ℕ) (c : Fin N) :
    (stepOf N j c : ℕ) = if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j := rfl

theorem stepOf_mem' (hj : j ≤ N) (c : Fin N) : c ∈ stepCols N j (stepOf N j c) := by
  have := c.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

theorem stepOf_top' (hj : j ≤ N) (c d : Fin N) (hd : d ∈ stepCols N j (stepOf N j c)) : d ≤ c := by
  have := c.2
  have := d.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rw [Fin.le_def]
  split_ifs at hv hd <;> omega

theorem stepOf_proper' (hj : j ≤ N) {a b : Fin N} (hlt : b < a) (hblk : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    IsProperStep N j (stepOf N j b) := by
  have := a.2
  have := b.2
  have h : (b : ℕ) < a := hlt
  have hv := stepOf_val' N j b
  simp only [IsProperStep]
  split_ifs at hv <;> omega

theorem sep_of_all (hj : j ≤ N) {keep : Ψ × Fin N → Prop} (hk : ∀ p, keep p) (q : LowIdx Ψ N j) : Sep keep q :=
  ⟨stepOf N j q.1.2.2, hk _, stepOf_proper' hj q.2.1 q.2.2, stepOf_mem' hj _,
    fun h => absurd (stepOf_top' hj _ _ h) (not_le.2 q.2.1)⟩

theorem card_pIdx_of_all : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (keep : Ψ × Fin N → Prop), j ≤ N →
    (∀ p, keep p) → Nat.card (PIdx j keep) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro Ψ _ _ N j keep hj hk
  have e : PIdx j keep ≃ LowIdx Ψ N j := Equiv.subtypeUnivEquiv (sep_of_all hj hk)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.card_lowIdx Ψ N j hj]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationAntiholomorphicCharts
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Helpers

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem affCoord_eq_of_orbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

theorem affCoord_cj (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) :
    affCoord p (cj z) = cj (affCoord p z) := by
  funext q
  simp [affCoord, cj, map_div₀]

theorem ne_zero_of_orbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z (cj z')) {q : Σ k, ι k}
    (hq : z q ≠ 0) : z' q ≠ 0 := by
  obtain ⟨c, -, rfl⟩ := h
  intro h0
  exact hq (by simp [cj, h0])

theorem analyticAt_affCoord {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → (Σ k, ι k) → ℂ} {a : E} (p : (k : K) → ι k)
    (hf : ∀ q, AnalyticAt ℂ (fun y => f y q) a) (h0 : ∀ k, f a ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun y => affCoord p (f y)) a := by
  rw [analyticAt_pi_iff]
  intro q
  exact (hf q).div (hf ⟨q.1, p q.1⟩) (h0 q.1)

theorem analyticAt_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : AnalyticAt ℂ ψ w) : AnalyticAt ℂ (star ∘ ψ ∘ star) (star w) := by
  refine GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_
  have hs : Filter.Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star w)) (𝓝 w) := by
    simpa using (continuous_star.tendsto (star w))
  filter_upwards [hs.eventually h.eventually_analyticAt] with v hv
  simpa using hv.differentiableAt.star_star

theorem ker_fderiv_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : DifferentiableAt ℂ ψ w) (hk : (fderiv ℂ ψ w).ker = ⊥) :
    (fderiv ℂ (star ∘ ψ ∘ star) (star w)).ker = ⊥ := by
  rw [h.hasFDerivAt.star_star.fderiv, eq_bot_iff]
  intro v hv
  have hv' : star (fderiv ℂ ψ w (star v)) = 0 := by simpa using hv
  have h1 : fderiv ℂ ψ w (star v) = 0 := by simpa using hv'
  have h2 : star v ∈ (fderiv ℂ ψ w).ker := by simpa using h1
  rw [hk] at h2
  have h3 : star v = 0 := by simpa using h2
  simpa using h3

end Helpers

theorem conj_analytic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)) := by
  intro K _ ι _ e X _ A P U lift hL c hc hcc j k w hw
  obtain ⟨hUo, hUm, hH, hM, hCp, -, -, hIm⟩ := hL
  obtain ⟨hw1, hw2⟩ := hw
  have hw2' : c ((A.chart j).symm w) ∈ (A.chart k).source := hw2
  generalize hx₀ : (A.chart j).symm w = x₀ at hw2'
  generalize hx₁ : c x₀ = x₁ at hw2'
  choose p hp using (hM x₁ x₁ (hUm x₁)).1
  have hp0 : ∀ b, lift x₀ x₀ ⟨b, p b⟩ ≠ 0 := fun b =>
    ne_zero_of_orbit_cj (hx₁ ▸ hc x₀) (by subst hx₁; exact hp b)
  have hsym₁ : (A.chart k).symm (A.chart k x₁) = x₁ := (A.chart k).left_inv hw2'
  have hψ : AnalyticAt ℂ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) (A.chart k x₁) := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₁ q k (A.chart k x₁) ⟨(A.chart k).map_source hw2', by simpa [hsym₁] using hUm x₁⟩
    · simpa [hsym₁] using hp b
  have hker := hIm x₁ p hp k hw2'
  have hHa : AnalyticAt ℂ (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₀ q j w ⟨hw1, by simpa [Set.mem_preimage, hx₀] using hUm x₀⟩
    · simpa [hx₀] using hp0 b
  have hsc : ContinuousAt (A.chart j).symm w := (A.chart j).continuousAt_symm hw1
  have hcs : ContinuousAt (fun y => c ((A.chart j).symm y)) w := hcc.continuousAt.comp hsc
  have hFc : ContinuousAt (fun z => star (A.chart k (c ((A.chart j).symm z)))) w := by
    have h1 : ContinuousAt (A.chart k) (c ((A.chart j).symm w)) := by
      rw [hx₀, hx₁]; exact (A.chart k).continuousAt hw2'
    exact continuous_star.continuousAt.comp (ContinuousAt.comp (f := fun y => c ((A.chart j).symm y)) h1 hcs)
  have hFw : star (A.chart k (c ((A.chart j).symm w))) = star (A.chart k x₁) := by
    rw [hx₀, hx₁]
  have e1 : ∀ᶠ y in 𝓝 w, (A.chart j).symm y ∈ U x₀ :=
    hsc ((hUo x₀).mem_nhds (by rw [hx₀]; exact hUm x₀))
  have e2 : ∀ᶠ y in 𝓝 w, c ((A.chart j).symm y) ∈ (A.chart k).source ∩ U x₁ :=
    hcs (((A.chart k).open_source.inter (hUo x₁)).mem_nhds (by
      change c ((A.chart j).symm w) ∈ _
      rw [hx₀, hx₁]; exact ⟨hw2', hUm x₁⟩))
  refine GlobalTheory.T.analytic_of_immersion_composition (fun z => star (A.chart k (c ((A.chart j).symm z))))
    (star ∘ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) ∘ star)
    (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w ?_ ?_ hHa hFc ?_
  · rw [hFw]; exact analyticAt_star_comp hψ
  · rw [hFw]; exact ker_fderiv_star_comp hψ.differentiableAt hker
  · filter_upwards [e1, e2] with y h1 h2
    obtain ⟨h2s, h2u⟩ := h2
    generalize hy' : (A.chart j).symm y = y' at h1 h2s h2u
    have ho1 : SameOrbit (lift x₁ (c y')) (lift (c y') (c y')) := hCp _ _ _ ⟨h2u, hUm _⟩
    have ho2 : SameOrbit (lift y' y') (lift x₀ y') := hCp _ _ _ ⟨hUm _, h1⟩
    have ho : SameOrbit (lift x₁ (c y')) (cj (lift x₀ y')) :=
      sameOrbit_trans ho1 (sameOrbit_trans (hc y') (sameOrbit_cj ho2))
    have hst : (star : ((Σ k, ι k) → ℂ) → _) (cj (affCoord p (lift x₀ y'))) = affCoord p (lift x₀ y') := by
      funext q; simp [cj]
    simp only [Function.comp, star_star, hy', (A.chart k).left_inv h2s]
    rw [affCoord_eq_of_orbit p ho, affCoord_cj, hst]

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateProjectionOfArithSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.coordinate_projection_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement := by
  first | exact @PositivityTheory.HtPt.Aig.pfCoord | exact PositivityTheory.HtPt.Aig.pfCoord
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorPropertiesStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_factor_properties : ∀ (N j : ℕ) (a b ca cb : Fin N) (t : ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) ∧ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 ∧ (∀ h : Matrix (Fin N) (Fin N) ℂ, ∀ i, facOf N j a (h * (1 + Matrix.single cb ca t)) i = facOf N j a h i) ∧ ∀ G h : Matrix (Fin N) (Fin N) ℂ, ∀ i, i ≠ a → blockPot j i G (h * (1 + Matrix.single cb ca t)) = blockPot j i G h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSectionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_orbit_section : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P ⊤ e), Nonempty R.X → ∃ r : ((Σ k, ι k) → ℂ) → R.X, (∀ z ∈ mcPts P, SameOrbit (R.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts P) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLowerUniBlockDiagFactorization
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

namespace GlobalTheory.CompanionTheory.Ar.PB.BigCellLU

variable {N : ℕ}

abbrev square_block_restriction (G : Matrix (Fin N) (Fin N) ℂ) (T : Finset (Fin N)) : Matrix {x // x ∈ T} {x // x ∈ T} ℂ :=
  G.submatrix Subtype.val Subtype.val

theorem minorIJ_self (G : Matrix (Fin N) (Fin N) ℂ) (T : Finset (Fin N)) :
    minorIJ G T T = (square_block_restriction G T).det := by
  unfold minorIJ
  rw [dif_pos rfl, ← Matrix.det_submatrix_equiv_self (T.orderIsoOfFin rfl).toEquiv (square_block_restriction G T)]
  congr 1

theorem det_squareBlockRestriction_ne_zero (G : Matrix (Fin N) (Fin N) ℂ) (hd : G.det ≠ 0) (T : Finset (Fin N))
    (h : ∀ x ∈ T, ∀ c, c ∉ T → G⁻¹ x c = 0) : (square_block_restriction G T).det ≠ 0 := by
  have hB : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hd)
  have hprod : square_block_restriction G⁻¹ T * square_block_restriction G T = 1 := by
    ext x y
    have h1 : (G⁻¹ * G) x.1 y.1 = (1 : Matrix (Fin N) (Fin N) ℂ) x.1 y.1 := by rw [hB]
    rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ T)
      (f := fun c => G⁻¹ x.1 c * G c y.1) (fun c _ hc => by rw [h x.1 x.2 c hc, zero_mul]),
      ← Finset.sum_coe_sort T, Matrix.one_apply] at h1
    have h3 : (square_block_restriction G⁻¹ T * square_block_restriction G T) x y = ∑ i : {x // x ∈ T}, G⁻¹ x.1 i.1 * G i.1 y.1 := rfl
    rw [h3, h1, Matrix.one_apply]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos (congrArg Subtype.val hxy)]
    · rw [if_neg hxy, if_neg (fun h => hxy (Subtype.ext h))]
  intro h0
  have h2 := congrArg Matrix.det hprod
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h2
  exact zero_ne_one h2

theorem exists_cols (G : Matrix (Fin N) (Fin N) ℂ) (F : Set (Finset (Fin N))) (hcov : ∀ b, ∃ T ∈ F, b ∈ T)
    (hnest : ∀ T ∈ F, ∀ T' ∈ F, ∀ b, b ∈ T → b ∈ T' → T ⊆ T' ∨ T' ⊆ T)
    (hinv : ∀ T ∈ F, (square_block_restriction G T).det ≠ 0) :
    ∃ W : Matrix (Fin N) (Fin N) ℂ, (∀ T ∈ F, ∀ c ∈ T, ∀ x, x ∉ T → W x c = 0) ∧
      ∀ a b, (∀ T ∈ F, b ∈ T → a ∈ T) → (G * W) a b = if a = b then 1 else 0 := by
  have hex : ∀ b, ∃ n, ∃ T ∈ F, b ∈ T ∧ T.card = n := fun b => by
    obtain ⟨T, hT, hb⟩ := hcov b
    exact ⟨T.card, T, hT, hb, rfl⟩
  have hmin : ∀ b, ∃ T ∈ F, b ∈ T ∧ ∀ T' ∈ F, b ∈ T' → T ⊆ T' := by
    intro b
    obtain ⟨T, hTF, hbT, hcard⟩ := Nat.find_spec (hex b)
    refine ⟨T, hTF, hbT, fun T' hT'F hbT' => ?_⟩
    rcases hnest T hTF T' hT'F b hbT hbT' with h1 | h1
    · exact h1
    · have hle : T.card ≤ T'.card := by
        rw [hcard]
        exact Nat.find_min' (hex b) ⟨T', hT'F, hbT', rfl⟩
      exact le_of_eq (Finset.eq_of_subset_of_card_le h1 hle).symm
  choose Tb hTbF hbTb hTbmin using hmin
  refine ⟨Matrix.of fun x b => if hx : x ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x, hx⟩ ⟨b, hbTb b⟩ else 0, ?_, ?_⟩
  · intro T hT c hc x hx
    have hx' : x ∉ Tb c := fun h' => hx (hTbmin c T hT hc h')
    simp only [Matrix.of_apply, dif_neg hx']
  · intro a b hab
    have ha : a ∈ Tb b := hab (Tb b) (hTbF b) (hbTb b)
    have hM : square_block_restriction G (Tb b) * (square_block_restriction G (Tb b))⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hinv _ (hTbF b)))
    have h1 := congrFun (congrFun hM ⟨a, ha⟩) ⟨b, hbTb b⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    have h2 : ∀ x : {x // x ∈ Tb b}, G a x.1 * (if hx : x.1 ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x.1, hx⟩ ⟨b, hbTb b⟩ else 0) =
        square_block_restriction G (Tb b) ⟨a, ha⟩ x * (square_block_restriction G (Tb b))⁻¹ x ⟨b, hbTb b⟩ := by
      intro x
      rw [dif_pos x.2]
      rfl
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [← Finset.sum_subset (Finset.subset_univ (Tb b))
      (f := fun x => G a x * (if hx : x ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x, hx⟩ ⟨b, hbTb b⟩ else 0))
      (fun x _ hx => by simp only [dif_neg hx, mul_zero]),
      ← Finset.sum_coe_sort (Tb b), Finset.sum_congr rfl (fun x _ => h2 x), h1]
    simp only [Subtype.mk.injEq]

def IsSeg (N j : ℕ) (T : Finset (Fin N)) : Prop :=
  (∃ m, m ≤ N - j ∧ T = Finset.univ.filter fun a : Fin N => (a : ℕ) < m) ∨
    ∃ m, T = Finset.univ.filter fun a : Fin N => N - j ≤ (a : ℕ) ∧ (a : ℕ) < m

theorem isSeg_omIdx (N j : ℕ) : IsSeg N j (omIdx N j) := by
  exact Or.inl ⟨N - j, le_refl _, rfl⟩

theorem isSeg_wIdx (N j : ℕ) : IsSeg N j (wIdx N j) :=
  Or.inr ⟨N, by ext a; simp [wIdx]⟩

theorem isSeg_stepCols (N j : ℕ) (i : Fin N) : IsSeg N j (stepCols N j i) := by
  have hi := i.isLt
  unfold IsSeg stepCols
  by_cases h : (i : ℕ) + 1 ≤ j
  · right
    exact ⟨N - j + ((i : ℕ) + 1), by ext a; simp [h]⟩
  · left
    exact ⟨(i : ℕ) + 1 - j, by omega, by ext a; simp [h]⟩

theorem IsSeg.nested {N j : ℕ} {T T' : Finset (Fin N)} (h : IsSeg N j T) (h' : IsSeg N j T') {b : Fin N}
    (hb : b ∈ T) (hb' : b ∈ T') : T ⊆ T' ∨ T' ⊆ T := by
  rcases h with ⟨m, hm, rfl⟩ | ⟨m, rfl⟩ <;> rcases h' with ⟨m', hm', rfl⟩ | ⟨m', rfl⟩ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
  all_goals first
    | (exfalso; omega)
    | (rcases le_total m m' with hmm | hmm
       · left
         intro a ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
         omega
       · right
         intro a ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
         omega)

theorem IsSeg.down {N j : ℕ} {T : Finset (Fin N)} (h : IsSeg N j T) {a b : Fin N} (hb : b ∈ T) (hab : a < b)
    (hs : (a : ℕ) < N - j ↔ (b : ℕ) < N - j) : a ∈ T := by
  have hab' : (a : ℕ) < b := hab
  rcases h with ⟨m, hm, rfl⟩ | ⟨m, rfl⟩ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  · omega
  · have h1 : ¬ ((b : ℕ) < N - j) := by omega
    have h2 : ¬ ((a : ℕ) < N - j) := fun h => h1 (hs.mp h)
    omega

theorem exists_lu : ∀ (N j : ℕ) (kp : Fin N → Prop) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 → (∀ i, kp i → IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ L W : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ (∀ a b : Fin N, b < a → ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) → (¬ ∃ i, kp i ∧ IsProperStep N j i ∧ b ∈ stepCols N j i ∧ a ∉ stepCols N j i) → L a b = 0) ∧ IsBlockDiag j W ∧ (∀ i, kp i → IsProperStep N j i → ∀ c ∈ stepCols N j i, ∀ x, x ∉ stepCols N j i → W x c = 0) ∧ G * W = L := by
  intro N j kp G hjN hbd hdet hstep
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet)
  have hGinv : ∀ x c : Fin N, ¬ ((x : ℕ) < N - j ↔ (c : ℕ) < N - j) → G⁻¹ x c = 0 := by
    set E : Matrix (Fin N) (Fin N) ℂ :=
      Matrix.of (fun x c => if ((x : ℕ) < N - j ↔ (c : ℕ) < N - j) then G⁻¹ x c else 0) with hEdef
    have hE : G * E = 1 := by
      ext a c
      by_cases hac : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
      · rw [← hGG, Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hEdef, Matrix.of_apply]
        by_cases hxc : ((x : ℕ) < N - j ↔ (c : ℕ) < N - j)
        · rw [if_pos hxc]
        · rw [if_neg hxc, hbd a x (fun hax => hxc (hax.symm.trans hac)), zero_mul, zero_mul]
      · have hne : a ≠ c := fun h => hac (by rw [h])
        rw [Matrix.one_apply_ne hne, Matrix.mul_apply]
        refine Finset.sum_eq_zero (fun x _ => ?_)
        rw [hEdef, Matrix.of_apply]
        by_cases hxc : ((x : ℕ) < N - j ↔ (c : ℕ) < N - j)
        · rw [hbd a x (fun hax => hac (hax.trans hxc)), zero_mul]
        · rw [if_neg hxc, mul_zero]
    have hEinv : G⁻¹ = E := Matrix.inv_eq_right_inv hE
    intro x c hxc
    rw [hEinv, hEdef, Matrix.of_apply, if_neg hxc]
  have hom : (square_block_restriction G (omIdx N j)).det ≠ 0 := det_squareBlockRestriction_ne_zero G hdet _ (fun x hx c hc => hGinv x c (fun h => by
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx hc
    exact hc (h.mp hx)))
  have hw : (square_block_restriction G (wIdx N j)).det ≠ 0 := det_squareBlockRestriction_ne_zero G hdet _ (fun x hx c hc => hGinv x c (fun h => by
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx hc
    exact (not_lt.mpr hx) (h.mpr (not_le.mp hc))))
  let F : Set (Finset (Fin N)) := {T | (∃ i, kp i ∧ IsProperStep N j i ∧ T = stepCols N j i) ∨
    T = omIdx N j ∨ T = wIdx N j}
  have hseg : ∀ T ∈ F, IsSeg N j T := by
    rintro T (⟨i, -, -, rfl⟩ | rfl | rfl)
    · exact isSeg_stepCols N j i
    · exact isSeg_omIdx N j
    · exact isSeg_wIdx N j
  have hcov : ∀ b, ∃ T ∈ F, b ∈ T := by
    intro b
    by_cases hb : (b : ℕ) < N - j
    · exact ⟨omIdx N j, Or.inr (Or.inl rfl), by
        simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact hb⟩
    · exact ⟨wIdx N j, Or.inr (Or.inr rfl), by
        simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact not_lt.mp hb⟩
  have hinv : ∀ T ∈ F, (square_block_restriction G T).det ≠ 0 := by
    rintro T (⟨i, hki, hpi, rfl⟩ | rfl | rfl)
    · rw [← minorIJ_self]
      exact hstep i hki hpi
    · exact hom
    · exact hw
  obtain ⟨W, hWsupp, hGW⟩ := exists_cols G F hcov
    (fun T hT T' hT' b hb hb' => (hseg T hT).nested (hseg T' hT') hb hb') hinv
  have hWblk : IsBlockDiag j W := by
    intro x c hxc
    by_cases hc : (c : ℕ) < N - j
    · refine hWsupp (omIdx N j) (Or.inr (Or.inl rfl)) c ?_ x ?_
      · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc
      · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hx
        exact hxc (iff_of_true hx hc)
    · refine hWsupp (wIdx N j) (Or.inr (Or.inr rfl)) c ?_ x ?_
      · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact not_lt.mp hc
      · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hx
        exact hxc (iff_of_false (not_lt.mpr hx) hc)
  have hLblk : IsBlockDiag j (G * W) := by
    intro a b hab
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hxb : ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [hbd a x (fun hax => hab (hax.trans hxb)), zero_mul]
    · rw [hWblk x b hxb, mul_zero]
  refine ⟨G * W, W, hLblk, ⟨fun a => ?_, fun a b hab => ?_⟩, ?_, hWblk, ?_, rfl⟩
  · rw [hGW a a (fun T _ h => h), if_pos rfl]
  · by_cases hs : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [hGW a b (fun T hT hb => (hseg T hT).down hb hab hs), if_neg (ne_of_lt hab)]
    · exact hLblk a b hs
  · intro a b hba hs hno
    refine (hGW a b ?_).trans (if_neg (ne_of_gt hba))
    rintro T (⟨i, hki, hpi, rfl⟩ | rfl | rfl) hb
    · by_contra ha
      exact hno ⟨i, hki, hpi, hb, ha⟩
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact hs.mpr hb
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact not_lt.mp (fun h => (not_lt.mpr hb) (hs.mp h))
  · intro i hki hpi c hc x hx
    exact hWsupp _ (Or.inl ⟨i, hki, hpi, rfl⟩) c hc x hx

end GlobalTheory.CompanionTheory.Ar.PB.BigCellLU
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFirstStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => wPhi M F bl h ε k₀ τ ca cb w p) (wD ε V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecondStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → (∀ τ' r s, AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) (wD ε V)) ∧ ∀ w ∈ wD ε V, (∀ τ', IsBlockDiag j (wH h ε τ' w) ∧ (wH h ε τ' w).det ≠ 0) ∧ baseOf M k₀ (wPhi M F bl h ε k₀ τ ca cb w) = bl (wB ε w) ∧ ∀ τ' i, M.ExactAt F (τ', i) (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (wH h ε τ' w) ∧ M.ExactAt F (τ', i) (sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (if τ' = τ then wH h ε τ w * (1 + Matrix.single cb ca (wT ε w)) else wH h ε τ' w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbitStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_plucker_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), fstPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b h ∧ sndPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fstPt_sndPt_wVec | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fstPt_sndPt_wVec | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fstPt_sndPt_wVec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijectiveStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_projection_bijective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Function.Bijective FA.Re.π := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.re_pi_bijective | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.re_pi_bijective | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.re_pi_bijective <;> assumption)
end


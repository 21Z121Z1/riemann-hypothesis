import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle0001
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsInvFn (X : Data E r) (ph : Frame X.Ψ r → ℝ) : Prop :=
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ph (lact γ (rmul x b)) = ph x

def leviM (X : Data E r) (g : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((g (cpt X x0 w) : ℝ) : ℂ)) z ξ).re

def cfwM (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  (∃ C A' : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x)) ∧
  ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ C A' : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
    (∀ τ, 1 ≤ X.tt ξ x τ) →
    ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ

structure ArchInM (X : Data E r) where
  L : Wt X.Ψ r
  de : Wt X.Ψ r
  Fp : Wt X.Ψ r
  T : ℕ
  i : ℕ
  g0 : ℕ
  N : ℕ
  c : ℝ
  c1 : ℝ
  a1 : ℝ
  rr : ℝ
  n_ge : 2 ≤ nd X
  T_ge : 11 * nd X ^ 2 ≤ T
  i_pos : 1 ≤ i
  genus_pos : 1 ≤ g0
  c_pos : 0 < c
  frame_theta_const_pos : 0 < c1
  frame_theta_weight_pos : 0 < a1
  rr_nonneg : 0 ≤ rr
  Tcg0 : (T : ℝ) * c * g0 ≤ 1
  rr_le : rr * (1 + c1 / a1) ≤ 2 * T
  w : Fin N → Frame X.Ψ r → ℂ
  w_van : ∀ k, w k ∈ X.SSgt L 0
  w_nz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0
  ph : Frame X.Ψ r → ℝ
  ph_inv : IsInvFn X ph
  ph_nonneg : ∀ x ∈ X.dom, 0 ≤ ph x
  p1 : ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x
  p2 : ∀ x ∈ X.dom, (T : ℝ) * c * ph x ≤ c1 / X.la1 x ^ 2
  p3 : ∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm L (w k) x ^ 2
  et : Frame X.Ψ r → ℂ
  genus_even : Even g0
  et_sec : X.IsSec ((i * (g0 / 2)) • de) et
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  p4 : ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm ((i * (g0 / 2)) • de) et x ^ 2 ≤ K * Real.exp (-(2 * i * ph x))
  th1 : Frame X.Ψ r → ℂ
  firstTheta_vanishes : th1 ∈ X.SSgt (2 • L - de) 0
  firstTheta_ne_zero : ∃ x ∈ X.dom, th1 x ≠ 0
  th2 : Frame X.Ψ r → ℂ
  secondTheta_vanishes : th2 ∈ X.SSgt ((nd X + 4) • L - Fp) 0
  secondTheta_ne_zero : ∃ x ∈ X.dom, th2 x ≠ 0
  thp : Frame X.Ψ r → ℂ
  thp_van : thp ∈ X.SSgt Fp 0
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0
  ps0 : Frame X.Ψ r → ℝ
  potential_invariant : IsInvFn X ps0
  potential_smooth : ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps0 (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}
  base_psi_levi_lower_bound : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
    -(rr / 2 * leviM X (phla X de) x0 z ξ) ≤ leviM X ps0 x0 z ξ
  base_psi_weighted_cf : cfwM X ps0 a1
  posL : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    0 < leviM X (phla X L) x0 z ξ
  posLde : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    0 < leviM X (phla X (2 • L - de)) x0 z ξ
  posF : ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * T →
    ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviM X (phla X L) x0 z ξ ≤
        leviM X (phla X (Fp - kapW X - nd X • L)) x0 z ξ - t * (rr / 2) * leviM X (phla X de) x0 z ξ

structure FlatM (X : Data E r) (Xa : ArchInM X) where
  w0 : Frame X.Ψ r → ℂ
  s : Fin (nd X) → Frame X.Ψ r → ℂ
  weightForm_vanishes : w0 ∈ X.SSgt Xa.L 0
  s_van : ∀ k, s k ∈ X.SSgt Xa.L 0
  δ : ℕ
  xs : Fin δ → Frame X.Ψ r
  xs_mem : ∀ j, xs j ∈ X.dom
  S_eq : ∀ x ∈ X.dom, (∀ k, s k x = 0) ↔
    ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)
  xs_inj : ∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j'
  w0_ne : ∀ j, w0 (xs j) ≠ 0
  coord : ∀ j, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
    s k (cpt X (xs j) z) / w0 (cpt X (xs j) z) : V (nd X))) 0).det ≠ 0
  w_le : ∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤
    K * (X.pnorm Xa.L w0 x ^ 2 + ∑ k, X.pnorm Xa.L (s k) x ^ 2)

  denom_le_family : ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm Xa.L w0 x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2
  s_le_w : ∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (s k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2

  family_le_coords : ∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ j, xs j ∈ U) →
    (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) →
    ∃ K : ℝ, ∀ x ∈ X.dom, x ∉ U → ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (s k) x ^ 2

def monoM {n : ℕ} (X : Data E r) (s : Fin n → Frame X.Ψ r → ℂ) (α : Fin n → ℕ) (x : Frame X.Ψ r) : ℂ :=
  ∏ k, s k x ^ α k

def leadM {n δ : ℕ} (X : Data E r) (s : Fin n → Frame X.Ψ r → ℂ) (w0 : Frame X.Ψ r → ℂ)
    (t : Fin δ → Frame X.Ψ r → ℂ) (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt n a0, ∑ k, cc α k * monoM X s α x * w0 x ^ (T - ∑ q, α q) * t k x

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

theorem analyticAt_of_diffOn {n : ℕ} {f : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : V n} (hz : z ∈ U) : AnalyticAt ℂ f z := by
  let e : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU' : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hf' : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    hf.comp (e.symm : (Fin n → ℂ) →L[ℂ] V n).differentiableOn (fun y hy => hy)
  have hz' : e z ∈ e.symm ⁻¹' U := by simpa using hz
  have ha := ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU' hf' (e z) hz'
  have hfe : f = (f ∘ e.symm) ∘ e := by
    funext w
    simp
  rw [hfe]
  exact ha.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt z)

theorem isBigO_norm_pow_of_le {F : Type*} [NormedAddCommGroup F] {k d : ℕ} (h : k ≤ d) :
    (fun y : F => ‖y‖ ^ d) =O[𝓝 0] (fun y => ‖y‖ ^ k) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : F) one_pos] with y hy
  rw [mem_ball_zero_iff] at hy
  simp only [norm_pow, norm_norm, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) hy.le h

theorem taylor_step {n d : ℕ} {G : V n → ℂ} (hG : AnalyticAt ℂ G 0)
    (hO : G =O[𝓝 0] fun z => ‖z‖ ^ d) :
    ∃ q : ContinuousMultilinearMap ℂ (fun _ : Fin d => V n) ℂ,
      (fun z => G z - q (fun _ => z)) =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) := by
  obtain ⟨p, hp⟩ := hG
  have hvan : ∀ m, m < d → ∀ y : V n, p m (fun _ => y) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm y0
      have hps : ∀ y : V n, p.partialSum (m + 1) y = p m (fun _ => y) := by
        intro y
        simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]
        rw [Finset.sum_eq_zero (fun j hj => ih j (Finset.mem_range.mp hj)
          (by have := Finset.mem_range.mp hj; omega) y), zero_add]
      have hA := hp.isBigO_sub_partialSum_pow (m + 1)
      simp only [zero_add, hps] at hA
      have hB : G =O[𝓝 0] fun z => ‖z‖ ^ (m + 1) := hO.trans (isBigO_norm_pow_of_le (by omega))
      have h : (fun y : V n => p m (fun _ => y)) =O[𝓝 0] fun y => ‖y‖ ^ (m + 1) :=
        (hB.sub hA).congr_left (fun y => by ring)
      have htend : Tendsto (fun t : ℂ => t • y0) (𝓝 0) (𝓝 0) := by
        have hc : Continuous fun t : ℂ => t • y0 := continuous_id.smul continuous_const
        have := hc.tendsto 0
        simpa using this
      have h2 := h.comp_tendsto htend
      obtain ⟨C, hC⟩ := h2.bound
      have hhom : ∀ t : ℂ, p m (fun _ => t • y0) = t ^ m * p m (fun _ => y0) := by
        intro t
        have := (p m).map_smul_univ (fun _ => t) (fun _ => y0)
        rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hbd : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖p m (fun _ => y0)‖ ≤ C * ‖y0‖ ^ (m + 1) * ‖t‖ := by
        filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with t ht ht0
        simp only [Function.comp_apply, hhom, norm_mul, norm_pow, norm_smul, mul_pow, norm_norm] at ht
        have htpos : 0 < ‖t‖ ^ m := pow_pos (norm_pos_iff.mpr (by simpa using ht0)) m
        refine le_of_mul_le_mul_left ?_ htpos
        calc ‖t‖ ^ m * ‖p m (fun _ => y0)‖ ≤ C * (‖t‖ ^ (m + 1) * ‖y0‖ ^ (m + 1)) := by
              linarith [ht]
          _ = ‖t‖ ^ m * (C * ‖y0‖ ^ (m + 1) * ‖t‖) := by ring
      have hlim : Tendsto (fun t : ℂ => C * ‖y0‖ ^ (m + 1) * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
        have hc : Continuous fun t : ℂ => C * ‖y0‖ ^ (m + 1) * ‖t‖ :=
          continuous_const.mul continuous_norm
        have := hc.tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have hc0 : ‖p m (fun _ => y0)‖ ≤ 0 := ge_of_tendsto hlim hbd
      exact norm_le_zero_iff.mp hc0
  refine ⟨p d, ?_⟩
  have hA := hp.isBigO_sub_partialSum_pow (d + 1)
  have hps : ∀ y : V n, p.partialSum (d + 1) y = p d (fun _ => y) := by
    intro y
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (fun j hj => hvan j (Finset.mem_range.mp hj) y), zero_add]
  simp only [zero_add, hps] at hA
  exact hA

theorem multilinear_expand {n d : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin d => V n) ℂ)
    (L : V n ≃L[ℂ] V n) :
    ∃ a : (Fin n → ℕ) → ℂ, ∀ z, q (fun _ => z) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple n d, a α * ∏ k, (L z) k ^ α k := by
  classical
  let b : Fin n → V n := fun k => L.symm (EuclideanSpace.basisFun (Fin n) ℂ k)
  let cnt : (Fin d → Fin n) → (Fin n → ℕ) := fun f k => (Finset.univ.filter fun i => f i = k).card
  have hcnt : ∀ f, cnt f ∈ Finset.Nat.antidiagonalTuple n d := by
    intro f
    rw [Finset.Nat.mem_antidiagonalTuple]
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin d)))
      (t := (Finset.univ : Finset (Fin n))) (f := f) (fun i _ => Finset.mem_univ (f i))
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have hprod : ∀ (f : Fin d → Fin n) (c : Fin n → ℂ), ∏ i, c (f i) = ∏ k, c k ^ cnt f k := by
    intro f c
    rw [← Finset.prod_fiberwise Finset.univ f (fun i => c (f i))]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.prod_congr rfl (fun i hi => congrArg c (Finset.mem_filter.mp hi).2), Finset.prod_const]
  refine ⟨fun α => ∑ f ∈ Finset.univ.filter (fun f => cnt f = α), q (fun i => b (f i)), fun z => ?_⟩
  have hz : z = ∑ k, (L z) k • b k := by
    have h1 := (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (L z)
    simp only [EuclideanSpace.basisFun_repr] at h1
    calc z = L.symm (L z) := (L.symm_apply_apply z).symm
      _ = L.symm (∑ k, (L z) k • EuclideanSpace.basisFun (Fin n) ℂ k) := by rw [h1]
      _ = ∑ k, (L z) k • b k := by simp only [map_sum, map_smul, b]
  have hL : q (fun _ => z) = ∑ f : Fin d → Fin n, q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k := by
    conv_lhs => rw [hz]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    congr 1
    have := hprod f (fun k => (L z) k)
    simpa using this
  rw [hL]
  symm
  calc ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        (∑ f ∈ Finset.univ.filter (fun f => cnt f = α), q (fun i => b (f i))) * ∏ k, (L z) k ^ α k
      = ∑ α ∈ Finset.Nat.antidiagonalTuple n d, ∑ f ∈ Finset.univ.filter (fun f => cnt f = α),
          q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f hf => ?_
        rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : Fin d → Fin n, q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k :=
        Finset.sum_fiberwise_of_maps_to (fun f _ => hcnt f) _

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfD
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem ext_glue (hU : IsOpen U) (g G : V n → ℂ) (hg : DifferentiableOn ℂ g U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0)
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ g y ≠ 0})
    (hL : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | g y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ g y ≠ 0} := by
  classical
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧ ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball p ρ) ∧
      Set.EqOn F G (ball p ρ \ {y | g y = 0}) := by
    intro p hp
    obtain ⟨ρ, hρ, hsub, hint⟩ := hL p hp
    obtain ⟨F, hF, hFeq⟩ := ReciprocityTheory.L2DbarEstimates.ext n p ρ g G (hg.mono hsub)
      (hG.mono fun y hy => ⟨hsub hy.1, hy.2⟩) hint
    exact ⟨ρ, hρ, hsub, F, hF, hFeq⟩
  choose ρ hρ hsub F hF hFeq using hloc
  have agree : ∀ y (hy : y ∈ U) z (hz : z ∈ U) x, x ∈ ball y (ρ y hy) → x ∈ ball z (ρ z hz) →
      F y hy x = F z hz x := by
    intro y hy z hz x hxy hxz
    by_contra hne
    have hcy : ContinuousAt (F y hy) x :=
      (hF y hy).continuousOn.continuousAt (isOpen_ball.mem_nhds hxy)
    have hcz : ContinuousAt (F z hz) x :=
      (hF z hz).continuousOn.continuousAt (isOpen_ball.mem_nhds hxz)
    have hev : ∀ᶠ t in 𝓝 x, F y hy t ≠ F z hz t := by
      first
        | exact hcy.eventually_ne hcz hne
        | exact ((hcy.sub hcz).eventually_ne (sub_ne_zero.mpr hne)).mono fun t ht h => ht (sub_eq_zero.mpr h)
    have hs : {t | t ∈ ball y (ρ y hy) ∧ t ∈ ball z (ρ z hz) ∧ F y hy t ≠ F z hz t} ∈ 𝓝 x :=
      Filter.inter_mem (isOpen_ball.mem_nhds hxy) (Filter.inter_mem (isOpen_ball.mem_nhds hxz) hev)
    obtain ⟨W, hWs, hWo, hxW⟩ := _root_.mem_nhds_iff.mp hs
    obtain ⟨t, htW, hgt⟩ := hgn W hWo (fun t ht => hsub y hy (hWs ht).1) ⟨x, hxW⟩
    have h1 := hFeq y hy ⟨(hWs htW).1, hgt⟩
    have h2 := hFeq z hz ⟨(hWs htW).2.1, hgt⟩
    exact (hWs htW).2.2 (h1.trans h2.symm)
  refine ⟨fun y => if hy : y ∈ U then F y hy y else 0, ?_, ?_⟩
  · intro y hy
    have hnb : ball y (ρ y hy) ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self (hρ y hy))
    have heq : (fun y => if hy : y ∈ U then F y hy y else 0) =ᶠ[𝓝 y] F y hy := by
      filter_upwards [hnb] with x hx
      have hxU : x ∈ U := hsub y hy hx
      rw [dif_pos hxU]
      exact agree x hxU y hy x (mem_ball_self (hρ x hxU)) hx
    exact (((hF y hy).differentiableAt hnb).congr_of_eventuallyEq heq).differentiableWithinAt
  · intro y hy
    show (if h : y ∈ U then F y h y else 0) = G y
    rw [dif_pos hy.1]
    exact hFeq y hy.1 ⟨mem_ball_self (hρ y hy.1), hy.2⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {n : ℕ}

abbrev lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Matrix (Fin i) (Fin i) ℂ :=
  M.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)

theorem det_lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (lb M i).det = lminor M (Fin.castSucc i) := rfl

def wv (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Fin i → ℂ :=
  vecMul (fun j : Fin i => M i (Fin.castLE i.isLt.le j)) (lb M i)⁻¹

def Lm (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => if h : (k : ℕ) < i then -wv M i ⟨k, h⟩ else if k = i then 1 else 0

theorem row_expand (N M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1) :
    (N * M) i j = (∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j) + M i j := by
  classical
  rw [Matrix.mul_apply]
  have h1 : ∑ k : Fin n, N i k * M k j = ∑ k ∈ Finset.univ.filter (fun k => k ≤ i), N i k * M k j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · rw [hup k (lt_of_not_ge hk), zero_mul]
  have h2 : Finset.univ.filter (fun k : Fin n => k ≤ i) = insert i (Finset.univ.filter (fun k => k < i)) := by
    ext k
    simp [le_iff_lt_or_eq, or_comm]
  have h3 : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < i), N i k * M k j =
      ∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j := by
    refine Finset.sum_bij' (fun k hk => (⟨k, (Finset.mem_filter.mp hk).2⟩ : Fin i))
      (fun k _ => Fin.castLE i.isLt.le k) (fun _ _ => Finset.mem_univ _) (fun k _ => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k.isLt
  rw [h1, h2, Finset.sum_insert (by simp), h3, hd, one_mul, add_comm]

theorem Lm_up (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) (h : i < k) : Lm M i k = 0 := by
  simp only [Lm, Matrix.of_apply]
  have h' : ¬ ((k : ℕ) < i) := by rw [Fin.lt_iff_val_lt_val] at h; omega
  rw [dif_neg h', if_neg (ne_of_gt h)]

theorem Lm_diag (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Lm M i i = 1 := by
  simp [Lm]

theorem Lm_det (M : Matrix (Fin n) (Fin n) ℂ) : (Lm M).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i k h => Lm_up M i k (OrderDual.toDual_lt_toDual.mp h))]
  simp [Lm_diag]

theorem row_sys (N M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1)
    (hz : ∀ j : Fin n, j < i → (N * M) i j = 0) :
    vecMul (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) (lb M i) =
      -fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
  funext j'
  have hrow := row_expand N M i (Fin.castLE i.isLt.le j') hup hd
  rw [hz _ (by simp [Fin.lt_iff_val_lt_val])] at hrow
  simp only [vecMul, dotProduct, lb, submatrix_apply, Pi.neg_apply]
  linear_combination (-1 : ℂ) * hrow

theorem Lm_mul_up (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (i j : Fin n) (h : j < i) : (Lm M * M) i j = 0 := by
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  rw [row_expand (Lm M) M i j (fun k hk => Lm_up M i k hk) (Lm_diag M i)]
  have hL : ∀ k : Fin i, Lm M i (Fin.castLE i.isLt.le k) = -wv M i k := by
    intro k
    simp only [Lm, Matrix.of_apply]
    rw [dif_pos (by simp)]
    rfl
  simp_rw [hL]
  have key : vecMul (wv M i) (lb M i) = fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
    rw [wv, vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, vecMul_one]
  have hk := congrFun key ⟨j, h⟩
  simp only [vecMul, dotProduct, lb, submatrix_apply] at hk
  have hk' : ∑ k : Fin i, wv M i k * M (Fin.castLE i.isLt.le k) j = M i j := hk
  simp only [neg_mul, Finset.sum_neg_distrib, hk', neg_add_cancel]

theorem Lm_unique (N M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (hup : ∀ i k : Fin n, i < k → N i k = 0) (hd : ∀ i, N i i = 1)
    (hz : ∀ i j : Fin n, j < i → (N * M) i j = 0) : N = Lm M := by
  ext i k
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  have h1 := row_sys N M i (hup i) (hd i) (hz i)
  have h2 := row_sys (Lm M) M i (fun k hk => Lm_up M i k hk) (Lm_diag M i)
    (fun j hj => Lm_mul_up M hM i j hj)
  have heq : (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) = fun k => Lm M i (Fin.castLE i.isLt.le k) := by
    have h3 := congrArg (fun v => vecMul v (lb M i)⁻¹) (h1.trans h2.symm)
    simpa only [vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, vecMul_one] using h3
  rcases lt_trichotomy k i with hk | rfl | hk
  · exact congrFun heq ⟨k, hk⟩
  · rw [hd, Lm_diag]
  · rw [hup i k hk, Lm_up M i k hk]

theorem lminor_nb (N B : Matrix (Fin n) (Fin n) ℂ) (hup : ∀ i k : Fin n, i < k → N i k = 0)
    (hd : ∀ i, N i i = 1) (hB : B.BlockTriangular id) (k : Fin (n + 1)) :
    lminor (N * B) k = ∏ j : Fin k, B (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  set e : Fin k → Fin n := Fin.castLE (Nat.le_of_lt_succ k.isLt) with he
  have hmono : ∀ a b : Fin k, a < b → e a < e b := fun a b h => h
  have hsub : (N * B).submatrix e e = N.submatrix e e * B.submatrix e e := by
    ext a b
    simp only [submatrix_apply, mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective _) _ _ (fun c hc => ?_) (fun _ => rfl)
    have hc' : (k : ℕ) ≤ c := by
      by_contra hlt
      exact hc ⟨⟨c, by omega⟩, Fin.ext rfl⟩
    have hac : e a < c := by
      rw [Fin.lt_iff_val_lt_val]
      show (a : ℕ) < c
      omega
    rw [hup _ _ hac, zero_mul]
  have hNt : (N.submatrix e e).BlockTriangular OrderDual.toDual :=
    fun a b h => hup _ _ (hmono _ _ (OrderDual.toDual_lt_toDual.mp h))
  have hBt : (B.submatrix e e).BlockTriangular id := fun a b h => hB (hmono _ _ h)
  rw [lminor, ← he, hsub, det_mul, Matrix.det_of_lowerTriangular _ hNt,
    Matrix.det_of_upperTriangular hBt]
  simp [hd]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ortho_holds : OrthoStatement (E := E) := by
  intro r X x hx

  have hBor := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem (X := X) hx
  refine ⟨ReciprocityTheory.ChartRestriction.G.FD.rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x),
    ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf (X := X) hx,
    fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹ :
      Matrix (Fin r) (Fin r) ℂ), ?_, ?_⟩
  · intro τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    haveI : Invertible (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ) :=
      Matrix.invertibleOfIsUnitDet _ hdet
    have hM : (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).BlockTriangular id :=
      fun i j hij => (hBor τ).2 i j hij
    have hMi := Matrix.blockTriangular_inv_of_blockTriangular hM
    refine ⟨?_, fun a c hca => hMi hca⟩
    show ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹).det ≠ 0
    exact (Matrix.isUnit_nonsing_inv_det _ hdet).ne_zero
  · funext τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    show ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat x τ *
      ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ *
      (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end


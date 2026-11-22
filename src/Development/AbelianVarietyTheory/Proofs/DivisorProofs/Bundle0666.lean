import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightLevi
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas

theorem frameWeight_levi : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (β J : ι → Y → ℂ), IsOpen U → A.IsFrameOn (A.kap + E) U β → A.IsFrameOn A.kap U J → ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source → ContDiffAt ℝ ∞ ((fun y => -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ f : Y → ℝ, ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) → ∀ ξ : Fin n → ℂ, A.leviAt i (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y) x ξ = A.leviAt i (fun y => A.ph E i y + f y) x ξ := by
  intro n Y _ _ _ _ _ ι La _ A E U β J hU hβ hJ x hx i hi
  have hne : ∀ (la : La) (s : ι → Y → ℂ), A.IsFrameOn la U s → ∀ y ∈ U,
      y ∈ (A.chart i).source → s i y ≠ 0 := by
    intro la s hs y hyU hyi
    rw [hs.1.2 i (A.pick y) y hyU hyi (A.mem_pick y)]
    exact mul_ne_zero (A.g_ne _ _ _ y hyi (A.mem_pick y)) (hs.2 y hyU)
  have hloc : (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y))) =ᶠ[𝓝 x]
      fun y => A.ph E i y + Real.log (‖J i y * (β i y)⁻¹‖ ^ 2) := by
    filter_upwards [(A.chart i).open_source.mem_nhds hi, hU.mem_nhds hx] with y hyi hyU
    have hp := A.mem_pick y
    have hb := hne _ β hβ y hyU hyi
    have hj := hne _ J hJ y hyU hyi
    have e1 := hyq_nsq_chart A (A.kap + E) β i y hyi (hβ.1.2 i _ y hyU hyi hp)
    have e2 := hyq_nsq_chart A A.kap J i y hyi (hJ.1.2 i _ y hyU hyi hp)
    have hb2 : 0 < ‖β i y‖ ^ 2 := by positivity
    have hj2 : 0 < ‖J i y‖ ^ 2 := by positivity
    rw [e1, e2, A.ph_add A.kap E i y hyi, norm_mul, norm_inv, mul_pow, inv_pow,
      Real.log_mul hb2.ne' (Real.exp_pos _).ne', Real.log_mul hj2.ne' (Real.exp_pos _).ne',
      Real.log_mul hj2.ne' (inv_pos.mpr hb2).ne', Real.log_inv, Real.log_exp, Real.log_exp]
    ring
  have hWo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hU
  have hxW : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  have hc : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hi
  have hT := (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hholo : ∀ (la : La) (s : ι → Y → ℂ), A.IsFrameOn la U s →
      ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ (s i ∘ (A.chart i).symm) v := by
    intro la s hs
    filter_upwards [hWo.mem_nhds hxW] with v hv
    exact (hs.1.1 i v hv).differentiableAt (hWo.mem_nhds hv)
  have hevW : ∀ᶠ v in 𝓝 (A.chart i x), v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    hWo.mem_nhds hxW
  have hqd : ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) v := by
    filter_upwards [hholo _ β hβ, hholo _ J hJ, hevW] with v h1 h2 h3
    have hb := hne _ β hβ _ h3.2 ((A.chart i).map_target h3.1)
    exact h2.mul (h1.inv hb)
  have hq : ContDiffAt ℝ ∞ ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) :=
    hyq_contDiffAt_of_ev hqd
  have hqne : ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simp only [Function.comp, hc]
    exact mul_ne_zero (hne _ J hJ x hx hi) (inv_ne_zero (hne _ β hβ x hx hi))
  have hlog : ContDiffAt ℝ ∞ ((fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i x) :=
    (hq.norm_sq ℝ).log (by positivity)
  have hphE : ContDiffAt ℝ ∞ (A.ph E i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph E i).contDiffAt hT
  have ht : Filter.Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have := ((A.chart i).continuousAt_symm ((A.chart i).map_source hi)).tendsto
    rwa [hc] at this
  refine ⟨?_, fun f hf ξ => ?_⟩
  · refine (hphE.add hlog).congr_of_eventuallyEq ?_
    filter_upwards [ht.eventually hloc] with v hv
    simp only [Function.comp] at hv ⊢
    rw [hv]
  · have hloc' : (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y)
        =ᶠ[𝓝 x] fun y => (A.ph E i y + f y) + Real.log (‖J i y * (β i y)⁻¹‖ ^ 2) := by
      filter_upwards [hloc] with y hy
      rw [hy]; ring
    have hf2 : ContDiffAt ℝ 2 ((fun y => A.ph E i y + f y) ∘ (A.chart i).symm) (A.chart i x) :=
      (hphE.add hf).of_le (WithTop.coe_le_coe.mpr le_top)
    have hg2 : ContDiffAt ℝ 2 ((fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
        (A.chart i x) := hlog.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [leviAt_congr A i _ _ x hi hloc' ξ,
      leviAt_add A i (fun y => A.ph E i y + f y)
        (fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) x hf2 hg2 ξ,
      leviAt_log_normSq A i (fun y => J i y * (β i y)⁻¹) x hi hqd
        (mul_ne_zero (hne _ J hJ x hx hi) (inv_ne_zero (hne _ β hβ x hx hi))) ξ, add_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLinearCombinationZeroLeftAinfFrame
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobComb

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_top_sum {ι : Type} [Fintype ι] (c : ι → B) (g : ι → MvPowerSeries σ Q)
    (hg : ∀ i, In (⊤ : Ideal B) (g i)) :
    In (⊤ : Ideal B) (∑ i, algebraMap B Q (c i) • g i) := by
  choose t ht using fun i => In.top_iff.1 (hg i)
  refine In.top_iff.2 ⟨∑ i, c i • t i, ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ht i, smul_eq_C_mul]

theorem frob_sum (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {ι : Type} [Fintype ι] (c : ι → Q)
    (f : ι → MvPowerSeries σ Q) :
    frob p s (∑ i, c i • f i) = ∑ i, s (c i) • frob p s (f i) := by
  have hX : HasSubst (fun i : σ => (X i : MvPowerSeries σ Q) ^ p) := HasSubst.X_pow hp
  simp only [frob, ← coe_substAlgHom hX, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, map_smul]

end GlobalTheory.FrobComb

open GlobalTheory.FrobComb

theorem GlobalTheory.frob_comb_zero_left : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j))) e) := by
  intro p _ O _ _ _ ε F d k e U he b
  set b' : Fin d ⊕ Fin k → F.B := Sum.elim (fun _ => 0) b with hb'
  set c : Fin d ⊕ Fin k → F.B := fun j => F.σ (b' j) with hc
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have key : ∀ l i, (U * blk d k (p : F.B) 1) l i * c i = U l i * c i := by
    intro l i
    rcases i with i | i
    · simp [hc, hb']
    · simp [blk, Matrix.mul_diagonal]
  have hf : frob p F.s (comb b' e) = ∑ i, algebraMap F.B F.Q (c i) • frob p F.s (e i) := by
    rw [comb, frob_sum p hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [F.s_alg]
  have hsplit : frob p F.s (comb b' e) - comb (U.mulVec c) e =
      ∑ i, algebraMap F.B F.Q (c i) •
        (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
    rw [hf]
    simp only [smul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [comb, Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, ← map_mul,
      map_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c _), key]
  rw [hsplit]
  exact in_top_sum c _ he
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubstMapCongrPowModP
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FrobCong

theorem frobenius_congr (p : ℕ) [hpf : Fact p.Prime] (B : Type) [CommRing B] (σB : B →+* B)
    (hσ : ∀ b, (p : B) ∣ σB b - b ^ p) (d : ℕ) (g : MvPowerSeries (Fin d) B) (α : Fin d →₀ ℕ) :
    (p : B) ∣ coeff α (subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) - g ^ p) := by
  have hp : p ≠ 0 := hpf.out.ne_zero
  set I : Ideal B := Ideal.span {(p : B)} with hI
  set π : B →+* B ⧸ I := Ideal.Quotient.mk I with hπ
  have hsub : subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g)
      = expand p hp (map σB g) := by
    rw [expand, substAlgHom_apply]
  rw [hsub, ← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem, ← hπ,
    ← coeff_map, map_sub, map_pow, map_expand, map_map]
  rcases subsingleton_or_nontrivial (B ⧸ I) with hs | hs
  · exact Subsingleton.elim _ _
  have hp0 : ((p : ℕ) : B ⧸ I) = 0 := by
    have h1 : π (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rwa [map_natCast] at h1
  haveI : CharP (B ⧸ I) p := (CharP.charP_iff_prime_eq_zero hpf.out).2 hp0
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime hpf.out
  have hcomp : π.comp σB = (frobenius (B ⧸ I) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [hcomp, ← map_map, ← map_expand, map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusXiEqPMulUnit
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.QLog.BFrame

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_xi (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.xi ε) = ∑ i ∈ Finset.range p, (1 + Sandwich.mu ε) ^ i := by
  rw [Sandwich.xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, Sandwich.mu,
    add_sub_cancel]
  congr 2
  exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε

theorem one_add_pow {ε : PreTilt O p} (F : BFrame ε) (i : ℕ) :
    (1 + (p : F.B) * F.τ) ^ i = 1 + (i : F.B) * ((p : F.B) * F.τ) := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((n : F.B) * (p : F.B) ^ 2) * F.τ_sq

theorem a_frobenius_xi {ε : PreTilt O p} (F : BFrame ε) :
    F.a (WittVector.frobenius (Sandwich.xi ε)) = p * (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) := by
  rw [frobenius_xi, map_sum]
  have h1 : ∀ i ∈ Finset.range p, F.a ((1 + Sandwich.mu ε) ^ i) = 1 + (i : F.B) * ((p : F.B) * F.τ) :=
    fun i _ => by rw [map_pow, map_add, map_one, ← F.p_τ, one_add_pow]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  have h2 : (∑ i ∈ Finset.range p, (i : F.B)) = ((p.choose 2 : ℕ) : F.B) := by
    rw [← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]
  rw [h2]
  ring

theorem frobenius_xi_unit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∃ u : F.B, IsUnit u ∧ F.τ ∣ u - 1 ∧ F.a (WittVector.frobenius (xi ε)) = p * u := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F
  refine ⟨1 + ((p.choose 2 : ℕ) : F.B) * F.τ, ?_, ⟨((p.choose 2 : ℕ) : F.B), by ring⟩,
    a_frobenius_xi F⟩
  have h : (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) * (1 - ((p.choose 2 : ℕ) : F.B) * F.τ) = 1 := by
    linear_combination (-(((p.choose 2 : ℕ) : F.B)) ^ 2) * F.τ_sq
  exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩

end GlobalTheory.QLog.BFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricSeriesSectionsL2Limit
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2Limit

theorem norm_sub_sq_le (a : ℕ → ℂ) (m k : ℕ) :
    ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m *
      ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
  have htel : a m - a (k + m) = ∑ i ∈ Finset.range k, (a (i + m) - a (i + m + 1)) := by
    have := Finset.sum_range_sub' (fun i => a (i + m)) k
    simp only [zero_add] at this
    rw [← this]; exact Finset.sum_congr rfl fun i _ => by rw [add_right_comm]
  have h1 : ‖a m - a (k + m)‖ ≤ ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ := by
    rw [htel]; exact norm_sum_le _ _
  have hg : ∀ i ∈ Finset.range k, (0:ℝ) < (1/2) ^ (i + m) := fun i _ => by positivity
  have h2 := Finset.sq_sum_div_le_sum_sq_div (Finset.range k)
    (fun i => ‖a (i + m) - a (i + m + 1)‖) hg
  have hsg : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ≤ 2 / 2 ^ m := by
    have : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) =
        (1/2) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
    rw [this]
    have := sum_geometric_two_le k
    have h2m : (0:ℝ) < (1/2) ^ m := by positivity
    calc (1/2:ℝ) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i ≤ (1/2) ^ m * 2 :=
          mul_le_mul_of_nonneg_left this h2m.le
      _ = 2 / 2 ^ m := by rw [one_div_pow]; ring
  have hsum_pos : 0 < ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.sum_pos (fun i hi => hg i hi) ⟨0, by simp [h]⟩)
  rcases hsum_pos with hpos | hk
  · have h3 : (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 ≤
        (∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m)) *
          ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) := by
      rwa [div_le_iff₀ hpos, mul_comm] at h2
    have h4 : ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) =
        ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_div_pow, div_div_eq_mul_div, div_one, mul_comm]
    rw [h4] at h3
    have hn : 0 ≤ ∑ i ∈ Finset.range k, (2:ℝ) ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    calc ‖a m - a (k + m)‖ ^ 2 ≤ (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right hsg hn
  · subst hk; simp

theorem tendsto_of_summable (a : ℕ → ℂ)
    (hs : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2)) :
    ∃ L, Tendsto a atTop (𝓝 L) ∧ ∀ m, ‖a m - L‖ ^ 2 ≤
      2 / 2 ^ m * ∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2 := by
  set c : ℕ → ℝ := fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2 with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  have hfin : ∀ m k, ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m * ∑' i, c (i + m) := by
    intro m k
    refine (norm_sub_sq_le a m k).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Summable.sum_le_tsum _ (fun i _ => hc0 _) ((summable_nat_add_iff m).mpr hs)
  have htail := tendsto_sum_nat_add c
  have hcau : CauchySeq a := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev : ∀ᶠ m in atTop, 2 * ∑' i, c (i + m) < ε ^ 2 := by
      have := htail.const_mul 2
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm⟩ := hev.exists_forall_of_atTop
    refine ⟨m, fun N hN => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, N = k + m := ⟨N - m, by omega⟩
    have h1 := hfin m k
    have h2 : 2 / 2 ^ m * ∑' i, c (i + m) ≤ 2 * ∑' i, c (i + m) := by
      refine mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun i => hc0 _)
      exact div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have h3 : dist (a (k + m)) (a m) ^ 2 < ε ^ 2 := by
      rw [dist_eq_norm, norm_sub_rev]; linarith [hm m le_rfl]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hL, fun m => ?_⟩
  have hlim : Tendsto (fun k => ‖a m - a (k + m)‖ ^ 2) atTop (𝓝 (‖a m - L‖ ^ 2)) :=
    (((hL.comp (tendsto_add_atTop_nat m)).const_sub (a m)).norm).pow 2
  exact le_of_tendsto' hlim fun k => hfin m k

end GlobalTheory.L2Limit

namespace GlobalTheory.L2Limit

section
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

open Classical in

noncomputable def limSec (F : ℕ → ι → Y → ℂ) : ι → Y → ℂ := fun i y =>
  if ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) then limUnder atTop (fun m => F m i y) else 0

theorem limSec_eq (F : ℕ → ι → Y → ℂ) (i : ι) (y : Y) {c : ℂ}
    (h : Tendsto (fun m => F m i y) atTop (𝓝 c)) : limSec F i y = c := by
  unfold limSec; rw [if_pos ⟨c, h⟩]; exact h.limUnder_eq

theorem limSec_trans (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i j : ι) (y : Y) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : limSec F i y = A.g la i j y * limSec F j y := by
  have hg := A.g_ne la i j y hi hj
  have hseq : (fun m => F m i y) = fun m => A.g la i j y * F m j y :=
    funext fun m => (hF m).2 i j y hi hj
  by_cases hc : ∃ c, Tendsto (fun m => F m j y) atTop (𝓝 c)
  · obtain ⟨c, hc⟩ := hc
    rw [limSec_eq F j y hc, limSec_eq F i y (by rw [hseq]; exact hc.const_mul _)]
  · have hc' : ¬ ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) := by
      rintro ⟨c, hc'⟩
      apply hc
      refine ⟨(A.g la i j y)⁻¹ * c, ?_⟩
      have h2 : Tendsto (fun m => A.g la i j y * F m j y) atTop (𝓝 c) := by
        rw [← hseq]; exact hc'
      have := h2.const_mul (A.g la i j y)⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hg] using this
    unfold limSec
    rw [if_neg hc, if_neg hc', mul_zero]

theorem limSec_aemeas (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i : ι) :
    AEMeasurable (limSec F i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target) := by
  classical
  set T := (A.chart i).target with hTdef
  have hT : MeasurableSet T := (A.chart i).open_target.measurableSet
  let G : ℕ → V n → ℂ := fun m => T.piecewise (F m i ∘ (A.chart i).symm) 0
  have hG : ∀ m, StronglyMeasurable (G m) := fun m =>
    (ContinuousOn.measurable_piecewise ((hF m).1 i).continuousOn continuousOn_const
      hT).stronglyMeasurable
  have hS := StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hG
  have hL := StronglyMeasurable.limUnder (l := atTop) hG
  have hmeas : StronglyMeasurable ({v | ∃ c, Tendsto (fun m => G m v) atTop (𝓝 c)}.piecewise
      (fun v => limUnder atTop (fun m => G m v)) (fun _ => (0:ℂ))) :=
    StronglyMeasurable.piecewise hS hL stronglyMeasurable_const
  refine hmeas.measurable.aemeasurable.congr ?_
  refine (ae_restrict_iff' hT).mpr (Eventually.of_forall fun v hv => ?_)
  have hGv : (fun m => G m v) = fun m => F m i ((A.chart i).symm v) :=
    funext fun m => by simp only [G, Set.piecewise_eq_of_mem _ _ _ hv, Function.comp_apply]
  simp only [Set.piecewise, Set.mem_setOf_eq, hGv, Function.comp_apply, limSec]

theorem measurable_step (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (j : ℕ) :
    Measurable (fun y => ENNReal.ofReal (A.nsq la (F j - F (j + 1)) y)) :=
  ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq la (F j - F (j + 1)) (fun i k y hi hk => by
      simp only [Pi.sub_apply]; rw [(hF j).2 i k y hi hk, (hF (j + 1)).2 i k y hi hk]; ring)
    (fun i => ((hF j).1 i).continuousOn.sub ((hF (j + 1)).1 i).continuousOn)).measurable

end

theorem exists_l2_limit : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (F : ℕ → ι → Y → ℂ) (K : ℝ), 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → ∃ f : ι → Y → ℂ, (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g (A.kap + la) i j y * f j y) ∧ (∀ i, AEMeasurable (f i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target)) ∧ ∀ m, n0 A la (F m - f) ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
  intro n Y _ _ _ _ _ ι La _ A la F K hK hF hn
  set L := A.kap + la with hLdef
  set e : ℕ → Y → ℝ≥0∞ := fun j y => ENNReal.ofReal (A.nsq L (F j - F (j + 1)) y) with he_def
  have he : ∀ j, Measurable (e j) := measurable_step A L F hF
  have hint : ∀ j, ∫⁻ y, e j y ∂A.mu ≤ ENNReal.ofReal (K / 4 ^ j) := hn
  set S : ℕ → Y → ℝ≥0∞ := fun m y => ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y with hSdef
  have hSm : ∀ m, Measurable (S m) := fun m =>
    Measurable.ennreal_tsum fun k => measurable_const.mul (he _)
  have hSint : ∀ m, ∫⁻ y, S m y ∂A.mu ≤ ENNReal.ofReal (K / 2 ^ m * 2) := by
    intro m
    show ∫⁻ y, ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu ≤ _
    rw [lintegral_tsum fun k => ((he (k + m)).const_mul _).aemeasurable]
    calc ∑' k, ∫⁻ y, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu
        = ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ∫⁻ y, e (k + m) y ∂A.mu := by
          congr 1; ext k; exact lintegral_const_mul _ (he _)
      _ ≤ ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ENNReal.ofReal (K / 4 ^ (k + m)) :=
          ENNReal.tsum_le_tsum fun k => by gcongr; exact hint _
      _ = ∑' k, ENNReal.ofReal (K / 2 ^ m * (1 / 2) ^ k) := by
          congr 1; ext k
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (4:ℝ) ^ (k + m) = 2 ^ (k + m) * 2 ^ (k + m) by rw [← mul_pow]; norm_num]
          rw [pow_add, one_div_pow]; field_simp
      _ = ENNReal.ofReal (∑' k, K / 2 ^ m * (1 / 2) ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            (summable_geometric_two.mul_left _)).symm
      _ = ENNReal.ofReal (K / 2 ^ m * 2) := by rw [tsum_mul_left, tsum_geometric_two]
  have hfin : ∀ᵐ y ∂A.mu, S 0 y < ⊤ :=
    ae_lt_top (hSm 0) ((hSint 0).trans_lt ENNReal.ofReal_lt_top).ne
  have hpt : ∀ m, ∀ᵐ y ∂A.mu, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ≤
      ENNReal.ofReal (2 / 2 ^ m) * S m y := by
    intro m
    filter_upwards [hfin] with y hy
    set p := A.pick y
    set E := Real.exp (-A.ph L p y) with hE
    have hEpos : 0 < E := Real.exp_pos _
    set a : ℕ → ℂ := fun j => F j p y with ha
    have he_eq : ∀ j, e j y = ENNReal.ofReal (‖a j - a (j + 1)‖ ^ 2 * E) := fun j => rfl
    set b : ℕ → ℝ := fun k => 2 ^ k * (‖a k - a (k + 1)‖ ^ 2 * E) with hb_def
    have hb0 : ∀ k, 0 ≤ b k := fun k => by positivity
    have hSb : ∀ m', S m' y = ∑' k, ENNReal.ofReal (b (k + m')) := by
      intro m'
      simp only [hSdef, he_eq]
      congr 1; ext k
      rw [← ENNReal.ofReal_mul (by positivity)]
    have hb : Summable b := by
      have h0 := hSb 0
      simp only [add_zero] at h0
      have hs := ENNReal.summable_toReal (h0 ▸ hy.ne)
      refine hs.congr fun k => ?_
      exact ENNReal.toReal_ofReal (hb0 k)
    have hb' : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2) := by
      refine (hb.div_const E).congr fun k => ?_
      simp only [hb_def]; field_simp
    obtain ⟨Lm, hLm, hbd⟩ := tendsto_of_summable a hb'
    have hf : limSec F p y = Lm := limSec_eq F p y hLm
    have hnsq : A.nsq L (F m - limSec F) y = ‖a m - Lm‖ ^ 2 * E := by
      show ‖F m p y - limSec F p y‖ ^ 2 * E = _
      rw [hf]
    rw [hnsq, hSb m, ← ENNReal.ofReal_tsum_of_nonneg (fun k => hb0 _)
      ((summable_nat_add_iff m).mpr hb), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right (hbd m) hEpos.le
    calc ‖a m - Lm‖ ^ 2 * E
        ≤ 2 / 2 ^ m * (∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2) * E := this
      _ = 2 / 2 ^ m * ∑' k, b (k + m) := by
          rw [mul_assoc, ← tsum_mul_right]
          congr 2; ext k; simp only [hb_def]; ring
  refine ⟨limSec F, fun i j y hi hj => limSec_trans A L F hF i j y hi hj,
    fun i => limSec_aemeas A L F hF i, fun m => ?_⟩
  calc n0 A la (F m - limSec F) = ∫⁻ y, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ∂A.mu := rfl
    _ ≤ ∫⁻ y, ENNReal.ofReal (2 / 2 ^ m) * S m y ∂A.mu := lintegral_mono_ae (hpt m)
    _ = ENNReal.ofReal (2 / 2 ^ m) * ∫⁻ y, S m y ∂A.mu := lintegral_const_mul _ (hSm m)
    _ ≤ ENNReal.ofReal (2 / 2 ^ m) * ENNReal.ofReal (K / 2 ^ m * 2) := by gcongr; exact hSint m
    _ = ENNReal.ofReal (4 * K / 4 ^ m) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (4:ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
      field_simp; ring

end GlobalTheory.L2Limit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDatumBiconnOf
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem hasDatum_biconn_of (hfr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), Nonempty (BFrame ε))
    (hmat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConn G → IsConn G.dual → ∀ F : BFrame ε, ∃ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin G.height) F.B) (Gm : Matrix (Fin G.height) (Fin d ⊕ Fin k) F.B) (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie), d + k = G.height ∧ IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin G.height) (Fin G.height) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) ∧ (∀ j m, F.θ (Y (Sum.inr j) m) = lb j (hodgeTate G (tb m))) ∧ ∀ m, dlog G (χ m) = ∑ i, F.θ (Gm m (Sum.inl i)) • w i)
    (hlift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i))
    (hfin : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (d k : ℕ), d + k = G.height → ∀ (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie) (Fa : Matrix (Fin d ⊕ Fin k) (Fin G.height) (Ainf p O)) (Ga : Matrix (Fin G.height) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin G.height) (Fin G.height) (Ainf p O)) → Fa = Ψ * Fa.map (phiInv p O) → Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) → (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) → (∀ i m, WittVector.fontaineTheta O p (Fa (Sum.inl i) m) = 0) → (∀ j m, WittVector.fontaineTheta O p (Fa (Sum.inr j) m) = lb j (hodgeTate G (tb m))) → (∀ m j, WittVector.fontaineTheta O p (Ga m (Sum.inr j)) = 0) → (∀ m, dlog G (χ m) = ∑ i, WittVector.fontaineTheta O p (Ga m (Sum.inl i)) • w i) → HasDatum hε G) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConn G → IsConn G.dual → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG hD
  obtain ⟨F⟩ := hfr p C v O hv ε hε
  obtain ⟨d, k, U, Y, Gm, tb, χ, w, lb, hdk, hU, hY, hGm, hGY, hY0, hG0, hn1, hn2, hpair, hYl, hdl⟩ :=
    hmat p C v O hv ε hε G hG hD F
  obtain ⟨Fa, Ga, Ψ, Ψ', h1, h2, h3, h4, h5⟩ :=
    hlift p C v O hv ε hε F d k G.height U Y Gm ⟨hU, hY, hGm, hGY, hY0, hG0, hn1, hn2⟩
  refine hfin p C v O hv ε hε G d k hdk tb χ w lb Fa Ga Ψ Ψ' h1 h2 h3 hpair
    (fun i m => (h4 _ _).trans (hY0 i m)) (fun j m => (h4 _ _).trans (hYl j m))
    (fun m j => (h5 _ _).trans (hG0 m j)) (fun m => ?_)
  rw [hdl m]
  exact Finset.sum_congr rfl fun i _ => by rw [h5]

end GlobalTheory.PDivLat
end
end


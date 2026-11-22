import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.ExistsDominantSubSmul
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Filter Topology

theorem exists_dominant_sub_smul (d : IndexData) (u w : Idx d → ℚ) (hu : IsRegular d (uR d u)) :
    ∃ s1 : ℝ, 0 < s1 ∧ ∀ s : ℚ, 0 < s → (s : ℝ) ≤ s1 → IsDominant d (uR d (u - s • w)) := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 →
      0 < ((u (τ, a) : ℝ) - u (τ, b)) - t * ((w (τ, a) : ℝ) - w (τ, b)) := by
    rw [Filter.eventually_all]; intro τ
    rw [Filter.eventually_all]; intro a
    rw [Filter.eventually_all]; intro b
    by_cases hab : b.val = a.val + 1
    · have hpos : (0 : ℝ) < (u (τ, a) : ℝ) - u (τ, b) := hu τ a b hab
      have hc : Continuous fun t : ℝ =>
          ((u (τ, a) : ℝ) - u (τ, b)) - t * ((w (τ, a) : ℝ) - w (τ, b)) := by
        fun_prop
      have h0 : (0 : ℝ) <
          (fun t : ℝ => ((u (τ, a) : ℝ) - u (τ, b)) - t * ((w (τ, a) : ℝ) - w (τ, b))) 0 := by
        simpa using hpos
      filter_upwards [(hc.tendsto 0).eventually (lt_mem_nhds h0)] with t ht _ using ht
    · exact Filter.Eventually.of_forall fun _ h => absurd h hab
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε / 2, by positivity, fun s hs hsle τ a b hab => ?_⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hd : dist (s : ℝ) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs']
    linarith
  have key := hball hd τ a b hab
  simp only [uR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  linarith

theorem TheoremTLower.proof (hL : LimitTheorem.Statement) : TheoremTLower.Statement := by
  intro d S u g B0 hyp _ hI1 hI2
  obtain ⟨C3, s0, hs0, hb⟩ := hI2
  obtain ⟨s1, hs1, hdom⟩ := exists_dominant_sub_smul d u S.shiftW hyp.1
  have key := hL (Idx d) (S.Ptwo B0) (fun p => (u p : ℝ)) (fun p => (S.shiftW p : ℝ))
    (S.Mbar B0 u) C3 (min s0 s1) (lt_min hs0 hs1) (by
      intro s hs hsle
      have h := hb s hs (le_trans hsle (min_le_left _ _))
        (hdom s hs (le_trans hsle (min_le_right _ _)))
      have hfun : (fun o : Option (Idx d) => o.elim (s : ℝ) (fun p => ((u - s • S.shiftW) p : ℝ))) =
          (fun o : Option (Idx d) => o.elim (s : ℝ) (fun p => (u p : ℝ) - s * (S.shiftW p : ℝ))) := by
        funext o
        cases o with
        | none => rfl
        | some p => simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rwa [hfun] at h)
  unfold bigP
  rw [← hI1 u]
  exact key

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.ImportsAlt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Filter Topology

theorem LimitTheorem.proof : LimitTheorem.Statement := by
  intro σ _ Pt u w M C3 s0 hs0 hM
  set g : ℚ → ℝ := fun s => eval (fun o : Option σ => o.elim (s : ℝ) (fun p => u p - s * w p)) Pt
    with hg
  have hgc : Continuous g := by
    refine (MvPolynomial.continuous_eval Pt).comp ?_
    refine continuous_pi fun o => ?_
    rcases o with _ | p
    · exact Rat.continuous_coe_real
    · exact continuous_const.sub (Rat.continuous_coe_real.mul continuous_const)
  have hg0 : g 0 = eval (fun o : Option σ => o.elim (0 : ℝ) u) Pt := by
    simp only [hg]
    congr 2
    funext o
    rcases o with _ | p <;> simp
  have h1 : Tendsto g (𝓝[>] (0 : ℚ)) (𝓝 (g 0)) :=
    (hgc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hC : Tendsto (fun s : ℚ => C3 * (s : ℝ)) (𝓝[>] (0 : ℚ)) (𝓝 0) := by
    have h : Tendsto (fun s : ℚ => C3 * (s : ℝ)) (𝓝 (0 : ℚ)) (𝓝 (C3 * ((0 : ℚ) : ℝ))) :=
      (continuous_const.mul Rat.continuous_coe_real).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hlt : ∀ᶠ s : ℚ in 𝓝 (0 : ℚ), (s : ℝ) < s0 := by
    have h : Tendsto (fun s : ℚ => (s : ℝ)) (𝓝 (0 : ℚ)) (𝓝 ((0 : ℚ) : ℝ)) :=
      Rat.continuous_coe_real.tendsto 0
    rw [Rat.cast_zero] at h
    exact h.eventually (gt_mem_nhds hs0)
  have hev : ∀ᶠ s : ℚ in 𝓝[>] (0 : ℚ), ‖M s - g s‖ ≤ C3 * (s : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hlt] with s hs hs'
    rw [Real.norm_eq_abs]
    exact hM s hs hs'.le
  have h2 : Tendsto (fun s => M s - g s) (𝓝[>] (0 : ℚ)) (𝓝 0) := squeeze_zero_norm' hev hC
  rw [← hg0]
  simpa using h1.add h2

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PCBounds
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

theorem dominant_antitone (d : IndexData) (u : Weight d) (hu : IsDominant d u) (τ : Fin d.f) :
    ∀ i l : Fin d.N, i.val ≤ l.val → u (τ, l) ≤ u (τ, i) := by
  have key : ∀ k : ℕ, ∀ i l : Fin d.N, l.val = i.val + k → u (τ, l) ≤ u (τ, i) := by
    intro k
    induction k with
    | zero =>
      intro i l h
      have : l = i := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro i l h
      have hm : i.val + k < d.N := by have := l.isLt; omega
      let m : Fin d.N := ⟨i.val + k, hm⟩
      have h1 : u (τ, l) ≤ u (τ, m) := by
        have := hu τ m l (by simp [m]; omega)
        linarith
      have h2 : u (τ, m) ≤ u (τ, i) := ih i m rfl
      linarith
  intro i l h
  exact key (l.val - i.val) i l (by omega)

theorem CBounds.proof : CBounds.Statement := by
  intro d u hu τ

  set S : ℝ := ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i) with hS
  set T : ℝ := ∑ i ∈ univ.filter (fun i : Fin d.N => ¬ i.val < d.j), u (τ, i) with hT
  set P : ℝ := ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), |u (τ, i)| with hP
  set R : ℝ := ∑ i ∈ univ.filter (fun i : Fin d.N => ¬ i.val < d.j), |u (τ, i)| with hR
  have hsum : ∑ i : Fin d.N, u (τ, i) = S + T :=
    (sum_filter_add_sum_filter_not univ (fun i : Fin d.N => i.val < d.j) _).symm
  have habs : ∑ i : Fin d.N, |u (τ, i)| = P + R :=
    (sum_filter_add_sum_filter_not univ (fun i : Fin d.N => i.val < d.j) _).symm
  have hN : (0 : ℝ) < d.N := by have := d.two_le_N; positivity
  have hjN : (d.j : ℝ) ≤ d.N := by exact_mod_cast d.j_lt_N.le
  have hj0 : (0 : ℝ) ≤ d.j := by positivity

  have hcard1 : ((univ.filter (fun i : Fin d.N => i.val < d.j)).card : ℝ) = d.j := by
    have := Fin.card_filter_val_lt (n := d.N) (m := d.j)
    rw [this, min_eq_right d.j_lt_N.le]
  have hcard2 : ((univ.filter (fun i : Fin d.N => ¬ i.val < d.j)).card : ℝ) = d.N - d.j := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin d.N)))
      (fun i : Fin d.N => i.val < d.j)
    rw [card_univ, Fintype.card_fin] at h
    have h' : ((univ.filter (fun i : Fin d.N => i.val < d.j)).card : ℝ) +
        ((univ.filter (fun i : Fin d.N => ¬ i.val < d.j)).card : ℝ) = d.N := by
      exact_mod_cast h
    linarith
  have hc : cTau d u τ = S - (d.j : ℝ) * ((1 / (d.N : ℝ)) * (S + T)) := by
    simp only [cTau, ubar, hsum]
    rfl

  have hSP : S ≤ P := sum_le_sum (fun i _ => le_abs_self _)
  have hTR : -T ≤ R := by
    rw [hT, ← sum_neg_distrib]
    exact sum_le_sum (fun i _ => neg_le_abs _)
  have hP0 : 0 ≤ P := sum_nonneg (fun i _ => abs_nonneg _)
  have hR0 : 0 ≤ R := sum_nonneg (fun i _ => abs_nonneg _)
  set r : ℝ := (d.j : ℝ) * (1 / (d.N : ℝ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, mul_one_div, div_le_one hN]; exact hjN
  have hc' : cTau d u τ = (1 - r) * S - r * T := by rw [hc, hr]; ring
  refine ⟨?_, ?_⟩
  ·
    let v : Fin d.N := ⟨d.j, d.j_lt_N⟩
    have hmono := dominant_antitone d u hu τ
    have hS1 : (d.j : ℝ) * u (τ, v) ≤ S := by
      rw [← hcard1, ← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum (fun i hi => ?_)
      have hi' : i.val < d.j := (mem_filter.mp hi).2
      exact hmono i v (by simp [v]; omega)
    have hT1 : T ≤ ((d.N : ℝ) - d.j) * u (τ, v) := by
      rw [← hcard2, ← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum (fun i hi => ?_)
      have hi' : ¬ i.val < d.j := (mem_filter.mp hi).2
      exact hmono v i (by simp [v]; omega)
    have hNc : (d.N : ℝ) * cTau d u τ = ((d.N : ℝ) - d.j) * S - (d.j : ℝ) * T := by
      rw [hc]; field_simp; ring
    have h0 : 0 ≤ ((d.N : ℝ) - d.j) * S - (d.j : ℝ) * T := by
      have hNj : 0 ≤ (d.N : ℝ) - d.j := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hS1 hNj, mul_le_mul_of_nonneg_left hT1 hj0]
    rw [← hNc] at h0
    by_contra hneg
    have hneg' : cTau d u τ < 0 := lt_of_not_ge hneg
    linarith [mul_neg_of_pos_of_neg hN hneg']
  · rw [hc', habs]
    nlinarith [mul_le_mul_of_nonneg_left hSP (by linarith : (0 : ℝ) ≤ 1 - r),
      mul_le_mul_of_nonneg_left hTR hr0, mul_nonneg hr0 hP0, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - r) hR0]

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PCFlPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem coeff_polarPoly {σ R : Type*} [CommRing R] [Fintype σ] (Φ : MvPolynomial σ R →ₗ[R] R)
    (n : ℕ) (m : σ →₀ ℕ) : coeff m (polarPoly Φ n) = Φ (coeff m ((-outerDot σ R) ^ n)) := by
  classical
  unfold polarPoly
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

theorem coeff_neg_outerDot_pow (σ : Type*) [Fintype σ] (m : σ →₀ ℕ) (n : ℕ) :
    coeff m ((-outerDot σ ℚ) ^ n) =
      if m.sum (fun _ e => e) = n then monomial m ((-1) ^ n * (m.multinomial : ℚ)) else 0 := by
  have hdot : outerDot σ ℚ =
      ∑ v, (X v : MvPolynomial σ ℚ) • (X v : MvPolynomial σ (MvPolynomial σ ℚ)) := by
    unfold outerDot
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_eq_C_mul, mul_comm]
  have hneg : (-outerDot σ ℚ) ^ n = C ((-1) ^ n) * outerDot σ ℚ ^ n := by
    rw [show (C ((-1 : MvPolynomial σ ℚ) ^ n) : MvPolynomial σ (MvPolynomial σ ℚ)) = (-1) ^ n by
      simp]
    exact neg_pow (outerDot σ ℚ) n
  rw [hneg, coeff_C_mul, hdot, coeff_linearCombination_X_pow_of_fintype]
  split_ifs with h
  · rw [monomial_eq, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  · rw [mul_zero]

theorem flagIntegral_monomial (f N : ℕ) (m : Fin f × Fin N →₀ ℕ) :
    RestTerms.flagIntegral f N (monomial m 1) =
      coeff m (RestTerms.blockVandermonde f N) * m.prod (fun _ e => (e.factorial : ℚ)) := by
  classical
  unfold RestTerms.flagIntegral
  rw [Finset.sum_eq_single m]
  · rw [coeff_monomial, if_pos rfl, one_mul]
  · intro b _ hb
    rw [coeff_monomial, if_neg (Ne.symm hb), zero_mul, zero_mul]
  · intro hm
    rw [MvPolynomial.notMem_support_iff.mp hm, coeff_monomial, if_pos rfl]
    ring

theorem prod_factorial_mul_multinomial {σ : Type*} (m : σ →₀ ℕ) :
    (m.prod (fun _ e => (e.factorial : ℚ))) * (m.multinomial : ℚ) =
      ((m.sum fun _ e => e).factorial : ℚ) := by
  rw [Finsupp.multinomial_eq]
  have := Nat.multinomial_spec m.support m
  unfold Finsupp.prod Finsupp.sum
  dsimp only
  exact_mod_cast this

theorem degPoly_eq (d : IndexData) :
    degPoly d = C (((d.D).factorial : ℚ) / (∏ i : Fin d.N, ((i : ℕ).factorial : ℚ)) ^ d.f) *
      RestTerms.blockVandermonde d.f d.N := by
  ext m
  rw [coeff_C_mul, degPoly, coeff_polarPoly, coeff_neg_outerDot_pow]
  split_ifs with h
  · rw [← mul_one ((-1) ^ d.D * (m.multinomial : ℚ)), ← smul_eq_mul, ← smul_monomial,
      map_smul, intFl, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    change _ * (flagNormalisation d.f d.N * RestTerms.flagIntegral d.f d.N (monomial m 1)) = _
    rw [flagIntegral_monomial, flagNormalisation]
    have hf := prod_factorial_mul_multinomial m
    rw [h] at hf
    have hD : d.D = RestTerms.topDegree d.f d.N := rfl
    rw [← hf, ← hD]
    have hP : (∏ i : Fin d.N, ((i : ℕ).factorial : ℚ)) ^ d.f ≠ 0 := by positivity
    field_simp
    have h1 : ((-1 : ℚ) ^ d.D) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h1, one_mul]
  · rw [map_zero]
    have hom := RestTerms.FlagVandermondeHomogeneous.proof d.f d.N
    rw [hom.coeff_eq_zero, mul_zero]
    intro hdeg
    apply h
    change _ = RestTerms.topDegree _ _
    rw [← hdeg]
    rfl

theorem CFlPos.proof : CFlPos.Statement := fun d =>
  ⟨_, by positivity, degPoly_eq d⟩

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PKaPBound
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem rankLie_bounds (d : IndexData) (e : Emb d) :
    1 ≤ (rankLie d e : ℝ) ∧ (rankLie d e : ℝ) ≤ d.N := by
  have h1 := d.one_le_j
  have h2 := d.j_lt_N
  unfold rankLie
  split_ifs
  · constructor
    · exact_mod_cast (by omega : 1 ≤ d.N - d.j)
    · exact_mod_cast (by omega : d.N - d.j ≤ d.N)
  · constructor
    · exact_mod_cast h1
    · exact_mod_cast h2.le

theorem geom_succ_inv (p : ℕ) (hp : 2 ≤ p) :
    HasSum (fun n : ℕ => ((p : ℝ) ^ (n + 1))⁻¹) (1 / ((p : ℝ) - 1)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (p : ℝ)⁻¹
  have hfun : (fun n : ℕ => (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ n) = fun n : ℕ => ((p : ℝ) ^ (n + 1))⁻¹ := by
    funext n
    rw [← inv_pow, pow_succ, mul_comm]
  rw [hfun] at h
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hsub : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  have hv : (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ = 1 / ((p : ℝ) - 1) := by
    rw [hsub, inv_div, ← mul_div_assoc, inv_mul_cancel₀ hp0]
  rw [hv] at h
  exact h

theorem KaPBound.proof : KaPBound.Statement := by
  intro d p φ hp _ τ
  have hp2 := hp.two_le
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hg := geom_succ_inv p hp2
  set a : ℕ → ℝ := fun n => ((p : ℝ) ^ (n + 1))⁻¹ with ha
  set r : ℕ → ℝ := fun n => (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ) with hr
  have ha0 : ∀ n, 0 < a n := fun n => inv_pos.mpr (pow_pos (by linarith) _)
  have hterm0 : ∀ n, 0 ≤ a n * r n := fun n =>
    mul_nonneg (ha0 n).le (by linarith [(rankLie_bounds d ((φ ^ (n + 1)) (τ, false))).1])
  have htermle : ∀ n, a n * r n ≤ (d.N : ℝ) * a n := fun n => by
    rw [mul_comm (d.N : ℝ)]
    exact mul_le_mul_of_nonneg_left (rankLie_bounds d ((φ ^ (n + 1)) (τ, false))).2 (ha0 n).le
  have hNs : HasSum (fun n => (d.N : ℝ) * a n) ((d.N : ℝ) * (1 / ((p : ℝ) - 1))) := hg.mul_left _
  have hsum : Summable (fun n => a n * r n) :=
    Summable.of_nonneg_of_le hterm0 htermle hNs.summable
  have hk : kaP d p φ τ = ∑' n, a n * r n := rfl
  rw [hk]
  constructor
  · have h0 : 0 < a 0 * r 0 :=
      mul_pos (ha0 0) (by linarith [(rankLie_bounds d ((φ ^ (0 + 1)) (τ, false))).1])
    exact hsum.tsum_pos hterm0 0 h0
  · calc ∑' n, a n * r n ≤ ∑' n, (d.N : ℝ) * a n := hsum.tsum_le_tsum htermle hNs.summable
      _ = (d.N : ℝ) * (1 / ((p : ℝ) - 1)) := hNs.tsum_eq
      _ = (d.N : ℝ) / ((p : ℝ) - 1) := by ring

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PKaPInert
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

theorem inertFrob_snd {d : IndexData} {φ : Equiv.Perm (Emb d)} (hφ : IsFrobLike d φ)
    (hi : IsInertFrob d φ) (e : Emb d) : (φ e).2 = !e.2 := by
  obtain ⟨σ, b⟩ := e
  cases b with
  | false => simpa using hi σ
  | true =>
    have h := hφ.1 (σ, false)
    have hc : conjEmb d (σ, false) = (σ, true) := rfl
    rw [hc] at h
    rw [h]
    simp [conjEmb, hi σ]

theorem inertFrob_pow_snd {d : IndexData} {φ : Equiv.Perm (Emb d)} (hφ : IsFrobLike d φ)
    (hi : IsInertFrob d φ) (e : Emb d) (n : ℕ) : ((φ ^ n) e).2 = (e.2 ^^ decide (Odd n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, inertFrob_snd hφ hi, ih]
    cases e.2 <;> by_cases h : Odd n <;> simp [h, Nat.odd_add_one]

theorem rankLie_inert_pow {d : IndexData} {φ : Equiv.Perm (Emb d)} (hφ : IsFrobLike d φ)
    (hi : IsInertFrob d φ) (τ : Fin d.f) (n : ℕ) :
    rankLie d ((φ ^ (n + 1)) (τ, false)) = if Odd n then d.j else d.N - d.j := by
  unfold rankLie
  rw [inertFrob_pow_snd hφ hi]
  by_cases h : Odd n <;> simp [h, Nat.odd_add_one]

theorem KaPInert.proof : KaPInert.Statement := by
  intro d p φ hp hφ hi τ
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set r : ℝ := ((p : ℝ) ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  set a : ℝ := ((d.N - d.j : ℕ) : ℝ)
  set t : ℕ → ℝ := fun n => ((p : ℝ) ^ (n + 1))⁻¹ * (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ)
  have heven : ∀ k, t (2 * k) = (a / p) * r ^ k := by
    intro k
    simp only [t, rankLie_inert_pow hφ hi, hr, a]
    have : ¬ Odd (2 * k) := by simp
    rw [if_neg this, inv_pow, ← pow_mul, pow_succ]
    field_simp
  have hodd : ∀ k, t (2 * k + 1) = ((d.j : ℝ) / p ^ 2) * r ^ k := by
    intro k
    simp only [t, rankLie_inert_pow hφ hi, hr]
    have : Odd (2 * k + 1) := odd_two_mul_add_one k
    rw [if_pos this, inv_pow, ← pow_mul, show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add]
    field_simp
  have hg : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hse : Summable (fun k => t (2 * k)) := by
    simp_rw [heven]; exact hg.mul_left _
  have hso : Summable (fun k => t (2 * k + 1)) := by
    simp_rw [hodd]; exact hg.mul_left _
  have hsum : kaP d p φ τ = ∑' k, t (2 * k) + ∑' k, t (2 * k + 1) :=
    (tsum_even_add_odd hse hso).symm
  rw [hsum]
  simp_rw [heven, hodd]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, hr]
  have hp2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp2' : (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 := by
    field_simp
  rw [hp2']
  field_simp

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PKaPSplit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem KaPSplit.proof : KaPSplit.Statement := by
  intro d p φ hp _ hs τ
  have h2 : ∀ n : ℕ, ((φ ^ (n + 1)) (τ, false)).2 = false := by
    intro n
    induction n with
    | zero => simpa using hs τ
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have e : (φ ^ (n + 1)) (τ, false) = (((φ ^ (n + 1)) (τ, false)).1, false) :=
        Prod.ext rfl ih
      rw [e]
      exact hs _
  have hterm : ∀ n : ℕ, ((p : ℝ) ^ (n + 1))⁻¹ * (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ) =
      (d.j : ℝ) * ((p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n) := by
    intro n
    simp only [rankLie, h2 n, Bool.false_eq_true, if_false]
    rw [pow_succ, mul_inv, inv_pow]
    ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  unfold kaP
  rw [tsum_congr hterm, tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have e1 : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [e1]
  field_simp

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTermA
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem TermA.proof : TermA.Statement := by
  intro d S hI9 u hu
  exact mul_nonneg S.vol_pos.le (hI9 u hu).1

end GroundTheory.Heights₂.Heights.TheoremB
end


import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.SingleDecompIsHomDecomp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

def singleDecomp (d : IndexData) (τ : Fin d.f) (Q : XPoly d) : ℕ → Fin d.f → XPoly d :=
  fun k σ => if k = 1 then (if σ = τ then Q else 0) else 0

theorem singleDecomp_isHomDecomp (d : IndexData) (τ : Fin d.f) (Q : XPoly d)
    (hQ : Q.IsHomogeneous d.D) :
    IsHomDecomp d (RestTerms.blockPowerSum d.f d.N 1 τ * Q) (singleDecomp d τ Q) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp : (RestTerms.blockPowerSum d.f d.N 1 τ).IsHomogeneous 1 := by
      unfold RestTerms.blockPowerSum
      exact IsHomogeneous.sum _ _ _ (fun i _ => by simpa using isHomogeneous_X ℚ (τ, i))
    simpa [add_comm] using hp.mul hQ
  · intro k hk σ
    unfold singleDecomp
    split_ifs with h1 h2
    · subst h1; simpa using hQ
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_zero _ _ _
  · unfold RestTerms.IsPowerSumDecomposition singleDecomp
    have h1 : 1 ∈ Icc 1 d.N := by
      have := d.two_le_N
      simp; omega
    rw [Finset.sum_eq_single_of_mem 1 h1]
    · simp
    · intro k _ hk
      simp [hk]

theorem restTot_singleDecomp (d : IndexData) (S : EndSystem d) (B0 : ℕ) (τ : Fin d.f)
    (Q : XPoly d) : restTot S B0 (singleDecomp d τ Q) = 0 := by
  unfold restTot rest₂
  have h : ∀ (p : ℕ) (σ : Fin d.f), ∑ k ∈ Icc 2 d.N,
      ∑' n : ℕ, restSeries d p (S.frob p) (singleDecomp d τ Q) σ k n = 0 := by
    intro p σ
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hk1 : k ≠ 1 := by
      simp at hk; omega
    have : ∀ n, restSeries d p (S.frob p) (singleDecomp d τ Q) σ k n = 0 := by
      intro n
      simp [restSeries, singleDecomp, hk1]
    simp [this]
  simp [h]

theorem card_lowerIdx_filter (d : IndexData) :
    (univ.filter (fun i : Fin d.N => i.val < d.j)).card = d.j := by
  have := d.j_lt_N
  rw [Fin.card_filter_val_lt]
  omega

theorem HeightLimitIdentity.proof (h83 : HeightTauIdentity.Statement) (hSh : ShFormula.Statement)
    (hTot : TotFormula.Statement) : HeightLimitIdentity.Statement := by
  intro d S hI hH B0 A0 b0 hA hb τ Q hQ hint
  set F := RestTerms.blockPowerSum d.f d.N 1 τ * Q with hF
  have hdec := singleDecomp_isHomDecomp d τ Q hQ
  have key := h83 d S hI B0 A0 b0 hA hb F (singleDecomp d τ Q) hdec
  rw [restTot_singleDecomp, hH τ Q hQ] at key
  have hsh : shSum d F = d.j := by
    unfold shSum
    rw [Finset.sum_eq_single τ]
    · rw [hSh d τ F _ hdec.1 hdec.2.1 hdec.2.2]
      have h1 : 1 ∈ Icc 1 d.N := by
        have := d.two_le_N
        simp; omega
      rw [Finset.sum_eq_single_of_mem 1 h1]
      · have hl : lowerPowerSum d (1 - 1) τ = (d.j : XPoly d) := by
          simp [lowerPowerSum, card_lowerIdx_filter]
        have hj : ((d.j : XPoly d)) * Q = d.j • Q := (nsmul_eq_mul _ _).symm
        simp only [singleDecomp, if_true, Nat.cast_one, one_mul, hl, hj, map_nsmul, hint]
        simp
      · intro k _ hk
        simp [singleDecomp, hk]
    · intro σ _ hσ
      rw [hSh d σ F _ hdec.1 hdec.2.1 hdec.2.2]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      simp [singleDecomp, hσ]
    · simp
  have htot : totSum d F = d.N := by
    unfold totSum
    rw [Finset.sum_eq_single τ]
    · rw [hTot d τ F _ hdec.1 hdec.2.1 hdec.2.2]
      simp [singleDecomp, hint]
    · intro σ _ hσ
      rw [hTot d σ F _ hdec.1 hdec.2.1 hdec.2.2]
      simp [singleDecomp, hσ]
    · simp
  rw [hsh, htot] at key
  have hv := S.vol_pos
  rw [key]
  push_cast
  field_simp
  ring

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.TauSumRearrangement
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem tauSum_rearrangement {ι : Type*} (s : Finset ι) (a c e : ℝ) (al be sh tot : ι → ℝ) :
    ∑ τ ∈ s, (((a - al τ) - (c - be τ)) * sh τ + (e - be τ) * tot τ) =
      (a - c) * ∑ τ ∈ s, sh τ + e * ∑ τ ∈ s, tot τ - ∑ τ ∈ s, (al τ - be τ) * sh τ -
        ∑ τ ∈ s, be τ * tot τ := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun τ _ => by ring

theorem HeightSumIdentity.proof : HeightSumIdentity.Statement := by
  intro d S hS B0
  obtain ⟨B1, CE, hcor⟩ := hS.corB
  obtain ⟨CA, hA⟩ := hS.propA
  refine ⟨max B1 2, fun F Q hFQ => ?_⟩
  have hF : F.IsHomogeneous (d.D + 1) := hFQ.1
  refine ⟨S.vol * ((∑ τ : Fin d.f, (2 * |(shiftFl d τ F : ℝ)| + |(totalFl d τ F : ℝ)|)) * CA) +
      (∑ m ∈ F.support, |((F.coeff m : ℚ) : ℝ)|) * CE, fun B hB0 hB => ?_⟩
  have hB1 : B1 ≤ B := le_of_max_le_left hB
  have hB2 : 2 ≤ B := le_of_max_le_right hB

  have hadd := hS.additivity B0 B hB0 F hF
  have hsum : ∑ p ∈ primesIn S B0 B, S.delta p F =
      -(∑ p ∈ primesIn S B0 B, Real.log p / ((p : ℝ) - 1)) * S.vol * (shSum d F : ℝ) +
        (∑ p ∈ primesIn S B0 B, kaNum S p * Real.log p) / (d.N : ℝ) * S.vol * (totSum d F : ℝ) +
        ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q := by
    rw [Finset.sum_congr rfl (fun p hp => by
      simp only [primesIn, Finset.mem_filter] at hp
      exact hS.eq81 p hp.2.1 hp.2.2 F Q hFQ)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_mul, Finset.sum_div, Finset.sum_neg_distrib, neg_mul]
  have hcorB := (hcor B hB1).1 F hF
  have key : S.PP B0 F - (S.vol * (S.hh F - aB S B0 B * (shSum d F : ℝ) -
        bB S B0 B * (totSum d F : ℝ)) + ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q) =
      S.vol * ∑ τ : Fin d.f, (((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) *
          (shiftFl d τ F : ℝ) + (S.beC B - S.be B τ) * (totalFl d τ F : ℝ)) + S.EE B F := by
    rw [tauSum_rearrangement, hadd, hsum, hcorB]
    simp only [aB, bB, shSum, totSum, Rat.cast_sum]
    ring
  rw [key]
  have hL0 : 0 ≤ Real.log B / B := div_nonneg (Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ B by omega))) (Nat.cast_nonneg B)
  have hT : |∑ τ : Fin d.f, (((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) *
        (shiftFl d τ F : ℝ) + (S.beC B - S.be B τ) * (totalFl d τ F : ℝ))| ≤
      (∑ τ : Fin d.f, (2 * |(shiftFl d τ F : ℝ)| + |(totalFl d τ F : ℝ)|)) * CA *
        (Real.log B / B) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => ?_
    obtain ⟨ha, hb⟩ := hA B hB2 τ
    have h1 : |S.alC B - S.al B τ| ≤ CA * (Real.log B / B) := by
      rw [abs_sub_comm, ← mul_div_assoc]; exact ha
    have h2 : |S.beC B - S.be B τ| ≤ CA * (Real.log B / B) := by
      rw [abs_sub_comm, ← mul_div_assoc]; exact hb
    calc _ ≤ |((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) * (shiftFl d τ F : ℝ)| +
          |(S.beC B - S.be B τ) * (totalFl d τ F : ℝ)| := abs_add_le _ _
      _ = |(S.alC B - S.al B τ) - (S.beC B - S.be B τ)| * |(shiftFl d τ F : ℝ)| +
          |S.beC B - S.be B τ| * |(totalFl d τ F : ℝ)| := by rw [abs_mul, abs_mul]
      _ ≤ (|S.alC B - S.al B τ| + |S.beC B - S.be B τ|) * |(shiftFl d τ F : ℝ)| +
          |S.beC B - S.be B τ| * |(totalFl d τ F : ℝ)| := by gcongr; exact abs_sub _ _
      _ ≤ (CA * (Real.log B / B) + CA * (Real.log B / B)) * |(shiftFl d τ F : ℝ)| +
          CA * (Real.log B / B) * |(totalFl d τ F : ℝ)| := by gcongr
      _ = _ := by ring
  have hEE : |S.EE B F| ≤ (∑ m ∈ F.support, |((F.coeff m : ℚ) : ℝ)|) * CE * (Real.log B / B) := by
    conv_lhs => rw [F.as_sum]
    rw [map_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    have hdeg : (m.sum fun _ e => e) = d.D + 1 := by
      have := hF (mem_support_iff.mp hm)
      simpa [Finsupp.weight_apply] using this
    have hmono := (hcor B hB1).2 m hdeg
    rw [show monomial m (F.coeff m) = (F.coeff m) • monomial m (1 : ℚ) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, Rat.smul_def, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [← mul_div_assoc]; exact hmono) (abs_nonneg _)
  calc _ ≤ |S.vol * ∑ τ : Fin d.f, (((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) *
          (shiftFl d τ F : ℝ) + (S.beC B - S.be B τ) * (totalFl d τ F : ℝ))| + |S.EE B F| :=
        abs_add_le _ _
    _ = S.vol * |∑ τ : Fin d.f, (((S.alC B - S.al B τ) - (S.beC B - S.be B τ)) *
          (shiftFl d τ F : ℝ) + (S.beC B - S.be B τ) * (totalFl d τ F : ℝ))| + |S.EE B F| := by
        rw [abs_mul, abs_of_pos S.vol_pos]
    _ ≤ S.vol * ((∑ τ : Fin d.f, (2 * |(shiftFl d τ F : ℝ)| + |(totalFl d τ F : ℝ)|)) * CA *
          (Real.log B / B)) + (∑ m ∈ F.support, |((F.coeff m : ℚ) : ℝ)|) * CE * (Real.log B / B) :=
        add_le_add (mul_le_mul_of_nonneg_left hT S.vol_pos.le) hEE
    _ = _ := by ring

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.TendstoSumPrimesInRestP
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset Filter Topology

theorem tendsto_sum_primesIn_restP {d : IndexData} (S : EndSystem d) (B0 : ℕ)
    (Q : ℕ → Fin d.f → XPoly d)
    (h : Summable (fun p : primesAbove S B0 => |rest₂ d S.vol p (S.frob p) Q|)) :
    Tendsto (fun B : ℕ => ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q) atTop
      (𝓝 (restTot S B0 Q)) := by
  set g : ℕ → ℝ := fun p => rest₂ d S.vol p (S.frob p) Q with hg
  have hs : Summable (fun p : primesAbove S B0 => g p) := summable_abs_iff.1 h
  have hi : Summable ((primesAbove S B0).indicator g) := summable_subtype_iff_indicator.1 hs
  have ht : restTot S B0 Q = ∑' p, (primesAbove S B0).indicator g p := by
    rw [restTot]
    exact _root_.tsum_subtype (primesAbove S B0) g
  rw [ht]
  refine (hi.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr ?_
  intro B
  classical
  have hset : primesIn S B0 B = (range (B + 1)).filter (fun p => p ∈ primesAbove S B0) := by
    ext p
    rw [primesIn, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    have hm : p ∈ primesAbove S B0 ↔ p.Prime ∧ ¬ p ∣ S.level ∧ B0 < p := Iff.rfl
    rw [hm]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨by omega, h3, h4, h1⟩
    · rintro ⟨h1, h3, h4, h5⟩
      exact ⟨⟨h5, by omega⟩, h3, h4⟩
  rw [Function.comp_apply, hset, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Set.indicator_apply]

theorem HeightTauIdentity.proof (h82 : HeightSumIdentity.Statement) (hsum : RestSummable.Statement) :
    HeightTauIdentity.Statement := by
  intro d S hin B0 A0 b0 hA hb F Q hQ
  obtain ⟨B1, hB1⟩ := h82 d S hin B0
  obtain ⟨C, hC⟩ := hB1 F Q hQ
  have hrest := tendsto_sum_primesIn_restP S B0 Q (hsum d S B0 F Q hQ.2.2)
  set L : ℕ → ℝ := fun B => S.vol * (S.hh F - aB S B0 B * (shSum d F : ℝ) -
      bB S B0 B * (totSum d F : ℝ)) + ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q with hLdef
  have hL : Tendsto L atTop (𝓝 (S.vol * (S.hh F - A0 * (shSum d F : ℝ) - b0 * (totSum d F : ℝ)) +
      restTot S B0 Q)) :=
    ((((tendsto_const_nhds (x := S.hh F)).sub (hA.mul_const _)).sub
      (hb.mul_const _)).const_mul S.vol).add hrest
  have hlog : Tendsto (fun B : ℕ => C * Real.log B / B) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).const_mul C
    simpa [Function.comp_def, mul_div_assoc] using h
  have hdiff : Tendsto (fun B => S.PP B0 F - L B) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_gt_atTop B0, eventually_ge_atTop B1] with B hB0 hB1'
    rw [Real.norm_eq_abs]
    exact hC B hB0 hB1'
  have hsum' := hL.add hdiff
  rw [add_zero] at hsum'
  have hconst : Tendsto (fun _ : ℕ => S.PP B0 F) atTop
      (𝓝 (S.vol * (S.hh F - A0 * (shSum d F : ℝ) - b0 * (totSum d F : ℝ)) + restTot S B0 Q)) :=
    hsum'.congr (fun B => by ring)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.TotSumLineF
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

theorem HeightEvaluation.shSum_lineF (d : IndexData) (u : Idx d → ℚ) :
    (shSum d (lineF d u) : ℝ) = -((d.D : ℝ) + 1) * (degAt d u : ℝ) *
      ∑ τ : Fin d.f, ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) := by
  unfold shSum lineF
  simp only [ShOfPower.proof d]
  push_cast
  rw [Finset.mul_sum]

theorem HeightEvaluation.totSum_lineF (d : IndexData) (u : Idx d → ℚ) :
    (totSum d (lineF d u) : ℝ) = -((d.D : ℝ) + 1) * (degAt d u : ℝ) *
      ∑ τ : Fin d.f, ∑ i : Fin d.N, (u (τ, i) : ℝ) := by
  unfold totSum lineF
  simp only [TotOfPower.proof d]
  push_cast
  rw [Finset.mul_sum]

theorem HeightEvaluation.N_mul_ubar (d : IndexData) (u : Idx d → ℚ) (τ : Fin d.f) :
    (d.N : ℝ) * ubar d (uR d u) τ = ∑ i : Fin d.N, (u (τ, i) : ℝ) := by
  have hN : (d.N : ℝ) ≠ 0 := by
    have := d.two_le_N
    exact_mod_cast (show d.N ≠ 0 by omega)
  unfold ubar uR
  field_simp

theorem HeightEvaluation.proof (h83 : HeightTauIdentity.Statement) : HeightEvaluation.Statement := by
  intro d S hS B0 A0 b0 hA hb u Q hQ
  have key := h83 d S hS B0 A0 b0 hA hb (lineF d u) Q hQ
  have hNu := HeightEvaluation.N_mul_ubar d u
  have first : bigP S B0 u = S.vol * S.hh (lineF d u) + ((d.D : ℝ) + 1) * (S.vol * (degAt d u : ℝ)) *
      ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
        (d.N : ℝ) * b0 * ubar d (uR d u) τ) + restTot S B0 Q := by
    have hsum : ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
        (d.N : ℝ) * b0 * ubar d (uR d u) τ) =
        A0 * ∑ τ : Fin d.f, ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
          b0 * ∑ τ : Fin d.f, ∑ i : Fin d.N, (u (τ, i) : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [← hNu τ]
      ring
    rw [hsum]
    show S.PP B0 (lineF d u) = _
    rw [key, HeightEvaluation.shSum_lineF, HeightEvaluation.totSum_lineF]
    ring
  refine ⟨first, ?_⟩
  have hsum2 : ∑ τ : Fin d.f, (A0 * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), (u (τ, i) : ℝ) +
        (d.N : ℝ) * b0 * ubar d (uR d u) τ) =
      ∑ τ : Fin d.f, (A0 * cTau d (uR d u) τ + ((d.j : ℝ) * A0 + (d.N : ℝ) * b0) * ubar d (uR d u) τ) := by
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    unfold cTau uR
    ring
  rw [first, hsum2]

end GroundTheory.Heights₂.Heights.TheoremB
end
end


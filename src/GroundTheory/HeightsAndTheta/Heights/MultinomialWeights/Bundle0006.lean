import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PDegAntisym
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem blockPermute_lamDotX_permWeight (d : IndexData) (w : Fin d.f → Equiv.Perm (Fin d.N))
    (u : Idx d → ℚ) :
    RestTerms.blockPermute d.f d.N w (lamDotX d (permWeight d w u)) = lamDotX d u := by
  simp only [lamDotX, map_sum, map_mul, RestTerms.blockPermute, rename_C, rename_X, permWeight]
  exact Fintype.sum_equiv (Equiv.prodShear (Equiv.refl _) w) _ _ (fun p => rfl)

theorem blockPermute_lineClass_permWeight (d : IndexData) (w : Fin d.f → Equiv.Perm (Fin d.N))
    (u : Idx d → ℚ) :
    RestTerms.blockPermute d.f d.N w (lineClass d (permWeight d w u)) = lineClass d u := by
  simp only [lineClass, map_neg, blockPermute_lamDotX_permWeight]

theorem intFl_blockPermute (d : IndexData) (w : Fin d.f → Equiv.Perm (Fin d.N)) (H : XPoly d) :
    intFl d (RestTerms.blockPermute d.f d.N w H) = RestTerms.blockSign d.f d.N w * intFl d H := by
  simp only [intFl, LinearMap.smul_apply, flagIntegralLin, LinearMap.coe_mk, AddHom.coe_mk,
    smul_eq_mul, RestTerms.FlagIntegralPermute.full d.f d.N w H]
  ring

theorem DegAntisym.proof : DegAntisym.Statement := by
  intro d w u
  have h : degAt d u = RestTerms.blockSign d.f d.N w * degAt d (permWeight d w u) := by
    simp only [degAt]
    rw [← intFl_blockPermute, map_pow (RestTerms.blockPermute d.f d.N w),
      blockPermute_lineClass_permWeight]
  rw [h, ← mul_assoc, RestTerms.Flag.blockSign_mul_self, one_mul]

theorem DegAntisym.full : DegAntisym.Statement := DegAntisym.proof

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PDelDividesDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial

theorem degPoly_isBlockAlternating (hAnti : DegAntisym.Statement) (hEval : DegPolyEval.Statement)
    (d : IndexData) : RestTerms.IsBlockAlternating d.f d.N (degPoly d) := by
  intro w
  apply MvPolynomial.funext
  intro u
  have h := hAnti d w u
  rw [← hEval, ← hEval] at h
  rw [RestTerms.blockPermute, eval_rename, smul_eval]
  exact h

theorem DelDividesDeg.proof (hAnti : DegAntisym.Statement) (hEval : DegPolyEval.Statement) :
    DelDividesDeg.Statement := fun d =>
  RestTerms.FlagVandermondeDvd.full d.f d.N (degPoly d) (degPoly_isBlockAlternating hAnti hEval d)

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PHomDecompExists
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem HomDecompExists.proof : HomDecompExists.Statement := by
  intro d F hF
  obtain ⟨Q, hQ, hsum⟩ := RestTerms.CoinvAboveTop.full ℚ d.f d.N (d.D + 1) F hF
    (by simp [RestTerms.Coinv.coinvTop, IndexData.D, RestTerms.topDegree])
  refine ⟨Q, hF, fun k _ τ => hQ k τ, ?_⟩
  rw [RestTerms.IsPowerSumDecomposition, hsum]
  rfl

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PLimitsExist
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

theorem tendsto_sum_primesIn {d : IndexData} (S : EndSystem d) (B0 : ℕ) (g : ℕ → ℝ)
    (hg : Summable (fun p : primesAbove S B0 => g p)) :
    Tendsto (fun B : ℕ => ∑ p ∈ primesIn S B0 B, g p) atTop
      (𝓝 (∑' p : primesAbove S B0, g p)) := by
  have hs : Summable ((primesAbove S B0).indicator g) := summable_subtype_iff_indicator.mp hg
  rw [_root_.tsum_subtype]
  have h' := (tendsto_add_atTop_iff_nat 1).mpr hs.hasSum.tendsto_sum_nat
  refine h'.congr (fun B => ?_)
  have hsub : primesIn S B0 B ⊆ range (B + 1) := by
    intro p hp
    simp only [primesIn, mem_filter, mem_Ioc] at hp
    exact mem_range.2 (Nat.lt_succ_of_le hp.1.2)
  rw [← Finset.sum_subset hsub ?_]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [primesIn, mem_filter, mem_Ioc] at hp
    exact Set.indicator_of_mem (show p ∈ primesAbove S B0 from ⟨hp.2.1, hp.2.2, hp.1.1⟩) g
  · intro p hp hpn
    refine Set.indicator_of_notMem (fun hmem => hpn ?_) g
    obtain ⟨h1, h2, h3⟩ := hmem
    simp only [primesIn, mem_filter, mem_Ioc]
    exact ⟨⟨h3, Nat.le_of_lt_succ (mem_range.1 hp)⟩, h1, h2⟩

theorem homDecomp_exists {d : IndexData} {F : XPoly d} (hF : F.IsHomogeneous (d.D + 1)) :
    ∃ Q : ℕ → Fin d.f → XPoly d, IsHomDecomp d F Q := by
  obtain ⟨Q, hQh, hQ⟩ :=
    RestTerms.CoinvAboveTop.full ℚ d.f d.N (d.D + 1) F hF (Nat.lt_succ_self _)
  exact ⟨Q, hF, fun k _ τ => hQh k τ, hQ⟩

theorem combo_tendsto (h82 : HeightSumIdentity.Statement) (hsum : RestSummable.Statement)
    {d : IndexData} (S : EndSystem d) (hin : HeightIdentityInputs S) (B0 : ℕ)
    (F : XPoly d) (Q : ℕ → Fin d.f → XPoly d) (hQ : IsHomDecomp d F Q) :
    ∃ L : ℝ, Tendsto (fun B : ℕ => aB S B0 B * (shSum d F : ℝ) + bB S B0 B * (totSum d F : ℝ))
      atTop (𝓝 L) := by
  obtain ⟨B1, hB1⟩ := h82 d S hin B0
  obtain ⟨C, hC⟩ := hB1 F Q hQ
  have hR : Tendsto (fun B : ℕ => ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q) atTop
      (𝓝 (restTot S B0 Q)) :=
    tendsto_sum_primesIn S B0 _ (summable_abs_iff.mp (hsum d S B0 F Q hQ.2.2))
  have hlog : Tendsto (fun B : ℕ => C * Real.log B / B) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).const_mul C
    rw [mul_zero] at h
    refine h.congr (fun B => ?_)
    simp [mul_div_assoc]
  have hE : Tendsto (fun B : ℕ => S.PP B0 F - (S.vol * (S.hh F - aB S B0 B * (shSum d F : ℝ) -
      bB S B0 B * (totSum d F : ℝ)) + ∑ p ∈ primesIn S B0 B, rest₂ d S.vol p (S.frob p) Q))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_ge_atTop (max (B0 + 1) B1)] with B hB
    rw [Real.norm_eq_abs]
    exact hC B (lt_of_lt_of_le (Nat.lt_succ_self B0) (le_trans (le_max_left _ _) hB))
      (le_trans (le_max_right _ _) hB)
  refine ⟨(0 - S.PP B0 F + S.vol * S.hh F + restTot S B0 Q) / S.vol, ?_⟩
  have hc1 : Tendsto (fun _ : ℕ => S.PP B0 F) atTop (𝓝 (S.PP B0 F)) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ => S.vol * S.hh F) atTop (𝓝 (S.vol * S.hh F)) :=
    tendsto_const_nhds
  refine ((((hE.sub hc1).add hc2).add hR).div_const S.vol).congr (fun B => ?_)
  rw [div_eq_iff S.vol_pos.ne']
  ring

theorem LimitsExist.proof (h82 : HeightSumIdentity.Statement) (hpair : ShTotInvertiblePair.Statement)
    (hsum : RestSummable.Statement) : LimitsExist.Statement := by
  intro d S hin B0
  obtain ⟨F1, F2, hF1, hF2, hdet⟩ := hpair d S.f_pos
  obtain ⟨Q1, hQ1⟩ := homDecomp_exists hF1
  obtain ⟨Q2, hQ2⟩ := homDecomp_exists hF2
  obtain ⟨L1, h1⟩ := combo_tendsto h82 hsum S hin B0 F1 Q1 hQ1
  obtain ⟨L2, h2⟩ := combo_tendsto h82 hsum S hin B0 F2 Q2 hQ2
  have hdetR : (shSum d F1 : ℝ) * (totSum d F2 : ℝ) - (totSum d F1 : ℝ) * (shSum d F2 : ℝ) ≠ 0 := by
    exact_mod_cast hdet
  refine ⟨((totSum d F2 : ℝ) * L1 - (totSum d F1 : ℝ) * L2) /
      ((shSum d F1 : ℝ) * (totSum d F2 : ℝ) - (totSum d F1 : ℝ) * (shSum d F2 : ℝ)),
    ((shSum d F1 : ℝ) * L2 - (shSum d F2 : ℝ) * L1) /
      ((shSum d F1 : ℝ) * (totSum d F2 : ℝ) - (totSum d F1 : ℝ) * (shSum d F2 : ℝ)), ?_, ?_⟩
  · refine (((h1.const_mul (totSum d F2 : ℝ)).sub (h2.const_mul (totSum d F1 : ℝ))).div_const
      _).congr (fun B => ?_)
    rw [div_eq_iff hdetR]
    ring
  · refine (((h2.const_mul (shSum d F1 : ℝ)).sub (h1.const_mul (shSum d F2 : ℝ))).div_const
      _).congr (fun B => ?_)
    rw [div_eq_iff hdetR]
    ring

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PRestPWellDefined
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem liePowerSum_isHomogeneous (d : IndexData) (m : ℕ) (e : Emb d) :
    (liePowerSum d m e).IsHomogeneous m := by
  unfold liePowerSum lowerPowerSum
  split_ifs
  · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℚ (e.1, i)).neg.pow m
  · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℚ (e.1, i)).pow m

theorem RestPWellDefined.proof : RestPWellDefined.Statement := by
  intro d vol p φ F Q Q' hQ hQ'
  unfold rest₂
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hk
  congr 1
  funext n
  unfold restSeries
  have hG := liePowerSum_isHomogeneous d (k - 1) ((φ ^ (n + 1)) (τ, false))
  have h := RestTerms.RestTermWellDefined.full d.f d.N F Q Q' hQ hQ' k (by omega) hkN τ _ hG
  unfold RestTerms.restTerm at h
  have e : ∀ R : ℕ → Fin d.f → XPoly d,
      (k : ℚ) * intFl d (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ) =
        flagNormalisation d.f d.N *
          ((k : ℚ) * RestTerms.flagIntegral d.f d.N (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * R k τ)) := by
    intro R
    simp only [intFl, LinearMap.smul_apply, flagIntegralLin, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [e Q, e Q', h]

theorem RestPWellDefined.full : RestPWellDefined.Statement := RestPWellDefined.proof

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTotFormula
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem intFl_apply (d : IndexData) (G : XPoly d) :
    intFl d G = flagNormalisation d.f d.N * RestTerms.flagIntegral d.f d.N G := rfl

theorem intFl_powerSum_mul (hK : RestTerms.FlagIntegralKillsPowerSums.Statement) (d : IndexData)
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ d.N) (σ : Fin d.f) (G : XPoly d) :
    intFl d (RestTerms.blockPowerSum d.f d.N k σ * G) = 0 := by
  rw [intFl_apply, hK d.f d.N k σ G hk1 hkN, mul_zero]

def totalDeriv (d : IndexData) (τ : Fin d.f) : Derivation ℚ (XPoly d) (XPoly d) :=
  ∑ i : Fin d.N, pderiv (τ, i)

theorem totalDeriv_apply (d : IndexData) (τ : Fin d.f) (G : XPoly d) :
    totalDeriv d τ G = ∑ i : Fin d.N, pderiv (τ, i) G := by
  rw [totalDeriv, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

theorem totalDeriv_blockPowerSum (d : IndexData) (τ σ : Fin d.f) (k : ℕ) :
    totalDeriv d τ (RestTerms.blockPowerSum d.f d.N k σ) =
      if σ = τ then C (k : ℚ) * RestTerms.blockPowerSum d.f d.N (k - 1) τ else 0 := by
  classical
  rw [totalDeriv_apply]
  simp only [RestTerms.blockPowerSum, map_sum, Derivation.leibniz_pow, pderiv_X]
  split_ifs with h
  · subst h
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [nsmul_eq_mul, smul_eq_mul]
    · intro b _ hb
      simp [hb]
    · simp
  · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
    have : ((σ, i') : Fin d.f × Fin d.N) ≠ (τ, i) := fun e => h (congrArg Prod.fst e)
    simp [this]

theorem TotFormula.proof (hK : RestTerms.FlagIntegralKillsPowerSums.Statement) :
    TotFormula.Statement := by
  intro d τ F Q _ _ hdec
  unfold RestTerms.IsPowerSumDecomposition at hdec
  subst hdec
  have hN := d.two_le_N
  have key : ∀ k ∈ Icc 1 d.N, ∀ σ : Fin d.f,
      intFl d (totalDeriv d τ (RestTerms.blockPowerSum d.f d.N k σ * Q k σ)) =
        if σ = τ then (k : ℚ) * intFl d (RestTerms.blockPowerSum d.f d.N (k - 1) τ * Q k τ)
        else 0 := by
    intro k hk σ
    rw [Finset.mem_Icc] at hk
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      intFl_powerSum_mul hK d hk.1 hk.2, zero_add, totalDeriv_blockPowerSum]
    split_ifs with h
    · subst h
      rw [show Q k σ * (C (k : ℚ) * RestTerms.blockPowerSum d.f d.N (k - 1) σ) =
          (k : ℚ) • (RestTerms.blockPowerSum d.f d.N (k - 1) σ * Q k σ) by
            rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]
    · rw [mul_zero, map_zero]
  have h0 : RestTerms.blockPowerSum d.f d.N 0 τ = C (d.N : ℚ) := by
    simp [RestTerms.blockPowerSum]
  unfold totalFl
  rw [← totalDeriv_apply]
  simp only [map_sum]
  rw [Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun σ _ => key k hk σ]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single 1]
  · rw [Nat.sub_self, h0, ← smul_eq_C_mul, map_smul, smul_eq_mul, Nat.cast_one, one_mul]
  · intro k hk hk1
    rw [Finset.mem_Icc] at hk
    rw [intFl_powerSum_mul hK d (k := k - 1) (by omega) (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) h

theorem TotFormula.full : TotFormula.Statement :=
  TotFormula.proof RestTerms.FlagIntegralKillsPowerSums.full

end GroundTheory.Heights₂.Heights.TheoremB
end
end


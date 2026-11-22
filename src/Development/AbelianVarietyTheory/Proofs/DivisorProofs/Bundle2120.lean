import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntryValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift
variable {D : D7}

theorem U_sub_c_eq_w (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ =
      (((lamL j τ).w ⟨a, ha⟩ : ℤ) : ℝ) + ((Vc D j).rank : ℝ) / 2 - a := by
  have h1 := lamT_of_lt j τ a ha
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  show ((Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a : ℤ) : ℝ) - cT j τ = _
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN cT
  push_cast
  rw [h2]
  ring

theorem valsAt_of_isLamPrime : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau),
    Formalism.IndefR.Bridge.IsLamPrime (GlobalTheory.ExpTie.Lift.lamL j τ) ((j : ℕ) + 1) τ → GlobalTheory.ExpTie.Lift.ValsAt L j τ := by
  intro D L j τ h
  obtain ⟨hj, W, hk, hm, ht, hJ, he, hv, hb, hw⟩ := h
  obtain ⟨k, m, t, J, e, v, b⟩ := W
  simp only at hk hm ht hJ he hv hb
  subst hk hm ht hJ
  have hN := rank_eq j
  have hK := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hjm := j.2
  have hrk : ((Vc D j).rank : ℚ) = (D.R.k : ℚ) + D.R.m + D.R.t - 1 := by
    rw [hN, Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
  have hmj : ((D.R.m - ((j : ℕ) + 1) : ℕ) : ℚ) = (D.R.m : ℚ) - j - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hk1 : ((D.R.k - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hr1 : D.R.k + D.R.m - 1 + D.R.t = (Vc D j).rank := by omega
  have hp : D.R.k + ((j : ℕ) + 1) - 1 = D.R.k + j := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have hal : a < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ a hal]
    have hq := hw ⟨a, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj] at hq
    have hv' : ((v (a + 1 + 1) : ℤ) : ℚ) = (D.hc τ).v ⟨a, ha⟩ := hv ⟨a, ha⟩
    have hQ : (((lamL j τ).w ⟨a, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - a = (D.hc τ).v ⟨a, ha⟩ := by
      rw [hq, ← hv']; push_cast; ring
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this
    exact this
  · intro i hi
    have hal : D.R.k - 1 + i < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj, show D.R.k - 1 + (i : ℕ) + 1 - (D.R.k - 1) = (i : ℕ) + 1 by omega,
      show D.R.k - 1 + (i : ℕ) + 1 = D.R.k + i by omega] at hq
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, hk1]
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this
  · intro s hs
    have hal : D.R.k + j + s < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : D.R.k + ↑j + s + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t := by omega
    simp only [c3, if_true] at hq
    rw [hp, hmj] at hq
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k + j + s : ℕ) : ℚ) =
        -(D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ + ((D.R.t : ℚ) - 1) / 2 - s := by
      push_cast at hq he ⊢
      linarith
    have hwj : wj D ((j : ℕ) + 1) τ = (((D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dif_pos hj.2]
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    rw [hwj]
    push_cast at this ⊢
    linarith
  · intro i hi
    have hal : D.R.k - 1 + i + D.R.t < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : ¬ (D.R.k - 1 + (i : ℕ) + D.R.t + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t) := by omega
    simp only [c3, if_false] at hq
    rw [show D.R.m - ((j : ℕ) + 1) + 1 - (D.R.m - ((j : ℕ) + 1) + 1 - (D.R.k - 1 + (i : ℕ) + D.R.t + 1 - (D.R.k + ((j : ℕ) + 1) - 1) - D.R.t))
        = (i : ℕ) - j by omega] at hq
    rw [show (j : ℕ) + 1 + ((i : ℕ) - j) = (i : ℕ) + 1 by omega, hp, hmj] at hq
    have hij : (((i : ℕ) - (j : ℕ) : ℕ) : ℚ) = (i : ℚ) - j := by
      rw [Nat.cast_sub (by omega)]
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i + D.R.t : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, Nat.cast_add, hk1]
      rw [hij] at hq
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this

end GlobalTheory.ExpTie.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoNonThickPlaceCentreWidth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

variable {D : Formalism.BasicNotions.D7}

theorem other_of_not_thick (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau)
    (hv : GlobalTheory.ExpTie.Lift.ValsAt L j τ) (hT : τ ∉ (GlobalTheory.ExpTie.Lift.wts L j).T2) :
    ((GlobalTheory.ExpTie.parOf L j).Top ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).b' * (1 + 1 / (GlobalTheory.ExpTie.parOf L j).x + 1 / (GlobalTheory.ExpTie.parOf L j).x ^ 2) + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) ∨ ((GlobalTheory.ExpTie.parOf L j).Thin ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).w'' + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) := by
  classical
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m

  have hw : ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ L.Sc + (GlobalTheory.ExpTie.Lift.wts L j).c τ := by
    have hU := U_last L j τ
    have h0 := hv.1 0 (by omega)
    have hcv := (L.cloud_v τ ⟨0, by omega⟩).2
    have hwd : (GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ = (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 := by
      show (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ 0 - (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ ((Vc D j).rank - 1) = _
      rw [hU, sub_zero]
    rw [hwd]
    linarith
  have hc := c_le L j τ hv
  have hnt : (D.eTau τ : D.R.GG) ∉ D.host.thickPlaces := by
    intro h
    apply hT
    simp only [wts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have he : (GlobalTheory.ExpTie.Lift.wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
      unfold Host.topPlaces at htop
      simpa using htop
    have x1 := L.sc.one_lt_alt
    have x0 : 0 < L.sc.x := by linarith
    have hb0 : 0 < L.sc.b' := by
      have hX : 0 < L.sc.X' := by unfold Scale.X'; positivity
      have hb : 0 < L.sc.b := by unfold Scale.b; positivity
      unfold Scale.b' Scale.a
      positivity
    have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
    have hLa : 0 < L.LaG := by
      have h1 := P5.S_le
      have h2 := L.Sc_pos
      by_contra hn
      push_neg at hn
      have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hb0.le) hk0.le
      linarith
    have hbT : ((L.bT ⟨t, ht1⟩ : ℝ)) ≤ L.sc.b' * (1 + 1 / L.sc.x ^ 2) := by
      have h1 := P5.bT_le ⟨t, ht1⟩
      have h2 := P5.rho_le
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      unfold LevelStarExponents.rhoP at h2
      rw [hx2] at h2
      have hq : 0 ≤ 1 / L.sc.x ^ 2 := by positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        linarith
      have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h6 := mul_le_mul_of_nonneg_right h5 hb0.le
      nlinarith
    have a := L.bT_ge ⟨t, ht1⟩
    have wj1 := L.win_top ((j : ℕ) + 1) (by omega) (by omega) τ ⟨t, ht1⟩ ht2.symm
    have wjm := L.win_top D.R.m (by omega) le_rfl τ ⟨t, ht1⟩ ht2.symm
    refine ⟨⟨(L.bT ⟨t, ht1⟩ : ℝ), a, hbT, ?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' * (1 + 1 / L.sc.x ^ 2) + L.sc.b' / L.sc.x := by ring
      linarith [wjm.2]
  · right
    have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨(D.eTau τ).2, htop, hnt⟩
    have wj1 := L.win_thin ((j : ℕ) + 1) (by omega) (by omega) τ hthin
    have wjm := L.win_thin D.R.m (by omega) le_rfl τ hthin
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he]; exact wj1.1
    · rw [he]; exact wj1.2
    · show _ ≤ L.Sc + L.sc.w'' D.R.n + L.etaSz + ((D.R.t : ℝ) - 1) / 2
      linarith [wjm.2]

end GlobalTheory.ExpTie.Lift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoThickPlaceCentreWindow
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

theorem thick_of_mem (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ)
    (hτ : τ ∈ (wts L j).T2) :
    (parOf L j).Thick ((wts L j).e τ) ∧ ((wts L j).xp τ : ℝ) ≤ (parOf L j).h := by
  have hmem : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces := by
    simpa [wts] using hτ
  have hm2 := D.R.two_le_m
  have hj := j.2
  have h1 := L.win_thick ((j : ℕ) + 1) (by omega) (by omega) τ hmem
  have h2 := L.win_thick D.R.m (by omega) le_rfl τ hmem
  have hc := c_le L j τ hv
  have hb : (parOf L j).b = L.sc.b := rfl
  refine ⟨?_, ?_⟩
  · show (parOf L j).b ≤ wj D ((j : ℕ) + 1) τ ∧ wj D ((j : ℕ) + 1) τ ≤ (parOf L j).b + L.etaSz + 1
    rw [hb]; exact h1
  · have hfl : ((wts L j).xp τ : ℝ) ≤ cT j τ + L.Sc := by
      show ((⌊cT j τ + L.Sc⌋ : ℤ) : ℝ) ≤ cT j τ + L.Sc
      exact Int.floor_le _
    have hc' : cT j τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := hc
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    show ((wts L j).xp τ : ℝ) ≤ (parOf L j).b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1
    rw [hb]
    linarith [h2.2]

end GlobalTheory.ExpTie.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoWindowContainsCloud
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem GlobalTheory.ExpTie.Lift.window_cloud : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ((GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).xm τ : ℝ) ∧ (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.parOf L j).S) ∧ ∀ a, a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
  intro D L j τ hv
  have hS : (GlobalTheory.ExpTie.parOf L j).S = L.Sc := rfl
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) = D.R.k - 1 := rfl
  have hxm : (GlobalTheory.ExpTie.Lift.wts L j).xm τ = ⌈(GlobalTheory.ExpTie.Lift.wts L j).c τ⌉ := rfl
  have hxp : (GlobalTheory.ExpTie.Lift.wts L j).xp τ = ⌊(GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc⌋ := rfl

  have hrow : ∀ a, a < D.R.k - 1 →
      (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧
        (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
    intro a ha
    have h1 := hv.1 a ha
    have h2 := L.cloud_v τ ⟨a, ha⟩
    have hlo : (GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) := by
      have : (0 : ℝ) ≤ (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) := by exact_mod_cast h2.1
      linarith
    have hhi : ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc := by
      have : (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) ≤ L.Sc := by exact_mod_cast h2.2
      linarith
    rw [hxm, hxp]
    exact ⟨Int.ceil_le.2 hlo, Int.le_floor.2 hhi⟩
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have h0 := hrow 0 (by omega)
  refine ⟨⟨?_, le_trans h0.1 h0.2, ?_⟩, ?_⟩
  · rw [hxm]; exact Int.le_ceil _
  · rw [hxp, hS]; exact Int.floor_le _
  · intro a ha
    rw [hkc] at ha
    exact hrow a ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalDeterminedByUnramified
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.WeilLinW

theorem one_mem_UAt' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem charW_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) →
    GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t ι hι β₀ hβ
  have hloc := (GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v
  obtain ⟨φ₀, hφ₀, hιφ₀⟩ := hι.bij.surjOn (GlobalTheory.KSplit.indicator_intM_mem_SB (k := Fv F v) (R := Fin a) (D := Fin (a + a')))
  have h0 : ι φ₀ 0 ≠ 0 := by
    rw [hιφ₀]
    have : (0 : Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∈ GlobalTheory.KSplit.intM (Fv F v) (Fin a) (Fin (a + a')) :=
      fun i j => by simp
    simp [Set.indicator_of_mem this]
  have omA_eq : ∀ (h' : GL (Fin (a + a')) (Fv F v)) (Φ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) Y,
      GlobalTheory.SplitFlip.omA 1 β₀ 1 h' Φ Y = ((β₀ (GlobalTheory.SplitFlip.gdet h') : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h') (-(a : ℂ) / 2)) * Φ (Y * (GlobalTheory.SplitFlip.invT h').1) := by
    intro h' Φ Y
    simp [GlobalTheory.SplitFlip.omA]
  have gdet_eq : ∀ (h : UA σ G.W.J) (h' : GL (Fin (a + a')) (Fv F v)), (mat h).map (piW t) = h'.1 →
      ((GlobalTheory.SplitFlip.gdet h' : (Fv F v)ˣ) : Fv F v) = ((mat h).map (piW t)).det := by
    intro h h' e
    rw [e]; rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU, hUφ⟩ := hloc.2.2 φ₀ hφ₀
    have hUW : {h : UA σ G.W.J | ((1 : UA σ G.V.J), h) ∈ U} ∈ 𝓝 (1 : UA σ G.W.J) := by
      have hc : Continuous (fun h : UA σ G.W.J => ((1 : UA σ G.V.J), h)) := continuous_const.prodMk continuous_id
      exact hc.continuousAt.preimage_mem_nhds hU
    obtain ⟨V, hV, hVx⟩ := GlobalTheory.T.unitary_determinant_open_image F E σ B a a' G X om om' hTr v hv t _ hUW
    unfold GlobalTheory.SmGL.IsSmoothChar
    apply Subgroup.isOpen_of_mem_nhds (g := 1)
    filter_upwards [hV, GlobalTheory.T.valuation_one_units_nhds (k := Fv F v)] with x hx hxv
    obtain ⟨h, hh, hhU, hdet⟩ := hVx x hx
    obtain ⟨h', hh', hrel⟩ := hβ h hh
    have hA := hUφ (1, h) hhU (one_mem_UAt' σ G.V _) hh
    have e := congrFun (hrel φ₀ hφ₀ φ₀ hφ₀ hA) 0
    rw [omA_eq] at e
    have hg : GlobalTheory.SplitFlip.gdet h' = x := Units.ext ((gdet_eq h h' hh').trans hdet)
    rw [hg, Matrix.zero_mul, GlobalTheory.SplitFlip.apow_of_valuation_eq_one hxv, mul_one] at e
    have e2 : (β₀ x : ℂ) = 1 := by
      have := mul_right_cancel₀ h0 (e.symm.trans (one_mul _).symm)
      exact this
    show β₀ x = 1
    exact Units.ext e2
  · intro x
    have ha : 0 < a + a' := by have := hTr.geo.lt; omega
    let i0 : Fin (a + a') := ⟨0, ha⟩
    let D : (Fv F v)ˣ → Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v) := fun y =>
      Matrix.diagonal (Function.update (1 : Fin (a + a') → Fv F v) i0 (y : Fv F v))
    have hD : ∀ y z : (Fv F v)ˣ, D y * D z = D (y * z) := by
      intro y z
      simp only [D, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : i = i0
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    have hD1 : D 1 = 1 := by
      simp only [D]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases hi : i = i0
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    let h' : GL (Fin (a + a')) (Fv F v) :=
      ⟨D x, D x⁻¹, by rw [hD, mul_inv_cancel, hD1], by rw [hD, inv_mul_cancel, hD1]⟩
    have hg : GlobalTheory.SplitFlip.gdet h' = x := by
      apply Units.ext
      change (D x).det = (x : Fv F v)
      simp only [D, Matrix.det_diagonal]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    obtain ⟨h, hh, hht⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear_right hP F E σ B a a' G X om om' hTr v hv t h'
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc.1 1 (one_mem_UAt' σ G.V _) h hh φ₀ hφ₀
    obtain ⟨h'', hh'', hrel⟩ := hβ h hh
    have : h'' = h' := Units.ext (hh''.symm.trans hht)
    subst this
    have e := hrel φ₀ hφ₀ φ₁ hφ₁ hA
    obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_add_haar_matrix_space (k := Fv F v) (a := a) (d := a + a')
    have hu := GlobalTheory.T.triple_local_unitary_action_preserves hP F E σ B a a' G X om om' hTr v h hh φ₀ hφ₀ φ₁ hφ₁ hA
    have hl := GlobalTheory.T.triple_linear_witt_model_nonvanishing hP F E σ B a a' G X om om' hTr v hv t ι hι φ₀ hφ₀ φ₁ hφ₁ hu ν hν
    rw [e] at hl
    simp_rw [omA_eq, hg] at hl
    set c : ℂ := (β₀ x : ℂ) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) with hcdef
    have hc : ∀ Y : Matrix (Fin a) (Fin (a + a')) (Fv F v), ‖c * ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2 =
        ‖c‖ₑ ^ 2 * ‖ι φ₀ (Y * (GlobalTheory.SplitFlip.invT h').1)‖ₑ ^ 2 := by
      intro Y; rw [enorm_mul, mul_pow]
    simp_rw [hc] at hl
    rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm]), GlobalTheory.T.lintegral_norm_sq_right_translate (ι φ₀) h' ν hν, hg] at hl
    obtain ⟨hn0, hntop⟩ := GlobalTheory.T.lintegral_norm_sq_schwartz_pos_finite (ι φ₀) (hι.bij.mapsTo hφ₀) (fun hz => h0 (by simp [hz])) ν hν
    rw [← mul_assoc] at hl
    have h1 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = 1 :=
      (ENNReal.mul_left_inj hn0 hntop).mp (hl.trans (one_mul _).symm)
    clear_value c
    have h2 : ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = ‖(β₀ x : ℂ)‖ₑ ^ 2 := by
      have : c * c * GlobalTheory.SplitFlip.apow x (a : ℂ) = (β₀ x : ℂ) * (β₀ x : ℂ) := by
        rw [hcdef]
        have e3 : GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (-(a : ℂ) / 2) * GlobalTheory.SplitFlip.apow x (a : ℂ) = 1 := by
          rw [← GlobalTheory.SplitFlip.apow_add, ← GlobalTheory.SplitFlip.apow_add]
          have : -(a : ℂ) / 2 + -(a : ℂ) / 2 + a = 0 := by ring
          rw [this, GlobalTheory.SplitFlip.apow_zero]
        linear_combination ((β₀ x : ℂ) * (β₀ x : ℂ)) * e3
      calc ‖c‖ₑ ^ 2 * ‖GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ = ‖c * c * GlobalTheory.SplitFlip.apow x (a : ℂ)‖ₑ := by
            rw [enorm_mul, enorm_mul]; ring
        _ = ‖(β₀ x : ℂ) * (β₀ x : ℂ)‖ₑ := by rw [this]
        _ = ‖(β₀ x : ℂ)‖ₑ ^ 2 := by rw [enorm_mul]; ring
    rw [h2] at h1
    have h3 : ‖(β₀ x : ℂ)‖₊ = 1 := by
      rw [enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_eq_one] at h1
      exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h1
    exact congrArg NNReal.toReal h3

end GlobalTheory.WeilLinW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralPotentialWeightChartLtTop
section
namespace GlobalTheory.ScalarPoin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem lintegral_kaF_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ s0 : ℝ, ∀ s : ℝ, s0 ≤ s →
      ∫⁻ z, ENNReal.ofReal (kaF X x0 s z) ∂muF X x0 < ⊤ := by
  intro E _ _ _ r X x0 ho
  obtain ⟨FF, hF⟩ := GlobalTheory.MetricWeightTest.exists_fundSet_orth X ho
  have hfin := (GlobalTheory.TrueCx.covol_eq X ho hF).1
  refine ⟨4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1, fun s hs => ?_⟩
  obtain ⟨C, hC, hCb⟩ := kaUnfoldStatement_holds r X x0 ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) FF hF s
    (by linarith)
  have h := hCb (fun _ => 1) measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul] at h
  exact h.trans_lt (ENNReal.mul_lt_top hC hfin)

end GlobalTheory.ScalarPoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivLOneBoundFamilyStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_deriv_L_one_bound_family : GlobalTheory.FunPr.Hypotheses₂ → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) := by
  first | exact @GlobalTheory.log_deriv_L_one_le_along_family | exact GlobalTheory.log_deriv_L_one_le_along_family | (intros; apply GlobalTheory.log_deriv_L_one_le_along_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffAdjointFrameMatrixInteStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedPairLattice_iff_adjointFrameMatrix_integral_conjHalf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ t : WO (Vc D i) (Wc D i), IsHalf (cA D eQ) t → (IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (t)) ↔ t ∈ lattice₂ R i) := by
  first | exact @GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP | exact GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP | (intros; apply GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPointsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_at_fitted_points : GlobalTheory.BigTop.Fun.SetAt → GlobalTheory.BigTop.Fun.MM @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie | exact GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie | (intros; apply GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie <;> assumption)
end


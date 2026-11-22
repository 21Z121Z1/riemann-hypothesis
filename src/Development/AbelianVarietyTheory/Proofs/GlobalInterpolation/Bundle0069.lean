import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.GradedWeylDivisibility.FinalC
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0064
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RpowLeExpRpowEventually
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem rpow_le_exp_rpow_eventually {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∃ x0 : ℝ, ∀ x ≥ x0, x ^ c ≤ Real.exp (x ^ ε) := by
  have h := ((tendsto_exp_div_rpow_atTop (c / ε)).comp (tendsto_rpow_atTop hε)).eventually_ge_atTop 1
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  simp only [Function.comp] at h1
  rw [← Real.rpow_mul h2.le, mul_div_cancel₀ _ hε.ne', le_div_iff₀ (Real.rpow_pos_of_pos h2 _), one_mul] at h1
  exact h1

theorem poly_sizes_ranks_weights : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, 0 ≤ Fm.Ct ∧ ((Fm.D x i).R.f : ℝ) ≤ x ^ (3 : ℝ) ∧ ((Fm.D x i).R.m : ℝ) ≤ x ∧ ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) ∧ ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ≤ x ^ (Fm.Ct + 6) ∧ ((Fm.D x i).R.nV : ℝ) ≤ x ^ (Fm.Ct + 6) ∧ ((Fm.D x i).host.TT.card : ℝ) ≤ x ^ (3 : ℝ) ∧ (Fm.L x i).sc.x = x ∧ (Fm.L x i).sc.a = x * (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.L ∧ (Fm.L x i).sc.L ≤ x ∧ x ^ (Fm.Ct + 6) ≤ (Fm.L x i).sc.b ∧ (∀ t, (0 : ℝ) ≤ (Fm.L x i).aT t ∧ ((Fm.L x i).aT t : ℝ) ≤ 2 * x * (Fm.L x i).sc.b) ∧ (Fm.L x i).B0 ≤ x ^ (5 : ℝ) * (Fm.L x i).sc.b ∧ 0 ≤ (Fm.L x i).B0) := by
  intro eps Fm
  have heps : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x0, hx0⟩ := rpow_le_exp_rpow_eventually heps (Fm.Ct + 6)
  refine ⟨max x0 4, fun x hx hx1 i => ?_⟩
  have hexp := hx0 x (le_trans (le_max_left _ _) hx)
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  have hS := Fm.sizes x hx1 i
  have hLx := Fm.L_x x i hx1
  have hLe := Fm.L_eps x i
  have hCt := Fm.Ct_eq x i
  generalize Fm.L x i = L at *
  generalize Fm.Ct = Ct at *
  obtain ⟨hN, hM, hK, -, -, -, -, hTT, -⟩ := hS
  have hlt : eps < 1 / 52 := hLe ▸ L.sc.eps_lt
  have h1x : (1 : ℝ) ≤ x := by linarith
  have h0x : (0 : ℝ) < x := by linarith
  have htw := L.t_win
  have haw := L.aT_win
  have hN2 := hN.2
  have hM2 := hM.2
  have hK2 := hK.2
  have hTT2 := hTT.2
  unfold szNst at hTT2
  unfold szTh at hN2 hM2 hK2
  unfold Scale.delta1 at hM2 hTT2
  rw [hLx, hLe] at hN2 hM2 hK2 hTT2
  rw [hLx, hCt] at htw
  have hd : x ^ (-(eps / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1x (by linarith)
  have hd0 : 0 < x ^ (-(eps / 8)) := Real.rpow_pos_of_pos h0x _
  have hs2 : (2 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le (by linarith)
  have hfn : ((Fm.D x i).R.f : ℝ) = 2 * (Fm.D x i).R.n := by unfold Ranks.f; push_cast; ring
  have hf : ((Fm.D x i).R.f : ℝ) ≤ x ^ (3 : ℝ) := by
    have h1 : ((Fm.D x i).R.n : ℝ) ≤ x ^ (5 / 2 : ℝ) :=
      hN2.trans (Real.rpow_le_rpow_of_exponent_le h1x (by linarith))
    rw [hfn, show (3 : ℝ) = 1 / 2 + 5 / 2 by norm_num, Real.rpow_add h0x]
    exact mul_le_mul hs2 h1 (by positivity) (by positivity)
  have hm : ((Fm.D x i).R.m : ℝ) ≤ x := by
    have h1 : x ^ (eps / 100) ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
    have h2 : Real.sqrt (x * x ^ (-(eps / 8))) ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt (by nlinarith)
    refine hM2.trans ((mul_le_mul h1 h2 (by positivity) (by positivity)).trans ?_)
    exact (Real.mul_self_sqrt h0x.le).le
  have hk : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) :=
    hK2.trans (Real.rpow_le_rpow_of_exponent_le h1x (by linarith))
  have hCt0 : 0 ≤ Ct := by
    by_contra hc
    have := Real.rpow_lt_one_of_one_lt_of_neg (show (1 : ℝ) < x by linarith) (not_le.1 hc)
    linarith [htw.1, htw.2]
  have h6 : 3 * x ≤ x ^ (6 : ℝ) := by
    have : x ^ ((2 : ℕ) : ℝ) ≤ x ^ (6 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x (by norm_num)
    rw [Real.rpow_natCast] at this
    nlinarith
  have hT0 : 0 < x ^ Ct := Real.rpow_pos_of_pos h0x _
  have hbig : 3 * x * (Fm.D x i).R.t ≤ x ^ (Ct + 6) := by
    rw [add_comm, Real.rpow_add h0x]
    exact mul_le_mul h6 htw.2 (by positivity) (by positivity)
  have hrt := (Fm.D x i).R.rank_add_five_le
  have h2m := (Fm.D x i).R.two_le_m
  have hk3 := (Fm.D x i).R.m_add_three_le_k
  have hNm : ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ≤ x ^ (Ct + 6) := by
    have h1 : (Fm.D x i).R.N (Fm.D x i).R.m ≤ 3 * (Fm.D x i).R.m * (Fm.D x i).R.t := by
      unfold Ranks.N
      have a1 : (Fm.D x i).R.k ≤ (Fm.D x i).R.t := by omega
      have a2 : 1 ≤ (Fm.D x i).R.t := by omega
      nlinarith
    have h2 : ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ≤ 3 * (Fm.D x i).R.m * (Fm.D x i).R.t := by exact_mod_cast h1
    refine h2.trans (le_trans ?_ hbig)
    gcongr
  have hnV : ((Fm.D x i).R.nV : ℝ) ≤ x ^ (Ct + 6) := by
    have h1 : (Fm.D x i).R.nV ≤ 2 * (Fm.D x i).R.t := by
      unfold Ranks.nV Ranks.r; omega
    have h2 : ((Fm.D x i).R.nV : ℝ) ≤ 2 * (Fm.D x i).R.t := by exact_mod_cast h1
    refine h2.trans (le_trans ?_ hbig)
    have := htw.1
    nlinarith
  have hTTc : ((Fm.D x i).host.TT.card : ℝ) ≤ x ^ (3 : ℝ) := by
    refine hTT2.trans (le_trans ?_ hf)
    rw [hfn]
    exact mul_le_of_le_one_right (by positivity) hd
  have ha : L.sc.a = x * L.sc.b := by unfold Scale.a; rw [hLx]
  have hL : L.sc.L = x ^ eps := by unfold Scale.L; rw [hLx, hLe]
  have hL1 : 1 ≤ L.sc.L := by rw [hL]; exact Real.one_le_rpow h1x heps.le
  have hL2 : L.sc.L ≤ x := by
    rw [hL]
    calc x ^ eps ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
      _ = x := Real.rpow_one x
  have hb : L.sc.b = Real.exp (x ^ eps) := by unfold Scale.b; rw [hL]
  have hb0 : 0 < L.sc.b := by rw [hb]; positivity
  have hB0 : L.B0 = (Fm.D x i).R.f * (Fm.D x i).R.m * L.sc.b * L.sc.L := by
    unfold SizeData₂.B0 sizeBudget bSize
    rw [hb, hL, hLx, hLe]
  refine ⟨hCt0, hf, hm, hk, hNm, hnV, hTTc, hLx, ha, hL1, hL2, hb ▸ hexp, fun t => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := haw t
    have ha0 : 0 < L.sc.a := by rw [ha]; positivity
    have hk1 : (1 : ℝ) ≤ (Fm.D x i).R.k := by
      have : 1 ≤ (Fm.D x i).R.k := by omega
      exact_mod_cast this
    have hA : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
    have h3 := div_le_self ha0.le (one_le_mul_of_one_le_of_one_le hk1 hA)
    refine ⟨by linarith, ?_⟩
    rw [mul_assoc, ← ha]; linarith
  · rw [hB0, show (5 : ℝ) = 3 + 1 + 1 by norm_num, Real.rpow_add h0x, Real.rpow_add h0x, Real.rpow_one]
    calc ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * L.sc.b * L.sc.L ≤ x ^ (3 : ℝ) * x * L.sc.b * x := by
          gcongr
      _ = _ := by ring
  · rw [hB0]; positivity

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScaleOneLeA
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem scale_one_le_a (s : Scale) : 1 ≤ s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 ≤ s.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ s.b := by
    unfold Scale.b
    exact Real.one_le_exp hL
  unfold Scale.a
  exact one_le_mul_of_one_le_of_one_le hx.le hb

theorem famP_La_nonneg : ∀ (eps : ℝ) (Fm : FamP eps), ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
    0 ≤ (Fm.L x i).La := by
  intro eps Fm x hx i
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx i
  obtain ⟨-, -, -, -, -, -, hrd, -⟩ := hQD
  unfold SizeData₂.La
  exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (scale_one_le_a _) hrd)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem _root_.GlobalTheory.scale_poly_comparison : ∀ eps c κ : ℝ, 0 < eps → 0 < κ → ∃ x0 : ℝ, ∀ s : _root_.Formalism.BasicNotions.Scale, s.eps = eps → x0 ≤ s.x → s.x ^ c ≤ Real.exp (s.x ^ (s.eps / 8)) ∧ s.x ^ c ≤ s.X' ^ κ ∧ s.x ^ c * s.X' ≤ s.b ^ κ ∧ s.b' * s.x ^ c ≤ s.b ∧ s.b ^ (1 - κ) * s.x ^ c ≤ s.b' ∧ (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ s.x ^ (3 : ℝ) → s.b ^ (1 - κ) * s.x ^ c ≤ s.w'' n ∧ s.w'' n ≤ s.b' ∧ s.X'' n = s.x * n * s.X') ∧ Real.exp (c * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ c ≤ s.X' ^ κ := by
  intro eps c κ heps hκ
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 8) c 0 1 0 le_rfl
    (by positivity) one_pos
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) c 0 κ 0 le_rfl
    (by positivity) hκ
  obtain ⟨x3, h3⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps (c + 3) 1 κ 0
    (by positivity) (by linarith) hκ
  obtain ⟨x4, h4⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) (c + 1) 0 1 0 le_rfl
    (by positivity) one_pos
  obtain ⟨x5, h5⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) (eps / 3) |c| |c| κ 2
    (by positivity) (by linarith) hκ
  refine ⟨max (max (max x1 x2) (max x3 x4)) x5, ?_⟩
  intro s hs hx
  subst hs
  have ht : 1 < s.x := s.one_lt_alt
  have ht0 : 0 < s.x := by linarith
  have hlog : 0 ≤ Real.log s.x := Real.log_nonneg ht.le
  have g1 := h1 s.x (le_trans (by simp) hx)
  have g2 := h2 s.x (le_trans (by simp) hx)
  have g3 := h3 s.x (le_trans (by simp) hx)
  have g4 := h4 s.x (le_trans (by simp) hx)
  have g5 := h5 s.x (le_trans (by simp) hx)
  simp only [Real.rpow_zero, pow_zero, mul_one, zero_mul, add_zero, one_mul] at g1 g2 g3 g4
  have hxc : s.x ^ c = Real.exp (Real.log s.x * c) := Real.rpow_def_of_pos ht0 c
  have hX' : s.X' = Real.exp (s.x ^ (s.eps / 3)) := by unfold _root_.Formalism.BasicNotions.Scale.X'; rfl
  have hb : s.b = Real.exp (s.x ^ s.eps) := by unfold _root_.Formalism.BasicNotions.Scale.b _root_.Formalism.BasicNotions.Scale.L; rfl
  have hb'def : s.b' = s.x * s.b / s.X' := by unfold _root_.Formalism.BasicNotions.Scale.b' _root_.Formalism.BasicNotions.Scale.a; rfl
  have hb' : s.b' = Real.exp (Real.log s.x + s.x ^ s.eps - s.x ^ (s.eps / 3)) := by
    rw [hb'def, hb, hX', Real.exp_sub, Real.exp_add, Real.exp_log ht0]
  have hw : ∀ n : ℕ, s.w'' n = s.b' / (s.x * n) := fun n => by unfold _root_.Formalism.BasicNotions.Scale.w''; rfl
  have hX'' : ∀ n : ℕ, s.X'' n = s.x * s.b / s.w'' n := fun n => by
    unfold _root_.Formalism.BasicNotions.Scale.X'' _root_.Formalism.BasicNotions.Scale.a; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxc]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [hxc, hX', ← Real.exp_mul]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [hxc, hX', hb, ← Real.exp_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [hb', hxc, hb, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [hb, ← Real.exp_mul, hxc, ← Real.exp_add, hb']
    exact Real.exp_le_exp.2 (by nlinarith)
  · intro n hn hnx
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hw, le_div_iff₀ (by positivity), hb, ← Real.exp_mul, hxc]
      calc Real.exp (s.x ^ s.eps * (1 - κ)) * Real.exp (Real.log s.x * c) * (s.x * n)
          ≤ Real.exp (s.x ^ s.eps * (1 - κ)) * Real.exp (Real.log s.x * c) *
              (s.x * s.x ^ (3 : ℝ)) := by gcongr
        _ = Real.exp (s.x ^ s.eps * (1 - κ) + Real.log s.x * c +
              (Real.log s.x + Real.log s.x * 3)) := by
            rw [Real.rpow_def_of_pos ht0 3, Real.exp_add, Real.exp_add, Real.exp_add,
              Real.exp_log ht0]
        _ ≤ s.b' := by
            rw [hb']
            exact Real.exp_le_exp.2 (by nlinarith)
    · rw [hw]
      have hpos : 0 ≤ s.b' := by rw [hb']; positivity
      exact div_le_self hpos (one_le_mul_of_one_le_of_one_le ht.le hn')
    · have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hbne : s.b ≠ 0 := by rw [hb]; positivity
      have hX'ne : s.X' ≠ 0 := by rw [hX']; positivity
      rw [hX'', hw, hb'def]
      field_simp
  · have hY : 0 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by positivity
    have hA : c * (s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤
        |c| * (s.x ^ (s.eps / 5) * Real.log s.x ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hY
    have hB : c * Real.log s.x ≤ |c| * Real.log s.x :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hlog
    have habs : 0 ≤ |c| := abs_nonneg c
    rw [hxc, hX', ← Real.exp_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylFieldSmul
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section
namespace GlobalTheory.Alc

theorem hcVal_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N : ℕ} (μ : Fin N → R) (k : ℕ) :
    hcVal S (fun i => φ (μ i)) k = φ (hcVal R μ k) := by
  have hM : hcMat S (fun i => φ (μ i)) = (hcMat R μ).map φ := by
    ext i l
    simp only [hcMat, shift, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hP : (hcMat S (fun i => φ (μ i))) ^ k = ((hcMat R μ) ^ k).map φ := by
    rw [hM]
    exact (map_pow (RingHom.mapMatrix φ) (hcMat R μ) k).symm
  simp only [hcVal, hP, Matrix.map_apply, map_sum]

theorem gel_dualWeyl_int (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (j : ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N ν) : gel ℤ N N j f = hcVal ℤ (fun i => (ν i : ℤ)) j • f := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℤ N N).2.2 ℚ (Int.castRingHom ℚ) j f,
    GlobalTheory.T.traceRowOperatorPower_dualWeyl_highestWeight N ν hν j _ (dualWeylMap ℤ ℚ (Int.castRingHom ℚ) N N ν f hf),
    smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  congr 2
  rw [← hcVal_map]
  simp

theorem gel_dualWeyl_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ j : ℕ,
    ∀ f ∈ dualWeyl k N N ν, gel k N N j f = hcVal k (fun i => (ν i : k)) j • f := by
  intro k _ N ν hν j f hf
  rw [standardMonomialSpanDomain k N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hg
    have hb : bideterminant k sz hsz I = map (Int.castRingHom k) (bideterminant ℤ sz hsz I) := by
      simp only [bideterminant, initMinor, map_prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [RingHom.map_det]
      congr 1
      ext p q
      simp
    have hmem : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ N N ν := hsh ▸ bidetMem ℤ N N K sz hsz I
    rw [hb, ← (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℤ N N).2.2 k (Int.castRingHom k) j, gel_dualWeyl_int N ν hν j _ hmem,
      smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
    congr 2
    rw [← hcVal_map]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory.Alc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingBoundedIntegralStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_bounded_integral : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c : ℕ) (psi : E → K) (N A B : ℕ) (Psi : Loc.SF E K (n' + c') (n + c)), HomBdd P N Psi → (∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj ≠ 0 → IntHom P (((qOf P : E) ^ N) • xj)) ∧ ∀ xj z : (Fin n' → E) →ₗ[E] (Fin n → E), IntHom P z → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi (xj + ((qOf P : E) ^ N) • z) = GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj := by
  first | exact @GlobalTheory.Proof.unfolding_bounded_integral.unfold_bdd | exact GlobalTheory.Proof.unfolding_bounded_integral.unfold_bdd | (intros; apply GlobalTheory.Proof.unfolding_bounded_integral.unfold_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingCharacterArgumentCompUnipotentRadicalsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingCharacterArgument_comp_unipotentRadicals : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∃ d : F, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) = Loc.chArg (Loc.xx1 xj t) + d := by
  first | exact @GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp | exact GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp | (intros; apply GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentRadicalsActAffineUnfoldingSpacesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadicals_act_affine_unfoldingSpaces : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∀ xj' : (Fin n' → F) →ₗ[F] (Fin n → F), ∃ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (T : (Loc.FC n' c' n c → F) ≃ₗ[F] (Loc.FC n' c' n c → F)) (b : Loc.FC n' c' n c → F), ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (T t + b) := by
  first | exact @GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action | exact GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action | (intros; apply GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryQuotientIntegralProdOverPlaces
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealQuotProd

variable {P Q P' Q' : ℕ}

theorem act_mul (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  unfold ActionCoordinates.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem act_mul_inv {a : UpqT P Q} {x : ActionCoordinates.Wsp P Q} (ha : ActionCoordinates.act a x = x) (g : UpqT P Q) :
    ActionCoordinates.act (a * g)⁻¹ x = ActionCoordinates.act g⁻¹ x := by
  have : ActionCoordinates.act a⁻¹ x = x := by
    conv_lhs => rw [← ha]
    rw [← act_mul, inv_mul_cancel, act_one]
  rw [_root_.mul_inv_rev, act_mul, this]

theorem measurable_act_inv (x : ActionCoordinates.Wsp P Q) :
    Measurable fun g : UpqT P Q => ActionCoordinates.act g⁻¹ x := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  exact ((GlobalTheory.UpqTopology.continuous_mat.comp continuous_inv).matrix_mulVec
    continuous_const).measurable

theorem sigmaFinite_cd (c : CDHaar) (P Q : ℕ) : SigmaFinite (c.cd P Q) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI : (c.cd P Q).IsHaarMeasure := c.haar P Q
  infer_instance

theorem one_place (H : ActionCoordinates.QuotientMeasure) (c : CDHaar) {β : ℝ} (hβ : β = 1 ∨ β = -1)
    {x : ActionCoordinates.Wsp P Q} (hx : ActionCoordinates.qf x = β) {k : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q}
    {ι : UpqT P' Q' → UpqT P Q} (hk : ActionCoordinates.IsPerpFrame x k ι) {u : UpqT P Q → ℝ≥0∞}
    (hu : Measurable u) (hu' : ∀ g, Measurable (fun h => u (ι h * g)) ∧
      ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1)
    {fib : ℝ → Measure (ActionCoordinates.Wsp P Q)} (hfib : ActionCoordinates.IsDxDq β fib)
    {φ : ActionCoordinates.Wsp P Q → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g, φ (ActionCoordinates.act g⁻¹ x) * u g ∂(c.cd P Q) =
      (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ y ∂(fib β) := by
  classical
  obtain ⟨h1, -, h3⟩ := H P Q β hβ x hx
  choose! s hs using h1
  have hae : ∀ᵐ y ∂(fib β), ActionCoordinates.qf y = β := by
    obtain ⟨U, B, -, -, -, hF⟩ := hfib
    have h1 : ∀ᵐ y ∂(fib β), y ∈ ActionCoordinates.qf ⁻¹' {id β} ∩ U := hF.1 β
    filter_upwards [h1] with y hy using hy.1
  rw [(h3 P' Q' k ι hk).2 c fib hfib s hs (fun g => φ (ActionCoordinates.act g⁻¹ x) * u g)
    ((hφ.comp (measurable_act_inv x)).mul hu),
    Measure.restrict_eq_self_of_ae_mem (s := {y | ActionCoordinates.qf y = β}) hae]
  congr 1
  refine lintegral_congr_ae (hae.mono fun y hy => ?_)
  have e : ∀ h, φ (ActionCoordinates.act (ι h * s y)⁻¹ x) = φ y := fun h => by
    rw [act_mul_inv (hk.2.2 h).1, hs y hy]
  simp only [e]
  rw [lintegral_const_mul _ (hu' _).1, (hu' _).2, mul_one]

theorem quot_integral_prod : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  intro H c T _ P Q P' Q' β hβ x hx k ι hk u hu j hj ν hν fib hfib φ hφ
  haveI := sigmaFinite_cd c P Q
  haveI := sigmaFinite_cd c P' Q'
  let f : T → UpqT P Q → ℝ≥0∞ := fun ρ g => φ ρ (ActionCoordinates.act g⁻¹ (x ρ)) * u ρ g
  have hf : ∀ ρ, Measurable (f ρ) := fun ρ =>
    ((hφ ρ).comp (measurable_act_inv (x ρ))).mul (hu ρ).1
  have key := hν (fun g => ∏ ρ, f ρ (g ρ))
    (Finset.measurable_prod _ fun ρ _ => (hf ρ).comp (measurable_pi_apply ρ))
  rw [GlobalTheory.SnMass.Push.lintegral_fintype_prod f hf] at key
  rw [← Finset.prod_congr rfl fun ρ _ =>
    one_place H c hβ (hx ρ) (hk ρ) (hu ρ).1 (hu ρ).2 hfib (hφ ρ)]
  refine Eq.trans (lintegral_congr fun s => ?_) key.symm
  have e : ∀ h : T → UpqT P' Q', ∏ ρ, f ρ ((j h * s.out) ρ) =
      ∏ ρ, (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ)) ρ (h ρ) :=
    fun h => Finset.prod_congr rfl fun ρ _ => by
      simp only [f, Pi.mul_apply, hj]
      rw [act_mul_inv ((hk ρ).2.2 _).1]
  rw [lintegral_congr e, GlobalTheory.SnMass.Push.lintegral_fintype_prod
    (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ))
    (fun ρ => (((hu ρ).2 _).1).const_mul _)]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [lintegral_const_mul _ ((hu ρ).2 _).1, ((hu ρ).2 _).2, mul_one]

end GlobalTheory.RealQuotProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VectorsLinearMapsBoundedDenominatorsAtPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectors_linearMaps_bounded_denominators_atPrime : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y) := by
  first | exact @GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators | exact GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators | (intros; apply GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedBoxSumAtPrimeEqOfBoundedSchwartzStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ A B : ℕ, N ≤ A → N ≤ B → boxSum P A B f = boxSum P N N f := by
  first | exact @GlobalTheory.boxSum_eq_of_funBdd | exact GlobalTheory.boxSum_eq_of_funBdd | (intros; apply GlobalTheory.boxSum_eq_of_funBdd <;> assumption)
end


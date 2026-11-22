import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0009
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0031
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscProperties
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem intg_nMul_for_point {K : Type} [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  induction n with
  | zero =>
    rw [nMul_zero]
    exact GlobalTheory.BddAlg.intg_zero
  | succ n ih =>
    rw [nMul_succ]
    have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1
    refine GlobalTheory.BddAlg.Le.subst (c := 1) (fun j => ?_) (fun j => ?_) hF
    · fin_cases j
      · exact ih
      · exact hX
    · fin_cases j
      · exact nMul_constantCoeff F n
      · exact PowerSeries.constantCoeff_X

private lemma ev1_zero {K : Type} [NormedField K] (y : K) : ev1 (0 : PowerSeries K) y = 0 := by
  simp [ev1]

theorem nMul_point : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (F : FormalGroup K), Intg F.toPowerSeries → (∀ n, Intg (nMul F n)) ∧ ∀ x : K, ‖x‖ < 1 → ev1 (nMul F 0) x = 0 ∧ ev1 (nMul F 1) x = x ∧ (∀ j, ‖ev1 (nMul F j) x‖ ≤ ‖x‖ ∧ (‖(j : K)‖ = 1 → ‖ev1 (nMul F j) x‖ = ‖x‖)) ∧ (∀ i j, ev F.toPowerSeries ![ev1 (nMul F i) x, ev1 (nMul F j) x] = ev1 (nMul F (i + j)) x) ∧ (∀ i j, ev1 (nMul F i) (ev1 (nMul F j) x) = ev1 (nMul F (i * j)) x) ∧ (∀ y : K, ‖y‖ < 1 → ev F.toPowerSeries ![0, y] = y ∧ ev F.toPowerSeries ![y, 0] = y) := by
  intro K _ _ _ F hF
  have hI : ∀ n, Intg (nMul F n) := intg_nMul_for_point F hF
  have hB : Bdd F.toPowerSeries := GlobalTheory.BddAlg.bdd_of_intg hF
  have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1

  have hleft : MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_succ F 0
    rw [nMul_zero, nMul_one] at h
    exact h.symm
  have hright : MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_add F 1 0
    rw [nMul_zero, nMul_one] at h
    simpa using h
  refine ⟨hI, fun x hx => ?_⟩
  obtain ⟨-, -, -, hevX, -, -, hnorm, hsub, hpair, -, -⟩ := _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  refine ⟨by rw [nMul_zero]; exact ev1_zero x, by rw [nMul_one]; exact hevX, fun j => ?_,
    fun i j => ?_, fun i j => ?_, fun y hy => ?_⟩
  · obtain ⟨-, h1, h2⟩ := hnorm (nMul F j) (hI j)
    have h0 : PowerSeries.coeff 0 (nMul F j) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact nMul_constantCoeff F j
    rw [h0, sub_zero] at h1 h2
    rw [nMul_coeff_one] at h2
    refine ⟨h1, fun hj => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using h1
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hsq : ‖x‖ ^ 2 < ‖x‖ := by nlinarith
      have hjx : ‖(j : K) * x‖ = ‖x‖ := by rw [norm_mul, hj, one_mul]
      set v := ev1 (nMul F j) x
      have hlt : ‖v - (j : K) * x‖ < ‖(j : K) * x‖ := by rw [hjx]; exact lt_of_le_of_lt h2 hsq
      have hdecomp : v = (j : K) * x + (v - (j : K) * x) := by ring
      rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne',
        max_eq_left hlt.le, hjx]
  · rw [← hpair F.toPowerSeries (nMul F i) (nMul F j) hB (hI i) (hI j)
      (nMul_constantCoeff F i) (nMul_constantCoeff F j), nMul_add]
  · rw [← hsub (nMul F i) (nMul F j) (hI j) (nMul_constantCoeff F j)
      (GlobalTheory.BddAlg.bdd_of_intg (hI i)), nMul_subst_nMul]
  · obtain ⟨-, -, -, hevXy, -, -, -, -, hpairy, -, -⟩ := _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K y hy
    have hz : Intg (0 : PowerSeries K) := GlobalTheory.BddAlg.intg_zero
    have hc0 : PowerSeries.constantCoeff (0 : PowerSeries K) = 0 := by simp
    have hcX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
    constructor
    · have h := hpairy F.toPowerSeries 0 PowerSeries.X hB hz hX hc0 hcX
      rw [hleft, hevXy, ev1_zero] at h
      exact h.symm
    · have h := hpairy F.toPowerSeries PowerSeries.X 0 hB hX hz hcX hc0
      rw [hright, hevXy, ev1_zero] at h
      exact h.symm

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralMvPowerSeriesTwoEqZeroOfVanishOnSquares
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

private theorem intg_of_norm_coeff_le_one {K : Type} [NormedField K] (f : PowerSeries K)
    (h : ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) : Intg f := by
  intro ν
  have h1 := h (ν ())
  have h2 : ν = Finsupp.single () (ν ()) := Finsupp.unique_single ν
  rw [h2]
  exact h1

theorem integralPowerSeries_eq_zero_of_vanish_on_points (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : ℕ → Finset K) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hG : ∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1)
    (hT : Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0))
    (h : PowerSeries K) (hh : Intg h) (m : ℕ)
    (hz : ∀ n, m ≤ n → ∀ x ∈ G n, ev1 h x = 0) : h = 0 := by
  ext k
  have key : ‖PowerSeries.coeff k h‖ * r ^ k ≤ 0 := by
    refine ge_of_tendsto hT ?_
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    exact (GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros K h (G n) hh (fun x hx => ⟨(hG n x hx).2, hz n hn x hx⟩)).1 r hr hr1
      (fun x hx => (hG n x hx).1) k
  have hp : 0 < r ^ k := pow_pos hr k
  have h0 : ‖PowerSeries.coeff k h‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hc hp
    linarith
  simpa using norm_le_zero_iff.mp h0

theorem eq_zero_of_ev_vanish : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ H : MvPowerSeries (Fin 2) K, Intg H → (∀ n, ∀ x ∈ G n, ∀ y ∈ G n, ev H ![x, y] = 0) → H = 0 := by
  intro K _ _ _ G r hr hr1 hmono hG hT H hH hz
  have hS : ∀ (x y : K), ‖x‖ < 1 → ‖y‖ < 1 →
      Intg (shift1 H y) ∧ ev1 (shift1 H y) x = ev H ![x, y] := fun x y hx hy =>
    (GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx).2.2.2.2.2.2.2.2.2.1 H y hy hH
  have h1 : ∀ m, ∀ y ∈ G m, shift1 H y = 0 := by
    intro m y hy
    have hy1 := (hG m y hy).2
    refine integralPowerSeries_eq_zero_of_vanish_on_points K G r hr hr1 hG hT _ (hS 0 y (by simp) hy1).1 m ?_
    intro n hn x hx
    rw [(hS x y (hG n x hx).2 hy1).2]
    exact hz n x hx y (hmono hn hy)
  have h2 : ∀ a b : ℕ,
      MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 b) H = 0 := by
    intro a b
    have h3 : (PowerSeries.mk fun b : ℕ =>
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b) H) = 0 := by
      refine integralPowerSeries_eq_zero_of_vanish_on_points K G r hr hr1 hG hT _ (intg_of_norm_coeff_le_one _ ?_) 0 ?_
      · intro n
        rw [PowerSeries.coeff_mk]
        exact hH _
      · intro n _ y hy
        have h4 := congrArg (PowerSeries.coeff a) (h1 n y hy)
        rw [shift1, PowerSeries.coeff_mk, map_zero] at h4
        simpa [ev1, PowerSeries.coeff_mk] using h4
    have h5 := congrArg (PowerSeries.coeff b) h3
    rwa [PowerSeries.coeff_mk, map_zero] at h5
  ext ν
  have hν : ν = Finsupp.single 0 (ν 0) + Finsupp.single 1 (ν 1) := by
    ext i
    fin_cases i <;> simp
  rw [hν, h2]
  simp

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelSumNormSqLe
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_gl_size : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M),
    IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
    ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv b w hM hS hb hj hL
  have hj' : j ≤ 4 * n ^ 2 + 2 := by omega
  obtain ⟨hbv, hpos, -⟩ := GlobalTheory.shape_position n kk j ε μ bv hS hj'
  have hoff := GlobalTheory.T.unitaryGlModule_level_offDiag_normSq_le M n ε E μ kk j bv w hM hS hj' hL
  have hdiag := (GlobalTheory.T.weightNear_diagonalOperators_bounds M n ε E (lowK ε μ) (j : ℝ) w hM.2.1 hL.2).2.2
  have hd : ∀ a, ‖E a a w‖ ^ 2 ≤ (3 * bv) ^ 2 * ‖w‖ ^ 2 := by
    intro a
    refine hdiag a (3 * bv) ?_
    intro ω hω
    obtain ⟨h1, h2⟩ := hpos ω hω a
    rw [abs_le]
    by_cases h : a.val + 1 < kk
    · obtain ⟨h3, h4⟩ := h1 h
      constructor <;> linarith
    · obtain ⟨h3, h4⟩ := h2 (by omega)
      constructor <;> linarith
  have hn : (1 : ℝ) ≤ n := by
    have := hS.1
    have := hS.2.1
    exact_mod_cast (by omega : 1 ≤ n)
  have hbig : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv := hS.2.2.2.2.2
  have hsplit : ∑ a, ∑ c, ‖E a c w‖ ^ 2
      = ∑ a, ‖E a a w‖ ^ 2 + ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (Finset.add_sum_erase univ (fun c => ‖E a c w‖ ^ 2) (Finset.mem_univ a)).symm
  have hsum : ∑ a, ‖E a a w‖ ^ 2 ≤ n * ((3 * bv) ^ 2 * ‖w‖ ^ 2) := by
    calc ∑ a, ‖E a a w‖ ^ 2 ≤ ∑ _a : Fin n, (3 * bv) ^ 2 * ‖w‖ ^ 2 := Finset.sum_le_sum fun a _ => hd a
      _ = n * ((3 * bv) ^ 2 * ‖w‖ ^ 2) := by simp
  have hO : 0 ≤ ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  have hO' : ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 :=
    le_trans (le_mul_of_one_le_left hO hn) hoff
  have hn7 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ hn (by norm_num)
  have hb1 : 10 ^ 6 * (n : ℝ) ≤ bv := by linarith
  have hb2 : 9 * (n : ℝ) + 1 ≤ bv ^ 2 := by nlinarith
  have hb4 : bv ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ hbv.le hb 4
  have hc : (n : ℝ) * (3 * bv) ^ 2 + (bv / 16) ^ 2 ≤ b ^ 4 := by
    have h1 : (9 * (n : ℝ) + 1) * bv ^ 2 ≤ bv ^ 2 * bv ^ 2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg _)
    nlinarith [sq_nonneg bv]
  have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖w‖)
  rw [hsplit]
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjDualTensorLevelAddTwo
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem algTens_pr_single_lev :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)]
      [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s))
      (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ)
      (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr →
      Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
      ∀ c s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w)) := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hE hF hT hS _ hw c s
  obtain ⟨hlow, hsq⟩ := GlobalTheory.T.lowK_sub_single_sqrt_ckv_le n kk ε μ bv s hS
  obtain ⟨hw1, hw2⟩ := hw
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS1, hS2, hS3, hS4⟩ :=
      GlobalTheory.T.compactCasimirBound_projection_dualTensor M n ε E N F io pr _ w hE.2.1 (fun s => (hF s).2.1) hT h0 hw1 s c
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (add_nonneg h0 (Real.sqrt_nonneg _))
    push_cast
    linarith
  · have h1 := (GlobalTheory.T.wtNear_pr_and_io_of_algTens M n ε E N F io pr (lowK ε μ) (j : ℝ) hT).1 w hw2 s c
    refine wtNear_le_of_add_dist_le (N s) n ε (F s) _ _ _ _ ?_ h1
    have h2 : ∑ a, |lowK ε μ a - lowK ε (μ - Pi.single s 1) a| = 1 := by
      rw [hlow, Finset.sum_eq_single s]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    rw [h2]
    push_cast
    linarith

end GlobalTheory
end


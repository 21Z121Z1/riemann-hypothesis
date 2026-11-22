import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRootOpenDiscOfWeierstrassDegreeStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] (h : PowerSeries K) (d : ℕ), 0 < d → Intg h → ‖PowerSeries.coeff d h‖ = 1 → (∀ k < d, ‖PowerSeries.coeff k h‖ < 1) → ∃ x : K, ‖x‖ < 1 ∧ ev1 h x = 0 := by
  first | exact @GlobalTheory.ConvSer.exists_root_of_weierstrassDegree | exact GlobalTheory.ConvSer.exists_root_of_weierstrassDegree | (intros; apply GlobalTheory.ConvSer.exists_root_of_weierstrassDegree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscPropertiesStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (F : FormalGroup K), Intg F.toPowerSeries → (∀ n, Intg (nMul F n)) ∧ ∀ x : K, ‖x‖ < 1 → ev1 (nMul F 0) x = 0 ∧ ev1 (nMul F 1) x = x ∧ (∀ j, ‖ev1 (nMul F j) x‖ ≤ ‖x‖ ∧ (‖(j : K)‖ = 1 → ‖ev1 (nMul F j) x‖ = ‖x‖)) ∧ (∀ i j, ev F.toPowerSeries ![ev1 (nMul F i) x, ev1 (nMul F j) x] = ev1 (nMul F (i + j)) x) ∧ (∀ i j, ev1 (nMul F i) (ev1 (nMul F j) x) = ev1 (nMul F (i * j)) x) ∧ (∀ y : K, ‖y‖ < 1 → ev F.toPowerSeries ![0, y] = y ∧ ev F.toPowerSeries ![y, 0] = y) := by
  first | exact @GlobalTheory.ConvSer.nMul_point | exact GlobalTheory.ConvSer.nMul_point | (intros; apply GlobalTheory.ConvSer.nMul_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralMvPowerSeriesTwoEqZeroOfVanishOnSquaresStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralMvPowerSeries_two_eq_zero_of_vanish_on_squares : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ H : MvPowerSeries (Fin 2) K, Intg H → (∀ n, ∀ x ∈ G n, ∀ y ∈ G n, ev H ![x, y] = 0) → H = 0 := by
  first | exact @GlobalTheory.ConvSer.eq_zero_of_ev_vanish | exact GlobalTheory.ConvSer.eq_zero_of_ev_vanish | (intros; apply GlobalTheory.ConvSer.eq_zero_of_ev_vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantHermitianFormNonnegOfCloudEigen
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem hhJ_nonneg_of_cloud_eigen : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∀ s : Fin n, s.val + 1 < kk → splitCas E x = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • x → 0 ≤ (hhJ ε x x).re := by
  intro M _ _ n ε E μ kk j bv x hM hS hj hL s hs hx
  obtain ⟨hb, hω, hζ⟩ := GlobalTheory.shape_position n kk j ε μ bv hS hj
  have hO := GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level M n ε E μ kk j bv x hM hS hj hL
  set ζ : ℝ := -μ s + (1 - (n : ℝ)) / 2 with hζdef
  have hζs : ζ ≤ bv / 32 := ((hζ s).1 hs).2
  have hnode : ∀ c : Fin n, kk ≤ c.val + 1 →
      (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 ≤ ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 := by
    intro c hc
    have h1 := (GlobalTheory.wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hM.2.1 (hL c).2).2.1 c (ζ : ℂ)
      (15 * bv / 16) (by positivity) (by
        intro ω hw
        have h2 := ((hω ω hw c).2 hc).1
        rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
        have := neg_abs_le (ζ + ω c)
        linarith)
    have h3 := congrFun hx c
    simp only [splitCas, Pi.smul_apply] at h3
    rw [← Finset.add_sum_erase univ (fun a => E c a (x a)) (mem_univ c)] at h3
    have h4 : (ζ : ℂ) • x c + E c c (x c) = -∑ a ∈ univ.erase c, E c a (x a) := by
      rw [← h3]; abel
    rw [h4, norm_neg] at h1
    exact h1
  have hterm : ∀ c : Fin n, (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 - 2 * ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 ≤
      (15 * bv / 16) ^ 2 * ((if ε c then 1 else -1) * ⟪x c, x c⟫_ℂ : ℂ).re := by
    intro c
    have hin : (⟪x c, x c⟫_ℂ : ℂ).re = ‖x c‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x c)
    by_cases he : ε c = true
    · rw [if_pos he, one_mul, hin]
      have := sq_nonneg ‖∑ a ∈ univ.erase c, E c a (x a)‖
      linarith
    · have hc : kk ≤ c.val + 1 := by
        by_contra h
        exact he (hS.2.2.2.1 c (not_le.mp h)).1
      rw [if_neg he, neg_one_mul, Complex.neg_re, hin]
      have := hnode c hc
      linarith
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin n))) => hterm c)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum] at hsum
  have hS0 : 0 ≤ ∑ c, ‖x c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hpos : 0 < (15 * bv / 16) ^ 2 := by positivity
  have hkey : 0 ≤ (15 * bv / 16) ^ 2 * (hhJ ε x x).re := by
    unfold hhJ
    have : 0 ≤ bv ^ 2 * ∑ c, ‖x c‖ ^ 2 := mul_nonneg (sq_nonneg _) hS0
    nlinarith
  exact (mul_nonneg_iff_of_pos_left hpos).mp hkey

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirResolventCircleBounds
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem splitCasRes_norm_sq_le_weighted {M : Type} [NormedAddCommGroup M] (u v : M) :
    ‖u‖ ^ 2 ≤ 15 / 13 * ‖u + v‖ ^ 2 + 15 / 2 * ‖v‖ ^ 2 := by
  have htri : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
    calc ‖u‖ = ‖(u + v) - v‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖u + v‖ + ‖v‖ := norm_sub_le _ _
  have hsq : ‖u‖ ^ 2 ≤ (‖u + v‖ + ‖v‖) ^ 2 := by gcongr
  nlinarith [sq_nonneg (2 * ‖u + v‖ - 13 * ‖v‖)]

theorem splitCasRes_norm_add_sq_le {M : Type} [NormedAddCommGroup M] (u v : M) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    gcongr
    exact norm_add_le u v
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

theorem splitCasRes_circle_dist (b t : ℝ) (ζ : ℂ) (hζ : ‖ζ + ((b / 16 : ℝ) : ℂ)‖ = 9 * b / 16)
    (ht : (-b / 8 - b / 32 ≤ -t ∧ -t ≤ b / 32) ∨ b - b / 32 ≤ -t) :
    15 * b / 32 ≤ ‖ζ + (t : ℂ)‖ := by
  have hb : 0 ≤ b := by
    have := norm_nonneg (ζ + ((b / 16 : ℝ) : ℂ))
    linarith
  have hsplit : ζ + (t : ℂ) = (ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ) := by
    push_cast
    ring
  have hshift : ‖((t - b / 16 : ℝ) : ℂ)‖ = |t - b / 16| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hsplit]
  rcases ht with ⟨h1, h2⟩ | h3
  ·
    have hclose : |t - b / 16| ≤ 3 * b / 32 := by
      rw [abs_le]
      constructor <;> linarith
    have key := norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) ((t - b / 16 : ℝ) : ℂ)
    rw [add_sub_cancel_right, hζ, hshift] at key
    linarith
  ·
    have hfar : 33 * b / 32 ≤ |t - b / 16| := by
      have := neg_le_abs (t - b / 16)
      linarith
    have key := norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) (ζ + ((b / 16 : ℝ) : ℂ))
    rw [add_sub_cancel_left, hζ, hshift] at key
    linarith

theorem splitCas_resolvent_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → (∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → (13 * bv / 32) ^ 2 * ∑ c, ‖x c‖ ^ 2 ≤ ∑ c, ‖ζ • x c - splitCas E x c‖ ^ 2) ∧ ∑ c, ‖splitCas E x c‖ ^ 2 ≤ (3 * bv) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv x hmod hshape hj hlev
  obtain ⟨hbv, hω, -⟩ := shape_position n kk j ε μ bv hshape hj
  have hun : IsUnitary ε E := hmod.2.1
  have hoff : ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 :=
    GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level M n ε E μ kk j bv x hmod hshape hj hlev
  have hsplit : ∀ b, splitCas E x b = -(E b b (x b) + ∑ c ∈ univ.erase b, E b c (x c)) := by
    intro b
    simp only [splitCas]
    congr 1
    exact (Finset.add_sum_erase univ (fun c => E b c (x c)) (Finset.mem_univ b)).symm
  have hdiag := fun c => wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hun (hlev c).2
  have hS : 0 ≤ ∑ c, ‖x c‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  constructor
  · intro ζ hζ
    have hlow : ∀ b, (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2 ≤ ‖ζ • x b + E b b (x b)‖ ^ 2 := by
      intro b
      refine (hdiag b).2.1 b ζ (15 * bv / 32) (by positivity) ?_
      intro ω hωn
      apply splitCasRes_circle_dist bv (ω b) ζ hζ
      obtain ⟨h1, h2⟩ := hω ω hωn b
      by_cases hb : b.val + 1 < kk
      · exact Or.inl (h1 hb)
      · exact Or.inr (h2 (by omega)).1
    have hper : ∀ b, 13 / 15 * (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2
        - 13 / 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ ‖ζ • x b - splitCas E x b‖ ^ 2 := by
      intro b
      have hw := splitCasRes_norm_sq_le_weighted (ζ • x b + E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))
      have he : ζ • x b - splitCas E x b
          = (ζ • x b + E b b (x b)) + ∑ c ∈ univ.erase b, E b c (x c) := by
        rw [hsplit]
        abel
      rw [he]
      nlinarith [hlow b]
    have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    nlinarith [hoff, hsum, mul_nonneg (sq_nonneg bv) hS]
  · have hD : ∀ b, ‖E b b (x b)‖ ^ 2 ≤ (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2 := by
      intro b
      refine (hdiag b).2.2 b (65 * bv / 32) ?_
      intro ω hωn
      obtain ⟨h1, h2⟩ := hω ω hωn b
      rw [abs_le]
      by_cases hb : b.val + 1 < kk
      · obtain ⟨a1, a2⟩ := h1 hb
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := h2 (by omega)
        constructor <;> linarith
    have hper : ∀ b, ‖splitCas E x b‖ ^ 2
        ≤ 2 * (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2 + 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 := by
      intro b
      rw [hsplit, norm_neg]
      have ha := splitCasRes_norm_add_sq_le (E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))
      nlinarith [hD b]
    have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    nlinarith [hoff, hsum, mul_nonneg (sq_nonneg bv) hS]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelSumNormSqLeStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M), IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.lev_gl_size | exact GlobalTheory.lev_gl_size | (intros; apply GlobalTheory.lev_gl_size <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwoStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_glModule_proj_components_level_add_two : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (j : ℕ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → Lev ε E μ j w → ∀ s c d, Lev ε E μ (j + 2) (io s (pr s (Pi.single c w)) d) := by
  first | exact @GlobalTheory.lev_io_pr_single | exact GlobalTheory.lev_io_pr_single | (intros; apply GlobalTheory.lev_io_pr_single <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjDualTensorLevelAddTwoStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_glModule_proj_dual_tensor_level_add_two : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w)) := by
  first | exact @GlobalTheory.algTens_pr_single_lev | exact GlobalTheory.algTens_pr_single_lev | (intros; apply GlobalTheory.algTens_pr_single_lev <;> assumption)
end


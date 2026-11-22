import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0061
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0067
import Formalism.HermitianCurvature.Bundle0005
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0005
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0026
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0053
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarginArithClosing
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

theorem margin_arith_closing : ∀ Cc C₀ : ℝ, 0 ≤ C₀ → ∃ Cg₀ : ℝ, 0 ≤ Cg₀ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ (k r n₀ p₀ : ℕ) (h d : ℝ), 1 ≤ k → n₀ ≤ 30 * (r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((r : ℝ) + 1) ^ 2 → Cg * (((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ≤ h → 0 ≤ d → (Cc * ((r : ℝ) + 1) ^ 4 * (((3 * (r + 1) : ℕ) : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ (ThreeDimData.aOf r (h / 2) - 1) - (((2 * r + 2) * p₀ + n₀ * (r + 1) : ℕ) : ℝ)) ∧ d + (((2 * r + 2) * p₀ + n₀ * (r + 1) : ℕ) : ℝ) ≤ max (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3) (200 * d) / 2 - 1 ∧ (((r + 1) * (2 * p₀ + n₀) + (r + 1) * (r + 2) : ℕ) : ℝ) ≤ (C₀ + 10) * ((2 * r + 2 : ℕ) : ℝ) ^ 3 := by
  intro Cc C₀ hC₀
  have habs : 0 ≤ |Cc| := abs_nonneg _
  have hle : Cc ≤ |Cc| := le_abs_self _
  refine ⟨|Cc| + C₀ + 40, by linarith, ?_⟩
  intro Cg hCg k r n₀ p₀ h d hk hn hp hh hd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn' : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  unfold ThreeDimData.aOf
  push_cast at hh ⊢
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (r : ℝ) + 1 := ⟨_, rfl⟩
  have hrR : (r : ℝ) = R - 1 := by linarith
  have e1 : 2 * (r : ℝ) + 2 = 2 * R := by linarith
  have e2 : (r : ℝ) + 2 = R + 1 := by linarith
  rw [e1] at hh ⊢
  rw [e2]
  rw [← hR] at hh hn' hp ⊢
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 2 * (r : ℝ) + k + 1 := ⟨_, rfl⟩
  rw [← hN] at hh ⊢
  have hN2 : 2 ≤ N := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 3 * R * N ^ 2 + N ^ 3 := ⟨_, rfl⟩
  rw [← hQ] at hh ⊢
  have hQ1 : 2 ≤ Q := by
    have h1 : 0 ≤ 3 * R * N ^ 2 := by positivity
    have h2 : (2 : ℝ) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN2 3
    linarith
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR1
  have hR23 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  have hR13 : R ≤ R ^ 3 := by
    have := pow_le_pow_right₀ hR1 (show 1 ≤ 3 by norm_num)
    simpa using this
  have hR34 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
  have hA : R * p₀ ≤ C₀ * R ^ 3 := by
    have := mul_le_mul_of_nonneg_left hp hR0.le
    calc R * p₀ ≤ R * (C₀ * R ^ 2) := this
      _ = C₀ * R ^ 3 := by ring
  have hB : R * n₀ ≤ 36 * R ^ 3 := by
    have := mul_le_mul_of_nonneg_left hn' hR0.le
    calc R * n₀ ≤ R * (30 * R ^ 2 + 6) := this
      _ = 30 * R ^ 3 + 6 * R := by ring
      _ ≤ _ := by linarith
  have hC3 : 0 ≤ C₀ * R ^ 3 := by positivity
  have hCg0 : 0 ≤ Cg := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hs : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by linarith)
    have hpow : (2 * R) ^ ((9 : ℝ) / 2) = (2 * R) ^ 4 * Real.sqrt (2 * R) := by
      rw [Real.sqrt_eq_rpow, show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num,
        Real.rpow_add (by linarith), Real.rpow_natCast]
    rw [hpow] at hh
    have h1 : Cg * (R ^ 4 * Q) ≤ h / 2 / (8 * Real.sqrt (2 * R)) := by
      rw [le_div_iff₀ (by positivity)]
      have : Cg * (R ^ 4 * Q) * (8 * Real.sqrt (2 * R))
          = Cg * ((2 * R) ^ 4 * Real.sqrt (2 * R) * Q) / 2 := by ring
      rw [this]
      linarith
    have hX : 2 * R ^ 3 ≤ R ^ 4 * Q := by
      have : R ^ 4 * 2 ≤ R ^ 4 * Q := mul_le_mul_of_nonneg_left hQ1 (by positivity)
      linarith
    have hX0 : 0 ≤ R ^ 4 * Q := by linarith
    have h2 : (|Cc| + C₀ + 40) * (R ^ 4 * Q) ≤ Cg * (R ^ 4 * Q) :=
      mul_le_mul_of_nonneg_right hCg hX0
    have h3 : Cc * (R ^ 4 * Q) ≤ |Cc| * (R ^ 4 * Q) := mul_le_mul_of_nonneg_right hle hX0
    have h4 : C₀ * (2 * R ^ 3) ≤ C₀ * (R ^ 4 * Q) := mul_le_mul_of_nonneg_left hX hC₀
    nlinarith
  · have h1 := le_max_left (Cg * (2 * R) ^ 3) (200 * d)
    have h2 := le_max_right (Cg * (2 * R) ^ 3) (200 * d)
    have h3 : (C₀ + 40) * R ^ 3 ≤ Cg * R ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : Cg * (2 * R) ^ 3 = 8 * (Cg * R ^ 3) := by ring
    nlinarith
  · nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorStProdRange
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

@[to_additive]
theorem minorSt_prod_range {M : Type} [CommMonoid M] {N r : ℕ} (hr : r ≤ N) (g : ℕ → M)
    (hg : ∀ s, ¬ (1 ≤ s ∧ s ≤ r) → g s = 1) :
    ∏ s ∈ Finset.range (N + 1), g s = ∏ s : Fin r, g (s.val + 1) := by
  rw [Finset.prod_range_succ', hg 0 (by omega), _root_.mul_one, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) r]
  symm
  apply Finset.prod_subset (Finset.range_subset_range.mpr hr)
  intro s _ hs
  apply hg
  rw [Finset.mem_range] at hs
  omega

theorem minorSt : MinorSt := by
  classical
  intro E _ _ _ H Dw K _ typ m n₁ n₂ hm
  let rk : (E →+* ℂ) → ℕ := fun τ => min (Dw.mult τ) (if typ τ then n₁ else n₂)
  have hrk : ∀ τ, rk τ ≤ Dw.mult τ := fun τ => min_le_left _ _
  have hrk1 : ∀ τ, typ τ → rk τ ≤ n₁ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hrk2 : ∀ τ, ¬ typ τ → rk τ ≤ n₂ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hm0 : ∀ τ s, ¬ (1 ≤ s ∧ s ≤ rk τ) → m τ s = 0 := by
    intro τ s hs
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hm τ s h
    exact hs ⟨h1, le_min h2 h3⟩
  let col : ∀ τ, Fin (rk τ) → Fin (n₁ + n₂) := fun τ i =>
    if h : typ τ then Fin.castAdd n₂ (Fin.castLE (hrk1 τ h) i) else Fin.natAdd n₁ (Fin.castLE (hrk2 τ h) i)
  refine ⟨rk, hrk, col, fun τ s => m τ (s.val + 1), ?_, ?_, ?_, ?_⟩
  · intro τ i j hij
    by_cases h : typ τ
    · simp only [col, dif_pos h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
    · simp only [col, dif_neg h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
  · intro τ i
    by_cases h : typ τ
    · have := hrk1 τ h
      have := i.isLt
      simp only [col, dif_pos h, h, iff_true, Fin.val_castAdd, Fin.val_castLE]
      omega
    · simp [col, h]
  · unfold degOf
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [minorSt_sum_range (hrk τ) (fun s => s * m τ s) (fun s hs => by simp [hm0 τ s hs])]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  · unfold minorProd FamGerm.minorsP
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod]
    by_cases h : typ τ
    · rw [if_pos h, if_neg (not_not.mpr h), _root_.mul_one,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₁ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk1 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_pos h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl
    · rw [if_neg h, if_pos h, _root_.one_mul,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₂ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk2 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_neg h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumOfStdHyp
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory.BpStdNum

theorem gapOK_of (k r : ℕ) (hk : 1 ≤ k) (h : ℝ)
    (hh : 10 ^ 6 * (((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ≤ h) :
    ThreeDimData.GapOK k r (h / 4) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = 2 * ((r : ℝ) + 1) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = 2 * (r : ℝ) + k + 1 := ⟨_, rfl⟩
  have em : ((2 * r + 2 : ℕ) : ℝ) = m := by rw [hm]; push_cast; ring
  have en : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  have hm1 : 1 ≤ m := by linarith
  have hmn : m ≤ n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hs1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm1
  have e9 : m ^ ((9 : ℝ) / 2) = m ^ 4 * Real.sqrt m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    norm_num
  rw [em, en, e9] at hh
  have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
  have hm4 : 1 ≤ m ^ 4 := one_le_pow₀ hm1
  have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ hn1
  have ha : 1000 * (m ^ 4 * n ^ 3) ≤ ThreeDimData.aOf r (h / 4) := by
    unfold ThreeDimData.aOf
    rw [← hm, le_div_iff₀ (by positivity)]
    have : 0 ≤ m ^ 4 * Real.sqrt m * n ^ 3 := by positivity
    nlinarith
  have hM : ThreeDimData.Mexp r ≤ m ^ 2 := by unfold ThreeDimData.Mexp; rw [hm]; nlinarith
  have hM0 : 0 ≤ ThreeDimData.Mexp r := by unfold ThreeDimData.Mexp; positivity
  have hG : ThreeDimData.AG k r ≤ 4 * n ^ 2 := by unfold ThreeDimData.AG; rw [hn]; nlinarith
  have hG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hd : ThreeDimData.dN k r ≤ n ^ 2 := by unfold ThreeDimData.dN; rw [hn]; nlinarith
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have hm24 : m ^ 2 ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hS : ThreeDimData.AS k r ≤ n ^ 3 := by
    unfold ThreeDimData.AS
    have h1 : ((2 * r + k : ℕ) : ℝ) ≤ n := by rw [hn]; push_cast; linarith
    calc ((2 * r + k : ℕ) : ℝ) * ThreeDimData.dN k r ≤ ((2 * r + k : ℕ) : ℝ) * n ^ 2 :=
          mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
      _ ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = n ^ 3 := by ring
  have hX : n ^ 3 ≤ m ^ 4 * n ^ 3 := le_mul_of_one_le_left (by positivity) hm4
  refine ⟨hk, ?_, ?_, ?_⟩
  · rw [en]
    have : m ^ 4 * n ^ 3 ≤ m ^ 4 * Real.sqrt m * n ^ 3 := by
      have := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ m ^ 4 * n ^ 3 by positivity)
      linarith
    linarith
  · have h1 : ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ m ^ 4 * (5 * n ^ 3) :=
      calc _ ≤ ThreeDimData.Mexp r * (5 * n ^ 3) := mul_le_mul_of_nonneg_left (by linarith) hM0
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  · rw [en]
    have h1 : ((r : ℝ) + 1) * n ^ 2 ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : n * n ^ 2 = n ^ 3 := by ring
    linarith

section
variable {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ}

theorem lt_left (hk : 1 ≤ k)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : a.val < k) : lam a < u (a.val + 1) := by
  by_cases h : a.val + 1 < k
  · exact (hI.1 a.val h).1
  · have h2 := hI.2 (by omega)
    have e : a = ⟨k - 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e]; exact h2

theorem lt_right
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < k) : u (a.val + 2) < lam a :=
  (hI.1 a.val ha).2

theorem cloud_of
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < k) :
    IsCloud (fun i : Fin k => u (i.val + 1)) lam a :=
  ⟨⟨⟨a.val, by omega⟩, (hI.1 a.val ha).1⟩, ⟨⟨a.val + 1, ha⟩, (hI.1 a.val ha).2⟩⟩

theorem not_cloud_of (hk : 1 ≤ k) (hA : StrictAnti lam)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : k ≤ a.val + 1) :
    ¬ IsCloud (fun i : Fin k => u (i.val + 1)) lam a := by
  rintro ⟨-, i, hi⟩
  have hik := i.isLt
  have key : ∀ j : ℕ, j < k → lam a < u (k - 1 - j + 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have h1 := lt_left hk hI ⟨k - 1, by omega⟩ (by simp only; omega)
      have h2 : lam a ≤ lam ⟨k - 1, by omega⟩ := hA.antitone (by
        rw [Fin.le_def]; simp only; omega)
      simp only [Nat.sub_zero] at h1 ⊢
      linarith
    | succ j ih =>
      intro hj
      have h0 := ih (by omega)
      have h1 := hI.1 (k - 1 - (j + 1)) (by omega)
      simp only at h1
      have e : k - 1 - (j + 1) + 1 = k - 1 - j := by omega
      have h4 : u (k - 1 - (j + 1) + 1 + 1) < u (k - 1 - (j + 1) + 1) := lt_trans h1.2 h1.1
      rw [e] at h4 ⊢
      linarith
  have h3 := key (k - 1 - i.val) (by omega)
  have e : k - 1 - (k - 1 - i.val) = i.val := by omega
  rw [e] at h3
  simp only at hi
  linarith

theorem half_of (hH : Formalism.QuantumDeterminants.IsHCParam lam)
    (hu : ∀ i ∈ Finset.Icc 1 k, ∃ a : ℤ, u i = (a : ℝ) + ((k : ℝ) - 1) / 2) :
    ∀ a, ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ, lam a - u i = (m : ℝ) + 1 / 2 := by
  intro a i hi
  obtain ⟨x, hx⟩ := hH.2 a
  obtain ⟨y, hy⟩ := hu i hi
  refine ⟨x - y + r, ?_⟩
  push_cast at hx ⊢
  linarith

theorem bound_of {b : ℝ} (hb : ∀ i : Fin k, |u (i.val + 1)| ≤ b) : ∀ i ∈ Finset.Icc 1 k, |u i| ≤ b := by
  intro i hi
  rw [Finset.mem_Icc] at hi
  have := hb ⟨i - 1, by omega⟩
  simp only at this
  rwa [Nat.sub_add_cancel hi.1] at this

end

theorem num_of_stdHyp : ∀ Cq : ℝ, 0 ≤ Cq → ∃ Cg₀ : ℝ, ∀ (Ch Cg : ℝ), Cg₀ ≤ Cg → ∀ (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (T T' ka b d : ℝ) (q0 : ℕ), 2 ≤ P.k → StdHyp Ch Cg P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) lam (fun i => P.u (i.val + 1)) (fun i => P.u' (i.val + 1)) T T' ka b → (∀ i ∈ Finset.Icc 1 P.k, (∃ a : ℤ, P.u i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) ∧ ∃ a : ℤ, P.u' i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) → 0 ≤ d → AllGaps lam (200 * d) → (q0 : ℝ) ≤ d + Cq * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 → ∃ bv ga h : ℝ, BranchingSupport.Num P.k P.r lam P.u b bv ga h q0 ∧ BranchingSupport.Num P.k P.r lam P.u' b bv ga h q0 ∧ Cg * (((2 * P.r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (P.r + 1) : ℕ) : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 3)) ≤ h := by
  intro Cq hCq
  refine ⟨10 ^ 6 + 200 * Cq, ?_⟩
  intro Ch Cg hCg P lam T T' ka b d q0 hk hS hint hd hgd hq
  obtain ⟨hH, hI, hI', -, -, -, -, -, -, -, hbl, hbu, hbu', hga, hgap, ⟨bv, hbv, hsh⟩, -⟩ := hS
  have hk1 : 1 ≤ P.k := by omega
  have hCg6 : (10 : ℝ) ^ 6 ≤ Cg := by linarith
  rw [mul_assoc] at hgap
  set h0 : ℝ := Cg * (((2 * P.r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (P.r + 1) : ℕ) : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 3)) with hh0
  set ga : ℝ := max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) (200 * d) with hgadef
  have hall : AllGaps lam ga := fun s s' hs => max_le (hga s s' hs) (hgd s s' hs)
  have hm3 : (1 : ℝ) ≤ ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * P.r + 2))
  have hq' : 100 * ((q0 : ℝ) + 1) ≤ ga := by
    have h1 : Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 ≤ ga := le_max_left _ _
    have h2 : 200 * d ≤ ga := le_max_right _ _
    have h3 := mul_le_mul_of_nonneg_right hCg (le_trans zero_le_one hm3)
    nlinarith
  have hgap' : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) lam (max h0 ga) := by
    intro a c hac
    exact max_le (hgap a c hac) (hall a c (fun e => hac (by rw [e])))
  have hok : ThreeDimData.GapOK P.k P.r (max h0 ga / 4) := by
    apply gapOK_of _ _ hk1
    refine le_trans ?_ (le_max_left _ _)
    rw [hh0]
    apply mul_le_mul hCg6 _ (by positivity) (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_left (by positivity)
  have hcl : ∀ a c : Fin (2 * P.r + P.k + 1), a < c → c.val + 1 < P.k → ga ≤ lam a - lam c := by
    intro a c hac _
    have := hall a c hac.ne
    rwa [abs_of_pos (sub_pos.mpr (hH.1 hac))] at this
  have hbv' : 10 ^ 6 * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv :=
    le_trans (mul_le_mul_of_nonneg_right hCg6 (by positivity)) hbv
  have hs1 : ∀ a : Fin (2 * P.r + P.k + 1), a.val + 1 < P.k → 0 ≤ lam a ∧ lam a ≤ bv / 8 :=
    fun a ha => (hsh a).1 (cloud_of hI a ha)
  have hs2 : ∀ a : Fin (2 * P.r + P.k + 1), P.k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv :=
    fun a ha => (hsh a).2 (not_cloud_of hk1 hH.1 hI a ha)
  refine ⟨bv, ga, max h0 ga, ?_, ?_, le_max_left _ _⟩
  · exact ⟨hk1, hH, half_of hH (fun i hi => (hint i hi).1), lt_left hk1 hI, lt_right hI, hs1, hs2, hbl,
      bound_of hbu, hcl, hgap', hok, hq', le_trans hq' (le_max_right _ _), hbv'⟩
  · exact ⟨hk1, hH, half_of hH (fun i hi => (hint i hi).2), lt_left hk1 hI', lt_right hI', hs1, hs2, hbl,
      bound_of hbu', hcl, hgap', hok, hq', le_trans hq' (le_max_right _ _), hbv'⟩

end GlobalTheory.BpStdNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quotMeas_ae_mem_and_measurable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq hR hS
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r := by
    obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    exact Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  have hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := by
    convert (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl using 1
    ext x
    simp
  have hrestr : νq.restrict {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} = νq :=
    Measure.restrict_eq_self_of_ae_mem hae
  have hcont : ∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V),
      ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq := by
    intro V _ _ φ hφ
    have hof : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mx k r)) := continuous_id
    have h1 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} :=
      hφ.comp hof.continuousOn (fun x hx => hx)
    have h2 := h1.aestronglyMeasurable (μ := νq) hmeas
    rwa [hrestr] at h2
  refine ⟨hae, hcont, ?_, ?_⟩
  · intro a
    exact (hcont ℝ _ (GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a)).aemeasurable
  · intro l hl w hw
    exact hcont Wp _ (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 w hw).1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SabBaseChangeStIffFree
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabPullCompare

variable {S S' : Scheme.{0}}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def FreeConcl (t : SAB H S) (f : S' ⟶ S) (PP' : RigLB ((Over.pullback f).obj t.G)) : Prop :=
  ∃ (semi : IsSemiAbelian ((Over.pullback f).obj t.G)) (act : OAct (𝓞 E) ((Over.pullback f).obj t.G))
    (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric)
    (adj : ∀ a, LBIso (cubeLB _ ![fst _ _ ≫ act.act a, snd _ _] PP'.L)
      (cubeLB _ ![fst _ _, snd _ _ ≫ act.act (H.bar a)] PP'.L))
    (prim : LBIso PP'.L (cubeLB _ ![𝟙 _, act.act H.w0] PP'.L)),
    Nonempty (SABMap ⟨(Over.pullback f).obj t.G, semi, act, PP', cub, sym, adj, prim⟩ t f)

def PinnedConcl (t : SAB H S) (f : S' ⟶ S) (PP' : RigLB ((Over.pullback f).obj t.G)) : Prop :=
  ∃ (semi : IsSemiAbelian ((Over.pullback f).obj t.G)) (act : OAct (𝓞 E) ((Over.pullback f).obj t.G))
    (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric)
    (adj : ∀ a, LBIso (cubeLB _ ![fst _ _ ≫ act.act a, snd _ _] PP'.L)
      (cubeLB _ ![fst _ _, snd _ _ ≫ act.act (H.bar a)] PP'.L))
    (prim : LBIso PP'.L (cubeLB _ ![𝟙 _, act.act H.w0] PP'.L))
    (m : SABMap ⟨(Over.pullback f).obj t.G, semi, act, PP', cub, sym, adj, prim⟩ t f),
    m.φ = pullback.fst t.G.hom f

theorem lbIso_cubeLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cubeLB_isLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

end GlobalTheory.SabPullCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleStandardStatement
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCasimir_eigenspace_irreducible_standard_alt : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + 0)) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + 0) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + 0)) ∧ Module.End.eigenspace Om (β + L l + 0) ≤ CapSp Et (shf β (Function.update L l (L l + 1))) := by
  first | exact @GlobalTheory.splitCasimir_eigenspace_irreducible_standard | exact GlobalTheory.splitCasimir_eigenspace_irreducible_standard | (intros; apply GlobalTheory.splitCasimir_eigenspace_irreducible_standard <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarProjectionSplitCasimirRaisingLast
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem starProjection_splitCasimirStd_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hadj hEt hOm M v hv
  have hq : ∀ w v, qdet E w v = (∏ j, (w + shf β L j)) • v := hH.cap
  obtain ⟨K, hK, hK'⟩ := comatrix_last_row_inverts_casimir V n E Om (shf β L) hH.gl hq hOm
  obtain ⟨-, -, hsym, -⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hH.gl hadj hEt hOm
  have hev := splitCasimirStd_eigenvalue V n E Et Om (shf β L) hH.gl hadj hq hEt hOm
  have hinj : Function.Injective (shf β L) := by
    intro a b h
    apply hH.anti.injective
    have h' : (L a : ℂ) = (L b : ℂ) := add_left_cancel h
    exact_mod_cast h'
  have hcont : Continuous fun u : ℂ => cpol (shf β M) (u - 1) := by
    unfold cpol
    fun_prop
  have h := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    (shf β L) 0 Om (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) (Fin.last n)) K
    (fun u : ℂ => cpol (shf β M) (u - 1)) (PiLp.single 2 (Fin.last n) v) v l hinj hsym hev hK hcont
    (fun u => (hK' u v).trans (mem_CapSp.1 hv (u - 1)))
  refine Eq.trans h ?_
  congr 1
  simp only [cpol, shf, WigSh.wP]
  push_cast
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by ring
  · exact Finset.prod_congr rfl fun j _ => by ring

end GlobalTheory
end


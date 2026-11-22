import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.Bundle0001
import Formalism.PeriodIntegrals.Bundle0009

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.NnrealOfEnnreal
section
namespace PI.Residue

open NumberField
open scoped ENNReal NNReal

noncomputable def wt (s : ℝ) : ℕ →* ℝ≥0∞ where
  toFun n := (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞)
  map_one' := by simp
  map_mul' a b := by
    rw [Nat.cast_mul, NNReal.mul_rpow, ENNReal.coe_mul]

theorem wt_apply (s : ℝ) (n : ℕ) : wt s n = (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞) := rfl

theorem nnreal_of_ennreal {β : Type*} (f : β → ℝ≥0) (g : ℕ → ℝ≥0) (m : ℕ) (hg : Summable g)
    (h : ∑' b, (f b : ℝ≥0∞) ≤ (∑' k, (g k : ℝ≥0∞)) ^ m) :
    Summable f ∧ ∑' b, f b ≤ (∑' k, g k) ^ m := by
  rw [← ENNReal.coe_tsum hg, ← ENNReal.coe_pow] at h
  have hf : Summable f :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp (ne_top_of_le_ne_top ENNReal.coe_ne_top h)
  refine ⟨hf, ?_⟩
  rw [← ENNReal.coe_tsum hf] at h
  exact_mod_cast h

theorem zetaLePow : ZetaLePow := by
  intro E _ _ s hs
  have h := tsum_ideal_le E (wt s)
  have h0 : wt s 0 = 0 := by
    rw [wt_apply, Nat.cast_zero, NNReal.zero_rpow (by linarith : -s ≠ 0), ENNReal.coe_zero]
  rw [tsum_eq_zero_add' ENNReal.summable, h0, zero_add] at h
  simp only [wt_apply] at h
  have hg : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0) ^ (-s))) := by
    rw [← NNReal.summable_coe]
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s < -1))
    simpa using this
  obtain ⟨hf, hle⟩ := nnreal_of_ennreal
    (fun I : {I : Ideal (𝓞 E) // I ≠ ⊥} => ((Ideal.absNorm I.1 : ℝ≥0) ^ (-s))) _ _ hg h
  constructor
  · have := NNReal.summable_coe.mpr hf
    simpa using this
  · have := NNReal.coe_le_coe.mpr hle
    rw [NNReal.coe_tsum, NNReal.coe_pow, NNReal.coe_tsum] at this
    simpa [idealZeta, zetaR] using this

end PI.Residue
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.ResidueBoundOf
section
open NumberField

namespace PI.Residue

theorem residueBound_of (hA1 : ZetaLePow) (hA2 : ZetaRLe) (hB : HeckeLower) (hC : Optimise) :
    PI.ResidueBound := by
  obtain ⟨C, hC1, hC⟩ := hC
  refine ⟨C, hC1, fun E _ _ hm => ?_⟩
  have hd : 4 / 9 * (3 * Real.pi / 4) ^ Module.finrank ℚ E ≤ ((|discr E| : ℤ) : ℝ) := by
    have := NumberField.abs_discr_ge (K := E) (by omega)
    exact_mod_cast this
  obtain ⟨s, hs, hle⟩ := hC (Module.finrank ℚ E) _ hm hd
  obtain ⟨hsum, hz⟩ := hA1 E s hs
  refine (hB E s hs hsum).trans (le_trans ?_ hle)
  have hd0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  have hz0 : 0 ≤ zetaR s := tsum_nonneg fun n => by positivity
  gcongr
  exact hz.trans (pow_le_pow_left₀ hz0 (hA2 s hs) _)

end PI.Residue
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.SumRangeLe
section
namespace PI.Residue

open MeasureTheory intervalIntegral

theorem sum_range_le (s : ℝ) (hs : 1 < s) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) ≤ 1 / (s - 1) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (1 : ℝ) (1 + N)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  refine h1.trans ?_
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + N) := by
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
  have hpos : 0 < s - 1 := by linarith
  have hN : 0 ≤ ((1 : ℝ) + N) ^ (-s + 1) := by positivity
  rw [Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, neg_sub]
  rw [show -(s - 1) = -s + 1 by ring]
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith

theorem zetaRLe : ZetaRLe := by
  intro s hs
  unfold zetaR
  have hpos : 0 < s - 1 := by linarith
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro n
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    | succ N =>
      rw [Finset.sum_range_succ']
      have := sum_range_le s hs N
      have e : ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) + 1) ^ (-s)
          = ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [add_comm]
      rw [e]
      simp only [Nat.cast_zero, zero_add, Real.one_rpow]
      linarith

end PI.Residue
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.ThirdLeLog
section
namespace PI.Residue

theorem third_le_log : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h3 : Real.exp (1 / 3) ^ 3 ≤ (3 / 2 : ℝ) ^ 3 := by
    rw [← Real.exp_nat_mul]
    have : ((3 : ℕ) : ℝ) * (1 / 3) = 1 := by norm_num
    rw [this]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h3

theorem pow_le_lower (m : ℕ) (hm : 2 ≤ m) :
    (3 / 2 : ℝ) ^ m ≤ 4 / 9 * (3 * Real.pi / 4) ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hpi := Real.pi_gt_three
  have h1 : (3 / 2 : ℝ) ^ k ≤ (3 * Real.pi / 4) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith) k
  have h2 : (3 / 2 : ℝ) ^ 2 ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by nlinarith
  have h3 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ k := by positivity
  have h4 : (0 : ℝ) ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by positivity
  calc (3 / 2 : ℝ) ^ (2 + k) = (3 / 2 : ℝ) ^ 2 * (3 / 2 : ℝ) ^ k := pow_add _ _ _
    _ ≤ (4 / 9 * (3 * Real.pi / 4) ^ 2) * (3 * Real.pi / 4) ^ k := mul_le_mul h2 h1 h3 h4
    _ = 4 / 9 * (3 * Real.pi / 4) ^ (2 + k) := by rw [pow_add]; ring

theorem optimise : Optimise := by
  refine ⟨128 * Real.pi * Real.exp (1 / 2), ?_, ?_⟩
  · have hpi := Real.pi_gt_three
    have he : 1 ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
    nlinarith
  intro m D hm hD
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hD1 : (3 / 2 : ℝ) ^ m ≤ D := (pow_le_lower m hm).trans hD
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD1
  set l : ℝ := Real.log (D ^ ((1 : ℝ) / m)) with hl
  have hlD : Real.log D = m * l := by
    rw [hl, Real.log_rpow hDpos]
    field_simp
  have hl3 : 1 / 3 ≤ l := by
    have h1 : Real.log ((3 / 2 : ℝ) ^ m) ≤ Real.log D := Real.log_le_log (by positivity) hD1
    rw [Real.log_pow, hlD] at h1
    have h2 : Real.log (3 / 2) ≤ l := le_of_mul_le_mul_left h1 hm0
    exact third_le_log.trans h2
  have hlpos : 0 < l := by linarith
  refine ⟨1 + 1 / l, by linarith [one_div_pos.mpr hlpos], ?_⟩
  have e1 : (1 + 1 / l - 1) = 1 / l := by ring
  rw [e1, one_div_one_div]

  have hDexp : D ^ (1 / l / 2) = Real.exp (1 / 2) ^ m := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hDpos, hlD]
    congr 1
    field_simp

  have h4 : (4 : ℝ) ^ (1 + 1 / l) ≤ 16 ^ m := by
    have hle : 1 + 1 / l ≤ 4 := by
      have : 1 / l ≤ 3 := by
        rw [div_le_iff₀ hlpos]
        linarith
      linarith
    calc (4 : ℝ) ^ (1 + 1 / l) ≤ (4 : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 16 ^ 2 := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
      _ ≤ 16 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have h5 : (1 + l) ^ m ≤ (4 * l) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
  rw [hDexp]
  have hpi : 0 < Real.pi := Real.pi_pos
  calc (4 : ℝ) ^ (1 + 1 / l) * (2 * Real.pi) ^ m * Real.exp (1 / 2) ^ m * (1 + l) ^ m
      ≤ 16 ^ m * (2 * Real.pi) ^ m * Real.exp (1 / 2) ^ m * (4 * l) ^ m := by
        gcongr
    _ = (128 * Real.pi * Real.exp (1 / 2) * l) ^ m := by
        rw [← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        ring

end PI.Residue
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving
section
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

section defs

variable (K : Type) [Field K] [NumberField K]

def box (r : InfinitePlace K → ℝ) : Set (mixedSpace K) := {y | ∀ w, normAtPlace w y < r w}

def shell : Set (mixedSpace K) :=
  {y | y ∈ fundamentalCone K ∧ 1 / 2 < mixedEmbedding.norm y ∧ mixedEmbedding.norm y ≤ 1}

def vfac : ℝ≥0∞ := 2 ^ nrRealPlaces K * (NNReal.pi : ℝ≥0∞) ^ nrComplexPlaces K

def hit (ρ : ℝ) (x : mixedSpace K) : Set (mixedSpace K) :=
  {y | ∀ w, normAtPlace w y * normAtPlace w x < ρ}

abbrev lat (J : (Ideal (𝓞 K))⁰) : Submodule ℤ (mixedSpace K) :=
  idealLattice K (FractionalIdeal.mk0 K J)

def classZeta (C : ClassGroup (𝓞 K)) (s : ℝ) : ℝ≥0∞ :=
  ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C},
    ENNReal.ofReal ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))

end defs

def LatticeCount : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (B : Set (mixedSpace K)), MeasurableSet B →
    volume B ≤ (∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : mixedSpace K)) *
      ENNReal.ofReal (ZLattice.covolume L)

def BoxVolume : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : InfinitePlace K → ℝ), (∀ w, 0 < r w) →
    volume (box K r) = vfac K * ENNReal.ofReal (∏ w, r w ^ mult w)

def ShellVolume : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    volume (shell K) = vfac K * ENNReal.ofReal (regulator K) / 2

def UnitPreserving : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (u : (𝓞 K)ˣ),
    MeasurePreserving (fun y : mixedSpace K => u • y) volume volume

def CountIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰) (ρ : ℝ), 0 < ρ →
    vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) * volume (shell K) ≤
      (∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K))) *
        ENNReal.ofReal (ZLattice.covolume (lat K J))

def Unfold : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰) (ρ : ℝ), 0 < ρ →
    ∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K)) ≤
      volume (shell K) +
        ∑' x : idealSet K J, volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ (x : mixedSpace K))

def HitBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ρ s : ℝ) (x : mixedSpace K), 0 < ρ → 1 < s →
    0 < mixedEmbedding.norm x →
    volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x) ≤
      vfac K * ENNReal.ofReal (ρ ^ Module.finrank ℚ K * (2 * ρ ^ Module.finrank ℚ K) ^ (s - 1) *
        mixedEmbedding.norm x ^ (-s))

def IdealSetSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (s : ℝ) (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰),
    ClassGroup.mk0 J = C⁻¹ →
    ∑' x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s)) ≤
      (torsionOrder K : ℝ≥0∞) * ENNReal.ofReal ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-s)) *
        classZeta K C s

def ClassSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (s : ℝ),
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℝ) ^ (-s)) →
    ∑ C : ClassGroup (𝓞 K), classZeta K C s ≤ ENNReal.ofReal (idealZeta K s)

def ClassLower : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (s : ℝ) (C : ClassGroup (𝓞 K)), 1 < s →
    ENNReal.ofReal (regulator K) ≤
      ENNReal.ofReal ((4 : ℝ) ^ s * ((|discr K| : ℤ) : ℝ) ^ (s / 2) * torsionOrder K) * classZeta K C s

end PI.Residue
end
end


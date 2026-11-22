import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZetaProdSphereVolumeBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0056
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0087
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0158
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0167
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0234
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanTraceFormDualLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSinglePairOrbitContribution
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSumEqTsumPairOrbits
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalf
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

namespace ConstBd

theorem dimN_le (n a : ℕ) (j : Fin a → ℕ) (h : 2 * ∑ i, j i ≤ n) :
    (dimN n j : ℝ) ≤ 2 * ((∑ i, j i : ℕ) : ℝ) * n := by
  have h1 := (GlobalTheory.dim_unipotent_radical_identities a (fun i => (j i : ℤ)) n).2.2
  have h2 : (dimN n j : ℤ) ≤ 2 * ((∑ i, j i : ℕ) : ℤ) * n := by
    refine le_trans (le_of_eq ?_) (h1.trans (le_of_eq ?_))
    · unfold dimN
      push_cast [Nat.cast_sub h, Finset.sum_filter]
      rfl
    · push_cast; rfl
  exact_mod_cast h2

theorem rpow_le (v x : ℝ) (hv : 3 / 4 ≤ v) (hx : 0 ≤ x) : v ^ (-x) ≤ Real.exp (x / 3) := by
  have hv0 : 0 < v := by linarith
  rw [Real.rpow_def_of_pos hv0]
  apply Real.exp_le_exp.2
  have h1 := Real.one_sub_inv_le_log_of_pos hv0
  have h2 : v⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ hv0 (by norm_num)]; linarith
  nlinarith

theorem inv_sph_le (J : ℕ) (s : ℝ) (hJ : (J : ℝ) ≤ s) (hJ1 : 1 ≤ J) :
    (sphV J)⁻¹ ≤ Real.exp (J * (s / 2 * Real.log s)) := by
  refine (GlobalTheory.T.unitarySphereVolumeProduct_ratio_and_inv_bounds.2 J).2.trans ?_
  have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have h0 : (0 : ℝ) < J := by linarith
  rw [← Real.exp_log (pow_pos h0 _), Real.log_pow]
  apply Real.exp_le_exp.2
  have h2 : ((J * (J - 1) / 2 : ℕ) : ℝ) ≤ J * (s / 2) := by
    have h3 : ((J * (J - 1) / 2 : ℕ) : ℝ) ≤ ((J * (J - 1) : ℕ) : ℝ) / (2 : ℕ) := Nat.cast_div_le
    rw [Nat.cast_mul, Nat.cast_sub hJ1] at h3
    push_cast at h3
    nlinarith
  have h4 : Real.log J ≤ Real.log s := Real.log_le_log h0 hJ
  have h5 : 0 ≤ Real.log J := Real.log_nonneg h1
  calc _ ≤ (J * (s / 2)) * Real.log s := mul_le_mul h2 h4 h5 (by nlinarith)
    _ = _ := by ring

theorem zeta_prod (E : Type) [Field E] [NumberField E] (J : ℕ) :
    0 ≤ ∏ l ∈ Finset.Icc 2 J, zetaE E l ∧
      ∏ l ∈ Finset.Icc 2 J, zetaE E l ≤ Real.exp (Module.finrank ℚ E) := by
  have h0 : ∀ l ∈ Finset.Icc 2 J, 0 ≤ zetaE E l := fun l hl =>
    zero_le_one.trans (GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow E l (Finset.mem_Icc.1 hl).1).1
  refine ⟨Finset.prod_nonneg h0, ?_⟩
  refine (Finset.prod_le_prod h0 fun l hl => (GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow E l (Finset.mem_Icc.1 hl).1).2).trans ?_
  rw [Finset.prod_pow, ← Real.exp_one_pow]
  apply pow_le_pow_left₀ (Finset.prod_nonneg fun l _ => GlobalTheory.ZetaProd.zeta_nonneg l)
  have := GlobalTheory.zetaProd_sphereVolume_bounds.1 J
  have := Real.exp_one_gt_d9
  linarith

theorem numeric (N s L c : ℝ) (hs : 100 ≤ s) (hN : N = s * s) (hL : 15 ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ 2) :
    N / 3 + (c - (N - 2 * s) * (L - (c + 1)) + 3.49 + s / 2 * (L / 2)) + 2 * (3 + N) + 2 + 1 ≤
      -(1 / 2 * N * L) := by
  have h1 : 100 * s ≤ N := by nlinarith
  have h2 : (N - 2 * s) * (c + 1) ≤ N * 3 := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h3 : 100 * s * L ≤ N * L := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h4 : N * 15 ≤ N * L := mul_le_mul_of_nonneg_left hL (by linarith)
  nlinarith

end ConstBd

set_option maxHeartbeats 1000000 in
open ConstBd in

theorem constantBound : ConstantBound := by
  intro E _ _ _ hE p q a j hj1 hjq hL hq hrd _
  obtain ⟨hdeg, hf1, hv, -⟩ := GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex E hE.1
  obtain ⟨hres0, hres⟩ := GlobalTheory.T.dedekindZeta_residue_le_sixteen_log_rootDiscr_pow E hE.1
  unfold kapBd
  have haJ : a ≤ ∑ i, j i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hj1 i)
  have hjJ : ∀ i, j i ≤ ∑ i, j i := fun i =>
    Finset.single_le_sum (f := j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hD := dimN_le (p + q) a j
  have hcast : ((∑ i, j i : ℕ) : ℝ) = ∑ i, (j i : ℝ) := by push_cast; rfl
  generalize hJ : ∑ i, j i = J at *
  have hp : ((p + q : ℕ) : ℝ) = p + q := by push_cast; rfl
  generalize hn : p + q = n at *
  generalize hf : Formalism.HermitianLatticesTheory.fDeg E = f at *
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num at hL
    · exact_mod_cast h
  have hN : (10000 : ℝ) ≤ n := by
    rw [Real.le_log_iff_exp_le hn0] at hL
    have h1 : Real.exp 15 = Real.exp 1 ^ 15 := by rw [Real.exp_one_pow]; norm_num
    have h2 : (2 : ℝ) ^ 15 ≤ Real.exp 1 ^ 15 :=
      pow_le_pow_left₀ (by norm_num) (by have := Real.exp_one_gt_d9; linarith) _
    norm_num at h2
    linarith
  set s := Real.sqrt n with hs
  have hss : (n : ℝ) = s * s := (Real.mul_self_sqrt hn0.le).symm
  have hs100 : 100 ≤ s := Real.le_sqrt_of_sq_le (by linarith)
  have hqs : (q : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by exact_mod_cast hq)
  have hJq : (J : ℝ) ≤ q := by exact_mod_cast hjq
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have haJ' : (a : ℝ) ≤ J := by exact_mod_cast haJ
  have h100 : 100 * s ≤ n := by nlinarith
  have h2J : 2 * J + 2 ≤ n := by
    have : (2 : ℝ) * J + 2 ≤ n := by linarith
    exact_mod_cast this
  have hJp : J ≤ p := by
    have : (J : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hlogs : Real.log s = Real.log n / 2 := Real.log_sqrt hn0.le
  have hpos : ∀ i, 0 < sphV i := fun i => (GlobalTheory.T.unitarySphereVolumeProduct_ratio_and_inv_bounds.2 i).1
  have hpi := Real.pi_pos
  have hc0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by have := Real.pi_gt_three; linarith)
  have hc2 : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
    have := Real.exp_one_gt_d9
    have := Real.pi_lt_d2
    nlinarith

  have T1 : Formalism.HermitianLatticesTheory.vInv E ^ (-((f : ℝ) * dimN n j / 2)) ≤ Real.exp (f * J * (n / 3)) := by
    refine (rpow_le _ _ (by linarith) (by positivity)).trans (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_left (hD (by omega)) hf0
    linarith

  have T2 : (2 : ℝ) ^ (-((f : ℝ) * ((n : ℝ) * J - (J : ℝ) ^ 2 + (J : ℝ) / 2))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) ≤ (n : ℝ) * J - (J : ℝ) ^ 2 + (J : ℝ) / 2 := by nlinarith
    have := mul_nonneg hf0 this
    linarith

  have hA := GlobalTheory.T.log_unitarySphereVolumeProduct_ratio_le_large_rank n p J (by exact_mod_cast (by linarith : (18 : ℝ) ≤ n)) hJp (by omega)
    (by linarith) (by linarith)
  rw [Real.log_div hn0.ne' (by positivity), Real.log_mul (x := 2 * Real.pi) (by positivity) (by positivity),
    Real.log_exp,
    Real.log_le_iff_le_exp (div_pos (hpos _) (hpos _))] at hA
  have hB := GlobalTheory.T.unitarySphereVolumeProduct_ratio_and_inv_bounds.1 q J hjq
  rw [Real.log_le_iff_le_exp (div_pos (hpos _) (hpos _))] at hB
  have hC : (∏ i, sphV (j i))⁻¹ ≤ Real.exp (J * (s / 2 * (Real.log n / 2))) := by
    rw [← Finset.prod_inv_distrib, hcast, Finset.sum_mul, Real.exp_sum, ← hlogs]
    apply Finset.prod_le_prod (fun i _ => (inv_pos.2 (hpos _)).le)
    intro i _
    apply inv_sph_le _ _ _ (hj1 i)
    have : (j i : ℝ) ≤ J := by exact_mod_cast hjJ i
    linarith
  have hP : 0 < ∏ i, sphV (j i) := Finset.prod_pos fun i _ => hpos _
  have T3 : (sphV p * sphV q / (sphV (p - J) * sphV (q - J) * ∏ i, sphV (j i))) ^ f ≤
      Real.exp (f * J * (Real.log (2 * Real.pi) - (n - 2 * s) * (Real.log n - (Real.log (2 * Real.pi) + 1)) +
        3.49 + s / 2 * (Real.log n / 2))) := by
    rw [mul_assoc (f : ℝ), Real.exp_nat_mul]
    have := hpos p; have := hpos q; have := hpos (p - J); have := hpos (q - J)
    apply pow_le_pow_left₀ (by positivity)
    have e : sphV p * sphV q / (sphV (p - J) * sphV (q - J) * ∏ i, sphV (j i)) =
        sphV p / sphV (p - J) * (sphV q / sphV (q - J)) * (∏ i, sphV (j i))⁻¹ := by
      field_simp
    rw [e]
    refine (mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hC (by positivity)
      (by positivity)).trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

  have T4 : dedekindZeta_residue E ^ a ≤ Real.exp (f * J * (2 * (3 + n))) := by
    have h16 : (16 : ℝ) ≤ Real.exp 3 := by
      have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [Real.exp_one_pow]; norm_num
      have h2 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (by have := Real.exp_one_gt_d9; linarith) _
      norm_num at h2
      linarith
    have hl0 : 0 ≤ Real.log (2 * Formalism.HermitianLatticesTheory.vInv E) := Real.log_nonneg (by linarith)
    have h3 : 16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ Real.exp (3 + n) := by
      rw [Real.exp_add]
      exact mul_le_mul h16 hrd hl0 (by positivity)
    have h4 := hres.trans (pow_le_pow_left₀ (by positivity) h3 _)
    refine (pow_le_pow_left₀ hres0.le h4 a).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast
    have : (a : ℝ) * (2 * f * (3 + n)) ≤ J * (2 * f * (3 + n)) :=
      mul_le_mul_of_nonneg_right haJ' (by positivity)
    linarith

  have T5 : ∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l ≤ Real.exp (f * J * 2) := by
    refine (Finset.prod_le_prod (fun i _ => (zeta_prod E (j i)).1)
      (fun i _ => (zeta_prod E (j i)).2)).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul, hdeg]
    apply Real.exp_le_exp.2
    push_cast
    have := mul_le_mul_of_nonneg_right haJ' hf0
    linarith
  have T5' : 0 ≤ ∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l :=
    Finset.prod_nonneg fun i _ => (zeta_prod E (j i)).1

  obtain ⟨hL1, hL0⟩ := GlobalTheory.T.neg_log_prod_lValEta_le_and_pos E hE (n - 2 * J) n (by omega)
  rw [hf] at hL1
  have FreeQuotientRank : (∏ M ∈ Finset.Ioc (n - 2 * J) n, Formalism.HermitianLatticesTheory.lValEta E M)⁻¹ ≤ Real.exp (f * J * 1) := by
    rcases Nat.eq_zero_or_pos J with h | h
    · subst h; simp
    · rw [← Real.log_le_iff_le_exp (inv_pos.2 hL0), Real.log_inv]
      refine hL1.trans ?_
      have h1 : (2 : ℝ) ^ ((1 : ℤ) - (n - 2 * J : ℕ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      have h2 : (1 : ℝ) ≤ J := by exact_mod_cast h
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (h1.trans h2) hf0
  have hv0 : 0 < Formalism.HermitianLatticesTheory.vInv E := by linarith
  have := hpos p; have := hpos q; have := hpos (p - J); have := hpos (q - J)
  rw [div_eq_mul_inv]
  refine (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul T1 T2 (by positivity) (by positivity))
    T3 (by positivity) (by positivity)) T4 (by positivity) (by positivity)) T5 T5' (by positivity)) FreeQuotientRank
    (by positivity) (by positivity)).trans ?_
  rw [mul_one, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_left (numeric n s _ _ hs100 hss hL hc0 hc2) (mul_nonneg hf0 hJ0)
  linarith

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
section
open NumberField

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

variable {E : Type} [Field E] [NumberField E]

def reV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).re

def imV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).im

end GlobalTheory.SnMass.SkewVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselCoefficientSmulEquivariantStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_besselCoefficient_smul_equivariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG := by
  first | exact @GlobalTheory.SgInf.AbsConv.integrable_coef_smul | exact GlobalTheory.SgInf.AbsConv.integrable_coef_smul | (intros; apply GlobalTheory.SgInf.AbsConv.integrable_coef_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselFubiniIntegrandProdStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_bessel_fubini_integrand_prod : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v (Matrix.of p.2 * Matrix.of p.1)) * ⟪PiS (psiGen k r z c) π (Matrix.of p.2)⁻¹ ξ, ξ⟫_ℂ) (μG.prod μS) := by
  first | exact @GlobalTheory.SgInf.prod_integrand_integrable | exact GlobalTheory.SgInf.prod_integrand_integrable | (intros; apply GlobalTheory.SgInf.prod_integrand_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralEqOfQuotientMeasuresBesselUnitaryStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν ν' : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → IsQuotMeas μG μR ν' → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : Mat k r → V), ContinuousOn F (GG k r) → (∀ ρ ∈ R, ∀ x ∈ GG k r, F (ρ * x) = F x) → (Integrable (fun x : Mt k r => F (Matrix.of x)) ν ↔ Integrable (fun x : Mt k r => F (Matrix.of x)) ν') ∧ ∫ x, F (Matrix.of x) ∂ν = ∫ x, F (Matrix.of x) ∂ν' := by
  first | exact @GlobalTheory.SnMass.QuotUniq.quot_uniq | exact GlobalTheory.SnMass.QuotUniq.quot_uniq | (intros; apply GlobalTheory.SnMass.QuotUniq.quot_uniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCornerEntryMemIdealLattice
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

section Corner

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem form_smul_smul' (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : E) (u v : Fin n → E) :
    form σ J (y • u) (x • v) = σ x * y * form σ J u v := by
  simp only [form, Matrix.mulVec_smul, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_mem_dInv_mul (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : GlobalTheory.SgGlob.SelfDual σ J Λ) (i j : ℕ) (u v : Fin n → E)
    (hu : ∀ y ∈ (dInv E j)⁻¹, y • u ∈ Λ) (hv : ∀ x ∈ (dInv E i)⁻¹, x • v ∈ Λ) :
    form σ J u v ∈ dInv E i * dInv E j := by
  have h0 : dInv E i * dInv E j ≠ 0 :=
    mul_ne_zero (FrameDual.dInv_ne_zero i) (FrameDual.dInv_ne_zero j)
  rw [← inv_inv (dInv E i * dInv E j), FractionalIdeal.mem_inv_iff (inv_ne_zero h0)]
  intro z hz
  rw [mul_inv] at hz
  refine FractionalIdeal.mul_induction_on hz (fun x hx y hy => ?_) (fun a b ha hb => ?_)
  · have hsx : σ x ∈ (dInv E i)⁻¹ :=
      FrameDual.Stab.inv hσ (FrameDual.stab_dInv hσ i) (FrameDual.dInv_ne_zero i) x hx
    have h1 := (hΛ.2 (y • u)).1 (hu y hy) ((σ x) • v) (hv _ hsx)
    rw [form_smul_smul', hσ] at h1
    obtain ⟨d, hd⟩ := h1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨d, ?_⟩
    rw [hd]; ring
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule ha hb

end Corner

theorem Hpk_esI_apply (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem Hpk_mulVec_esI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp only [Matrix.mulVec, dotProduct, Hpk_esI_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem map_mulVec_comp {E : Type} [Field E] (φ : E →+* ℂ) {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (v : Fin n → E) : (γ.map φ) *ᵥ (fun i => φ (v i)) = fun i => φ ((γ *ᵥ v) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem corner_entry {E : Type} [Field E] (σ : E →+* E) (φ : E →+* ℂ) (hφ : ∀ x, φ (σ x) = star (φ x))
    {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hJ : J.det ≠ 0)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hM : Mᴴ * Hpk k r * M = J.map φ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (a b : Fin r) (fa fb : Fin (2 * r + k + 1) → E)
    (sa sb : ℝ) (hsa : sa ≠ 0) (hsb : sb ≠ 0)
    (ha : M *ᵥ (fun i => φ (fa i)) = ((sa : ℂ)⁻¹) • bvec (esI k r a))
    (hb : M *ᵥ (fun i => φ (fb i)) = ((sb : ℂ)⁻¹) • bvec (esI k r b)) :
    (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = ((sa * sb : ℝ) : ℂ) * φ (form σ J (γ *ᵥ fb) fa) := by
  have hsa' : (sa : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsa
  have hsb' : (sb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsb
  have hdet : (J.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero φ).2 hJ
  have hU : IsUnit M.det := by
    refine isUnit_iff_ne_zero.2 fun h => hdet ?_
    rw [← hM, Matrix.det_mul, h, mul_zero]
  have hinv : M⁻¹ *ᵥ bvec (esI k r b) = (sb : ℂ) • fun i => φ (fb i) := by
    have e1 : M⁻¹ *ᵥ (M *ᵥ (fun i => φ (fb i))) = fun i => φ (fb i) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
    rw [hb, Matrix.mulVec_smul] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hsb', one_smul]
  have hreal : star (M *ᵥ (fun i => φ (fa i))) = M *ᵥ (fun i => φ (fa i)) := by
    rw [ha]; funext j
    simp only [Pi.star_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hbv : bvec (esI k r a) = (sa : ℂ) • (M *ᵥ (fun i => φ (fa i))) := by
    rw [ha, smul_smul, mul_inv_cancel₀ hsa', one_smul]
  set X : Fin (2 * r + k + 1) → ℂ := fun i => φ ((γ *ᵥ fb) i) with hX
  have h1 : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = (sb : ℂ) * (M *ᵥ X) (eI k r a) := by
    have : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) =
        ((M * γ.map φ * M⁻¹) *ᵥ bvec (esI k r b)) (eI k r a) := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, Matrix.mulVec_smul,
      map_mulVec_comp, Matrix.mulVec_smul]
    rfl
  have h2 : (M *ᵥ X) (eI k r a) = (sa : ℂ) * (star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X)) := by
    rw [← Hpk_mulVec_esI k r a (M *ᵥ X)]
    have e2 : (Hpk k r *ᵥ (M *ᵥ X)) (esI k r a) = bvec (esI k r a) ⬝ᵥ (Hpk k r *ᵥ (M *ᵥ X)) := by
      simp [bvec]
    rw [e2, hbv, smul_dotProduct, smul_eq_mul, ← hreal, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  have h3 : star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X) = φ (form σ J (γ *ᵥ fb) fa) := by
    rw [hX, map_mulVec_comp]
    simp [form, dotProduct, map_sum, map_mul, hφ]
  rw [h1, h2, h3]
  push_cast; ring

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem corner_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (esI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD γ hγ p
  obtain ⟨hCM, -, hJ, hΛ, -, -, hlat, hA, hs, had⟩ := hD
  obtain ⟨-, -, -, hcc⟩ := hCM
  obtain ⟨-, hγΛ⟩ := hγ
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    let τ : E →+* ℂ := Classical.arbitrary _
    apply τ.injective
    change τ (σ (σ x)) = τ x
    rw [hcc, hcc, star_star]
  have hcol : ∀ (b : Fin r) (y : E), y ∈ (dInv E (r - (b : ℕ)))⁻¹ → y • (fun i => f i b) ∈ Λ := by
    intro b y hy
    refine hlat (Submodule.subset_span ⟨Fin.natAdd (r + 1) b, y, ?_, ?_⟩)
    · simpa [id1] using hy
    · funext i; simp [sideM]
  have hmap : ∀ v ∈ Λ, γ *ᵥ v ∈ Λ := by
    intro v hv
    have : γ *ᵥ v ∈ latMap γ Λ := ⟨v, hv, rfl⟩
    rwa [hγΛ] at this
  have hc : form (σ : E →+* E) J (γ *ᵥ fun i => f i p.1.2) (fun i => f i p.1.1) ∈
      dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val) := by
    refine form_mem_dInv_mul (σ : E →+* E) hσ J Λ hΛ _ _ _ _ (fun y hy => ?_) (fun x hx => hcol _ x hx)
    rw [← Matrix.mulVec_smul]
    exact hmap _ (hcol _ y hy)
  refine ⟨_, hc, fun w => ?_⟩
  have hJ0 : J.det ≠ 0 := hJ.2
  have hφ : ∀ x, w.embedding ((σ : E →+* E) x) = star (w.embedding x) := fun x => hcc _ x
  have := corner_entry (σ : E →+* E) w.embedding hφ J hJ0 (A w) (hA w) γ p.1.1 p.1.2
    (fun i => f i p.1.1) (fun i => f i p.1.2) (s p.1.1) (s p.1.2) (hs _).ne' (hs _).ne'
    (had w p.1.1).2 (had w p.1.2).2
  simp only [gM]
  rw [this]

end GlobalTheory.SnMass.VolN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanTraceFormDualLatticeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeClassMean_traceFormDualLattice : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ F : Submodule ℤ (VecInf E j) → ENNReal, (∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => F (latAt E j Λ g)) g)) → latMean E j (fun L => F (dualAt E j L)) = latMean E j F := by
  first | exact @GlobalTheory.MeanDual.latMean_dualAt | exact GlobalTheory.MeanDual.latMean_dualAt | (intros; apply GlobalTheory.MeanDual.latMean_dualAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSinglePairOrbitContributionStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeMean_single_pair_orbit_contribution : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, 1 ≤ k → ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → ∀ (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ → Submodule.IsLattice E Λ' → covol {x | x ∈ autGL E (k + 1) (Lf 𝔞 Λ') ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞 Λ') g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} = slabVol E k Λ' * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) * ((Ideal.absNorm 𝔞 : ℝ) ^ (k + 1))⁻¹) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  first | exact @GlobalTheory.OrbitTerm.orbit_term | exact GlobalTheory.OrbitTerm.orbit_term | (intros; apply GlobalTheory.OrbitTerm.orbit_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSumEqTsumPairOrbitsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeMean_sum_eq_tsum_pair_orbits : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → latMean E (k + 1) (fun L => w (covAt E (k + 1) L) * ∑' x : {x : VecInf E (k + 1) // x ∈ L ∧ x ≠ 0}, Φ x.1) = ∑' 𝔞 : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥}, ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin k → E) // Submodule.IsLattice E Λ} => ∃ γ : GL (Fin k) E, ∀ y, (γ : Matrix (Fin k) (Fin k) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1), covol {x | x ∈ autGL E (k + 1) (Lf 𝔞.1 (Quot.out c).1) ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞.1 (Quot.out c).1) g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} := by
  first | exact @GlobalTheory.PairOrbit.latMean_sum_eq_tsum_orbits | exact GlobalTheory.PairOrbit.latMean_sum_eq_tsum_orbits | (intros; apply GlobalTheory.PairOrbit.latMean_sum_eq_tsum_orbits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralPiProdMulFintypeProduct
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem lintegral_pi_prod_mul : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν] (f : ∀ i, X i → ENNReal) (g : Y → ENNReal), (∀ i, Measurable (f i)) → Measurable g → ∫⁻ p, (∏ i, f i (p.1 i)) * g p.2 ∂((Measure.pi μ).prod ν) = (∏ i, ∫⁻ y, f i y ∂(μ i)) * ∫⁻ y, g y ∂ν := by
  intro ι _ X _ μ _ Y _ ν _ f g hf hg
  have hm : Measurable fun x : ∀ i, X i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)
  rw [← GlobalTheory.SnMass.Push.lintegral_fintype_prod f hf]
  exact lintegral_prod_mul hm.aemeasurable hg.aemeasurable

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilVolumes
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.St

theorem siegelWeil_volumes : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J ∧ Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J := by
  intro hSW F E _ _ _ _ _ σ hσ n J hJ

  exact hSW F E σ hσ n J hJ

end GlobalTheory.St
end


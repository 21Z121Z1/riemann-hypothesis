import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0514
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0508
import Formalism.WeaklyAdmissibleFiltrations.Statement

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisLogTeichmullerAssociatedSubOneOnDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

open Filter Topology

namespace GlobalTheory.BSP.SeedT

section Gen

variable (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)

theorem norm_intCast_le (z : ℤ) : ‖(z : Disc l u ρ)‖ ≤ 1 := by
  have := norm_toDisc_le (l := l) (u := u) (ρ := ρ) (z : A)
  rwa [map_intCast] at this

theorem norm_natCast_le (z : ℕ) : ‖(z : Disc l u ρ)‖ ≤ 1 := by
  have := norm_toDisc_le (l := l) (u := u) (ρ := ρ) (z : A)
  rwa [map_natCast] at this

theorem norm_lpow_mul (e : ℕ) (y : Disc l u ρ) : ‖((l : Disc l u ρ)) ^ e * y‖ = ‖y‖ / (l : ℝ) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', mul_assoc, DiscBasic.norm_l_mul l u ρ, ih, pow_succ']
    field_simp

theorem norm_coprime_mul (n : ℕ) (h : Nat.Coprime l n) (x : Disc l u ρ) : ‖(n : Disc l u ρ) * x‖ = ‖x‖ := by
  haveI := DiscBasic.isUltrametricDist_disc l u ρ
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hc := congrArg (Int.cast : ℤ → Disc l u ρ) hab
  push_cast at hc
  have e : x = (a : Disc l u ρ) * ((l : Disc l u ρ) * x) + (b : Disc l u ρ) * ((n : Disc l u ρ) * x) := by
    linear_combination (-x) * hc
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  apply le_antisymm
  · exact (norm_mul_le _ _).trans (by nlinarith [norm_natCast_le l u ρ n, norm_nonneg x])
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : ‖(a : Disc l u ρ) * ((l : Disc l u ρ) * x)‖ ≤ ‖x‖ / l := by
      rw [← DiscBasic.norm_l_mul l u ρ x]
      exact (norm_mul_le _ _).trans (by nlinarith [norm_intCast_le l u ρ a, norm_nonneg ((l : Disc l u ρ) * x)])
    have h2 : ‖(b : Disc l u ρ) * ((n : Disc l u ρ) * x)‖ ≤ ‖(n : Disc l u ρ) * x‖ :=
      (norm_mul_le _ _).trans (by nlinarith [norm_intCast_le l u ρ b, norm_nonneg ((n : Disc l u ρ) * x)])
    have h3 := IsUltrametricDist.norm_add_le_max ((a : Disc l u ρ) * ((l : Disc l u ρ) * x))
      ((b : Disc l u ρ) * ((n : Disc l u ρ) * x))
    rw [← e] at h3
    have h0 := norm_nonneg ((n : Disc l u ρ) * x)
    rcases le_max_iff.1 h3 with h4 | h4
    · have : ‖x‖ ≤ ‖x‖ / l := h4.trans h1
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
    · linarith

theorem isUnit_coprime (n : ℕ) (h : Nat.Coprime l n) : IsUnit (n : Disc l u ρ) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hc := congrArg (Int.cast : ℤ → Disc l u ρ) hab
  push_cast at hc
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hn : ‖(a : Disc l u ρ) * (l : Disc l u ρ)‖ < 1 := by
    rw [mul_comm, DiscBasic.norm_l_mul l u ρ, div_lt_one (by linarith)]
    linarith [norm_intCast_le l u ρ a]
  have hu : IsUnit ((b : Disc l u ρ) * (n : Disc l u ρ)) := by
    refine ⟨Units.oneSub _ hn, ?_⟩
    rw [Units.val_oneSub]
    linear_combination -hc
  exact isUnit_of_mul_isUnit_right hu

theorem isUnit_natCast (n : ℕ) (hn : n ≠ 0) : IsUnit (n : Disc l u ρ) := by
  obtain ⟨e, n', hd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  push_cast
  exact ((isUnit_l_disc l u ρ).pow e).mul (isUnit_coprime l u ρ n' ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hd))

theorem norm_le_natCast_mul (n : ℕ) (hn : n ≠ 0) (x : Disc l u ρ) : ‖x‖ ≤ n * ‖(n : Disc l u ρ) * x‖ := by
  obtain ⟨e, n', hd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hn' : n' ≠ 0 := by rintro rfl; simp at hn
  have hle : (l : ℝ) ^ e ≤ ((l ^ e * n' : ℕ) : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ n' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn'
    nlinarith [pow_pos (show (0 : ℝ) < l by exact_mod_cast hl.out.pos) e]
  have hpos : (0 : ℝ) < (l : ℝ) ^ e := pow_pos (by exact_mod_cast hl.out.pos) e
  have key : ‖((l ^ e * n' : ℕ) : Disc l u ρ) * x‖ = ‖x‖ / (l : ℝ) ^ e := by
    push_cast
    rw [mul_assoc, norm_lpow_mul, norm_coprime_mul l u ρ n' ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hd)]
  rw [key]
  calc ‖x‖ = (l : ℝ) ^ e * (‖x‖ / (l : ℝ) ^ e) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)

end Gen

end GlobalTheory.BSP.SeedT

namespace GlobalTheory.BSP.SeedT

theorem gamma_partial {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (γ : Per.Acris l →+* bk.DA bk.ρ₀)
    (hγ : ∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) (μ : Ainf l) (n : ℕ) (s : Per.Acris0 l)
    (hs : ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) μ) ^ (k + 1)) :
    γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      ∑ k ∈ Finset.range n, (-1) ^ k * bk.iA μ ^ (k + 1) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
  set P : Ainf l := ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Ainf l) * μ ^ (k + 1) with hP
  have h1 : ((n.factorial : ℕ) : Per.Acris0 l) * s = algebraMap (Ainf l) (Per.Acris0 l) P := by
    apply Subtype.ext
    change ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) = algebraMap (Ainf l) (Per.AinfP l) P
    rw [hs, hP]
    simp [map_sum, map_mul, map_pow, map_natCast, map_neg, map_one]
  have h2 := congrArg (fun x => γ (algebraMap (Per.Acris0 l) (Per.Acris l) x)) h1
  simp only [map_mul, map_natCast] at h2
  rw [show algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Ainf l) (Per.Acris0 l) P) =
    algebraMap (Ainf l) (Per.Acris l) P from (GlobalTheory.RingIface.tower l P).symm, hγ, hP] at h2
  simp only [map_sum, map_mul, map_pow, map_natCast, map_neg, map_one] at h2
  have hu := isUnit_natCast l (bk.ev X) bk.ρ₀ n.factorial (Nat.factorial_ne_zero n)
  refine hu.mul_left_cancel (h2.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  have hd : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) hk'
  have hv := isUnit_natCast l (bk.ev X) bk.ρ₀ (k + 1) (Nat.succ_ne_zero k)
  have hq : ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀) =
      ((n.factorial : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
    calc ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀)
        = ((n.factorial / (k + 1) : ℕ) : bk.DA bk.ρ₀) *
            (((k + 1 : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀)) := by
          rw [Ring.mul_inverse_cancel _ hv, mul_one]
      _ = ((n.factorial / (k + 1) * (k + 1) : ℕ) : bk.DA bk.ρ₀) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) := by
          push_cast; ring
      _ = _ := by rw [Nat.div_mul_cancel hd]
  rw [hq]
  ring

theorem t_assoc_mu : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l)
    (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) →
    (∀ x, ‖γ x‖ ≤ 1) → Associated (γ C.t) (bk.iA (mu C.ε)) := by
  intro l hl K bk C γ hγ hγn
  haveI := DiscBasic.isUltrametricDist_disc l (bk.ev X) bk.ρ₀
  set m := bk.iA (mu C.ε) with hm_def
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hm : ‖m‖ ≤ 1 / 3 := by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.norm_teichmullerTiltMinusOne_le l K bk C.ε (core_isEps l C)
    by_cases h : l = 2
    · exact (h2 h).trans (by norm_num)
    · have h3 : (3 : ℝ) ≤ l := by
        have := hl.out.two_le
        exact_mod_cast (show 3 ≤ l by omega)
      refine h1.trans ?_
      rw [one_div]
      exact inv_anti₀ (by norm_num) h3
  set f : ℕ → bk.DA bk.ρ₀ := fun k => (-m) ^ (k + 1) * Ring.inverse ((k + 2 : ℕ) : bk.DA bk.ρ₀) with hf_def
  have hf : ∀ k, ‖f k‖ ≤ (2 / 3 : ℝ) ^ (k + 1) := by
    intro k
    have hu := isUnit_natCast l (bk.ev X) bk.ρ₀ (k + 2) (by omega)
    have e : ((k + 2 : ℕ) : bk.DA bk.ρ₀) * f k = (-m) ^ (k + 1) := by
      rw [hf_def, mul_left_comm, Ring.mul_inverse_cancel _ hu, mul_one]
    have h1 := norm_le_natCast_mul l (bk.ev X) bk.ρ₀ (k + 2) (by omega) (f k)
    rw [e] at h1
    have h2 : ‖(-m) ^ (k + 1)‖ ≤ ‖m‖ ^ (k + 1) := by
      rw [← norm_neg m]; exact norm_pow_le' _ (Nat.succ_pos k)
    have h3 : ‖m‖ ^ (k + 1) ≤ (1 / 3 : ℝ) ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) hm _
    have h4 : ((k + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      have : k + 2 ≤ 2 ^ (k + 1) := Nat.lt_two_pow_self
      exact_mod_cast this
    calc ‖f k‖ ≤ ((k + 2 : ℕ) : ℝ) * ‖(-m) ^ (k + 1)‖ := h1
      _ ≤ (2 : ℝ) ^ (k + 1) * (1 / 3 : ℝ) ^ (k + 1) :=
          mul_le_mul h4 (h2.trans h3) (norm_nonneg _) (by positivity)
      _ = (2 / 3 : ℝ) ^ (k + 1) := by rw [← mul_pow]; norm_num
  have hsum : Summable f := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (2 / 3 : ℝ) < 1)).mul_left (2 / 3)) fun k => ?_
    rw [← pow_succ']
    exact hf k
  set y := ∑' k, f k with hy_def
  have hy : ‖y‖ ≤ 2 / 3 :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun k =>
      (hf k).trans (pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero k))
  have hunit : IsUnit (1 + y) := by
    refine ⟨Units.oneSub (-y) (by rw [norm_neg]; linarith), ?_⟩
    rw [Units.val_oneSub, sub_neg_eq_add]
  set S : ℕ → bk.DA bk.ρ₀ := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * m ^ (k + 1) * Ring.inverse ((k + 1 : ℕ) : bk.DA bk.ρ₀) with hS_def
  have hS : ∀ n, S (n + 1) = m * (1 + ∑ k ∈ Finset.range n, f k) := by
    intro n
    induction n with
    | zero => simp [hS_def]
    | succ n ih =>
      have e1 : S (n + 1 + 1) = S (n + 1) + (-1) ^ (n + 1) * m ^ (n + 1 + 1) *
          Ring.inverse ((n + 1 + 1 : ℕ) : bk.DA bk.ρ₀) := by
        simp only [hS_def]; rw [Finset.sum_range_succ]
      rw [e1, ih, Finset.sum_range_succ, hf_def]
      simp only
      rw [neg_pow]
      ring
  have hlim1 : Tendsto (fun n => S (n + 1)) atTop (𝓝 (m * (1 + y))) := by
    simp_rw [hS]
    exact (tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat).const_mul m
  have hlim2 : Tendsto (fun n => S (n + 1)) atTop (𝓝 (γ C.t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε hlinv
    obtain ⟨N, hN⟩ := C.t_log r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨s, hs1, z, hz⟩ := hN (n + 1) (by omega)
    have key := gamma_partial bk γ hγ (mu C.ε) (n + 1) s hs1
    rw [dist_eq_norm, norm_sub_rev]
    have e2 : γ C.t - S (n + 1) = (l : bk.DA bk.ρ₀) ^ r * γ z := by
      rw [hS_def]
      simp only
      rw [← key, ← map_sub, hz, map_mul, map_pow, map_natCast]
    rw [e2, norm_lpow_mul]
    calc ‖γ z‖ / (l : ℝ) ^ r ≤ 1 / (l : ℝ) ^ r :=
          div_le_div_of_nonneg_right (hγn z) (by positivity)
      _ = (l : ℝ)⁻¹ ^ r := by rw [inv_pow, one_div]
      _ < ε := hr
  have heq : γ C.t = m * (1 + y) := tendsto_nhds_unique hlim2 hlim1
  refine ⟨hunit.unit⁻¹, ?_⟩
  rw [heq, mul_assoc, IsUnit.mul_val_inv, mul_one]

end GlobalTheory.BSP.SeedT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisLpowDvdBoundTeichmullerMonoidStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_lpow_dvd_bound_teichmullerMonoid : ∀ (l : ℕ) [Fact l.Prime] (y : Ainf l), WittVector.constantCoeff y ≠ 0 → ∃ C : ℕ, ∀ (z : ℤ_[l]) (N : ℕ), z ≠ 0 → (l : Per.Acris l) ^ N ∣ ainfToAcris l y * algebraMap ℤ_[l] (Per.Acris l) z → N ≤ z.valuation + C := by
  first | exact @GlobalTheory.AcrisMonBound.main | exact GlobalTheory.AcrisMonBound.main | (intros; apply GlobalTheory.AcrisMonBound.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisToBcrisMemFiltrationOfLadicApprox
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

open GlobalTheory.Decompl

variable {l : ℕ} [Fact l.Prime]

theorem ι_smul_mem_FilD (C : GlobalTheory.MemLoc.Core l) {n : ℤ} (a : ℤ_[l]) {β : Per.Bcris l}
    (h : C.ι β ∈ Per.FilD l n) : C.ι (a • β) ∈ Per.FilD l n := by
  rw [Algebra.smul_def, map_mul]
  refine mul_mem_FilD_of_zero ?_ h
  have h1 : algebraMap ℤ_[l] (Per.Bcris l) a = acrisToBcris l (algebraMap ℤ_[l] (Per.Acris l) a) :=
    ((acrisToBcris l).commutes a).symm
  rw [h1]
  change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _
  rw [C.ι_j]
  exact (mem_FilD_zero_iff _).2 ⟨_, rfl⟩

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] {I : Type} [Fintype I] (b : Module.Basis I ℤ_[l] O)

theorem crd_smul_eq {W : Type} [CommRing W] [Algebra ℤ_[l] W] (o : O) (w : O ⊗[ℤ_[l]] W) (i : I) :
    crd b i (o • w) = ∑ k, b.repr (o * b k) i • crd b k w := by
  conv_lhs => rw [← sum_crd b w]
  simp only [Finset.smul_sum, smul_tmul', smul_eq_mul, map_sum, crd_tmul]

theorem crd_mem_of_mem_filO (C : GlobalTheory.MemLoc.Core l) {n : ℤ} {w : OB l O} (hw : w ∈ filO O C n)
    (i : I) : C.ι (crd b i w) ∈ Per.FilD l n := by
  induction hw using Submodule.span_induction generalizing i with
  | mem w hw =>
    obtain ⟨β, hβ, rfl⟩ := hw
    rw [crd_tmul]
    exact ι_smul_mem_FilD C _ hβ
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [map_add, map_add]; exact add_mem (h i) (h' i)
  | smul o w _ h =>
    rw [crd_smul_eq, map_sum]
    exact Submodule.sum_mem _ fun k _ => ι_smul_mem_FilD C _ (h k)

theorem crd_toOB (x : OCr l O) (i : I) : crd b i (toOB l O x) = acrisToBcris l (crd b i x) :=
  crd_map b (acrisToBcris l) i x

theorem toOB_mem_filO_of_approx (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O)
    (h : ∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) :
    toOB l O x ∈ filO O C m := by
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hc : ∀ i, C.j (crd b i x) ∈ Per.FilP l m := by
    intro i
    refine j_mem_FilP_of_approx C m _ fun r => ?_
    obtain ⟨y, z, hxyz, hy⟩ := h r
    refine ⟨crd b i y, crd b i z, ?_, ?_⟩
    · rw [hxyz, map_add]
      congr 1
      rw [show (l : OCr l O) ^ r = ((l ^ r : ℕ) : OCr l O) by push_cast; rfl, crd_natCast_mul]
      push_cast; rfl
    · have h1 := crd_mem_of_mem_filO b C hy i
      rw [crd_toOB] at h1
      change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _ at h1
      rw [C.ι_j] at h1
      exact (alg_mem_FilD_iff m _).1 h1
  rw [← sum_crd b x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : (b i ⊗ₜ[ℤ_[l]] crd b i x : OCr l O) = b i • ((1 : O) ⊗ₜ[ℤ_[l]] crd b i x) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (toOB_tmul_mem_filO (hc i))

end GlobalTheory.BKGal.TaylorFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadius
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem vr_iterate_phi (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (hx : x ≠ 0) :
    ∀ k : ℕ, (φc l)^[k] x ≠ 0 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      vr l r ((φc l)^[k] x) = (l : ℝ) ^ k * vr l (r / (l : ℝ) ^ k) x := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  have hl0 : (0 : ℝ) < l := by linarith
  intro k
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    obtain ⟨hne, hv⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨((GlobalTheory.T.acrisValuation_radius_laws l 1 one_pos le_rfl).2.1 _ hne).1, ?_⟩
    intro r hr0 hr1
    rw [((GlobalTheory.T.acrisValuation_radius_laws l r hr0 hr1).2.1 _ hne).2]
    have h1 : 0 < r / l := div_pos hr0 hl0
    have h2 : r / l ≤ 1 := by rw [div_le_one hl0]; linarith
    rw [hv (r / l) h1 h2, pow_succ]
    have e : r / (l : ℝ) / (l : ℝ) ^ k = r / ((l : ℝ) ^ k * l) := by rw [div_div, mul_comm]
    rw [e]
    ring

theorem vr_sub_eq_int_mul : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l,
    (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w ≠ 0 → w' ≠ 0 →
    φc l w * w' = w * φc l w' → ∃ n : ℤ, ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r w - vr l r w' = n * r := by
  intro l _ h s hsh w w' hfix hw hw' hrat
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  obtain ⟨cA, kA, sA⟩ := GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l w hw
  obtain ⟨cB, kB, sB⟩ := GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l w' hw'
  have key := GlobalTheory.T.exists_int_sub_mul_eq_int_mul_of_homogeneous l h s 1 hl2 hsh le_rfl (fun r => vr l r w) (fun r => vr l r w')
    cA cB kA kB sA sB ?_ ?_
  · obtain ⟨n, hn⟩ := key
    exact ⟨n, fun r hr => by simpa using hn r hr⟩
  · rintro r ⟨hr0, hr1⟩
    have e1 := (vr_iterate_phi l w' hw' h).2 r hr0 hr1
    rw [hfix, (GlobalTheory.T.acrisValuation_radius_laws l r hr0 hr1).2.2.1 w' s hw'] at e1
    show (l : ℝ) ^ h * vr l (r / (l : ℝ) ^ h) w' = vr l r w' + s * r
    linarith
  · rintro r ⟨hr0, hr1⟩
    have hlr0 : 0 < (l : ℝ) * r := mul_pos hl0 hr0
    have hlr1 : (l : ℝ) * r ≤ 1 := by rw [le_div_iff₀ hl0] at hr1; linarith
    obtain ⟨hmul, hphi, -, -⟩ := GlobalTheory.T.acrisValuation_radius_laws l (l * r) hlr0 hlr1
    have e := congrArg (vr l (l * r)) hrat
    rw [hmul _ _ (hphi w hw).1 hw', hmul _ _ hw (hphi w' hw').1, (hphi w hw).2,
      (hphi w' hw').2] at e
    have hc : (l : ℝ) * r / l = r := by field_simp
    rw [hc] at e
    show vr l (l * r) w - ((1 : ℕ) : ℝ) * vr l (l * r) w' = l * (vr l r w - ((1 : ℕ) : ℝ) * vr l r w')
    simp only [Nat.cast_one, one_mul]
    linarith

end GlobalTheory.PMon.Gauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBoundsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_table_of_local_bounds : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → (∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) → ∀ π ∈ D.nd.Zgood i, Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)) → TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) := by
  first | exact @GlobalTheory.NLink.admissible_table_of_conclusion | exact GlobalTheory.NLink.admissible_table_of_conclusion | (intros; apply GlobalTheory.NLink.admissible_table_of_conclusion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedDiscLinearDisjointOverPowerSeries
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem breuilKisinDatum_uniformizer_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨?_, ?_⟩
  · unfold BK.ρ₀
    exact NNReal.rpow_pos (by positivity)
  · unfold BK.ρ₀
    exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
      have : (0:ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith)

theorem linDisjoint_disc (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (sA : bk.S →+* A) (ι : Type) (TB : TopBasis sA bk.J ι) (j : bk.DS bk.ρ₀ →+* Disc l (sA X) bk.ρ₀)
    (hj : IsDiscMap sA j) (x y : A) (f g : bk.DS bk.ρ₀) (hg : g ≠ 0) (hy : y ≠ 0)
    (h : toDisc l (sA X) bk.ρ₀ x * j g = toDisc l (sA X) bk.ρ₀ y * j f) :
    ∃ δ a : bk.S, δ ≠ 0 ∧ sA δ * x = sA a * y := by
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_uniformizer_radius_pos_lt_one bk
  obtain ⟨cD, hc1, hc2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A sA ι TB bk.ρ₀ hρ0 hρ1 j hj
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hH : IsHausdorff bk.J bk.S := inferInstance
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.TopBasis.basic_facts bk.S A sA bk.J ι TB hH
  have hinj : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) :=
    (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) bk.ρ₀ hρ0 hρ1).1
  have hmul := GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative l K bk bk.ρ₀ hρ0 hρ1

  have key : ∀ i, g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i x) = f * toDisc l (X : bk.S) bk.ρ₀ (TB.c i y) := by
    intro i
    have e := congrArg (cD i) h
    rw [mul_comm, mul_comm (toDisc l (sA X) bk.ρ₀ y), hc2, hc2, hc1, hc1] at e
    exact e
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, TB.c i₀ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (hz y hc)
  refine ⟨TB.c i₀ y, TB.c i₀ x, hi₀, ?_⟩
  rw [← sub_eq_zero]
  apply hz
  intro i
  rw [map_sub, TB.c_mul, TB.c_mul]
  apply hinj
  rw [map_zero]
  have h0 : g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y * TB.c i x - TB.c i₀ x * TB.c i y) = 0 := by
    rw [map_sub, map_mul, map_mul, mul_sub]
    have e1 := key i
    have e2 := key i₀
    linear_combination (toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y)) * e1 - (toDisc l (X : bk.S) bk.ρ₀ (TB.c i y)) * e2
  have hn := congrArg norm h0
  rw [hmul, norm_zero, mul_eq_zero] at hn
  rcases hn with hn | hn
  · exact absurd (norm_eq_zero.1 hn) hg
  · exact norm_eq_zero.1 hn

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_dvd_of_closed_disc_dvd_eisenstein_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), (∀ m : ℕ, bk.iS bk.E ^ m ∣ bk.iA a → bk.ev bk.E ^ m ∣ a) ∧ (bk.iS X ∣ bk.iA a → bk.ev X ∣ a) := by
  first | exact @GlobalTheory.BSP.ainf_dvd_of_disc_dvd | exact GlobalTheory.BSP.ainf_dvd_of_disc_dvd | (intros; apply GlobalTheory.BSP.ainf_dvd_of_disc_dvd; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStableStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (C : GlobalTheory.MemLoc.Core l), ∀ v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}, actB (sQ l) T g v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.FilStable.fil_zero_stable | exact GlobalTheory.BKGal.FilStable.fil_zero_stable | (intros; apply GlobalTheory.BKGal.FilStable.fil_zero_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeToDeRhamEquivariantStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (g : Gl l) (b : TW (OB l ↥(OL LL)) T), X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  first | exact @GlobalTheory.BKGal.JumpDR.X_equivariant | exact GlobalTheory.BKGal.JumpDR.X_equivariant | (intros; apply GlobalTheory.BKGal.JumpDR.X_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfSplitStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrys_of_split_alt : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Module.Basis (Fin n) Qp V) [FiniteDimensional Qp LL] (W : Matrix (Fin n) (Fin n) B), IsUnit W.det → (∀ g, (Matrix.of fun i j => algebraMap Qp B (e.repr (ρ g (e j)) i)) * W.map (PD.actB g) = W) → Formalism.WeaklyAdmissibleFiltrations.IsCrys PD ρ := by
  first | exact @GlobalTheory.SplitCrys.isCrys_of_split | exact GlobalTheory.SplitCrys.isCrys_of_split | (intros; apply GlobalTheory.SplitCrys.isCrys_of_split <;> assumption)
end


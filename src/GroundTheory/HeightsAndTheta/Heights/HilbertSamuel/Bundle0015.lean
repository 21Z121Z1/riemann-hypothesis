import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StandardLatticeVecIndep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HasDerivAtDet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Matrix Equiv
open scoped ComplexOrder

noncomputable section

theorem LogDetDerivative.hasDerivAt_det {m : ℕ} {G : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {G' : Matrix (Fin m) (Fin m) ℂ} {t : ℝ} (h : ∀ i j, HasDerivAt (fun s ↦ G s i j) (G' i j) t) :
    HasDerivAt (fun s ↦ (G s).det) (∑ i, (G t).cramer (fun k ↦ G' k i) i) t := by
  have key : ∀ σ : Perm (Fin m), HasDerivAt (fun s ↦ ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i)
      (((Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) * G' (σ i) i) t := by
    intro σ
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s ↦ G s (σ i) i)
      (f' := fun i ↦ G' (σ i) i) (x := t) (fun i _ ↦ h (σ i) i)
    simpa [smul_eq_mul] using this.const_mul ((Perm.sign σ : ℤ) : ℂ)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ ↦ key σ)
  have hfun : (fun s ↦ (G s).det) =
      fun s ↦ ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i := by
    ext s
    exact det_apply' _
  rw [hfun]
  refine hsum.congr_deriv ?_
  symm
  rw [Finset.sum_congr rfl fun i _ ↦ cramer_apply (G t) (fun k ↦ G' k i) i]
  simp only [det_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, (G t).updateCol i (fun k ↦ G' k i) (σ j) j =
      ∏ j ∈ Finset.univ.erase i, G t (σ j) j := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [updateCol_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, updateCol_self]
  ring

theorem LogDetDerivative.sum_cramer_eq {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) :
    ∑ i, A.cramer (fun k ↦ B k i) i = A.det * (A⁻¹ * B).trace := by
  simp only [← det_smul_inv_mulVec_eq_cramer A _ hA, Pi.smul_apply, smul_eq_mul, trace,
    diag_apply, mul_apply, mulVec, dotProduct, Finset.mul_sum]

theorem LogDetDerivative.intersectionNumber_baseChange : LogDetDerivative.Statement := by
  intro m G G' hpos hG t
  have hdet := LogDetDerivative.hasDerivAt_det (hG t)
  rw [LogDetDerivative.sum_cramer_eq _ _ (hpos t).det_pos.ne'.isUnit] at hdet
  have hre : HasDerivAt (fun s ↦ (G s).det.re)
      ((G t).det * ((G t)⁻¹ * G' t).trace).re t := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdet
  have hp := (hpos t).det_pos
  rw [Complex.lt_def] at hp
  obtain ⟨hre0, him0⟩ := hp
  simp only [Complex.zero_re, Complex.zero_im] at hre0 him0
  have hlog := (hre.log hre0.ne').const_mul (-(1 / 2) : ℝ)
  refine hlog.congr_deriv ?_
  rw [Complex.mul_re, ← him0, zero_mul, sub_zero]
  field_simp

theorem LogDetDerivative.equiv :
    GroundTheory.Heights₂.Heights.HilbertSamuel.LogDetDerivative.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.LogDetDerivative.Statement := by
  constructor
  · intro h m F t
    refine h m F.G (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.entryDeriv F.G) F.posDef
      (fun s i j ↦ ?_) t
    have hd := ((F.smooth i j).differentiable (by norm_num) s).hasDerivAt
    simpa [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.entryDeriv] using hd
  · intro _
    exact LogDetDerivative.intersectionNumber_baseChange

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBetaSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

theorem BetaSum.proof : BetaSum.Statement := by
  intro D i hi

  set I : ℝ := ∫ t in (0 : ℝ)..1, t ^ i * (1 - t) ^ (D - i) with hIdef
  have hB : Complex.betaIntegral ((i : ℂ) + 1) (((D - i : ℕ) : ℂ) + 1) = (I : ℂ) := by
    rw [Complex.betaIntegral, hIdef, ← intervalIntegral.integral_ofReal]
    congr 1
    ext x
    rw [add_sub_cancel_right, add_sub_cancel_right, Complex.cpow_natCast, Complex.cpow_natCast]
    push_cast
    ring
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (i : ℂ) + 1)
    (t := ((D - i : ℕ) : ℂ) + 1) (by simp; positivity) (by simp; positivity)
  have hst : (i : ℂ) + 1 + (((D - i : ℕ) : ℂ) + 1) = ((D + 1 : ℕ) : ℂ) + 1 := by
    push_cast [Nat.cast_sub hi]
    ring
  rw [hst, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial, hB] at hG
  have hR : (i.factorial : ℝ) * (D - i).factorial = (D + 1).factorial * I := by
    exact_mod_cast hG

  have hc : (D.choose i : ℝ) * i.factorial * (D - i).factorial = D.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    push_cast [Nat.factorial_succ]
    ring
  have hpos : (0 : ℝ) < D.factorial := by positivity
  have hint : ∫ t in (0 : ℝ)..1, (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i)
      = (D.choose i : ℝ) * I := by
    rw [hIdef, ← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [hint, eq_div_iff (by positivity)]
  apply mul_right_cancel₀ hpos.ne'
  calc (D.choose i : ℝ) * I * ((D : ℝ) + 1) * D.factorial
      = (D.choose i : ℝ) * ((D + 1).factorial * I) := by rw [hf]; ring
    _ = (D.choose i : ℝ) * i.factorial * (D - i).factorial := by rw [← hR]; ring
    _ = 1 * D.factorial := by rw [hc, one_mul]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClopenComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem vanishingIdeal_zeroLocus_diff_of_nonempty {σ : Type} [Fintype σ]
    (W J : Ideal (MvPolynomial σ ℂ)) [hW : W.IsPrime]
    (hne : (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty) :
    vanishingIdeal ℂ (zeroLocus ℂ W \ zeroLocus ℂ J) = W := by
  refine le_antisymm ?_ ?_
  · intro f hf
    obtain ⟨z₀, hz₀W, hz₀J⟩ := hne
    simp only [mem_zeroLocus_iff, not_forall] at hz₀J
    obtain ⟨g, hgJ, hg⟩ := hz₀J
    have hgW : g ∉ W := fun h => hg (hz₀W g h)
    have hfg : f * g ∈ W := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W, mem_vanishingIdeal_iff]
      intro z hz
      by_cases hzJ : z ∈ zeroLocus ℂ J
      · rw [map_mul, hzJ g hgJ, mul_zero]
      · rw [map_mul, (mem_vanishingIdeal_iff.mp hf) z ⟨hz, hzJ⟩, zero_mul]
    exact (hW.mem_or_mem hfg).resolve_right hgW
  · calc W ≤ vanishingIdeal ℂ (zeroLocus ℂ W) := le_vanishingIdeal_zeroLocus W
      _ ≤ _ := vanishingIdeal_anti_mono Set.sdiff_subset

variable (ι) in

def multiIrrelevantIdeal : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.span (Set.range fun i : (∀ k, ι k) => ∏ k, (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))

omit [∀ k, Fintype (ι k)] in

theorem not_mem_zeroLocus_multiIrrelevantIdeal (z : (Σ k, ι k) → ℂ) :
    z ∉ zeroLocus ℂ (multiIrrelevantIdeal ι) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  rw [multiIrrelevantIdeal, zeroLocus_span]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, not_forall, map_prod, aeval_X]
  constructor
  · rintro ⟨i, hi⟩ k
    exact ⟨i k, fun h => hi (Finset.prod_eq_zero (Finset.mem_univ k) h)⟩
  · intro h
    choose i hi using h
    exact ⟨i, Finset.prod_ne_zero_iff.mpr fun k _ => hi k⟩

omit [∀ k, Fintype (ι k)] in

theorem mcPts_eq_zeroLocus_diff (P : Ideal (MRing ι)) :
    mcPts P = zeroLocus ℂ (P.map (MvPolynomial.map (Int.castRingHom ℂ))) \
      zeroLocus ℂ (multiIrrelevantIdeal ι) := by
  ext z
  rw [Set.mem_sdiff, not_mem_zeroLocus_multiIrrelevantIdeal]
  simp only [mcPts, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hb, hv⟩
    refine ⟨fun p hp => ?_, hb⟩
    have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact hv f hf
    have h0 := RingHom.mem_ker.mp (hle hp)
    exact h0
  · rintro ⟨hz, hb⟩
    refine ⟨hb, fun f hf => ?_⟩
    have := hz _ (Ideal.mem_map_of_mem _ hf)
    exact this

theorem ClopenComponents.proof (h : IrreducibleConnected.Statement) : ClopenComponents.Statement := by
  classical
  intro K _ _ ι _ P e A _ hAsub hA
  set PC := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  set J := multiIrrelevantIdeal ι with hJ
  have hmc : mcPts P = zeroLocus ℂ PC \ zeroLocus ℂ J := mcPts_eq_zeroLocus_diff P
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing _ PC
  let S := hfin.toFinset.filter fun W =>
    (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty ∧ zeroLocus ℂ W \ zeroLocus ℂ J ⊆ A
  have hS : ∀ W ∈ S, W ∈ PC.minimalPrimes ∧ (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty ∧
      zeroLocus ℂ W \ zeroLocus ℂ J ⊆ A := by
    intro W hW
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    exact hW
  have hcover : ∀ z ∈ A, ∃ W ∈ S, z ∈ zeroLocus ℂ W \ zeroLocus ℂ J := by
    intro z hz
    have hzm : z ∈ mcPts P := hAsub hz
    rw [hmc] at hzm
    obtain ⟨hzPC, hzJ⟩ := hzm
    have hker : PC ≤ RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ℂ) :=
      fun p hp => RingHom.mem_ker.mpr (hzPC p hp)
    have : (RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ℂ)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le hker
    have hzW : z ∈ zeroLocus ℂ W \ zeroLocus ℂ J := ⟨fun p hp => RingHom.mem_ker.mp (hWle hp), hzJ⟩
    have hsub : zeroLocus ℂ W \ zeroLocus ℂ J ⊆ mcPts P := by
      rw [hmc]
      exact Set.sdiff_subset_sdiff_left (zeroLocus_anti_mono hWmin.1.2)
    have hpc : IsPreconnected (zeroLocus ℂ W \ zeroLocus ℂ J) := h _ W J hWmin.1.1
    have hpc' : IsPreconnected (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' (zeroLocus ℂ W \ zeroLocus ℂ J)) := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        Set.inter_eq_right.mpr hsub]
      exact hpc
    have hin := hpc'.subset_isClopen hA ⟨⟨z, hsub hzW⟩, hzW, hz⟩
    refine ⟨W, ?_, hzW⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hWmin, ⟨z, hzW⟩, fun y hy => hin (show (⟨y, hsub hy⟩ : mcPts P) ∈ _ from hy)⟩
  have hAU : A = ⋃ W ∈ S, (zeroLocus ℂ W \ zeroLocus ℂ J) := by
    ext z
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun hz => hcover z hz, fun ⟨W, hW, hz⟩ => (hS W hW).2.2 hz⟩
  refine ⟨S, fun W hW => (hS W hW).1, ?_, ?_⟩
  · ext z
    rw [hAU, hmc]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨W, hW, hzW, hzJ⟩
      exact ⟨⟨fun p hp => hzW p ((hS W hW).1.1.2 hp), hzJ⟩, W, hW, hzW⟩
    · rintro ⟨⟨_, hzJ⟩, W, hW, hzW⟩
      exact ⟨W, hW, hzW, hzJ⟩
  · rw [hAU]
    ext f
    rw [mem_vanishingIdeal_iff]
    simp only [Submodule.mem_iInf]
    constructor
    · intro hf W hW
      have : W.IsPrime := (hS W hW).1.1.1
      rw [← vanishingIdeal_zeroLocus_diff_of_nonempty W J (hS W hW).2.1, mem_vanishingIdeal_iff]
      exact fun x hx => hf x (Set.mem_biUnion hW hx)
    · intro hf x hx
      obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hx
      have : W.IsPrime := (hS W hW).1.1.1
      have hfW := hf W hW
      rw [← vanishingIdeal_zeroLocus_diff_of_nonempty W J (hS W hW).2.1, mem_vanishingIdeal_iff] at hfW
      exact hfW x hxW

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Finset Filter Asymptotics

theorem GridSum.choose_antidiagonal (m i j : ℕ) :
    ∑ p ∈ antidiagonal m, p.1.choose i * p.2.choose j = (m + 1).choose (i + j + 1) := by
  induction m generalizing i with
  | zero =>
    cases i <;> cases j <;> simp <;> exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ m ih =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    cases i with
    | zero =>
      have h := ih 0
      simp only [Nat.choose_zero_right, one_mul, zero_add] at h ⊢
      rw [h, Nat.choose_succ_succ (m + 1) j]
    | succ i =>
      have h1 := ih i
      have h2 := ih (i + 1)
      have e : ∀ p : ℕ × ℕ, (p.1 + 1).choose (i + 1) * p.2.choose j =
          p.1.choose i * p.2.choose j + p.1.choose (i + 1) * p.2.choose j := fun p ↦ by
        rw [Nat.choose_succ_succ', add_mul]
      simp only [Nat.choose_zero_succ, zero_mul, zero_add, e, Finset.sum_add_distrib, h1, h2]
      rw [show i + 1 + j + 1 = (i + j + 1) + 1 by omega, Nat.choose_succ_succ' (m + 1) (i + j + 1)]

theorem GridSum.choose_range (n i j : ℕ) :
    ∑ a ∈ range n, a.choose i * (n - 1 - a).choose j = n.choose (i + j + 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [← GridSum.choose_antidiagonal m i j, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp

theorem GridSum.choose_le_pow_div_factorial (a i : ℕ) :
    (a.choose i : ℝ) ≤ (a : ℝ) ^ i / (i.factorial : ℝ) := by
  rw [le_div_iff₀ (by positivity)]
  have h : a.choose i * i.factorial ≤ a ^ i := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow a i
  exact_mod_cast h

theorem GridSum.pow_div_factorial_le (a i : ℕ) :
    (a : ℝ) ^ i / (i.factorial : ℝ) ≤ ((a + i).choose i : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have h : a ^ i ≤ (a + i).choose i * i.factorial := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    calc a ^ i ≤ (a + i + 1 - i) ^ i := Nat.pow_le_pow_left (by omega) i
      _ ≤ (a + i).descFactorial i := Nat.pow_sub_le_descFactorial _ _
  exact_mod_cast h

theorem GridSum.pow_sub_pow_le (x y : ℝ) (k : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ k - y ^ k ≤ k * (x - y) * x ^ (k - 1) := by
  rw [← geom_sum₂_mul]
  have hx : 0 ≤ x := hy.trans hxy
  have hs : ∑ l ∈ range k, x ^ l * y ^ (k - 1 - l) ≤ k * x ^ (k - 1) := by
    calc ∑ l ∈ range k, x ^ l * y ^ (k - 1 - l) ≤ ∑ l ∈ range k, x ^ (k - 1) := by
          apply sum_le_sum
          intro l hl
          have hl' : l + (k - 1 - l) = k - 1 := by have := mem_range.mp hl; omega
          calc x ^ l * y ^ (k - 1 - l) ≤ x ^ l * x ^ (k - 1 - l) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hxy _) (pow_nonneg hx _)
            _ = x ^ (k - 1) := by rw [← pow_add, hl']
      _ = k * x ^ (k - 1) := by simp
  have hd : 0 ≤ x - y := sub_nonneg.mpr hxy
  calc (∑ l ∈ range k, x ^ l * y ^ (k - 1 - l)) * (x - y) ≤ (k * x ^ (k - 1)) * (x - y) :=
        mul_le_mul_of_nonneg_right hs hd
    _ = k * (x - y) * x ^ (k - 1) := by ring

theorem GridSum.proof : GridSum.Statement := by
  intro D i hi
  set j := D - i with hj
  have hD : i + j + 1 = D + 1 := by omega
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF1 : (1 : ℝ) ≤ F := by
    rw [hFdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF : 0 < F := lt_of_lt_of_le one_pos hF1
  have lower : ∀ n : ℕ, ((n.choose (D + 1) : ℕ) : ℝ) ≤ ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) := by
    intro n
    have h := GridSum.choose_range n i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    apply sum_le_sum
    intro a _
    rw [mul_div_mul_comm, Nat.cast_mul]
    exact mul_le_mul (GridSum.choose_le_pow_div_factorial _ _)
      (GridSum.choose_le_pow_div_factorial _ _) (by positivity) (by positivity)
  have upper : ∀ n : ℕ, ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) ≤
        (((n + D).choose (D + 1) : ℕ) : ℝ) := by
    intro n
    have h := GridSum.choose_range (n + D) i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    calc ∑ a ∈ range n,
          (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ))
        ≤ ∑ a ∈ range n, (((a + i).choose i * (n + D - 1 - (a + i)).choose j : ℕ) : ℝ) := by
          apply sum_le_sum
          intro a ha
          have hb : n + D - 1 - (a + i) = (n - 1 - a) + j := by
            have := mem_range.mp ha; omega
          rw [hb, mul_div_mul_comm, Nat.cast_mul]
          exact mul_le_mul (GridSum.pow_div_factorial_le _ _)
            (GridSum.pow_div_factorial_le _ _) (by positivity) (by positivity)
      _ = ∑ a ∈ (range n).map (addRightEmbedding i),
            ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          rw [sum_map]; rfl
      _ ≤ ∑ a ∈ range (n + D), ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_map] at hx
            obtain ⟨a, ha, rfl⟩ := hx
            rw [mem_range] at ha ⊢
            change a + i < n + D
            omega
          · intros; positivity
  refine IsBigO.of_bound (((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D) ?_
  filter_upwards [eventually_ge_atTop D] with n hn
  have hL := lower n
  have hU := upper n
  set S := ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) with hS
  have hnD : (D : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - D) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
    have h : (n - D) ^ (D + 1) ≤ n.choose (D + 1) * (D + 1).factorial := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      have := Nat.pow_sub_le_descFactorial n (D + 1)
      rwa [show n + 1 - (D + 1) = n - D by omega] at this
    have h' : (((n - D : ℕ) : ℝ)) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
      rw [hFdef]; exact_mod_cast h
    rwa [Nat.cast_sub hn] at h'
  have h2 : (((n + D).choose (D + 1) : ℕ) : ℝ) * F ≤ ((n : ℝ) + D) ^ (D + 1) := by
    have h : (n + D).choose (D + 1) * (D + 1).factorial ≤ (n + D) ^ (D + 1) := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow _ _
    rw [hFdef]; exact_mod_cast h
  have hSlo : ((n : ℝ) - D) ^ (D + 1) / F ≤ S := by
    rw [div_le_iff₀ hF]; nlinarith
  have hShi : S ≤ ((n : ℝ) + D) ^ (D + 1) / F := by
    rw [le_div_iff₀ hF]; nlinarith
  have hy : (0 : ℝ) ≤ (n : ℝ) - D := sub_nonneg.mpr hnD
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hp1 : ((n : ℝ) - D) ^ (D + 1) ≤ (n : ℝ) ^ (D + 1) :=
    pow_le_pow_left₀ hy (by linarith) _
  have hp2 : (n : ℝ) ^ (D + 1) ≤ ((n : ℝ) + D) ^ (D + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _
  have hgap := GridSum.pow_sub_pow_le ((n : ℝ) + D) ((n : ℝ) - D) (D + 1) hy (by linarith)
  rw [Nat.add_sub_cancel] at hgap
  have hpow : ((n : ℝ) + D) ^ D ≤ 2 ^ D * (n : ℝ) ^ D := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have habs : |S - (n : ℝ) ^ (D + 1) / F| ≤
      ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F := by
    rw [abs_le, sub_div]
    constructor
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
  have hnum : 0 ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := by linarith
  have hdiv : ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F ≤
      ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := div_le_self hnum hF1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)]
  have hk : (0 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) := by positivity
  calc |S - (n : ℝ) ^ (D + 1) / F|
      ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := habs.trans hdiv
    _ ≤ ((D + 1 : ℕ) : ℝ) * ((n + D) - (n - D)) * ((n : ℝ) + D) ^ D := hgap
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * ((n : ℝ) + D) ^ D := by ring
    _ ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) * (2 ^ D * (n : ℝ) ^ D) := mul_le_mul_of_nonneg_left hpow hk
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D * (n : ℝ) ^ D := by ring

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ShortFamilyEquivSmallFamilyVec
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField TensorProduct

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem fibreNorm_one_tmul (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (v : E.carrier) :
    fibreNorm E σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) = ‖fibreVec E.metric σ v‖ :=
  rfl

def ShortFamily.toSmallFamily {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.SmallFamily E lam where
  vec := F.vec
  indep := F.linearIndependent
  norm_le σ i := by
    rw [← fibreNorm_one_tmul]
    exact F.norm_le σ i

def ShortFamily.ofSmallFamily {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.SmallFamily E lam) : ShortFamily E lam where
  vec := F.vec
  linearIndependent := F.indep
  norm_le σ i := by
    rw [fibreNorm_one_tmul]
    exact F.norm_le σ i

def shortFamilyEquivSmallFamily (E : HermitianBundle.{0} K) (lam : (K →+* ℂ) → ℝ) :
    ShortFamily E lam ≃ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.SmallFamily E lam where
  toFun := ShortFamily.toSmallFamily
  invFun := ShortFamily.ofSmallFamily
  left_inv _ := rfl
  right_inv _ := rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end


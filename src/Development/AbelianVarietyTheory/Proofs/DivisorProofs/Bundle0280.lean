import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Formalism.LatticeTheta.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeBalancedLatticeDoubleSumStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_heckeBalancedLatticeDoubleSum : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (C₀ : ℝ) (m : ℕ), ∃ N : ℕ,
    ∀ ε : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → (𝓞 F)ˣ,
      (∀ c (τ τ' : Emb F), |τ (((ε c : 𝓞 F) : F) * c.out.1)| ≤ C₀ * |τ' (((ε c : 𝓞 F) : F) * c.out.1)|) →
      Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
        ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N) := by
  first | exact @GlobalTheory.HeckeTwo.summable_balanced_latSum | exact GlobalTheory.HeckeTwo.summable_balanced_latSum | (intros; apply GlobalTheory.HeckeTwo.summable_balanced_latSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeWeightTwoLatticeSum
section
open NumberField Complex
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeTwo

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem norm_phi_le (σ w : ℂ) (hσ : 0 < σ.re) (c : ℝ) (hc : 0 < c) (hcw : c ≤ |w.im|) :
    ‖phi σ w‖ ≤ ‖w⁻¹ ^ 2‖ * c ^ (-2 * σ.re) := by
  have hw : 0 < ‖w‖ := lt_of_lt_of_le hc (hcw.trans (Complex.abs_im_le_norm w))
  unfold phi
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : (-2 * σ).re = -2 * σ.re := by simp
  rw [hre]
  exact Real.rpow_le_rpow_of_nonpos hc (hcw.trans (Complex.abs_im_le_norm w)) (by linarith)

theorem summable_latSum (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : Frac F) (σ : ℂ)
    (hσ : 0 < σ.re) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) (b : F) (hb : b ≠ 0) :
    Summable (fun a : {a : F // a ∈ latM 𝔞} =>
      ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by
  classical
  have hM : latM 𝔞 ≠ 0 := by
    rw [latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero 𝔞)
  set z' : Emb F → ℂ := fun τ => ((τ b : ℝ) : ℂ) * z τ with hz'
  have hc : ∀ τ : Emb F, 0 < |τ b * (z τ).im| := fun τ =>
    abs_pos.2 (mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne')
  have him : ∀ τ : Emb F, (z' τ).im ≠ 0 := fun τ => by
    have := hc τ
    simp only [hz', Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact abs_pos.1 this
  have hs := GlobalTheory.LipschitzTR.summable_lhsTerm_ideal F (latM 𝔞) hM 2 le_rfl z' him
  have hs' : Summable (fun a : {a : F // a ∈ latM 𝔞} => GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1) := hs
  set C : ℝ := ∏ τ : Emb F, |τ b * (z τ).im| ^ (-2 * σ.re) with hC
  refine Summable.of_norm_bounded ((summable_norm_iff.2 hs').mul_left C) fun a => ?_
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1 =
      ∏ τ : Emb F, (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)⁻¹ ^ 2 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm
    rw [zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hz', inv_pow, add_comm]
  rw [hl, norm_prod, norm_prod, hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [mul_comm (|τ b * (z τ).im| ^ (-2 * σ.re))]
  refine norm_phi_le σ _ hσ _ (hc τ) (le_of_eq ?_)
  simp

end GlobalTheory.HeckeTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHilbertEisensteinWeightTwoQSeries
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoSum

variable {F : Type} [Field F] [NumberField F]

theorem pow_mul_exp_neg_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (n : ℕ) :
    t ^ n * Real.exp (-(c * t)) ≤ n.factorial / c ^ n := by
  have h := Real.pow_div_factorial_le_exp (c * t) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have he := Real.exp_pos (c * t)
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ (pow_pos hc n), Real.exp_neg]
  rw [show t ^ n * (Real.exp (c * t))⁻¹ * c ^ n = (c ^ n * t ^ n) / Real.exp (c * t) by field_simp]
  rw [div_le_iff₀ he]
  linarith

theorem exists_norm_lower (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ν ∈ I, ν ≠ 0 → κ ≤ |((Algebra.norm ℚ ν : ℚ) : ℝ)| := by
  obtain ⟨d, hd, hdI⟩ := GlobalTheory.HeckeTwo.APart.exists_den I
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| := by
    simp [Algebra.norm_eq_zero_iff, hd']
  refine ⟨|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)|⁻¹, inv_pos.2 hNd, fun ν hν hν0 => ?_⟩
  obtain ⟨x, hx⟩ := hdI ν hν
  have e1 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ ν := by
    rw [Algebra.coe_norm_int, hx, map_mul]
  have hxz : (Algebra.norm ℤ x : ℤ) ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at e1
    have h1 : Algebra.norm ℚ (d : F) ≠ 0 := (Algebra.norm_ne_zero_iff).2 hd'
    have h2 : Algebra.norm ℚ ν ≠ 0 := (Algebra.norm_ne_zero_iff).2 hν0
    exact mul_ne_zero h1 h2 e1.symm
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ x : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hxz
  have e2 : ((Algebra.norm ℤ x : ℤ) : ℝ) =
      ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ ν : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  rw [e2, abs_mul] at h1
  have := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hNd).le
  rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hNd.ne', one_mul] at this

theorem norm_qPow (ξ : F) (z : Emb F → ℂ) :
    ‖qPow ξ z‖ = Real.exp (-(2 * Real.pi * ∑ τ, τ ξ * (z τ).im)) := by
  rw [qPow, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

end GlobalTheory.HeckeTwoSum

namespace GlobalTheory.HeckeTwoSum

open GlobalTheory.LipschitzTR

variable {F : Type} [Field F] [NumberField F]

theorem summable_qClass_two [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) :
    Summable (qClass 𝔞 𝔟 2 z) := by
  classical
  obtain ⟨τ₀⟩ := GlobalTheory.HeckeTwoExp.emb_nonempty (F := F)
  obtain ⟨m, hm, hmy⟩ : ∃ m : ℝ, 0 < m ∧ ∀ τ, m ≤ (z τ).im := by
    obtain ⟨τ₁, -, hτ₁⟩ := Finset.exists_min_image Finset.univ (fun τ => (z τ).im) ⟨τ₀, Finset.mem_univ _⟩
    exact ⟨_, hz τ₁, fun τ => hτ₁ τ (Finset.mem_univ _)⟩
  obtain ⟨κ, hκ, hκν⟩ := exists_norm_lower (𝔞 : FractionalIdeal (𝓞 F)⁰ F)
  have hnrm : 0 < nrm 𝔞 := lt_of_le_of_ne (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _)
    (GlobalTheory.HeckeTwoExp.nrm_ne_zero 𝔞).symm
  set N : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) with hN
  haveI : DiscreteTopology (latOf N) := discrete_latOf F N
  set n : ℕ := Module.finrank ℤ (latOf N) + 1 with hn
  have hL : Summable fun v : latOf N => ‖v‖⁻¹ ^ n := ZLattice.summable_norm_pow_inv (latOf N) n (Nat.lt_succ_self _)
  set f : ℕ := Fintype.card (Emb F) with hf
  set K : ℝ := ((2 * f + n).factorial : ℝ) / (2 * Real.pi * m) ^ (2 * f + n) with hK
  set C : ℝ := K / (nrm 𝔞 * κ) with hC
  have hK0 : 0 < K := by positivity
  have hC0 : 0 < C := by positivity
  have key : ∀ ν b : F, ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ν ≠ 0 → b ≠ 0 → (∀ τ : Emb F, 0 < τ (ν * b)) →
      ‖qTerm 𝔞 2 z (ν, b)‖ ≤
        C * ((|((Algebra.norm ℚ b : ℚ) : ℝ)| ^ 2)⁻¹ * ‖remb F (ν * b)‖⁻¹ ^ n) := by
    intro ν b hν hν0 hb0 hpos
    set ξ := ν * b with hξ
    set s := ∑ τ : Emb F, τ ξ with hs_def
    set A := |((Algebra.norm ℚ ν : ℚ) : ℝ)| with hA_def
    set B := |((Algebra.norm ℚ b : ℚ) : ℝ)| with hB_def
    set w := ‖remb F ξ‖ with hw_def
    have hs : 0 < s := Finset.sum_pos (fun τ _ => hpos τ) ⟨τ₀, Finset.mem_univ _⟩
    have hA : κ ≤ A := hκν ν hν hν0
    have hA0 : 0 < A := hκ.trans_le hA
    have hB0 : 0 < B := by
      rw [hB_def, abs_pos, Rat.cast_ne_zero]; exact (Algebra.norm_ne_zero_iff).2 hb0
    have hw0 : 0 < w := by
      rw [hw_def, norm_pos_iff]
      intro h
      have := congrArg (fun v : RSp F => v τ₀) h
      have h3 : τ₀ ξ = 0 := by simpa using this
      have h2 := hpos τ₀
      linarith
    have hws : w ≤ s := by
      rw [hw_def, EuclideanSpace.norm_eq]
      refine Real.sqrt_le_iff.2 ⟨hs.le, ?_⟩
      calc ∑ τ, ‖(remb F ξ) τ‖ ^ 2 = ∑ τ : Emb F, (τ ξ) ^ 2 := by
            refine Finset.sum_congr rfl fun τ _ => ?_
            rw [remb_apply, Real.norm_eq_abs, sq_abs]
        _ ≤ (∑ τ : Emb F, τ ξ) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun τ _ => (hpos τ).le
    have hAB : A * B ≤ s ^ f := by
      have h2 := GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ξ
      rw [← Complex.ofReal_prod] at h2
      have h3 := Complex.ofReal_injective h2
      have h1 : A * B = ∏ τ : Emb F, τ ξ := by
        rw [hA_def, hB_def, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hξ, h3]
        exact Finset.prod_congr rfl fun τ _ => abs_of_pos (hpos τ)
      rw [h1, hf, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun τ _ => (hpos τ).le)
        (fun τ _ => Finset.single_le_sum (fun τ _ => (hpos τ).le) (Finset.mem_univ τ))
    set E := Real.exp (-(2 * Real.pi * ∑ τ, τ ξ * (z τ).im)) with hE
    set E' := Real.exp (-((2 * Real.pi * m) * s)) with hE'
    have hEE : E ≤ E' := by
      apply Real.exp_le_exp.2
      have : m * s ≤ ∑ τ, τ ξ * (z τ).im := by
        rw [hs_def, Finset.mul_sum]
        exact Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hmy τ]
      nlinarith [Real.pi_pos]
    have hKs := pow_mul_exp_neg_le (c := 2 * Real.pi * m) (t := s) (by positivity) hs.le (2 * f + n)
    have hP : (A * B) ^ 2 * w ^ n ≤ s ^ (2 * f + n) := by
      rw [show s ^ (2 * f + n) = (s ^ f) ^ 2 * s ^ n by ring]
      gcongr
    have hE'K : E' * ((A * B) ^ 2 * w ^ n) ≤ K := by
      have hE'0 : 0 ≤ E' := (Real.exp_pos _).le
      calc E' * ((A * B) ^ 2 * w ^ n) ≤ E' * s ^ (2 * f + n) := mul_le_mul_of_nonneg_left hP hE'0
        _ = s ^ (2 * f + n) * E' := mul_comm _ _
        _ ≤ K := hKs
    have hnorm : ‖qTerm 𝔞 2 z (ν, b)‖ = A / nrm 𝔞 * E := by
      rw [qTerm, norm_mul, norm_qPow, Complex.norm_real, Real.norm_eq_abs, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
        abs_of_nonneg (div_nonneg (abs_nonneg _) hnrm.le)]
    have hR : C * ((B ^ 2)⁻¹ * w⁻¹ ^ n) = K / (nrm 𝔞 * κ * B ^ 2 * w ^ n) := by
      rw [hC, inv_pow]
      field_simp
    rw [hnorm, hR, le_div_iff₀ (by positivity)]
    calc A / nrm 𝔞 * E * (nrm 𝔞 * κ * B ^ 2 * w ^ n) = E * (A * κ * B ^ 2 * w ^ n) := by
          field_simp
      _ ≤ E' * (A * A * B ^ 2 * w ^ n) := by
          gcongr
      _ = E' * ((A * B) ^ 2 * w ^ n) := by ring
      _ ≤ K := hE'K
  set e := Equiv.ofBijective (GlobalTheory.HeckeTwoExp.toQ 𝔞 𝔟)
    ⟨GlobalTheory.HeckeTwoExp.toQ_injective 𝔞 𝔟, GlobalTheory.HeckeTwoExp.toQ_surjective 𝔞 𝔟⟩ with he
  let ι : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)} → latOf N :=
    fun c ν => ⟨remb F (ν.1.1 * c.out.1),
      (mem_latOf N _).2 ⟨_, FractionalIdeal.mul_mem_mul ν.1.2.1 c.out.2.1, rfl⟩⟩
  have hι : ∀ c, Function.Injective (ι c) := by
    intro c ν ν' h
    have h1 := congrArg (fun v : latOf N => (v : RSp F) τ₀) h
    simp only [ι, remb_apply] at h1
    have h2 : ν.1.1 * c.out.1 = ν'.1.1 * c.out.1 := τ₀.injective h1
    exact Subtype.ext (Subtype.ext (mul_right_cancel₀ c.out.2.2 h2))
  set Bf : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → ℝ :=
    fun c => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| with hBf
  set G : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → ℝ :=
    fun p => C * ((Bf p.1 ^ 2)⁻¹ * ‖ι p.1 p.2‖⁻¹ ^ n) with hG
  have hG0 : ∀ p, 0 ≤ G p := fun p => by
    simp only [hG]; positivity
  have hbound : ∀ p, ‖qClass 𝔞 𝔟 2 z (e p)‖ ≤ G p := by
    rintro ⟨c, ν⟩
    calc ‖qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩)‖ = ‖qTerm 𝔞 2 z (ν.1.1, c.out.1)‖ :=
          congrArg norm (qClass_mk 𝔞 𝔟 2 z ⟨(ν.1.1, c.out.1), ν.1.2.1, c.out.2.1, ν.2⟩)
      _ ≤ G ⟨c, ν⟩ := key ν.1.1 c.out.1 ν.1.2.1 ν.1.2.2 c.out.2.2 ν.2
  have hGs : Summable G := by
    refine (summable_sigma_of_nonneg hG0).2 ⟨fun c => ?_, ?_⟩
    · exact ((hL.comp_injective (hι c)).mul_left ((Bf c ^ 2)⁻¹)).mul_left C
    · have hZ := GlobalTheory.HeckeTwo.APart.summable_norm_rpow (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (s := 2) one_lt_two
      refine Summable.of_nonneg_of_le (fun c => tsum_nonneg fun ν => hG0 ⟨c, ν⟩) (fun c => ?_)
        (hZ.mul_left (C * ∑' v : latOf N, ‖v‖⁻¹ ^ n))
      show ∑' ν, C * ((Bf c ^ 2)⁻¹ * ‖ι c ν‖⁻¹ ^ n) ≤ _
      rw [tsum_mul_left, tsum_mul_left, Real.rpow_neg (abs_nonneg _), Real.rpow_two]
      have hH : ∑' ν, ‖ι c ν‖⁻¹ ^ n ≤ ∑' v : latOf N, ‖v‖⁻¹ ^ n :=
        tsum_comp_le_tsum_of_inj hL (fun _ => by positivity) (hι c)
      have hB : 0 ≤ (Bf c ^ 2)⁻¹ := by positivity
      calc C * ((Bf c ^ 2)⁻¹ * ∑' ν, ‖ι c ν‖⁻¹ ^ n) ≤ C * ((Bf c ^ 2)⁻¹ * ∑' v : latOf N, ‖v‖⁻¹ ^ n) := by
            gcongr
        _ = _ := by simp only [hBf]; ring
  refine Summable.of_norm ?_
  rw [← e.summable_iff]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hGs

end GlobalTheory.HeckeTwoSum

theorem GlobalTheory.HeckeTwoSum.summable_qClass : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) :=
  fun _ _ _ _ 𝔞 𝔟 z hz => GlobalTheory.HeckeTwoSum.summable_qClass_two 𝔞 𝔟 z hz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummandStatement
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_lipschitzLatticeNormPowSummand : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 → ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  first | exact @GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | exact GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | (intros; apply GlobalTheory.LipschitzTR.summable_lhsTerm_ideal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSeminormGaussianConvolutionSeriesTerm
section
open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

theorem summable_seminorm_term : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ)
    (t : ℕ → SchwartzMap E ℂ), (∀ j y, t j y = GlobalTheory.ConvSeries.term b c h j y) →
    ∀ (k n : ℕ), Summable (fun j => SchwartzMap.seminorm ℂ k n (t j)) := by
  intro E _ _ _ _ _ b c hb hc h t ht k n

  set δ : ℝ := min 1 (b / (6 * c)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ b / (6 * c) := min_le_right _ _
  set θ : ℝ := 1 + δ with hθ
  set α : ℝ := (2 * c + b) / (2 * (b + c)) with hα
  have hθ1 : 1 ≤ θ := by linarith
  have hθpos : 0 < θ := by linarith
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by positivity)]; linarith
  have hθα : c * θ ^ 2 ≤ α * (b + c) := by
    have e1 : α * (b + c) = c + b / 2 := by rw [hα]; field_simp
    have e2 : δ * (6 * c) ≤ b := by rwa [le_div_iff₀ (by positivity)] at hδ2
    rw [e1, hθ]; nlinarith

  choose K hK using fun m => GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded E c α hc hα1 k m
  set M : ℕ → ℝ := fun i => ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ with hM
  have hM0 : ∀ i, 0 ≤ M i := fun i => integral_nonneg fun a => by positivity
  set B : ℝ := θ ^ n * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M (n - i) * K i with hB
  have hK0 : ∀ m, 0 ≤ K m := fun m => le_trans (by positivity) (hK m 0)
  have hB0 : 0 ≤ B := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (mul_nonneg (by positivity) (hM0 _)) (hK0 _)
  have hbound : ∀ j, SchwartzMap.seminorm ℂ k n (t j) ≤ θ⁻¹ ^ j * B := by
    intro j
    refine SchwartzMap.seminorm_le_bound ℂ k n (t j) (by positivity) fun y => ?_
    set s : ℝ := (2 * c) ^ j / (j.factorial : ℝ) with hs
    have hs0 : 0 ≤ s := by positivity
    set f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ :=
      ((s : ℝ) : ℂ) • GlobalTheory.ConvSeries.coef b c (⇑h) j with hf
    have hfun : (⇑(t j)) = fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y) := by
      funext y
      rw [ht, GlobalTheory.ConvSeries.term, hf, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_assoc]
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) := by
      refine Complex.contDiff_exp.comp ?_
      refine ContDiff.neg ?_
      exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
    have hP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => f (fun _ => y)) :=
      f.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
    have hL := norm_iteratedFDeriv_mul_le hG hP y (n := n) (by exact_mod_cast le_top)
    rw [hfun]
    have hfn : ‖f‖ ≤ s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by
      rw [hf, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left (GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral E b c hb.le hc.le h j) hs0
    have hterm : ∀ i ∈ Finset.range (n + 1),
        ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) ≤
        θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      set m := n - i
      have h1 := GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le E j f m y
      have h3 := GlobalTheory.T.gaussianConvolutionSeriesCoefficient_descFactorial_estimate E b c θ α hc hθ1 hα0 hθα h j m y
      have hPm : ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖ ≤
          θ⁻¹ ^ (j - m) * Real.exp (c * α * ‖y‖ ^ 2) * M m := by
        refine h1.trans (le_trans ?_ h3)
        have := mul_le_mul_of_nonneg_left hfn (by positivity : (0:ℝ) ≤ (j.descFactorial m : ℝ))
        calc (j.descFactorial m : ℝ) * ‖f‖ * ‖y‖ ^ (j - m)
            ≤ (j.descFactorial m : ℝ) * (s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) * ‖y‖ ^ (j - m) := by
              gcongr
          _ = _ := by rw [hs]; ring
      have hθj : θ⁻¹ ^ (j - m) ≤ θ⁻¹ ^ j * θ ^ n := by
        have hinv : 0 < θ⁻¹ := inv_pos.2 hθpos
        have hle : θ⁻¹ ^ (j - m + m) ≤ θ⁻¹ ^ j :=
          pow_le_pow_of_le_one hinv.le (inv_le_one_of_one_le₀ hθ1) (by omega)
        have e : θ⁻¹ ^ (j - m) = θ⁻¹ ^ (j - m + m) * θ ^ m := by
          rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hθpos.ne', one_pow, mul_one]
        rw [e]
        exact mul_le_mul hle (pow_le_pow_right₀ hθ1 (by omega)) (by positivity) (by positivity)
      have hGk := hK i y
      have hch : (0:ℝ) ≤ n.choose i := by positivity
      calc ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖)
          ≤ ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            (θ⁻¹ ^ j * θ ^ n * Real.exp (c * α * ‖y‖ ^ 2) * M m)) := by
            gcongr
            exact hPm.trans (by gcongr)
        _ = θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m *
            (‖y‖ ^ k * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
              Real.exp (c * α * ‖y‖ ^ 2)))) := by ring
        _ ≤ θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m * K i)) := by
            gcongr
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y)) y‖
        ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), ‖y‖ ^ k * ((n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) :=
            Finset.sum_le_sum hterm
      _ = θ⁻¹ ^ j * B := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hgeom : Summable fun j : ℕ => θ⁻¹ ^ j * B :=
    (summable_geometric_of_lt_one (inv_nonneg.2 hθpos.le) (inv_lt_one_of_one_lt₀ (by linarith))).mul_right B
  exact Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) hbound hgeom

end GlobalTheory.ConvSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfTraceOfSmulMemRange
section
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

theorem surjective_of_trace_of_smul_mem_range (S A B : Type) [CommRing S] [IsLocalRing S]
    [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A]
    [Algebra.Etale S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B]
    [Algebra.Etale S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ) (s : S) (hs : s ≠ 0)
    (hcok : ∀ b : B, s • b ∈ φ.range)
    (htr : ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x) : Function.Surjective φ := by
  classical
  have htf : ∀ b : B, s • b = 0 → b = 0 := by
    intro b hb
    let e := Module.Free.chooseBasis S B
    apply e.repr.injective
    ext i
    have := congrArg (fun x => e.repr x i) hb
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
    simpa using (mul_eq_zero.mp this).resolve_left hs
  let L : A →ₗ[S] B := φ.toLinearMap
  have hL : Function.Injective L := hφ
  let E : A ≃ₗ[S] LinearMap.range L := LinearEquiv.ofInjective L hL
  let g : B →ₗ[S] LinearMap.range L :=
    { toFun := fun b => ⟨s • b, by obtain ⟨a, ha⟩ := hcok b; exact ⟨a, ha⟩⟩
      map_add' := fun x y => by ext; simp [smul_add]
      map_smul' := fun c x => by ext; simp [smul_comm s c] }
  have hg : Function.Injective g := by
    intro x y hxy
    have : s • x = s • y := congrArg Subtype.val hxy
    have h0 : s • (x - y) = 0 := by rw [smul_sub, this, sub_self]
    exact sub_eq_zero.mp (htf _ h0)
  have h1 : Module.finrank S A ≤ Module.finrank S B :=
    LinearMap.finrank_le_finrank_of_injective hL
  have h2 : Module.finrank S B ≤ Module.finrank S A :=
    LinearMap.finrank_le_finrank_of_injective (f := E.symm.toLinearMap ∘ₗ g)
      (E.symm.injective.comp hg)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex S A) =
      Fintype.card (Module.Free.ChooseBasisIndex S B) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex]
    omega
  let eι := Fintype.equivOfCardEq hcard
  let a := (Module.Free.chooseBasis S A).reindex eι
  let bB := Module.Free.chooseBasis S B
  let v : Module.Free.ChooseBasisIndex S B → B := fun i => φ (a i)
  have htm : Algebra.traceMatrix S v = Algebra.traceMatrix S a := by
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, v, ← map_mul, htr]
  have hdv : Algebra.discr S v = Algebra.discr S a := by
    rw [Algebra.discr_def, Algebra.discr_def, htm]
  let P := bB.toMatrix v
  have hv : Matrix.vecMul (⇑bB) (P.map (algebraMap S B)) = v := by
    funext j
    rw [← bB.sum_toMatrix_smul_self v j]
    simp [Matrix.vecMul, dotProduct, P, Algebra.smul_def, mul_comm]
  have hdisc : Algebra.discr S v = P.det ^ 2 * Algebra.discr S bB := by
    rw [← hv, Algebra.discr_of_matrix_vecMul]
  have hu : IsUnit (P.det ^ 2 * Algebra.discr S bB) := by
    rw [← hdisc, hdv]; exact discr_isUnit S A a
  have hPu : IsUnit P.det := (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left hu)
  have hbd : IsUnit (bB.det v) := by rw [Module.Basis.det_apply]; exact hPu
  have hspan := ((Module.Basis.is_basis_iff_det bB).mpr hbd).2
  intro y
  have hy : y ∈ Submodule.span S (Set.range v) := by rw [hspan]; trivial
  have hle : Submodule.span S (Set.range v) ≤ LinearMap.range L := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact ⟨a i, rfl⟩
  obtain ⟨x, hx⟩ := hle hy
  exact ⟨x, hx⟩

end GlobalTheory.EtaleCoker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorBasisCriterion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_basis_criterion : ∀ (A B R S : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] [CommRing S] (κ : R ⊗[A] B →+* S) {r : ℕ} (v : Fin r → B), Function.Bijective (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) ↔ (Function.Surjective κ ∧ LinearIndependent R (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) = ⊤) := by
  first | (exact @GlobalTheory.tensorSum_bijective_iff) | (exact GlobalTheory.tensorSum_bijective_iff) | (intros; apply GlobalTheory.tensorSum_bijective_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembershipStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  first | exact @GlobalTheory.WpFam.TorsMem.main | exact GlobalTheory.WpFam.TorsMem.main | (intros; apply GlobalTheory.WpFam.TorsMem.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibreStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  first | (exact @GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (exact GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (intros; apply GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin  <;> assumption)
end


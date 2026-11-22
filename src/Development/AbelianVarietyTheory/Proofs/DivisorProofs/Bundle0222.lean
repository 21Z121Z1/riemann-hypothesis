import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import ReciprocityTheory.Chebotarev.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumLambertDoubleSeriesDivisors
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem summable_lambert_prod (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ) (hQ : ‖Q‖ < 1)
    (hc : ∀ d m, ‖c d m‖ ≤ 1) :
    Summable fun x : ℕ+ × ℕ+ =>
      ((x.2 : ℕ) : ℂ) ^ e * c x.1 x.2 * Q ^ ((x.1 : ℕ) * (x.2 : ℕ)) := by
  have h := summable_prod_mul_pow (𝕜 := ℝ) e (r := ‖Q‖) (by simpa using hQ)
  refine Summable.of_norm_bounded h fun x => ?_
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  gcongr
  calc ((x.2 : ℕ) : ℝ) ^ e * ‖c x.1 x.2‖ ≤ ((x.2 : ℕ) : ℝ) ^ e * 1 := by
        gcongr; exact hc _ _
    _ = _ := mul_one _

theorem hasSum_lambert : ∀ (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ), ‖Q‖ < 1 → (∀ d m, ‖c d m‖ ≤ 1) → HasSum (fun k : ℕ => (∑ m ∈ k.divisors, (m : ℂ) ^ e * c (k / m) m) * Q ^ k) (∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c d m * Q ^ ((d : ℕ) * (m : ℕ))) := by
  intro e Q c hQ hc
  have hs := summable_lambert_prod e Q c hQ hc
  rw [← hs.tsum_prod]
  have h1 := sigmaAntidiagonalEquivProd.hasSum_iff.mpr hs.hasSum
  have h2 := h1.sigma (fun n => hasSum_fintype _)
  refine (Function.Injective.hasSum_iff (g := PNat.val) PNat.coe_injective ?_).mp ?_
  · intro k hk
    have : k = 0 := by
      by_contra h
      exact hk ⟨⟨k, Nat.pos_of_ne_zero h⟩, rfl⟩
    simp [this]
  · refine HasSum.congr_fun h2 fun n => ?_
    symm
    have h3 : ∀ x : Nat.divisorsAntidiagonal (n : ℕ),
        ((fun x : ℕ+ × ℕ+ => ((x.2 : ℕ) : ℂ) ^ e * c x.1 x.2 * Q ^ ((x.1 : ℕ) * (x.2 : ℕ))) ∘
          sigmaAntidiagonalEquivProd) ⟨n, x⟩ =
        (fun y : ℕ × ℕ => (y.2 : ℂ) ^ e * c y.1 y.2 * Q ^ (y.1 * y.2)) x.1 := fun x => rfl
    rw [Finset.sum_congr rfl (fun x _ => h3 x),
      Finset.sum_coe_sort (Nat.divisorsAntidiagonal (n : ℕ))
        (fun y : ℕ × ℕ => (y.2 : ℂ) ^ e * c y.1 y.2 * Q ^ (y.1 * y.2)),
      Nat.sum_divisorsAntidiagonal' (fun a b : ℕ => (b : ℂ) ^ e * c a b * Q ^ (a * b))]
    simp only [Function.comp_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m hm => by
      rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)]

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumRowsInvCubeDerivWeierstrassP
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem hasSum_prod_derivWeierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3)
      (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  have h := ((tauPair τ).hasSum_derivWeierstrassP z).mul_left (-(1 / 2))
  let e : ℤ × ℤ ≃ (tauPair τ).lattice :=
    (Equiv.neg (ℤ × ℤ)).trans (tauPair τ).latticeEquivProd.symm.toEquiv
  rw [← e.hasSum_iff] at h
  have key : (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3) =
      (fun i : (tauPair τ).lattice => -(1 / 2) * (-2 / (z - (i : ℂ)) ^ 3)) ∘ e := ?_
  · rw [key]; exact h
  funext p
  have he : ((e p : (tauPair τ).lattice) : ℂ) = -(p.1 * (τ : ℂ) + p.2) := by
    change ((tauPair τ).latticeEquivProd.symm (-p)).1 = _
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp [tauPair]
    ring
  simp only [Function.comp, he]
  rw [show z - -(p.1 * (τ : ℂ) + p.2) = z + p.1 * (τ : ℂ) + p.2 by ring]
  ring

theorem hasSum_rows_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  intro τ z
  have h := hasSum_prod_derivWeierstrassP τ z
  exact h.prod_fiberwise fun n => (h.summable.prod_factor n).hasSum

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraceSumInnerOfRangeLe
section
namespace GlobalTheory.OpTrace

theorem hasTrace_sum_inner_of_range_le (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [CompleteSpace U] (L : Submodule ℂ U) [FiniteDimensional ℂ L] (T : U →L[ℂ] U)
    (hT : ∀ u, T u ∈ L) :
    HasTrace T (∑ j, inner ℂ (stdOrthonormalBasis ℂ L j : U)
      (T (stdOrthonormalBasis ℂ L j : U))) := by
  have hle : LinearMap.range (T : U →ₗ[ℂ] U) ≤ L := by
    rintro _ ⟨x, rfl⟩; exact hT x
  have := Submodule.finiteDimensional_of_le hle
  have h := hasTrace_of_finiteRank T
  rw [finRankTrace_eq (T : U →ₗ[ℂ] U) L hT,
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ L)] at h
  exact h

end GlobalTheory.OpTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseJetVanishingMemPowStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_mem_pow_of_hasse_vanishing : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k), 2 ≤ N → Δ 0 1 = 1 → (∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ p u * Δ (l - p) w) → (∃ π : A, Δ 1 π = 1) → ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧ ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  first | exact @GlobalTheory.hasseJet_vanishing_mem_pow | exact GlobalTheory.hasseJet_vanishing_mem_pow | (intros; apply GlobalTheory.hasseJet_vanishing_mem_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.APart

variable {F : Type} [Field F] [NumberField F]

theorem exists_den (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ b ∈ I, ∃ x : 𝓞 F, (x : F) = (d : F) * b := by
  obtain ⟨d, hd, h⟩ := I.isFractional
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun b hb => ?_⟩
  obtain ⟨x, hx⟩ := h b hb
  exact ⟨x, by rw [← Algebra.smul_def] at *; simpa using hx⟩

theorem summable_norm_rpow (I : FractionalIdeal (𝓞 F)⁰ F) {s : ℝ} (hs : 1 < s) :
    Summable (fun c : Quotient (unitRel I) => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| ^ (-s)) := by
  obtain ⟨d, hd, hdI⟩ := exists_den I
  choose g hg using fun c : Quotient (unitRel I) => hdI c.out.1 c.out.2.1
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have hinj : Function.Injective (fun c : Quotient (unitRel I) => Ideal.span ({g c} : Set (𝓞 F))) := by
    intro c c' h
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h
    have h2 := congrArg (fun x : 𝓞 F => (x : F)) hu
    push_cast at h2
    refine Quotient.out_equiv_out.1 ⟨u, ?_⟩
    apply mul_left_cancel₀ hd'
    linear_combination ((u : 𝓞 F) : F) * hg c - hg c' - h2
  have hS := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective hinj
  have hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| := by
    simp [Algebra.norm_eq_zero_iff, hd']
  refine (hS.mul_left (|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| ^ s)).congr fun c => ?_
  have e1 : ((Algebra.norm ℤ (g c) : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ c.out.1 := by
    rw [Algebra.coe_norm_int, hg, map_mul]
  have e2 : ((Algebra.norm ℤ (g c) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ c.out.1 : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  have hN : ((Ideal.absNorm (Ideal.span ({g c} : Set (𝓞 F))) : ℕ) : ℝ) =
      |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]
  simp only [Function.comp_apply]
  rw [hN, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hNd, add_neg_cancel,
    Real.rpow_zero, one_mul]

theorem inv_natPow_rpow_neg_half_even_eq_pow {x : ℝ} (hx : 0 < x) (t : ℝ) : x ^ (-(2 + 2 * t)) = x⁻¹ ^ 2 * x ^ (-2 * t) := by
  rw [show -(2 + 2 * t) = -(2 : ℝ) + -2 * t by ring, Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_two, inv_pow]

theorem rpow_le_add {x : ℝ} (hx : 0 < x) {r t R : ℝ} (hr : r ≤ t) (hR : t ≤ R) :
    x ^ (-2 * t) ≤ x ^ (-2 * r) + x ^ (-2 * R) := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hx h (show -2 * R ≤ -2 * t by linarith)
    linarith [Real.rpow_nonneg hx.le (-2 * r)]
  · have := Real.rpow_le_rpow_of_exponent_le h (show -2 * t ≤ -2 * r by linarith)
    linarith [Real.rpow_nonneg hx.le (-2 * R)]

variable [IsTotallyReal F]

theorem prod_latPt_zero (a : F) :
    ∏ τ : Emb F, latPt 0 (a, 0) τ =
      (2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F) * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
  simp only [latPt, Pi.zero_apply, map_zero, ofReal_zero, zero_mul, add_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, prod_emb]

end GlobalTheory.HeckeTwo.APart

open GlobalTheory.HeckeTwo.APart in

theorem GlobalTheory.HeckeTwo.aPart_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (GlobalTheory.HeckeTwo.aPart 𝔞) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ _ 𝔞
  set P : Quotient (unitRel (latM 𝔞)) → ℂ := fun c => ∏ τ : Emb F, latPt 0 ((c.out.1 : F), (0 : F)) τ with hP
  have hP0 : ∀ c, P c ≠ 0 := fun c => by
    simp only [hP, prod_latPt_zero]
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero
    · exact_mod_cast (Algebra.norm_ne_zero_iff).2 c.out.2.2
  set K : ℝ := ‖(2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F)‖ with hK
  have hK0 : 0 < K := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact norm_pos_iff.2 (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero))
  have hnP : ∀ c, ‖P c‖ = K * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := fun c => by
    simp only [hP, prod_latPt_zero, norm_mul, hK]
    congr 1
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have hsum : ∀ t : ℝ, 1 < t → Summable fun c => ‖P c‖ ^ (-t) := fun t ht =>
    ((summable_norm_rpow (latM 𝔞) ht).mul_left (K ^ (-t))).congr fun c => by
      rw [hnP, Real.mul_rpow hK0.le (abs_nonneg _)]
  have hnorm : ∀ c σ, ‖eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))‖ = ‖P c‖⁻¹ ^ 2 * ‖P c‖ ^ (-2 * σ.re) := fun c σ => by
    show ‖(P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)‖ = _
    rw [norm_mul, norm_pow, norm_inv, norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.2 (hP0 c))]
    simp
  intro σ₀ hσ₀
  have hσ₀' : -1 / 2 < σ₀.re := hσ₀
  set r : ℝ := (σ₀.re - 1 / 2) / 2 with hr
  set R : ℝ := σ₀.re + 1 with hR
  set U : Set ℂ := {σ | r < σ.re} ∩ {σ | σ.re < R} with hUdef
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hmem : σ₀ ∈ U := ⟨by show r < σ₀.re; rw [hr]; linarith, by show σ₀.re < R; rw [hR]; linarith⟩
  have hd : DifferentiableOn ℂ (fun σ => ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun c => ‖P c‖⁻¹ ^ 2 * (‖P c‖ ^ (-2 * r) + ‖P c‖ ^ (-2 * R))) ?_ ?_ hU ?_
    · refine ((hsum (2 + 2 * r) (by rw [hr]; linarith)).add (hsum (2 + 2 * R) (by rw [hR]; linarith))).congr
        fun c => ?_
      have hx := norm_pos_iff.2 (hP0 c)
      rw [inv_natPow_rpow_neg_half_even_eq_pow hx, inv_natPow_rpow_neg_half_even_eq_pow hx]
      ring
    · intro c σ _
      show DifferentiableWithinAt ℂ (fun σ => (P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)) U σ
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.const_mul ?_ _)
      refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
      exact_mod_cast (norm_pos_iff.2 (hP0 c)).ne'
    · intro c σ hσ
      rw [hnorm]
      have hx := norm_pos_iff.2 (hP0 c)
      gcongr
      exact rpow_le_add hx hσ.1.le hσ.2.le
  exact (hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOn
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoC

open MeasureTheory

def lg (t : ℝ) : ℝ := Real.log ‖(t : ℂ) + I‖

theorem tI_ne (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

theorem sq_norm_tI (t : ℝ) : ‖(t : ℂ) + I‖ ^ 2 = 1 + ‖t‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]; simp; ring

theorem norm_tI_eq (t : ℝ) : ‖(t : ℂ) + I‖ = Real.exp (lg t) :=
  (Real.exp_log (norm_pos_iff.2 (tI_ne t))).symm

theorem lg_nonneg (t : ℝ) : 0 ≤ lg t := by
  apply Real.log_nonneg
  have h := sq_norm_tI t
  nlinarith [norm_nonneg ((t : ℂ) + I), sq_nonneg ‖t‖]

theorem continuous_lg : Continuous lg := by
  unfold lg
  exact (Continuous.norm (by fun_prop)).log (fun t => (norm_pos_iff.2 (tI_ne t)).ne')

def G (σ : ℂ) (t : ℝ) : ℂ := ((t : ℂ) + I)⁻¹ ^ 2 * Complex.exp ((lg t : ℂ) * (-2 * σ))

def G' (σ : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + I)⁻¹ ^ 2 * (Complex.exp ((lg t : ℂ) * (-2 * σ)) * ((lg t : ℂ) * (-2)))

theorem cConst_eq : cConst = fun σ => ∫ t, G σ t := by
  funext σ
  unfold cConst hTrans G
  congr 1; funext t
  simp only [ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one, ofReal_one, one_mul]
  unfold phi
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (norm_pos_iff.2 (tI_ne t)).ne'),
    ← Complex.ofReal_log (norm_nonneg _)]
  rfl

theorem norm_G (σ : ℂ) (t : ℝ) : ‖G σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) := by
  unfold G
  rw [norm_mul, norm_pow, norm_inv, norm_tI_eq, Complex.norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_G' (σ : ℂ) (t : ℝ) : ‖G' σ t‖ = Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t) := by
  have : G' σ t = G σ t * ((lg t : ℂ) * (-2)) := by unfold G G'; ring
  rw [this, norm_mul, norm_G, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lg_nonneg t)]
  simp; ring

theorem bound_G {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G σ t‖ ≤ Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G]
  apply Real.exp_le_exp.2
  have := lg_nonneg t
  nlinarith

theorem bound_G' {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G' σ t‖ ≤ 2 / ε * Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G']
  have hL := lg_nonneg t
  have h1 : Real.exp (-(2 + 2 * σ.re) * lg t) ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have h2 : ε * lg t + 1 ≤ Real.exp (ε * lg t) := Real.add_one_le_exp _
  have h3 : Real.exp (-(ε * lg t)) * (2 * lg t) ≤ 2 / ε := by
    rw [Real.exp_neg, le_div_iff₀ hε]
    have hp := Real.exp_pos (ε * lg t)
    rw [show (Real.exp (ε * lg t))⁻¹ * (2 * lg t) * ε = 2 * (ε * lg t) / Real.exp (ε * lg t) by field_simp]
    rw [div_le_iff₀ hp]
    linarith
  calc Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t)
      ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) * (2 * lg t) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ = Real.exp (-(1 + ε) * lg t) * (Real.exp (-(ε * lg t)) * (2 * lg t)) := by ring
    _ ≤ Real.exp (-(1 + ε) * lg t) * (2 / ε) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 2 / ε * Real.exp (-(1 + ε) * lg t) := by ring

theorem integrable_expL {ε : ℝ} (hε : 0 < ε) : Integrable (fun t : ℝ => Real.exp (-(1 + ε) * lg t)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 1 + ε) (by simp; linarith)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [← sq_norm_tI, norm_tI_eq, ← Real.exp_nat_mul, ← Real.exp_mul]
  congr 1; push_cast; ring

theorem hasDerivAt_G (σ : ℂ) (t : ℝ) : HasDerivAt (fun s => G s t) (G' σ t) σ := by
  unfold G G'
  have h : HasDerivAt (fun s : ℂ => (lg t : ℂ) * (-2 * s)) ((lg t : ℂ) * (-2)) σ := by
    exact (((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (lg t : ℂ)).congr_deriv (by ring)
  exact h.cexp.const_mul _

theorem continuous_G (σ : ℂ) : Continuous (G σ) := by
  unfold G
  have : Continuous fun t : ℝ => ((t : ℂ) + I)⁻¹ :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + I).inv₀ tI_ne
  exact (this.pow 2).mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const))

theorem continuous_G' (σ : ℂ) : Continuous (G' σ) := by
  have : G' σ = fun t => G σ t * ((lg t : ℂ) * (-2)) := by funext t; unfold G G'; ring
  rw [this]
  exact (continuous_G σ).mul ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const)

end GlobalTheory.HeckeTwoC

namespace GlobalTheory.HeckeTwo

open MeasureTheory GlobalTheory.HeckeTwoC

theorem cConst_differentiableOn : DifferentiableOn ℂ cConst halfPlane := by
  rw [cConst_eq]
  intro σ₀ hσ₀
  have hre : -1 / 2 < σ₀.re := hσ₀
  set ε := (σ₀.re + 1 / 2) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re := by
    intro σ hσ
    have h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖σ - σ₀‖ < ε := by simpa [dist_eq_norm] using hσ
    have h3 := (abs_lt.1 (lt_of_le_of_lt h1 h2)).1
    simp only [sub_re] at h3
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := G) (F' := G')
    (x₀ := σ₀) (bound := fun t => 2 / ε * Real.exp (-(1 + ε) * lg t))
    (Metric.ball_mem_nhds σ₀ hε)
    (Filter.Eventually.of_forall fun σ => (continuous_G σ).aestronglyMeasurable)
    ((integrable_expL hε).mono' (continuous_G σ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => bound_G hε (hball σ₀ (Metric.mem_ball_self hε)) t))
    (continuous_G' σ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t σ hσ => bound_G' hε (hball σ hσ) t)
    ((integrable_expL hε).const_mul _)
    (Filter.Eventually.of_forall fun t σ _ => hasDerivAt_G σ t)
  exact key.2.differentiableAt.differentiableWithinAt

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroZero
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

lemma ofReal_add_I_ne_zero (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma norm_inv_ofReal_add_I_sq (t : ℝ) : ‖((t : ℂ) + I)⁻¹ ^ 2‖ = (1 + t ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma tendsto_inv_ofReal_add_I_atTop :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)⁻¹) Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)) Filter.atTop (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_abs_atTop_atTop
    have := Complex.abs_re_le_norm ((t : ℂ) + I)
    simpa using this
  exact Filter.Tendsto.comp Filter.tendsto_inv₀_cobounded hb

lemma tendsto_inv_ofReal_add_I_atBot :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)⁻¹) Filter.atBot (nhds 0) := by
  have hb : Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)) Filter.atBot (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_abs_atBot_atTop
    have := Complex.abs_re_le_norm ((t : ℂ) + I)
    simpa using this
  exact Filter.Tendsto.comp Filter.tendsto_inv₀_cobounded hb

lemma hasDerivAt_neg_inv_ofReal_add_I (t : ℝ) :
    HasDerivAt (fun s : ℝ => -((s : ℂ) + I)⁻¹) (((t : ℂ) + I)⁻¹ ^ 2) t := by
  have h1 : HasDerivAt (fun w : ℂ => w + I) 1 (t : ℂ) := (hasDerivAt_id _).add_const I
  have h2 := (h1.inv (ofReal_add_I_ne_zero t)).neg
  have h3 := h2.comp_ofReal
  convert h3 using 1
  · funext s
    simp
  · rw [inv_pow]
    field_simp

lemma integral_inv_ofReal_add_I_sq : ∫ t : ℝ, ((t : ℂ) + I)⁻¹ ^ 2 = 0 := by
  have hint : MeasureTheory.Integrable (fun t : ℝ => ((t : ℂ) + I)⁻¹ ^ 2) := by
    refine integrable_inv_one_add_sq.mono' ?_ ?_
    · exact (((continuous_ofReal.add continuous_const).inv₀ ofReal_add_I_ne_zero).pow 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => (norm_inv_ofReal_add_I_sq t).le)
  rw [MeasureTheory.integral_of_hasDerivAt_of_tendsto hasDerivAt_neg_inv_ofReal_add_I hint
    (by simpa using tendsto_inv_ofReal_add_I_atBot.neg)
    (by simpa using tendsto_inv_ofReal_add_I_atTop.neg)]
  simp

theorem cConst_zero : cConst 0 = 0 := by
  unfold cConst hTrans phi
  simp only [mul_zero, neg_zero, Complex.cpow_zero, mul_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, one_mul]
  exact integral_inv_ofReal_add_I_sq

end GlobalTheory.HeckeTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOnePrimeAssociate
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_prime_associate : ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [IsDomain B'] [IsNoetherianRing B']
    [IsIntegrallyClosed B'] [Algebra A' B'] (𝔭 : Ideal A'), (𝔭.map (algebraMap A' B')).IsPrime →
    (𝔭.map (algebraMap A' B')).height = 1 → ∀ c : B', c ≠ 0 →
    ∃ j : A', (∃ t ∉ 𝔭.map (algebraMap A' B'), c ∣ t * algebraMap A' B' j) ∧
      (∃ t ∉ 𝔭.map (algebraMap A' B'), algebraMap A' B' j ∣ t * c) := by
  first | (exact @GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one) | (exact GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one) | (intros; apply GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSetStatement
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_smooth_of_weak_derivative_closed_set : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) → (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) → (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B, (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) → (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) → ∀ f ∈ Θ, Sm ρ f := by
  first | exact @GlobalTheory.RealWeil.sm_of_weak_deriv_closed | exact GlobalTheory.RealWeil.sm_of_weak_deriv_closed | (intros; apply GlobalTheory.RealWeil.sm_of_weak_deriv_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormConstMulInnerStatement
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_const_mul_inner : ∀ (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ), (∀ h h', B h' h = starRingEnd ℂ (B h h')) →
    (∀ h, 0 ≤ (B h h).re) →
    (∀ f f' g g' : Sch (Fin n), (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' = (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  first | exact @GlobalTheory.hermitian_form_eq_smul_l2 | exact GlobalTheory.hermitian_form_eq_smul_l2 | (intros; apply GlobalTheory.hermitian_form_eq_smul_l2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtSpecProdSelfOfBasicOpenPreimageEqStatement
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O → h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) → h = h' := by
  first | exact @GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | exact GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | (intros; apply GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen <;> assumption)
end


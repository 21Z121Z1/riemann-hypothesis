import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarMod
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirst
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchange

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQOfIntegralQuot
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem hasQ_periodic {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N) (h : HasQ N f a) (τ : ℍ) :
    f ((N : ℝ) +ᵥ τ) = f τ := by
  have h1 := hasQ_vadd N f a (N : ℝ) h
  have hc : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N)) = a := by
    funext n
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : 2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; field_simp
    rw [this, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [hc] at h1
  exact congrFun (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique.2 N _ _ a h1 h) τ

theorem hasQ_of_integral_quot : ∀ (N n : ℕ) (A D : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N →
    (∃ a, HasQ N A a) → (∃ d, HasQ N D d) → (∀ j, ∃ c, HasQ N (s j) c) → D ≠ 0 →
    (∀ τ, A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) = 0) →
    ∃ (h : ℍ → ℂ) (b : ℕ → ℂ), HasQ N h b ∧ ∀ τ, A τ = h τ * D τ := by
  intro N n A D s hN ⟨a, hA⟩ ⟨d, hD⟩ hs hD0 heq
  choose c hc using hs
  obtain ⟨hAm, -⟩ := GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N A a hN hA
  obtain ⟨hDm, -⟩ := GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N D d hN hD
  have hsm : ∀ j, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s j) ∧ UpperHalfPlane.IsBoundedAtImInfty (s j) :=
    fun j => GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N (s j) (c j) hN (hc j)
  have hUo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, D τ ≠ 0 := by
    by_contra hc'
    push_neg at hc'
    exact hD0 (funext hc')
  have hofc : ∀ z : ℂ, 0 < z.im → ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  obtain ⟨h₀, hh₀d, hh₀A, hh₀p⟩ := GlobalTheory.T.exists_differentiableOn_quotient_of_integral {z : ℂ | 0 < z.im} n
    (A ∘ UpperHalfPlane.ofComplex) (D ∘ UpperHalfPlane.ofComplex)
    (fun j => s j ∘ UpperHalfPlane.ofComplex) hUo hUc (UpperHalfPlane.mdifferentiable_iff.1 hAm)
    (UpperHalfPlane.mdifferentiable_iff.1 hDm) (fun j => UpperHalfPlane.mdifferentiable_iff.1 (hsm j).1)
    ⟨(τ₀ : ℂ), τ₀.im_pos, by simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hτ₀⟩
    (fun z _ => heq _)
  set h : ℍ → ℂ := fun τ => h₀ τ with hdef
  have hAh : ∀ τ, A τ = h τ * D τ := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀A (τ : ℂ) τ.im_pos
  have hhp : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0 := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀p (τ : ℂ) τ.im_pos
  have hhm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    refine UpperHalfPlane.mdifferentiable_iff.2 (hh₀d.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, hofc z hz]
  have hhNm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => h ((N : ℝ) +ᵥ τ)) := by
    have hd : DifferentiableOn ℂ (fun z : ℂ => h₀ (((N : ℝ) : ℂ) + z)) {z : ℂ | 0 < z.im} :=
      hh₀d.comp ((differentiableOn_const _).add differentiableOn_id) fun z hz => by
        show 0 < (((N : ℝ) : ℂ) + z).im
        simpa using hz
    refine UpperHalfPlane.mdifferentiable_iff.2 (hd.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, UpperHalfPlane.coe_vadd, hofc z hz]
  have hper : ∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ := by
    have hz : ∀ τ, (fun τ => h ((N : ℝ) +ᵥ τ) - h τ) τ * D τ = 0 := fun τ => by
      have e1 := hAh ((N : ℝ) +ᵥ τ)
      rw [hasQ_periodic hN hA, hasQ_periodic hN hD, hAh τ] at e1
      simp only
      linear_combination -e1
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ D (hhNm.sub hhm) hDm hz with h0 | h0
    · exact fun τ => sub_eq_zero.1 (congrFun h0 τ)
    · exact absurd h0 hD0
  have hbd : UpperHalfPlane.IsBoundedAtImInfty h := by
    have hS : (fun τ => ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
      have hb : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (fun τ => ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := fun j _ => by
        have : (s j) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := (hsm j).2
        exact this.norm_left
      exact (Asymptotics.IsBigO.sum hb).congr_left fun τ => Finset.sum_apply _ _ _
    have h1 : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) :=
      ((Asymptotics.isBigO_refl (1 : ℍ → ℝ) _).add hS).congr_left fun τ => rfl
    have h2 : h =O[UpperHalfPlane.atImInfty] (fun τ => 1 + ∑ j, ‖s j τ‖) := by
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_)
      have hb := GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff n (fun j => s j τ) (h τ) (hhp τ)
      have hnn : (0 : ℝ) ≤ 1 + ∑ j, ‖s j τ‖ := by positivity
      rw [Real.norm_of_nonneg hnn, one_mul]
      exact hb
    exact h2.trans h1
  obtain ⟨b, hb⟩ := GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic N h hN hhm hper hbd
  exact ⟨h, b, hb, hAh⟩

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTCoeffFormulaCommDistinctPrimes
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma isDia_mul_of_isDia {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : IsDia N l d σ)
    (hτ : IsDia N l e τ) : IsDia N l (d * e) (σ * τ) := by
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h3, h4⟩ := hτ
  have h1' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) h1
    simpa using this
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h3]; ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1', h2, h4]; ring

lemma heckeT_congr_dia {N l q : ℕ} {k : ℤ} {σ τ : SL(2, ℤ)} (hN : 0 < N)
    (hσ : IsDia N l q σ) (hτ : IsDia N l q τ) (f : ModularForm (lev N l) k) :
    heckeT k q σ ⇑f = heckeT k q τ ⇑f := by
  have := GlobalTheory.T.diamondOperatorOfMatrix_congr N l k q σ τ hN hσ hτ f
  unfold dia at this
  unfold heckeT
  rw [this]

lemma heckeT_coeff_formula_comm_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (kq kr : ℂ)
    (a b c e : ℕ → ℂ) (n : ℕ) :
    a (r * (q * n)) + kr * (if r ∣ q * n then b (q * n / r) else 0)
      + kq * (if q ∣ n then c (r * (n / q)) + kr * (if r ∣ n / q then e (n / q / r) else 0)
        else 0)
    = a (q * (r * n)) + kq * (if q ∣ r * n then c (r * n / q) else 0)
      + kr * (if r ∣ n then b (q * (n / r)) + kq * (if q ∣ n / r then e (n / r / q) else 0)
        else 0) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hqr
  have i1 : r ∣ q * n ↔ r ∣ n := hcop.symm.dvd_mul_left
  have i2 : q ∣ r * n ↔ q ∣ n := hcop.dvd_mul_left
  have ha : r * (q * n) = q * (r * n) := by ring
  simp only [ha, i1, i2]
  by_cases hqn : q ∣ n <;> by_cases hrn : r ∣ n
  · have i3 : r ∣ n / q := by
      obtain ⟨m, rfl⟩ := hqn
      rw [Nat.mul_div_cancel_left _ hq.pos]
      exact (hcop.symm.dvd_mul_left).1 hrn
    have i4 : q ∣ n / r := by
      obtain ⟨m, rfl⟩ := hrn
      rw [Nat.mul_div_cancel_left _ hr.pos]
      exact (hcop.dvd_mul_left).1 hqn
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    have d3 : n / r / q = n / q / r := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    simp only [hqn, hrn, i3, i4, if_true, d1, d2, d3]
    ring
  · have i3 : ¬ r ∣ n / q := by
      intro h
      exact hrn (h.trans (Nat.div_dvd_of_dvd hqn))
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    simp only [hqn, hrn, i3, if_true, if_false, d2]
    ring
  · have i4 : ¬ q ∣ n / r := by
      intro h
      exact hqn (h.trans (Nat.div_dvd_of_dvd hrn))
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    simp only [hqn, hrn, i4, if_true, if_false, d1]
    ring
  · simp only [hqn, hrn, if_false]
    ring

theorem heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ τ : SL(2, ℤ)), 0 < N → q.Prime → r.Prime →
    ¬ q ∣ N * l → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l r τ →
    ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.heckeT k r τ ⇑f) = GlobalTheory.Hk.heckeT k r τ (GlobalTheory.Hk.heckeT k q σ ⇑f) := by
  intro N l q r k σ τ hN hq hr hqN hrN hσ hτ f
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨g, hg⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k τ hN hq hqN hτ f
    rw [heckeT_congr_dia hN hσ hτ f, ← hg, heckeT_congr_dia hN hσ hτ g]
  · obtain ⟨gr, hgr⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l r k τ hN hr hrN hτ f
    obtain ⟨gq, hgq⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN hq hqN hσ f
    obtain ⟨h1, hh1⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN hq hqN hσ gr
    obtain ⟨h2, hh2⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l r k τ hN hr hrN hτ gq
    obtain ⟨fσ, hfσ⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k q σ hN hσ f
    obtain ⟨fτ, hfτ⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k r τ hN hτ f
    have dσ : dia k σ ⇑gr = heckeT k r τ ⇑fσ := by
      rw [hgr, hfσ, GlobalTheory.T.hecke_operator_commutes_diamond N l r k q τ σ hN hr hrN hτ hσ f]
    have dτ : dia k τ ⇑gq = heckeT k q σ ⇑fτ := by
      rw [hgq, hfτ, GlobalTheory.T.hecke_operator_commutes_diamond N l q k r σ τ hN hq hqN hσ hτ f]
    have dd : dia k τ ⇑fσ = dia k σ ⇑fτ := by
      have h' : IsDia N l ((r : ℤ) * q) (σ * τ) := by
        rw [mul_comm]; exact isDia_mul_of_isDia hσ hτ
      rw [hfσ, hfτ, GlobalTheory.T.diamondOperatorOfMatrix_comp_mul N l k q r σ τ (σ * τ) hN hσ hτ (isDia_mul_of_isDia hσ hτ) f,
        GlobalTheory.T.diamondOperatorOfMatrix_comp_mul N l k r q τ σ (σ * τ) hN hτ hσ h' f]
    have key : h1 = h2 := by
      apply GlobalTheory.T.modularForm_gamma1InterGamma0_ext_qExpansionCoeff N l k hN
      intro n
      rw [hh1, hh2, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ gr, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ gq,
        dσ, dτ, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ fσ, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ fτ,
        hgr, hgq, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ f, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ f,
        dd, hfσ, hfτ]
      exact heckeT_coeff_formula_comm_distinct_primes hq hr hqr _ _ _ _ _ _ n
    rw [← hgr, ← hgq, ← hh1, ← hh2, key]

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOver
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section
namespace GlobalTheory.FN

theorem gact_one_bij (N : ℕ) : ActBij (gact N 1) := by
  intro γ
  simp only [gact, one_mul, inv_one, mul_one]
  exact (Group.mulRight_bijective _)

theorem redGL_one (N : ℕ) : redGL N 1 = 1 := by
  ext i j; simp [redGL]

theorem rel_div (w n : ℕ) (D x J : ℂ) (hD : D ≠ 0) (s : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (hs : ∀ j : Fin n, s j = D ^ (w * (n - j)) * (P j).eval J)
    (h : (D ^ w * x) ^ n + ∑ j, s j * (D ^ w * x) ^ (j : ℕ) = 0) :
    x ^ n + ∑ j, (P j).eval J * x ^ (j : ℕ) = 0 := by
  have hD' : D ^ (w * n) ≠ 0 := pow_ne_zero _ hD
  refine (mul_eq_zero.mp ?_).resolve_left hD'
  rw [← h, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_pow, pow_mul]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) ≤ n := j.2.le
    have e : w * n = w * (n - j) + w * j := by rw [← mul_add, Nat.sub_add_cancel hj]
    rw [hs, e, mul_pow, pow_add, ← pow_mul]
    ring

theorem integral_over_jT : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → ∃ (n : ℕ) (c : Fin n → Polynomial ℂ), (∀ i k, (c i).coeff k ∈ E) ∧ ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0 := by
  intro E f ⟨N, w, hN, hinv, hq⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  have hslash : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ = fun τ => DD τ ^ w * f (γ • τ) :=
    fun γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w f γ
  have hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma N, (fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ = (fun τ => DD τ ^ w * f τ) := by
    intro γ hγ
    rw [hslash]; funext τ; rw [hinv γ hγ τ]
  obtain ⟨F, hFam, hFγ, hF0⟩ := GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level N ((12 * w : ℕ) : ℤ) _ hΓ
  have hQ : ∀ α, QAll (· ∈ E) N (F α) := by
    intro α
    rcases hF0 α with ⟨γ, rfl⟩ | h0
    · rw [hFγ, hslash]; exact hq γ
    · rw [h0]
      refine ⟨fun _ => 0, fun τ => ?_, fun _ => E.zero_mem⟩
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have h1 : F 1 = fun τ => DD τ ^ w * f τ := by
    rw [← redGL_one N, hFγ]; exact SlashAction.slash_one _ _
  obtain ⟨s, hs, hpoly⟩ := GlobalTheory.T.permutedModularFamily_monic_poly_coeff_invariant (GL (Fin 2) (ZMod N)) (gact N 1) (12 * w) N F E hN
    (gact_one_bij N) hFam hQ
  have key := hpoly 1
  rw [h1] at key
  clear hpoly hFam hF0 hFγ hQ h1 hslash hΓ
  revert s
  generalize Fintype.card (GL (Fin 2) (ZMod N)) = n
  intro s hs key
  have hP : ∀ j : Fin n, ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ E) ∧
      ∀ τ, s j τ = DD τ ^ (w * (n - j)) * P.eval (jT τ) := by
    intro j
    refine GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT E N (w * (n - j)) (s j) hN (fun γ => ?_) (hs j).2
    have := (hs j).1 γ
    convert this using 3
    push_cast; ring
  choose P hPc hPe using hP
  exact ⟨n, P, hPc, fun τ => rel_div w n (DD τ) (f τ) (jT τ) (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
    (fun j => s j τ) P (fun j => hPe j τ) (key τ)⟩

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowCalculus
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue

section Calc

variable {Ω : Type} [Field Ω]

def DvA (A : ValuationSubring Ω) (l n : ℕ) (D : HahnSeries ℚ Ω) : Prop :=
  ∀ r, ∃ z ∈ A, D.coeff r = (l : Ω) ^ n * z

theorem coeffA_mul (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω) (hP : ∀ r, P.coeff r ∈ A)
    (hQ : ∀ r, Q.coeff r ∈ A) (r : ℚ) : (P * Q).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact Finset.sum_induction _ (fun x => x ∈ A) (fun x y hx hy => add_mem hx hy) (zero_mem A)
    (fun ij _ => mul_mem (hP _) (hQ _))

theorem dvA_mul (A : ValuationSubring Ω) (l n : ℕ) (P D : HahnSeries ℚ Ω) (hP : ∀ r, P.coeff r ∈ A)
    (hD : DvA A l n D) : DvA A l n (P * D) := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = (l : Ω) ^ n * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, add_mem hz hw, by ring⟩
  · exact ⟨0, (zero_mem A), by ring⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hD ij.2
    exact ⟨P.coeff ij.1 * z, mul_mem (hP _) hz, by rw [e]; ring⟩

theorem dvA_add (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω) (hD : DvA A l n D)
    (hE : DvA A l n E) : DvA A l n (D + E) := by
  intro r
  obtain ⟨z, hz, e⟩ := hD r
  obtain ⟨w, hw, e'⟩ := hE r
  exact ⟨z + w, add_mem hz hw, by rw [HahnSeries.coeff_add, e, e']; ring⟩

theorem cgA_iff (A : ValuationSubring Ω) (l n : ℕ) (P Q : HahnSeries ℚ Ω) :
    (∀ r, CgA A l n (P.coeff r) (Q.coeff r)) ↔ DvA A l n (P - Q) := by
  simp only [CgA, DvA, HahnSeries.coeff_sub]

end Calc

theorem isDl_calc : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f g : X.K) (φ ψ : HahnSeries ℚ Ω), (IsDl X A l n s f φ → IsDl X A l n s g ψ → IsDl X A l n s (f * g) (φ + ψ)) ∧ (IsDl X A l n s f φ → IsDl X A l n s f⁻¹ (-φ)) ∧ (IsDl X A l n s f φ → (∀ r, ψ.coeff r ∈ A) → (∀ r, CgA A l n (φ.coeff r) (ψ.coeff r)) → IsDl X A l n s f ψ) ∧ (∀ κ : Ω, κ ≠ 0 → IsDl X A l n s (algebraMap Ω X.K κ) 0) ∧ (∀ n', n' ≤ n → IsDl X A l n s f φ → IsDl X A l n' s f φ) := by
  intro Ω _ _ _ ε X _ l _ A _ n s f g φ ψ
  have lei := fun P Q => (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (Ω := Ω) s P Q).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ ⟨hψ, a2, b2, κ2, hκ2, hgb, hpa2, hpb2, hc2⟩
    refine ⟨fun r => by rw [HahnSeries.coeff_add]; exact add_mem (hφ r) (hψ r),
      a * a2, b * b2, κ * κ2, mul_ne_zero hκ hκ2, ?_, ?_, ?_, ?_⟩
    · calc f * g * (b * b2) = (f * b) * (g * b2) := by ring
        _ = _ := by rw [hfb, hgb, map_mul]; ring
    · rw [map_mul]; exact GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hpa hpa2
    · rw [map_mul]; exact GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hpb hpb2
    · rw [cgA_iff] at hc hc2 ⊢
      rw [map_mul, map_mul, lei, lei]
      have key : (φ + ψ) * (X.exp a * X.exp a2) * (X.exp b * X.exp b2) -
          ((theta s (X.exp a) * X.exp a2 + X.exp a * theta s (X.exp a2)) * (X.exp b * X.exp b2) -
            X.exp a * X.exp a2 * (theta s (X.exp b) * X.exp b2 + X.exp b * theta s (X.exp b2))) =
          (X.exp a2 * X.exp b2) * (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) +
          (X.exp a * X.exp b) * (ψ * X.exp a2 * X.exp b2 - (theta s (X.exp a2) * X.exp b2 - X.exp a2 * theta s (X.exp b2))) := by
        ring
      rw [key]
      exact dvA_add A l n _ _ (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa2.1 hpb2.1) hc)
        (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa.1 hpb.1) hc2)
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩
    have hf : f ≠ 0 := by
      rintro rfl
      have ha : a = 0 := by
        have : algebraMap Ω X.K κ * a = 0 := by rw [← hfb, zero_mul]
        rcases mul_eq_zero.mp this with h | h
        · exact absurd ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).mp h) hκ
        · exact h
      obtain ⟨r, hr, _⟩ := hpa.2
      exact hr (by rw [ha, map_zero, HahnSeries.coeff_zero])
    refine ⟨fun r => by rw [HahnSeries.coeff_neg]; exact neg_mem (hφ r), b, a, κ⁻¹, inv_ne_zero hκ, ?_, hpb, hpa, ?_⟩
    · have hk : algebraMap Ω X.K κ ≠ 0 := (map_ne_zero _).mpr hκ
      rw [map_inv₀]
      field_simp
      rw [mul_comm, hfb]
    · rw [cgA_iff] at hc ⊢
      have key : -φ * X.exp b * X.exp a - (theta s (X.exp b) * X.exp a - X.exp b * theta s (X.exp a)) =
          -(φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) := by ring
      rw [key]
      intro r
      obtain ⟨z, hz, e⟩ := hc r
      exact ⟨-z, neg_mem hz, by rw [HahnSeries.coeff_neg, e]; ring⟩
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ hψ hcg
    refine ⟨hψ, a, b, κ, hκ, hfb, hpa, hpb, ?_⟩
    rw [cgA_iff] at hc hcg ⊢
    have key : ψ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)) =
        (-(X.exp a * X.exp b)) * (φ - ψ) + (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) := by
      ring
    rw [key]
    refine dvA_add A l n _ _ (dvA_mul A l n _ _ ?_ hcg) hc
    intro r
    rw [HahnSeries.coeff_neg]
    exact neg_mem (coeffA_mul A _ _ hpa.1 hpb.1 r)
  · intro κ hκ
    have hp1 : Prim A (X.exp 1) := by
      rw [map_one]
      refine ⟨fun r => ?_, 0, ?_, ?_⟩
      · rw [HahnSeries.coeff_one]; split_ifs <;> simp
      · simp [HahnSeries.coeff_one]
      · simp [HahnSeries.coeff_one]
    refine ⟨fun r => by simp, 1, 1, κ, hκ, by simp, hp1, hp1, fun r => ⟨0, (zero_mem A), ?_⟩⟩
    simp
  · rintro n' hn ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩
    refine ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, fun r => ?_⟩
    obtain ⟨z, hz, e⟩ := hc r
    refine ⟨(l : Ω) ^ (n - n') * z, mul_mem (pow_mem (natCast_mem A l) _) hz, ?_⟩
    rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hn]

end GlobalTheory.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem jT_invariant (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ :=
  ReciprocityTheory.ChartRestriction.L1.jT_smul γ τ

theorem DD_mul_jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD τ * jT (γ • τ) = E₄ τ ^ 3 := by
  rw [jT_invariant, jT, ReciprocityTheory.ChartRestriction.L1.AA, mul_div_cancel₀ _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)]

theorem jT_level_one : ∀ E : Subring ℂ, Lv E 1 1 jT ∧ ∀ (γ : SL(2, ℤ)) (τ : ℍ), jT (γ • τ) = jT τ := by
  intro E
  refine ⟨⟨fun γ _ τ => jT_invariant γ τ, fun γ => ?_⟩, jT_invariant⟩
  have hE4 : QAll (· ∈ E) 1 ⇑E₄ := ((eis_q 1 one_pos _ (Or.inl rfl)).2.1) E
  have h3 : QAll (· ∈ E) 1 fun τ => E₄ τ ^ 3 := (QAllSubring.ring_closed E 1 one_pos).2.2.2.2.1 _ 3 hE4
  have hfun : (fun τ => DD τ ^ 1 * jT (γ • τ)) = fun τ => E₄ τ ^ 3 := by
    funext τ; rw [pow_one, DD_mul_jT_smul]
  rw [hfun]; exact h3

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarModStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jTranslates_level_and_scalar_mod : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ m : ℕ, 0 < m → (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), Lev X m (X.sl (toGQ g) X.jK)) ∧ ∀ γ : SL(2, ℤ), (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), X.sl (ofSL γ) (X.sl (toGQ g) X.jK) = X.sl (toGQ g) X.jK) → (en γ 0 1 : ZMod m) = 0 ∧ (en γ 1 0 : ZMod m) = 0 ∧ (en γ 0 0 : ZMod m) = en γ 1 1 := by
  first | exact @GlobalTheory.KZ.ES.Scal.lev_and_scalar | exact GlobalTheory.KZ.ES.Scal.lev_and_scalar | (intros; apply GlobalTheory.KZ.ES.Scal.lev_and_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationTrivialEqZeroStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerPotentialRelation_trivial_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ b F, Rel X l b F → F ∈ Triv ℤ_[l] w Γ → b = 0 := by
  first | exact @GlobalTheory.KZ.H3.rel_triv_eq_zero | exact GlobalTheory.KZ.H3.rel_triv_eq_zero | (intros; apply GlobalTheory.KZ.H3.rel_triv_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankGeOfGenericFreeRowsFirstStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatum_idempotent_rank_ge_of_generic_free_rows_first : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, L.sharp = true → L.s = 0 → (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  first | exact @GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero | exact GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero | (intros; apply GlobalTheory.BadShare.rk_ge_of_isGeneric_of_s_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumIdempotentRankLeRootExchangeStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatum_idempotent_rank_le_root_exchange : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = true → L'.sharp = true → L.k = L'.k → L.s = L'.s + 1 → rk ρ L'.e ≤ rk ρ L.e := by
  first | exact @GlobalTheory.BadShare.RxStep.rk_le_step | exact GlobalTheory.BadShare.RxStep.rk_le_step | (intros; apply GlobalTheory.BadShare.RxStep.rk_le_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonalStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp (fun i => ψ (Fin.castAdd t i)), ∀ b ∈ grp (fun i => ψ (Fin.natAdd r i)), theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) = theta (fun i => ψ (Fin.castAdd t i)) a * theta (fun i => ψ (Fin.natAdd r i)) b := by
  first | exact @GlobalTheory.PsType.theta_emb₂_std | exact GlobalTheory.PsType.theta_emb₂_std | (intros; apply GlobalTheory.PsType.theta_emb₂_std <;> assumption)
end


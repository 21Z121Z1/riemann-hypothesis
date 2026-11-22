import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0020
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0046
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardSpacedDetectedLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZetaZeroDetect
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConstStatement
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.brunTitchmarsh_exists_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by
  first | exact @GlobalTheory.Lin.brun_titchmarsh_const | exact GlobalTheory.Lin.brun_titchmarsh_const | (intros; apply GlobalTheory.Lin.brun_titchmarsh_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaAndWindowCount
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZeroBounds

theorem explicit_formula_and_window_count :
    (∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm7 D C) ∧ ∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm11 D C := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C', hC', h'⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  exact ⟨⟨C, hC, fun _ => h⟩, ⟨C', hC', fun _ => h'⟩⟩

end GlobalTheory.ZeroBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralPowerExpansion
section
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.Proof.IntegralPowerExpansion

open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram depthSub)

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  · intro h
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer a h
    exact ⟨n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem val_q {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) :
    P.valuation E (qOf P : E) = WithZero.exp (-1) := by
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  rw [e, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 : P.intValuation (qOf P : 𝓞 E) < 1 :=
    (P.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have h2 : ¬ P.intValuation (qOf P : 𝓞 E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact hP.2
  have hx : P.intValuation (qOf P : 𝓞 E) ≠ 0 := by
    intro h0
    exact h2 (h0 ▸ zero_le)
  rw [← WithZero.exp_log hx] at h1 h2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  rw [WithZero.exp_le_exp] at h2
  congr 1
  omega

theorem q_ne_zero {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) : (qOf P : E) ≠ 0 :=
  Nat.cast_ne_zero.2 hP.1.ne_zero

theorem exists_int_add_q_mul {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) {u : E} (hu : IntAt P u) :
    ∃ (k : ℤ) (u' : E), IntAt P u' ∧ u = k + (qOf P : E) * u' := by
  obtain ⟨r, s, hs, h⟩ := hu
  haveI : Fact (qOf P).Prime := ⟨hP.1⟩
  have hc : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
    rw [qOf, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1
    (mem_zmultiples_of_prime_card (g' := Ideal.Quotient.mk P.asIdeal r) hc (mk_ne_zero hs))
  have hm : r - k * s ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_intCast, ← hk, zsmul_eq_mul, sub_self]
  have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hs
  have h2 : algebraMap (𝓞 E) E s * (u - k) = algebraMap (𝓞 E) E (r - k * s) := by
    rw [map_sub, map_mul, map_intCast, ← h]; ring
  have h3 : P.valuation E (u - k) < 1 := by
    have := congrArg (P.valuation E) h2
    rw [map_mul, h1, one_mul, HeightOneSpectrum.valuation_of_algebraMap] at this
    rw [this]
    exact (P.intValuation_lt_one_iff_mem _).2 hm
  have hq := q_ne_zero hP
  refine ⟨k, (u - k) / qOf P, ?_, by field_simp; ring⟩
  rw [intAt_iff_val, map_div₀, val_q hP]
  exact div_le_one_of_le₀ (le_exp_neg_one_of_lt_one h3) zero_le

theorem exists_int_add_q_pow_mul {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) (j : ℕ) {u : E}
    (hu : IntAt P u) : ∃ (k : ℤ) (u' : E), IntAt P u' ∧ u = k + (qOf P : E) ^ j * u' := by
  induction j with
  | zero => exact ⟨0, u, hu, by simp⟩
  | succ j ih =>
    obtain ⟨k, u', hu', e⟩ := ih
    obtain ⟨k', u'', hu'', e'⟩ := exists_int_add_q_mul hP hu'
    refine ⟨k + (qOf P : ℤ) ^ j * k', u'', hu'', ?_⟩
    rw [e, e']
    push_cast
    ring

end GlobalTheory.Proof.IntegralPowerExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsRowOperatorStableDualWeylAndGLSubmodules
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rename_rowPerm_eq_rowAct (R : Type) [CommRing R] (r n : ℕ) (σ : Equiv.Perm (Fin r)) :
    (rename (fun v : Fin r × Fin n => (σ v.1, v.2)) : MvPolynomial (Fin r × Fin n) R →ₐ[R] _) =
      rowAct R (n := n) (Matrix.of fun a b : Fin r => if b = σ a then (1 : R) else 0) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rowAct]

theorem good_nablaSq (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) : Good (nablaSq k N lam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b f hf
    rw [(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).2.1 a b f]
    exact rowDivStable k N N _ a b 1 f hf
  · intro μ f hf
    exact dualWeylRowGraded k N N _ μ f hf
  · intro σ f hf
    rw [rename_rowPerm_eq_rowAct]
    exact dualWeylRowStable k N N _ _ f hf

theorem good_of_isGLSubmodule (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : GlobalTheory.Published.IsGLSubmodule k N lam M) : Good M := by
  have hw : ∀ μ : Fin N → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW N N) μ f ∈ M :=
    GlobalTheory.T.weightedHomogeneousComponent_mem_of_GLSchemeSubmodule k N lam M hM
  refine ⟨?_, hw, GlobalTheory.T.GLSchemeSubmodule_stable_under_row_perm k N lam M hM⟩
  intro a b f hf
  by_cases hab : a = b
  · subst hab
    classical
    have hsum := sum_weightedHomogeneousComponent (rowW N N) f
    rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)] at hsum
    rw [← hsum, map_sum]
    refine Submodule.sum_mem _ fun μ _ => ?_
    rw [((GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ _ (weightedHomogeneousComponent_isWeightedHomogeneous μ f)).1 a)]
    exact Submodule.smul_mem _ _ (hw μ f hf)
  · exact GlobalTheory.T.rowPolarization_mem_of_isGLSchemeSubmodule k N lam M hM a b hab f hf

theorem good_nablaSq_and_submodules : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N), Good (nablaSq k N lam) ∧
    ∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), GlobalTheory.Published.IsGLSubmodule k N lam M → Good M :=
  fun k _ N lam => ⟨good_nablaSq k N lam, good_of_isGLSubmodule k N lam⟩

end GlobalTheory.Alc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NcardUnitCellsDirichletLZerosNearOneLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroCells

lemma one_le_abs_sub_of_floor {x y : ℝ} (hne : ⌊x⌋ ≠ ⌊y⌋) (hpar : ⌊x⌋ % 2 = ⌊y⌋ % 2) :
    1 ≤ |x - y| := by
  obtain ⟨k, hk⟩ := Int.ModEq.dvd hpar
  have hx1 := Int.floor_le x
  have hx2 := Int.lt_floor_add_one x
  have hy1 := Int.floor_le y
  have hy2 := Int.lt_floor_add_one y
  rcases lt_or_gt_of_ne hne with h | h
  · have h2 : ⌊x⌋ + 2 ≤ ⌊y⌋ := by omega
    have h2' : (⌊x⌋ : ℝ) + 2 ≤ ⌊y⌋ := by exact_mod_cast h2
    rw [le_abs]
    right
    linarith
  · have h2 : ⌊y⌋ + 2 ≤ ⌊x⌋ := by omega
    have h2' : (⌊y⌋ : ℝ) + 2 ≤ ⌊x⌋ := by exact_mod_cast h2
    rw [le_abs]
    left
    linarith

lemma ne_one_of_primitive {N : ℕ} (hN : N ≠ 0) {χ : DirichletCharacter ℂ (N + 1)}
    (h : χ.IsPrimitive) : χ ≠ 1 := by
  rintro rfl
  rw [isPrimitive_def, conductor_one] at h
  omega

private theorem exists_subset_injOn_card_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Nonempty α] (U : Finset α) (f : α → β) :
    ∃ R ⊆ U, (U.image f).card = R.card ∧ ∀ r ∈ R, ∀ r' ∈ R, f r = f r' → r = r' := by
  have hback : ∀ r ∈ (U.image f).image (Function.invFunOn f ↑U),
      Function.invFunOn f ↑U (f r) = r := by
    intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    rw [Function.invFunOn_eq (f := f) (s := ↑U) ⟨p, hp, rfl⟩]
  refine ⟨(U.image f).image (Function.invFunOn f ↑U), ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    exact Function.invFunOn_mem ⟨p, hp, rfl⟩
  · refine (Finset.card_image_of_injOn ?_).symm
    intro c hc c' hc' h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc')
    calc f p = f (Function.invFunOn f ↑U (f p)) :=
          (Function.invFunOn_eq (f := f) (s := ↑U) ⟨p, hp, rfl⟩).symm
      _ = f (Function.invFunOn f ↑U (f p')) := by rw [h]
      _ = f p' := Function.invFunOn_eq (f := f) (s := ↑U) ⟨p', hp', rfl⟩
  · intro r hr r' hr' h
    rw [← hback r hr, ← hback r' hr', h]

theorem ncard_cells_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((((fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => (⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ)) '' (T : Set (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))).ncard : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 8) := by
  classical
  obtain ⟨Q₁, hQ₁⟩ := GlobalTheory.ZeroDetect.zero_detect
  obtain ⟨Q₂, hQ₂⟩ := GlobalTheory.ZeroDetect.zeta_zero_detect
  obtain ⟨C₁, hC₁, hsp⟩ := GlobalTheory.SpacedDetected.card_spaced_detected_le
  refine ⟨(2 * C₁ + 5) * ((Q₁ + Q₂ + 2 : ℕ) : ℝ), by positivity, ?_⟩
  intro Q hQ T hT
  set Qn : ℕ := max (max Q₁ Q₂) ⌈Q⌉₊ with hQn_def
  have hceil3 : 2 < ⌈Q⌉₊ := Nat.lt_ceil.2 (by push_cast; linarith)
  have hQn2 : 2 ≤ Qn := le_trans (by omega : 2 ≤ ⌈Q⌉₊) (le_max_right _ _)
  have hQle : Q ≤ (Qn : ℝ) := (Nat.le_ceil Q).trans (by exact_mod_cast le_max_right _ _)
  have hQn1 : (1 : ℝ) ≤ Qn := by exact_mod_cast (by omega : 1 ≤ Qn)
  have hQnpos : (0 : ℝ) < Qn := by linarith
  have hQnle : (Qn : ℝ) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q := by
    have h1 : Qn ≤ Q₁ + Q₂ + ⌈Q⌉₊ := max_le (max_le (by omega) (by omega)) (by omega)
    have h2 : (⌈Q⌉₊ : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by linarith)
    have h1' : (Qn : ℝ) ≤ Q₁ + Q₂ + ⌈Q⌉₊ := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ Q₁ := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ Q₂ := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hpow : (Qn : ℝ) ^ ((1 : ℝ) / 8) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8) := by
    have hB : (1 : ℝ) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q₁ + Q₂ + 2)
    calc (Qn : ℝ) ^ ((1 : ℝ) / 8) ≤ (((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q) ^ ((1 : ℝ) / 8) :=
          Real.rpow_le_rpow hQnpos.le hQnle (by norm_num)
      _ = ((Q₁ + Q₂ + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) * Q ^ ((1 : ℝ) / 8) :=
          Real.mul_rpow (by positivity) (by linarith)
      _ ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8) := by
          gcongr
          calc ((Q₁ + Q₂ + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
            _ = _ := Real.rpow_one _
  have hA : ∀ p ∈ T, ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)) →
      p.1 + 1 ≤ Qn ∧ p.2.1.IsPrimitive ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ p.2.2.re ≤ 1 ∧
        |p.2.2.im| ≤ Qn ∧ (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Qn ^ 3) (Qn ^ 6),
          ((∑ d ∈ n.divisors.filter (fun d => d ≤ Qn ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
            p.2.1 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-p.2.2)‖ := by
    rintro ⟨N, χ, ρ⟩ hp hns
    obtain ⟨hlev, hprim, hL, hre, him⟩ : ((N + 1 : ℕ) : ℝ) ≤ Q ∧ χ.IsPrimitive ∧
        LFunction χ ρ = 0 ∧ 1 - 1 / 400 ≤ ρ.re ∧ |ρ.im| ≤ Q := hT _ hp
    have hlevN : N + 1 ≤ Qn := by
      have : ((N + 1 : ℕ) : ℝ) ≤ (Qn : ℝ) := hlev.trans hQle
      exact_mod_cast this
    have him' : |ρ.im| ≤ (Qn : ℝ) := him.trans hQle
    have hre1 : ρ.re ≤ 1 := by
      by_contra hgt
      rw [not_le] at hgt
      have hne : ρ ≠ 1 := by
        intro h
        rw [h, Complex.one_re] at hgt
        exact lt_irrefl _ hgt
      exact LFunction_ne_zero_of_one_le_re χ (.inr hne) hgt.le hL
    refine ⟨hlevN, hprim, hre, hre1, him', ?_⟩
    by_cases hN : N = 0
    · subst hN
      have hpos : 0 < (Qn : ℝ) ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hQnpos _
      have hbig : (Qn : ℝ) ^ ((1 : ℝ) / 20) ≤ |ρ.im| := by
        by_contra h
        rw [not_le] at h
        exact hns ⟨rfl, h⟩
      have hne1 : ρ ≠ 1 := by
        intro h
        rw [h, Complex.one_im, abs_zero] at hbig
        linarith
      have hrelt : ρ.re < 1 := by
        rcases lt_or_eq_of_le hre1 with h | h
        · exact h
        · exact absurd hL (LFunction_ne_zero_of_one_le_re χ (.inr hne1) h.ge)
      have hz : riemannZeta ρ = 0 := by
        have e : LFunction χ ρ = riemannZeta ρ := congrFun LFunction_modOne_eq ρ
        rw [← e]
        exact hL
      have key := hQ₂ Qn (le_trans (le_max_right _ _) (le_max_left _ _)) ρ hre hrelt hbig him' hz
      have : Subsingleton (ZMod (0 + 1)) := ZMod.subsingleton_iff.2 rfl
      have hχ : ∀ a : ZMod (0 + 1), χ a = 1 := fun a => by
        rw [Subsingleton.elim a 1, MulChar.map_one]
      show (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Qn ^ 3) (Qn ^ 6),
          ((∑ d ∈ n.divisors.filter (fun d => d ≤ Qn ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
            χ (n : ZMod (0 + 1)) * (n : ℂ) ^ (-ρ)‖
      simp only [hχ]
      exact key
    · exact hQ₁ Qn (le_trans (le_max_left _ _) (le_max_left _ _)) (N + 1) χ
        (ne_one_of_primitive hN hprim) hlevN ρ hre him' hL
  rw [← Finset.coe_image, Set.ncard_coe_finset]
  set f : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) → (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) :=
    fun p => ⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ with hf
  have : Nonempty (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) := ⟨⟨0, 1, 0⟩⟩
  have hcount : ∀ U ⊆ T, (∀ p ∈ U, ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20))) →
      (∀ p ∈ U, ∀ p' ∈ U, ⌊p.2.2.im⌋ % 2 = ⌊p'.2.2.im⌋ % 2) →
      ((U.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8) := by
    intro U hU hns hpar
    obtain ⟨R, hRU, hcard, hinj⟩ := exists_subset_injOn_card_image U f
    rw [hcard]
    refine hsp Qn hQn2 R ?_ ?_
    · intro p hp
      exact hA p (hU (hRU hp)) (hns p (hRU hp))
    · intro N χ ρ ρ' h1 h2 hne
      by_cases hfl : ⌊ρ.im⌋ = ⌊ρ'.im⌋
      · exfalso
        apply hne
        have e := hinj _ h1 _ h2 (by
          show (⟨N, χ, ⌊ρ.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) = ⟨N, χ, ⌊ρ'.im⌋⟩
          rw [hfl])
        exact congrArg (fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => p.2.2) e
      · exact one_le_abs_sub_of_floor hfl (hpar _ (hRU h1) _ (hRU h2))
  set Ts := T.filter (fun p => p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)) with hTs
  set Tb := T.filter (fun p => ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20))) with hTb
  set T0 := Tb.filter (fun p => ⌊p.2.2.im⌋ % 2 = 0) with hT0
  set T1 := Tb.filter (fun p => ¬ ⌊p.2.2.im⌋ % 2 = 0) with hT1
  have hsub : T.image f ⊆ Ts.image f ∪ (T0.image f ∪ T1.image f) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    by_cases h1 : p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hp, h1⟩))
    · by_cases h2 : ⌊p.2.2.im⌋ % 2 = 0
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem f
          (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hp, h1⟩, h2⟩)))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem f
          (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hp, h1⟩, h2⟩)))
  have hb0 : ((T0.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8) :=
    hcount T0 (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
      (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2)
      (fun p hp p' hp' => by rw [(Finset.mem_filter.1 hp).2, (Finset.mem_filter.1 hp').2])
  have hb1 : ((T1.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8) :=
    hcount T1 (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
      (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2)
      (fun p hp p' hp' => by
        have e1 := (Finset.mem_filter.1 hp).2
        have e2 := (Finset.mem_filter.1 hp').2
        omega)
  set M : ℕ := ⌈(Qn : ℝ) ^ ((1 : ℝ) / 20)⌉₊ with hM
  have : Subsingleton (DirichletCharacter ℂ (0 + 1)) :=
    (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
  have hsmallsub : Ts.image f ⊆ (Finset.range (2 * M + 1)).image
      (fun k : ℕ => (⟨0, 1, (k : ℤ) - M⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ)) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨N, χ, ρ⟩ := p
    obtain ⟨-, hN0, hlt⟩ := Finset.mem_filter.1 hp
    have hN : N = 0 := hN0
    subst hN
    have hlt' : |ρ.im| < (M : ℝ) := lt_of_lt_of_le hlt (Nat.le_ceil _)
    have hfl1 : (⌊ρ.im⌋ : ℝ) ≤ ρ.im := Int.floor_le _
    have hfl2 : ρ.im < ⌊ρ.im⌋ + 1 := Int.lt_floor_add_one _
    have ha := abs_lt.1 hlt'
    have hA1 : ⌊ρ.im⌋ < (M : ℤ) := by
      have : (⌊ρ.im⌋ : ℝ) < ((M : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hA2 : -(M : ℤ) < ⌊ρ.im⌋ + 1 := by
      have : ((-(M : ℤ) : ℤ) : ℝ) < ((⌊ρ.im⌋ + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have ht : (((⌊ρ.im⌋ + M).toNat : ℕ) : ℤ) = ⌊ρ.im⌋ + M := Int.toNat_of_nonneg (by omega)
    refine Finset.mem_image.2 ⟨(⌊ρ.im⌋ + M).toNat, Finset.mem_range.2 (by omega), ?_⟩
    have hχ : χ = 1 := Subsingleton.elim _ _
    subst hχ
    show (⟨0, 1, (((⌊ρ.im⌋ + M).toNat : ℕ) : ℤ) - M⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) =
      ⟨0, 1, ⌊ρ.im⌋⟩
    rw [ht, add_sub_cancel_right]
  have hsmallcard : ((Ts.image f).card : ℝ) ≤ 2 * (M : ℝ) + 1 := by
    have h := (Finset.card_le_card hsmallsub).trans Finset.card_image_le
    rw [Finset.card_range] at h
    exact_mod_cast h
  have hcard : ((T.image f).card : ℝ) ≤
      (Ts.image f).card + ((T0.image f).card + (T1.image f).card) := by
    have h := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (add_le_add (le_refl _) (Finset.card_union_le _ _)))
    exact_mod_cast h
  have hM1 : (M : ℝ) < (Qn : ℝ) ^ ((1 : ℝ) / 20) + 1 := Nat.ceil_lt_add_one (by positivity)
  have he1 : (Qn : ℝ) ^ ((1 : ℝ) / 20) ≤ (Qn : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hQn1 (by norm_num)
  have he2 : (1 : ℝ) ≤ (Qn : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hQn1 (by norm_num)
  calc ((T.image f).card : ℝ) ≤ (2 * C₁ + 5) * (Qn : ℝ) ^ ((1 : ℝ) / 8) := by linarith
    _ ≤ (2 * C₁ + 5) * (((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8)) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
    _ = (2 * C₁ + 5) * ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8) := by ring

end GlobalTheory.ZeroCells
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceGlMatrixUnitPowHighestWeightModStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ) (E : Matrix (Fin N) (Fin N) (Module.End R V)), GlRel E → ∀ (M : Submodule R V), (∀ a b, ∀ f ∈ M, E a b f ∈ M) → ∀ (μ : Fin N → R) (v : V), (∀ a b, a < b → E a b v ∈ M) → (∀ a, E a a v - μ a • v ∈ M) → ∀ k : ℕ, (E ^ k).trace v - hcVal R μ k • v ∈ M := by
  first | exact @GlobalTheory.Alc.trace_pow_hw | exact GlobalTheory.Alc.trace_pow_hw | (intros; apply GlobalTheory.Alc.trace_pow_hw <;> assumption)
end


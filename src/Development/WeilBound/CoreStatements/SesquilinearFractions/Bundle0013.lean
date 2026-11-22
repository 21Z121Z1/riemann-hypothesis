import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsUnitValueSkewHermitian
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0024

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.DifferentIdealEqTopOfUnramified
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

theorem differentIdeal_eq_top_of_unramified (E : Type) [Field E] [NumberField E] [IsCMField E]
    [h : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] :
    differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hdvd : P ∣ differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) := Ideal.dvd_iff_le.mpr hle
  haveI : P.IsPrime := hP.isPrime
  have hU : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P := by
    unfold Algebra.IsUnramifiedAt
    haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := inferInstance
    exact Algebra.FormallyUnramified.comp (𝓞 (maximalRealSubfield E)) (𝓞 E) (Localization.AtPrime P)
  exact (not_dvd_differentIdeal_iff.mpr hU) hdvd

theorem exists_real_different_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : Nat.Primes, ∃ δ ∈ differentIdeal ℤ (𝓞 E), δ ≠ 0 ∧ IsCMField.complexConj E (δ : E) = δ ∧ ∀ j : E →+* ℂ_[p], Real.log ‖j (δ : E)‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  intro E _ _ _ hU p
  set F := maximalRealSubfield E
  have hD : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E), differentIdeal_eq_top_of_unramified E, Ideal.top_mul]
  have hD0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨δ, hδI, hδ0, ⟨n, hn, hnI⟩, -⟩ := ideal_padic_generator_log_norm F (differentIdeal ℤ (𝓞 F)) p hD0
  set δ' : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) δ
  have hδ'I : δ' ∈ differentIdeal ℤ (𝓞 E) := by rw [hD]; exact Ideal.mem_map_of_mem _ hδI
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  refine ⟨δ', hδ'I, fun h => hδ0 (hinj (h.trans (map_zero _).symm)), ?_, fun j => ?_⟩
  · have : ((δ' : 𝓞 E) : E) = ((δ : F) : E) := rfl
    rw [this]
    exact IsCMField.complexConj_apply_eq_self E (δ : F)
  ·
    set j' : 𝓞 E →+* ℂ_[p] := j.comp (algebraMap (𝓞 E) E) with hj'
    have hmax : ∀ b ∈ differentIdeal ℤ (𝓞 E), ‖j' b‖ ≤ ‖j' δ'‖ := by
      intro b hb
      rw [hD] at hb
      induction hb using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hnI a ha)
        have e := congrArg (fun z : 𝓞 F => j' (algebraMap (𝓞 F) (𝓞 E) z)) hy
        simp only [map_mul, map_natCast] at e
        have h1 := congrArg norm e
        simp only [norm_mul] at h1
        rw [LocGen.norm_natCast_cp p n hn, one_mul] at h1
        rw [← h1]
        have : ‖j' (algebraMap (𝓞 F) (𝓞 E) y)‖ ≤ 1 := NI.norm_int_le j' _
        calc ‖j' (algebraMap (𝓞 F) (𝓞 E) y)‖ * ‖j' δ'‖ ≤ 1 * ‖j' δ'‖ :=
              mul_le_mul_of_nonneg_right this (norm_nonneg _)
          _ = ‖j' δ'‖ := one_mul _
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      | smul c x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        have : ‖j' c‖ ≤ 1 := NI.norm_int_le j' c
        calc ‖j' c‖ * ‖j' x‖ ≤ 1 * ‖j' δ'‖ := mul_le_mul this hx (norm_nonneg _) zero_le_one
          _ = ‖j' δ'‖ := one_mul _
    exact (NI.logIdeal_eq (j.comp (algebraMap (𝓞 E) E)) _ hδ'I hmax).symm

end PositivityTheory.Xgf

end
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.PadicIntegralIffDenominator
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl Polynomial
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

namespace UI

variable {p : Nat.Primes}

theorem coeff_prod_le (s : Multiset ℂ_[p]) (hs : ∀ r ∈ s, ‖r‖ ≤ 1) :
    ∀ i, ‖((s.map fun r => X - C r).prod).coeff i‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.PadicComplexProdXSubCCoeffNorm.main s hs

theorem norm_p_cp_lt : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_nat_cp_lt (n : ℕ) (hn : (p : ℕ) ∣ n) : ‖(n : ℂ_[p])‖ < 1 := by
  obtain ⟨m, rfl⟩ := hn
  rw [Nat.cast_mul, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ m)) norm_p_cp_lt

theorem norm_natAbs_cp (k : ℤ) : ‖(k : ℂ_[p])‖ = ‖(k.natAbs : ℂ_[p])‖ := by
  rcases Int.natAbs_eq k with h | h
  · conv_lhs => rw [h]
    rw [Int.cast_natCast]
  · conv_lhs => rw [h]
    rw [Int.cast_neg, norm_neg, Int.cast_natCast]

theorem not_dvd_den (c : ℚ) (hc : ‖algebraMap ℚ ℂ_[p] c‖ ≤ 1) : ¬ (p : ℕ) ∣ c.den := by
  intro hd
  have hnum : ¬ (p : ℕ) ∣ c.num.natAbs := fun h1 =>
    (Nat.Prime.coprime_iff_not_dvd p.2).mp (Nat.Coprime.coprime_dvd_left h1 c.reduced) hd
  have hden : ‖((c.den : ℕ) : ℂ_[p])‖ < 1 := norm_nat_cp_lt _ hd
  have e : algebraMap ℚ ℂ_[p] c * ((c.den : ℕ) : ℂ_[p]) = (c.num : ℂ_[p]) := by
    have := congrArg (algebraMap ℚ ℂ_[p]) (Rat.mul_den_eq_num c)
    rw [map_mul, map_natCast, map_intCast] at this
    exact this
  have h2 := congrArg norm e
  rw [norm_mul, norm_natAbs_cp, LocGen.norm_natCast_cp p _ hnum] at h2
  have : ‖algebraMap ℚ ℂ_[p] c‖ * ‖((c.den : ℕ) : ℂ_[p])‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hc) hden
  linarith

end UI

theorem padic_integral_iff_denominator : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (x : E), ((∀ j : E →+* ℂ_[p], ‖j x‖ ≤ 1) ↔ ∃ (n : ℕ) (a : 𝓞 E), ¬ (p : ℕ) ∣ n ∧ (n : E) * x = a) := by
  intro E _ _ p x
  constructor
  · intro h
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    set q := minpoly ℚ x with hqdef
    have hq : q.Monic := minpoly.monic hint

    have hA : ∀ i, ‖algebraMap ℚ ℂ_[p] (q.coeff i)‖ ≤ 1 := by
      set Q := q.map (algebraMap ℚ ℂ_[p])
      have hQs : Q.Splits := IsAlgClosed.splits Q
      have hQm : Q.Monic := hq.map _
      have hroots : ∀ r ∈ Q.roots, ‖r‖ ≤ 1 := by
        intro r hr
        have hr' : aeval r q = 0 := by
          rw [aeval_def, ← eval_map]
          exact (mem_roots hQm.ne_zero).mp hr
        obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
          (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hr'
        rw [← hφ]
        exact h φ.toRingHom
      intro i
      have e : Q.coeff i = algebraMap ℚ ℂ_[p] (q.coeff i) := coeff_map _ _
      rw [← e, hQs.eq_prod_roots_of_monic hQm]
      exact UI.coeff_prod_le _ hroots i
    have hB : ∀ i, ¬ (p : ℕ) ∣ (q.coeff i).den := fun i => UI.not_dvd_den _ (hA i)
    set N : ℕ := ∏ i ∈ Finset.range (q.natDegree + 1), (q.coeff i).den with hN
    have hNp : ¬ (p : ℕ) ∣ N := by
      rw [hN, Prime.dvd_finsetProd_iff (Nat.Prime.prime p.2)]
      rintro ⟨i, -, hi⟩
      exact hB i hi
    have hN0 : (N : ℚ) ≠ 0 := by
      rw [hN]; push_cast
      exact Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (q.coeff i).den_ne_zero

    have hlift : C (N : ℚ) * q ∈ lifts (Int.castRingHom ℚ) := by
      rw [lifts_iff_coeff_lifts]
      intro i
      rw [coeff_C_mul]
      by_cases hi : i ≤ q.natDegree
      · have hdvd : (q.coeff i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
        obtain ⟨k, hk⟩ := hdvd
        refine ⟨k * (q.coeff i).num, ?_⟩
        simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
        rw [hk]
        push_cast
        rw [mul_comm ((q.coeff i).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), mul_zero]
        exact ⟨0, by simp⟩
    obtain ⟨P, hP0⟩ := hlift
    have hP : P.map (Int.castRingHom ℚ) = C (N : ℚ) * q := hP0
    have hPlc : P.leadingCoeff = N := by
      have h1 := leadingCoeff_map_of_injective (Int.castRingHom ℚ).injective_int P
      rw [hP, leadingCoeff_mul, leadingCoeff_C, hq.leadingCoeff, mul_one] at h1
      have h2 : ((P.leadingCoeff : ℤ) : ℚ) = ((N : ℤ) : ℚ) := by
        have h3 : (Int.castRingHom ℚ) P.leadingCoeff = ((N : ℕ) : ℚ) := h1.symm
        rw [eq_intCast] at h3
        rw [h3]; push_cast; rfl
      exact_mod_cast h2
    have hPx : aeval x P = 0 := by
      rw [← aeval_map_algebraMap ℚ x P, algebraMap_int_eq, hP, map_mul, aeval_C, minpoly.aeval, mul_zero]
    have hi : IsIntegral ℤ (P.leadingCoeff • x) := isIntegral_leadingCoeff_smul P x hPx
    rw [hPlc, natCast_zsmul] at hi
    refine ⟨N, ⟨N • x, hi⟩, hNp, ?_⟩
    simp [nsmul_eq_mul]
  · rintro ⟨n, a, hn, h⟩ j
    have h1 := congrArg (fun z => ‖j z‖) h
    simp only [map_mul, norm_mul, map_natCast] at h1
    rw [LocGen.norm_natCast_cp p n hn, one_mul] at h1
    rw [h1]
    exact NI.norm_int_le (j.comp (algebraMap (𝓞 E) E)) a

end PositivityTheory.Xgf

end
end


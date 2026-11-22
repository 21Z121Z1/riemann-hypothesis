import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSelfDualPairGaloisConjugateHomLattice

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomLatticeCommensurableOrthonormal
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_nat_common_denom {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] (c : ι → K) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, ∃ a : 𝓞 K, (a : K) = (k : K) * c i := by
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨(m * m).natAbs, Int.natAbs_pos.2 (mul_ne_zero hm0 hm0), fun i => ?_⟩
  have h := hm (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨(m : 𝓞 K) * ⟨m • c i, h⟩, ?_⟩
  have h2 : (((m * m).natAbs : ℕ) : K) = (m : K) * m := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg m)]; push_cast; rfl
  rw [h2]
  change ((m : 𝓞 K) : K) * (m • c i) = _
  simp [mul_assoc]

theorem smul_mem_YYl (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (a : 𝓞 D.host.K)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L L') : (a : D.host.K) • y ∈ YYl D L L' := by
  have h := (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a) hy
  exact h

theorem exists_comm_YYl (D : D7) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hb : OnB D b) (hL : SD D L) (hL' : SD D L') :
    ∃ k : ℕ, 0 < k ∧ Comm D b k (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  have hc : ∀ i, ∃ c : Fin r → D.host.K, ∑ j, c j • b j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hb.2]; trivial)
  choose c hc using hc
  obtain ⟨k, hk, hden⟩ := exists_nat_common_denom (K := D.host.K) (ι := (Fin s × Fin r) ⊕ (Fin s × Fin r))
    (Sum.elim (fun p => c p.1 p.2) (fun p => hYY D (b p.2) (y' p.1)))
  choose a ha using hden
  refine ⟨k, hk, fun x hx => ?_, fun j => ?_⟩
  · have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine ⟨fun j => ∑ i, t i * a (Sum.inl (i, j)), ?_⟩
    conv_lhs => rw [hexp x]
    rw [← Nat.cast_smul_eq_nsmul D.host.K]
    simp only [← hc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ha, ht]
    simp only [Sum.elim_inl]
    ring
  · apply AddSubgroup.subset_closure
    rw [hexp (b j), ← Nat.cast_smul_eq_nsmul D.host.K, Finset.smul_sum]
    refine (YYl D L L').sum_mem fun i _ => ?_
    rw [smul_smul]
    have := ha (Sum.inr (i, j))
    simp only [Sum.elim_inr] at this
    rw [← this]
    exact smul_mem_YYl D L L' _ (hy i)

end GlobalTheory.ThetaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Nat

namespace GlobalTheory.IdealIdele

theorem pow_factorial_mul {M : Type} [Monoid M] [Fintype M] (a : M) (t : ℕ) (ht : 0 < t) :
    a ^ ((Fintype.card M)! * t) = a ^ (Fintype.card M)! := by
  obtain ⟨i, j, hij, hj, e⟩ : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card M ∧ a ^ i = a ^ j := by
    obtain ⟨i, j, hne, e⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card M + 1) => a ^ (i : ℕ)) (by simp)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, Nat.lt_succ_iff.1 j.2, e⟩
    · exact ⟨j, i, h, Nat.lt_succ_iff.1 i.2, e.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  have hd : 0 < d := by omega
  have key : ∀ u : ℕ, a ^ (i + d * u) = a ^ i := by
    intro u
    induction u with
    | zero => simp
    | succ u ih => rw [Nat.mul_succ, ← add_assoc, pow_add, ih, ← pow_add, ← e]
  obtain ⟨c, hc⟩ : d ∣ (Fintype.card M)! := Nat.dvd_factorial hd (by omega)
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le
    (show i ≤ (Fintype.card M)! from le_trans (by omega) (Nat.self_le_factorial _))
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  have : (Fintype.card M)! * t.succ = i + d * (c * t) + s := by
    rw [Nat.mul_succ, ← mul_assoc, ← hc]; omega
  rw [this, pow_add, key, ← pow_add, ← hs]

theorem int_dvd_pow_sub (m N t : ℕ) (hN : 0 < N) (ht : 0 < t) :
    ∃ c : ℤ, (m : ℤ) ^ (N ! * t) = (m : ℤ) ^ N ! + N * c := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h := pow_factorial_mul (m : ZMod N) t ht
  rw [ZMod.card] at h
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((m : ℤ) ^ (N ! * t) - (m : ℤ) ^ N !) N).1
    (by push_cast; rw [h, sub_self])
  exact ⟨c, by linear_combination hc⟩

section Abstract

variable {A : Type} [CommRing A] (S : Subring A)

theorem exists_idem
    (hsep : ∀ y : A, (∀ N : ℕ, 0 < N → ∃ w ∈ S, y = (N : A) * w) → y = 0)
    (hcpl : ∀ x : ℕ → A, (∀ N, x N ∈ S) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ S, x (N * m) = x N + (N : A) * w) →
      ∃ y ∈ S, ∀ N : ℕ, 0 < N → ∃ w ∈ S, y = x N + (N : A) * w)
    (m : ℕ) (hm : 0 < m) :
    ∃ f ∈ S, f * f = f ∧ (∃ w ∈ S, f = (m : A) * w) ∧
      ∀ n : ℕ, 0 < n → m.Coprime n → ∃ w ∈ S, 1 - f = (n : A) * w := by
  have hc : ∀ N t : ℕ, 0 < N → 0 < t →
      ∃ c : ℤ, (m : A) ^ (N ! * t) = (m : A) ^ N ! + N * c := fun N t hN ht => by
    obtain ⟨c, h⟩ := int_dvd_pow_sub m N t hN ht
    refine ⟨c, ?_⟩
    have := congrArg (Int.cast : ℤ → A) h
    push_cast at this
    exact this
  have hx : ∀ k : ℕ, (m : A) ^ k ∈ S := fun k => pow_mem (natCast_mem S m) k
  obtain ⟨f, hf, h⟩ := hcpl (fun N => (m : A) ^ N !) (fun N => hx _) (by
    intro N k hN hk
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right N hk)
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by
      rintro rfl
      exact (Nat.factorial_ne_zero _) (by simpa using ht))
    obtain ⟨c, hc⟩ := hc N t hN ht0
    exact ⟨c, intCast_mem S c, by simp only [ht, hc]⟩)
  refine ⟨f, hf, ?_, ?_, fun n hn hmn => ?_⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨c, hc⟩ := hc N 2 hN two_pos
    refine ⟨c + (2 * (m : A) ^ N ! * w + N * w * w - w), ?_, ?_⟩
    · exact add_mem (intCast_mem S c) (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (hx _)) hw)
        (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
    · rw [pow_mul] at hc
      rw [hh]; linear_combination hc
  · obtain ⟨w, hw, hh⟩ := h m hm
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero m)
    refine ⟨(m : A) ^ s + w, add_mem (hx s) hw, ?_⟩
    rw [hh, hs, pow_succ]; ring
  · obtain ⟨w, hw, hh⟩ := h n hn
    obtain ⟨t, ht⟩ := Nat.dvd_factorial (Nat.totient_pos.2 hn) (Nat.totient_le n)
    have h1 : m ^ n ! ≡ 1 [MOD n] := by
      have := (Nat.ModEq.pow_totient hmn).pow t
      rwa [← pow_mul, ← ht, one_pow] at this
    obtain ⟨c, hc⟩ := h1.dvd
    have hc' := congrArg (Int.cast : ℤ → A) hc
    push_cast at hc'
    refine ⟨c - w, sub_mem (intCast_mem S c) hw, ?_⟩
    rw [hh]; linear_combination hc'

end Abstract

theorem exists_local_generator {E : Type} [Field E] [NumberField E] (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    ∃ (m n : ℕ) (β : 𝓞 E), 0 < m ∧ 0 < n ∧ m.Coprime n ∧ (m : 𝓞 E) ∈ B ∧ β ∈ B ∧ β ≠ 0 ∧
      ∀ b ∈ B, β ∣ (n : 𝓞 E) * b := by
  set m := 2 * Ideal.absNorm B with hm
  have hN : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hB)
  have hm2 : 2 ≤ m := by omega
  have hmB : (m : 𝓞 E) ∈ B := by
    rw [hm, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem B)
  have hm0 : (m : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨β, hβ⟩ := IsDedekindDomain.exists_sup_span_eq (I := B * Ideal.span {(m : 𝓞 E)}) (J := B)
    Ideal.mul_le_left (mul_ne_zero hB (by simpa using hm0))
  have hβB : β ∈ B := hβ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self β)
  obtain ⟨C, hC⟩ : B ∣ Ideal.span {β} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hβB)
  have hsup : Ideal.span {(m : 𝓞 E)} ⊔ C = ⊤ := by
    apply mul_left_cancel₀ hB
    rw [Ideal.mul_sup, ← hC, hβ, Ideal.mul_top]
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq, Ideal.span_singleton_eq_top] at hsup
    have h1 := Ideal.absNorm_eq_one_iff.2 (Ideal.span_singleton_eq_top.2 hsup)
    rw [Ideal.absNorm_span_natCast] at h1
    have h2 := (Nat.pow_eq_one.1 h1).resolve_left (by omega)
    exact Module.finrank_pos.ne' h2
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hB hC0 (by rw [← hC]; simp)
  haveI : Finite (𝓞 E ⧸ C) := Ideal.finiteQuotientOfFreeOfNeBot C hC0
  have hu : IsUnit (Ideal.Quotient.mk C (m : 𝓞 E)) := by
    obtain ⟨x, hx, c, hc, e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk C a) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk C), Ideal.Quotient.eq]
    rw [show (m : 𝓞 E) * a - 1 = -c by linear_combination e]
    exact neg_mem hc
  obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hu.unit)
  have e' : (m : 𝓞 E) ^ k - 1 ∈ C := by
    rw [← Ideal.Quotient.eq, map_pow, map_one]
    simpa using congrArg Units.val e
  have h1 : 1 < m ^ k := Nat.one_lt_pow hk.ne' (by omega)
  refine ⟨m, m ^ k - 1, β, by omega, by omega, ?_, hmB, hβB, hβ0, fun b hb => ?_⟩
  · refine Nat.Coprime.of_dvd_left (dvd_pow_self m hk.ne') ?_
    exact (Nat.coprime_self_sub_right h1.le).2 (Nat.coprime_one_right _)
  · rw [← Ideal.mem_span_singleton, hC, mul_comm (((m ^ k - 1 : ℕ)) : 𝓞 E)]
    refine Ideal.mul_mem_mul hb ?_
    rw [Nat.cast_sub h1.le]
    push_cast
    exact e'

theorem exists_idele_generator : ∀ (D : D7) (B : Ideal (𝓞 D.host.E)), B ≠ ⊥ → ∃ y : (AE D)ˣ, (∀ b ∈ B, ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (b : D.host.E) ∈ OhE D) ∧ ∃ (k : ℕ) (b : Fin k → 𝓞 D.host.E) (w : Fin k → AE D), (∀ i, b i ∈ B) ∧ (∀ i, w i ∈ OhE D) ∧ (y : AE D) = ∑ i, inc D (b i : D.host.E) * w i := by
  intro D B hB
  obtain ⟨m, n, β, hm, hn, hmn, hmB, hβB, hβ0, hdvd⟩ := exists_local_generator B hB
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := exists_idem (OhE D) hsep hcpl m hm
  obtain ⟨v, hv, hfv⟩ := h3 n hn hmn
  have hint : ∀ b : 𝓞 D.host.E, inc D (b : D.host.E) ∈ OhE D := fun b =>
    (GlobalTheory.HeckeVal.inc_mem_iff D _).2 b.isIntegral_coe
  have hβE : (β : D.host.E) ≠ 0 := by simpa using hβ0
  have hinv : inc D (β : D.host.E) * inc D (β : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hβE, map_one]
  have hy : ((1 - f) * inc D (β : D.host.E) + f) * ((1 - f) * inc D (β : D.host.E)⁻¹ + f) = 1 := by
    linear_combination (1 - f) ^ 2 * hinv +
      (2 - inc D (β : D.host.E) - inc D (β : D.host.E)⁻¹) * hff
  refine ⟨⟨_, _, hy, by rw [mul_comm, hy]⟩, fun b hb => ?_, 2, ![β, m], ![1 - f, w], ?_, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hdvd b hb
    have hd' : (n : AE D) * inc D (b : D.host.E) = inc D (β : D.host.E) * inc D (d : D.host.E) := by
      rw [← map_natCast (inc D), ← map_mul, ← map_mul]
      congr 1
      exact_mod_cast congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hd
    change ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) ∈ OhE D
    rw [show ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) =
      v * inc D (d : D.host.E) + f * inc D (b : D.host.E) by
        rw [hfv]
        linear_combination v * inc D (β : D.host.E)⁻¹ * hd' + v * inc D (d : D.host.E) * hinv]
    exact add_mem (mul_mem hv (hint d)) (mul_mem hf (hint b))
  · intro i
    fin_cases i
    · exact hβB
    · exact hmB
  · intro i
    fin_cases i
    · exact sub_mem (one_mem _) hf
    · exact hw
  · have : inc D (((m : 𝓞 D.host.E)) : D.host.E) = (m : AE D) := by
      rw [← map_natCast (inc D)]; congr 1
    change (1 - f) * inc D (β : D.host.E) + f = _
    rw [Fin.sum_univ_two]
    change _ = inc D (β : D.host.E) * (1 - f) + inc D (((m : 𝓞 D.host.E)) : D.host.E) * w
    rw [this, ← hfw]; ring

end GlobalTheory.IdealIdele
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLogDerivQExpansionModPrimePowOfTranslation
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.DlEx

variable {Ω : Type} [Field Ω]

def Sp (L : ℕ) (x : HahnSeries ℚ Ω) : Prop := ∀ r : ℚ, x.coeff r ≠ 0 → (r * L).den = 1

lemma den_add {a b : ℚ} (ha : a.den = 1) (hb : b.den = 1) : (a + b).den = 1 := by
  rw [Rat.den_eq_one_iff] at ha hb
  rw [← ha, ← hb, ← Int.cast_add]; simp

lemma exists_of_coeff_mul_ne {x y : HahnSeries ℚ Ω} {r : ℚ} (h : (x * y).coeff r ≠ 0) :
    ∃ r₁ r₂, r₁ + r₂ = r ∧ x.coeff r₁ ≠ 0 ∧ y.coeff r₂ ≠ 0 := by
  rw [HahnSeries.coeff_mul] at h
  obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_antidiagonal] at hij
  exact ⟨ij.1, ij.2, hij.2.2, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

lemma sp_mul {L : ℕ} {x y : HahnSeries ℚ Ω} (hx : Sp L x) (hy : Sp L y) : Sp L (x * y) := by
  intro r hr
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := exists_of_coeff_mul_ne hr
  rw [add_mul]; exact den_add (hx _ h1) (hy _ h2)

lemma sp_sub {L : ℕ} {x y : HahnSeries ℚ Ω} (hx : Sp L x) (hy : Sp L y) : Sp L (x - y) := by
  intro r hr
  rw [HahnSeries.coeff_sub] at hr
  by_cases h : x.coeff r = 0
  · exact hy r (by intro h'; apply hr; rw [h, h', sub_zero])
  · exact hx r h

variable [Algebra ℚ Ω]

lemma sp_theta {L : ℕ} (s : ℚ) {x : HahnSeries ℚ Ω} (hx : Sp L x) : Sp L (theta s x) := by
  intro r hr
  exact hx r (fun h => hr (by simp [theta, h]))

lemma intA_mul (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : (x * y).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hx _) (hy _))

lemma intA_sub (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : (x - y).coeff r ∈ A := by
  rw [HahnSeries.coeff_sub]; exact sub_mem (hx r) (hy r)

lemma intA_theta (A : ValuationSubring Ω) {L : ℕ} {x : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hs : Sp L x) (r : ℚ) : (theta (L : ℚ) x).coeff r ∈ A := by
  show algebraMap ℚ Ω ((L : ℚ) * r) * x.coeff r ∈ A
  by_cases h : x.coeff r = 0
  · rw [h, mul_zero]; exact zero_mem A
  · have hd := hs r h
    rw [Rat.den_eq_one_iff] at hd
    rw [mul_comm (L : ℚ) r, ← hd, map_intCast]
    exact mul_mem (intCast_mem A _) (hx r)

end GlobalTheory.DlEx

open GlobalTheory.DlEx in

theorem GlobalTheory.dl_exists : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (f : X.K), 0 < L → f ≠ 0 → f ∈ KT X L → ∃ φ : HahnSeries ℚ Ω, IsDl X A l n L f φ ∧ ∀ r : ℚ, φ.coeff r ≠ 0 → (r * L).den = 1 := by
  intro Ω _ _ _ ε X hj l _ A hl n L f hL hf hfK
  obtain ⟨a, b, κ, S, hκ, hfb, ha, hb, hbinv, -⟩ := GlobalTheory.T.exists_primitive_expansion_quotient_level_one ε X hj l A hl f hf
  have hbK : b ∈ KT X L := (RingHom.mem_eqLocusField).2 (hbinv _)
  have hcK : algebraMap Ω X.K κ ∈ KT X L := (RingHom.mem_eqLocusField).2 ((X.sl _).commutes κ)
  have haK : a ∈ KT X L := by
    have e : a = (algebraMap Ω X.K κ)⁻¹ * (f * b) := by
      rw [hfb, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 hκ), one_mul]
    rw [e]; exact (KT X L).mul_mem ((KT X L).inv_mem hcK) ((KT X L).mul_mem hfK hbK)
  have hsa : Sp L (X.exp a) := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X L hL a).1 haK
  have hsb : Sp L (X.exp b) := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X L hL b).1 hbK
  have hP : Prim A (X.exp a * X.exp b) := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ ha hb
  obtain ⟨Q, hQA, hQs, hQP⟩ := GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow l A hl n L (X.exp a * X.exp b) hL hP (sp_mul hsa hsb)
  have hDA : ∀ r, (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)).coeff r ∈ A :=
    intA_sub A (intA_mul A (intA_theta A ha.1 hsa) hb.1) (intA_mul A ha.1 (intA_theta A hb.1 hsb))
  have hDs : Sp L (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)) :=
    sp_sub (sp_mul (sp_theta _ hsa) hsb) (sp_mul hsa (sp_theta _ hsb))
  refine ⟨Q * (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)),
    ⟨intA_mul A hQA hDA, a, b, κ, hκ, hfb, ha, hb, ?_⟩, sp_mul hQs hDs⟩
  intro r
  generalize theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b) = D at hDA ⊢
  choose z hzA hz using hQP
  have e : (Q * D * X.exp a * X.exp b).coeff r - D.coeff r = (D * (Q * (X.exp a * X.exp b) - 1)).coeff r := by
    rw [show Q * D * X.exp a * X.exp b = D * (Q * (X.exp a * X.exp b)) by ring, mul_sub, mul_one,
      HahnSeries.coeff_sub]
  refine ⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support (Q * (X.exp a * X.exp b) - 1).isPWO_support r,
    D.coeff ij.1 * z ij.2, Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hDA _) (hzA _)), ?_⟩
  rw [e, HahnSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ij _ => ?_)
  rw [HahnSeries.coeff_sub, hz ij.2]; ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremalStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  first | exact @GlobalTheory.ExtremalGen.exists_generated | exact GlobalTheory.ExtremalGen.exists_generated | (intros; apply GlobalTheory.ExtremalGen.exists_generated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNsmulPaddedLatticeMemBasisProduct
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.PadCommensurable

def sat {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] (f : V →+ V') (B : AddSubgroup V') : AddSubgroup V where
  carrier := {y | ∃ n : ℕ, 0 < n ∧ n • f y ∈ B}
  zero_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨k, hk, hy⟩
    refine ⟨n * k, Nat.mul_pos hn hk, ?_⟩
    rw [map_add, smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.nsmul_mem hx _
    · rw [mul_smul]; exact B.nsmul_mem hy _
  neg_mem' := by
    rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [map_neg, smul_neg]; exact B.neg_mem hx⟩

theorem uniform_of_fg {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] (f : V →+ V') (A : AddSubgroup V)
    (B : AddSubgroup V') (hA : A.FG) (h : A ≤ sat f B) : ∃ R : ℕ, 0 < R ∧ ∀ y ∈ A, R • f y ∈ B := by
  obtain ⟨S, rfl⟩ := hA
  have h' : ∀ y : S, ∃ n : ℕ, 0 < n ∧ n • f y ∈ B := fun y => h (AddSubgroup.subset_closure y.2)
  choose n hn hy using h'
  refine ⟨∏ y, n y, Finset.prod_pos fun y _ => hn y, fun y hy' => ?_⟩
  induction hy' using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ : n ⟨x, hx⟩ ∣ ∏ y, n y := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    rw [hc, mul_comm, mul_smul]
    exact B.nsmul_mem (hy ⟨x, hx⟩) _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact B.add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact B.neg_mem hx

theorem exists_nat_mul_int {K : Type*} [Field K] [NumberField K] (κ : K) :
    ∃ (n : ℕ) (a : 𝓞 K), 0 < n ∧ (a : K) = n * κ := by
  have halg : IsAlgebraic ℤ κ := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic κ)
  obtain ⟨d, hd, hi⟩ := halg.exists_integral_multiple
  rcases Int.natAbs_eq d with h | h
  · refine ⟨d.natAbs, ⟨d • κ, hi⟩, Int.natAbs_pos.2 hd, ?_⟩
    change d • κ = _
    rw [zsmul_eq_mul]
    conv_lhs => rw [h]
    rw [Int.cast_natCast]
  · refine ⟨d.natAbs, -⟨d • κ, hi⟩, Int.natAbs_pos.2 hd, ?_⟩
    change -(d • κ) = _
    rw [zsmul_eq_mul]
    conv_lhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast]
    ring

theorem exists_nsmul_mem (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (w : ℂ) (hw : w ∈ lamOf D cc δ)
    (A : Matrix (Fin N') (Fin N) D.host.E) :
    w • embV D (tor0 D cc δ) A ∈ sat (AddMonoidHom.id _) (LaB D (tor0 D cc δ) b) := by
  obtain ⟨-, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ hc
  have hA : A ∈ Submodule.span D.host.K (Set.range b) := by rw [hb.2]; trivial
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hA
  have e : w • embV D (tor0 D cc δ) (∑ i, κ i • b i) =
      ∑ i, (D.host.φ₀ (κ i : D.host.E) * w) • embV D (tor0 D cc δ) (b i) := by
    funext τ s t
    have h1 : ∀ i, (κ i • b i) s t = (κ i : D.host.E) * b i s t := fun i => rfl
    have h2 := hD.1 τ
    simp only [embV, tor0, Pi.smul_apply, Finset.sum_apply, Matrix.sum_apply, h1, map_sum, map_mul, h2,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨n, a, hn, ha⟩ := exists_nat_mul_int (κ i)
  refine ⟨n, hn, AddSubgroup.subset_closure ⟨_, hst a w hw, i, ?_⟩⟩
  rw [AddMonoidHom.id_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ha]
  congr 1
  push_cast
  rw [map_mul, map_natCast]
  ring

theorem nsmul_pad_mem : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b → (La D (tor0 D cc δ) L L').FG → ∃ R : ℕ, 0 < R ∧ ∀ y ∈ La D (tor0 D cc δ) L L', R • pad D m y ∈ LaB D (tor0 D cc δ) b := by
  intro D hD cc δ hc N N' m r L L' b hb hfg
  refine uniform_of_fg (padL D m).toAddMonoidHom _ _ hfg ?_
  rw [La, AddSubgroup.closure_le]
  rintro _ ⟨w, hw, A, -, rfl⟩
  obtain ⟨n, hn, h⟩ := exists_nsmul_mem D hD cc δ hc b hb w hw (padM D m A)
  refine ⟨n, hn, ?_⟩
  change n • pad D m _ ∈ _
  rw [pad_smul, pad_embV D _ (fun τ => map_zero (embT D τ))]
  exact h

end GlobalTheory.PadCommensurable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLatticeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodPair_idealCurveLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  first | exact @GlobalTheory.CurveLattice.exists_periodPair_lamOf | exact GlobalTheory.CurveLattice.exists_periodPair_lamOf | (intros; apply GlobalTheory.CurveLattice.exists_periodPair_lamOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSelfDualPairGaloisConjugateHomLatticeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_pair_galoisConjugate_homLattice : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L₁ ∧ SD D L₁' ∧ ∀ A : Matrix (Fin N') (Fin N) D.host.E, A ∈ YYl D L L' ↔ A.map σ ∈ YYl D L₁ L₁' := by
  first | exact @GlobalTheory.GaloisTwist.exists_conjugate_pair | exact GlobalTheory.GaloisTwist.exists_conjugate_pair | (intros; apply GlobalTheory.GaloisTwist.exists_conjugate_pair <;> assumption)
end


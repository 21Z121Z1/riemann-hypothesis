import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralBinomLePowCardPrimesBetween
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassNoLargePrimeFactorLe
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem add_le_sum_of_mem_of_ne {s : Multiset ℕ} {p q : ℕ} (hp : p ∈ s) (hq : q ∈ s) (h : p ≠ q) : p + q ≤ s.sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hp
  have hq' : q ∈ t := (Multiset.mem_cons.mp hq).resolve_left (Ne.symm h)
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hq'
  rw [Multiset.sum_cons, Multiset.sum_cons, ← add_assoc]
  exact Nat.le_add_right _ _

theorem card_perm_no_long_cycle (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, N < 2 * p) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card +
      ∑ p ∈ S, (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card = N.factorial := by
  have hsum : ∀ σ : Equiv.Perm (Fin N), σ.partition.parts.sum = N := fun σ => by
    simpa using σ.partition.parts_sum
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_filter]
    intro σ _ hpσ hqσ
    have h1 := add_le_sum_of_mem_of_ne hpσ hqσ hpq
    rw [hsum σ] at h1
    have h2 := hS p hp
    have h3 := hS q hq
    omega
  rw [← Finset.card_biUnion hdisj]
  have hc : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts) =
      (S.biUnion fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts)ᶜ := by
    ext σ
    simp
  rw [hc, Finset.card_compl_add_card, Fintype.card_perm, Fintype.card_fin]

theorem mass_not_hasPrimeFactor_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N →
    (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  intro g _ N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hSdef
  have hS : ∀ p ∈ S, N < 2 * p := fun p hp => (Finset.mem_filter.mp hp).2.2.1
  have hSN : ∀ p ∈ S, p ≤ N := fun p hp =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  have hmono : (mass g N fun f => ¬ HasPrimeFactor g N f) ≤
      mass g N fun f => ∀ p ∈ S, p ∉ degType g f := by
    have hsub : (sqSet g N).filter (fun f => ¬ HasPrimeFactor g N f) ⊆
        (sqSet g N).filter (fun f => ∀ p ∈ S, p ∉ degType g f) := by
      intro f hf
      rw [Finset.mem_filter] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro p hp hpf
      apply hf.2
      unfold degType at hpf
      unfold HasPrimeFactor
      obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hpf
      obtain ⟨-, hpr, h2, h3⟩ := Finset.mem_filter.mp hp
      exact ⟨h, UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh, hpr, h2, h3⟩
    unfold mass
    convert Finset.sum_le_sum_of_subset_of_nonneg (f := fun f => ((torusCard g f : ℝ))⁻¹) hsub
      (fun f _ _ => by positivity)
    rfl
  have hT := GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun m : Multiset ℕ => ∀ p ∈ S, p ∉ m)
  have hcount := card_perm_no_long_cycle N S hS
  have hlong : ∀ p ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      p ∈ σ.partition.parts).card : ℝ) = N.factorial / p := by
    intro p hp
    have hp0 : 0 < p := by have := hS p hp; omega
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [eq_div_iff hp0']
    exact_mod_cast card_perm_long_cycle N p (hS p hp) (hSN p hp)
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  have hratio : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) / N.factorial = 1 - ∑ p ∈ S, (1 : ℝ) / p := by
    have hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) = N.factorial - ∑ p ∈ S, (N.factorial : ℝ) / p := by
      rw [← Finset.sum_congr rfl hlong]
      have := congrArg (fun n : ℕ => (n : ℝ)) hcount
      push_cast at this
      linarith
    rw [hc, sub_div, div_self hfac, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_right_comm, div_self hfac]
  have hprimes := inv_log_le_sum_inv_primes_between N hN
  calc _ ≤ _ := hmono
    _ ≤ _ := hT
    _ = 1 - ∑ p ∈ S, (1 : ℝ) / p := by convert hratio
    _ ≤ 1 - 1 / (10 * Real.log N) := by linarith

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelAdjoinRootsIntegrallyClosedQuotient
section
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.K5.LevClosed

open Polynomial

theorem mem_adjoin_inv_of_isIntegral {R K : Type*} [CommRing R] [Field K] [Algebra R K] {z : K}
    (hz : z ≠ 0) (hi : IsIntegral R z) : z ∈ Algebra.adjoin R {z⁻¹} := by
  obtain ⟨f, hm, hf⟩ := hi
  letI : Invertible z := invertibleOfNonzero hz
  have h1 := eval₂_reverse_mul_pow (algebraMap R K) z f
  rw [hf, invOf_eq_inv] at h1
  have h2 : eval₂ (algebraMap R K) z⁻¹ f.reverse = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ hz)
  have h3 := divX_mul_X_add f.reverse
  rw [coeff_zero_reverse, hm.leadingCoeff] at h3
  have h4 := congrArg (eval₂ (algebraMap R K) z⁻¹) h3
  rw [h2, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, map_one] at h4
  have hzz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  have h5 : z = -(aeval z⁻¹ (divX f.reverse)) := by
    rw [aeval_def]
    linear_combination z * h4 - eval₂ (algebraMap R K) z⁻¹ (divX f.reverse) * hzz
  have hm' : -(aeval z⁻¹ (divX f.reverse)) ∈ Algebra.adjoin R {z⁻¹} :=
    neg_mem (aeval_mem_adjoin_singleton R _)
  rwa [← h5] at hm'

theorem lev_closed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
      IsInt p (a / b) → a / b ∈ Lev T m := by
  intro p _ Ω _ _ hΩ T m hm a ha b hb hb0 hint
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T m
  obtain ⟨-, hrange⟩ := GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hΩ T m hm ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
  rw [← hrange] at ha hb ⊢
  obtain ⟨a', rfl⟩ := (AlgHom.mem_range ι).1 ha
  obtain ⟨b', rfl⟩ := (AlgHom.mem_range ι).1 hb
  rcases ValuationRing.dvd_total b' a' with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine (AlgHom.mem_range ι).2 ⟨c, ?_⟩
    rw [hc, map_mul, mul_div_cancel_left₀ _ hb0]
  · have ha0 : ι a' ≠ 0 := by
      intro h; apply hb0; rw [hc, map_mul, h, zero_mul]
    have hz0 : ι a' / ι b' ≠ 0 := div_ne_zero ha0 hb0
    have hzi : (ι a' / ι b')⁻¹ = ι c := by
      rw [inv_div, hc, map_mul, mul_div_cancel_left₀ _ ha0]
    have hmem := mem_adjoin_inv_of_isIntegral hz0 hint
    rw [hzi] at hmem
    have hle : Algebra.adjoin (O0 p) {ι c} ≤ ι.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 ⟨c, rfl⟩)
    exact hle hmem

end GlobalTheory.K5.LevClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterPowersOrthogonalGeometricInvariant
section
open GlobalTheory.K5

namespace GlobalTheory.K5.Orth

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem p_ne_zero' (h : IsClo p Ω) : (p : Ω) ≠ 0 := by
  haveI := GlobalTheory.K5.Basic.charZero_of_isClo h
  exact_mod_cast hp.out.ne_zero

theorem not_isInt_inv_p (h : IsClo p Ω) : ¬ IsInt p ((p : Ω)⁻¹) := by
  intro hi
  apply GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
  refine ⟨(p : Ω)⁻¹, hi, ?_⟩
  rw [pow_one, sub_zero, mul_inv_cancel₀ (p_ne_zero' h)]

theorem isInt_natPow_p (k : ℕ) : IsInt p ((p : Ω) ^ k) := by
  have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) ((p : ℤ) ^ k)
  simpa using this

theorem isInt_div (h : IsClo p Ω) {x y : Ω} (hy : y ≠ 0) {a a' : ℤ} {b b' : ℕ} (hb : 0 < b)
    (hb' : 0 < b') (h1 : IsInt p (x ^ b / (p : Ω) ^ a)) (h2 : IsInt p ((p : Ω) ^ a' / y ^ b'))
    (hle : (a' : ℚ) / b' ≤ a / b) : IsInt p (x / y) := by
  have hp0 := p_ne_zero' h
  have he : 0 ≤ a * b' - a' * b := by
    have hb0 : (0 : ℚ) < b := by exact_mod_cast hb
    have hb0' : (0 : ℚ) < b' := by exact_mod_cast hb'
    rw [div_le_div_iff₀ hb0' hb0] at hle
    have : (a' * b : ℚ) ≤ a * b' := hle
    exact_mod_cast (sub_nonneg.2 this)
  obtain ⟨e, he'⟩ := Int.eq_ofNat_of_zero_le he
  have key : (x / y) ^ (b * b') = (x ^ b / (p : Ω) ^ a) ^ b' * ((p : Ω) ^ a' / y ^ b') ^ b *
      (p : Ω) ^ e := by
    have hpe : (p : Ω) ^ e = ((p : Ω) ^ a) ^ b' / ((p : Ω) ^ a') ^ b := by
      rw [← zpow_natCast, ← he', zpow_sub₀ hp0, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [hpe]
    have hP : (p : Ω) ^ a ≠ 0 := zpow_ne_zero _ hp0
    have hP' : (p : Ω) ^ a' ≠ 0 := zpow_ne_zero _ hp0
    generalize (p : Ω) ^ a = P at *
    generalize (p : Ω) ^ a' = P' at *
    have e1 : (y ^ b') ^ b = y ^ (b * b') := by rw [← pow_mul, mul_comm]
    have e2 : (x ^ b) ^ b' = x ^ (b * b') := by rw [← pow_mul]
    simp only [div_pow, e1, e2]
    have h3 : (P ^ b') ≠ 0 := pow_ne_zero _ hP
    have h4 : (P' ^ b) ≠ 0 := pow_ne_zero _ hP'
    have h5 : y ^ (b * b') ≠ 0 := pow_ne_zero _ hy
    rw [div_mul_div_comm, div_mul_div_comm, div_eq_div_iff h5 (mul_ne_zero (mul_ne_zero h3 h5) h4)]
    ring
  have hi : IsInt p ((x / y) ^ (b * b')) := by
    rw [key]
    exact ((h1.pow b').mul (h2.pow b)).mul (isInt_natPow_p e)
  exact IsIntegral.of_pow (Nat.mul_pos hb hb') hi

end GlobalTheory.K5.Orth

namespace GlobalTheory.K5.Orth

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem normalize (h : IsClo p Ω)
    (hV : ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt p (x ^ b / (p : Ω) ^ a) ∧
      IsInt p ((p : Ω) ^ a / x ^ b))
    (n : ℕ) (c : ℕ → Ω) (hc : ∃ j < n, ¬ IsInt p (c j)) :
    ∃ l : Ω, IsAlgZp p l ∧ (∃ m : ℕ, 0 < m ∧ IsInt p (l ^ m / (p : Ω))) ∧
      (∀ j < n, IsInt p (l * c j)) ∧
      ∃ j < n, ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((l * c j) ^ m / (p : Ω)) := by
  classical
  have hp0 := p_ne_zero' h
  choose A B hB h1 h2 using hV
  let w : Ω → ℚ := fun x => if hx : x = 0 then 0 else (A x hx : ℚ) / B x hx
  obtain ⟨j1, hj1, hnj1⟩ := hc
  have hc1 : c j1 ≠ 0 := fun e => hnj1 (e ▸ isIntegral_zero)
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image ((Finset.range n).filter (fun j => c j ≠ 0))
    (fun j => w (c j)) ⟨j1, by simp [hj1, hc1]⟩
  simp only [Finset.mem_filter, Finset.mem_range] at hj0 hmin
  obtain ⟨hj0n, hx0⟩ := hj0
  have hdiv : ∀ j < n, c j ≠ 0 → IsInt p (c j / c j0) := by
    intro j hj hcj
    refine isInt_div h hx0 (hB _ hcj) (hB _ hx0) (h1 _ hcj) (h2 _ hx0) ?_
    have := hmin j ⟨hj, hcj⟩
    simpa [w, hcj, hx0] using this
  have hb := hB _ hx0
  have hu := h1 _ hx0
  have hu' := h2 _ hx0
  generalize A (c j0) hx0 = a at hu hu'
  generalize B (c j0) hx0 = b at hb hu hu'
  have hxInt_of : IsInt p (c j0) → ∀ j < n, IsInt p (c j) := by
    intro hxi j hj
    by_cases hcj : c j = 0
    · rw [hcj]; exact isIntegral_zero
    · have := (hdiv j hj hcj).mul hxi
      rwa [div_mul_cancel₀ _ hx0] at this
  have ha : a < 0 := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hneg
    apply hnj1
    apply hxInt_of _ j1 hj1
    have e : c j0 ^ b = (c j0 ^ b / (p : Ω) ^ a) * (p : Ω) ^ k := by
      rw [hk, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ hp0)]
    exact IsIntegral.of_pow hb (e ▸ hu.mul (isInt_natPow_p k))
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 ha.le)
  haveI := h.clo
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq ((p : Ω) ^ k) hb
  have hk1 : 1 ≤ k := by omega
  have hpa : (p : Ω) ^ a = ((p : Ω) ^ k)⁻¹ := by
    rw [← zpow_natCast, ← hk, zpow_neg, inv_inv]
  have hlx : (l * c j0) ^ b = c j0 ^ b / (p : Ω) ^ a := by
    rw [mul_pow, hl, hpa, div_inv_eq_mul, mul_comm]
  have hlxi : IsInt p (l * c j0) := IsIntegral.of_pow hb (hlx ▸ hu)
  refine ⟨l, ?_, ⟨b, hb, ?_⟩, ?_, j0, hj0n, ?_⟩
  · refine ⟨Polynomial.X ^ b - Polynomial.C ((p : ℤ_[p]) ^ k), Polynomial.X_pow_sub_C_ne_zero hb _, ?_⟩
    simp [hl]
  · rw [hl]
    have e : (p : Ω) ^ k / p = (p : Ω) ^ (k - 1) := by
      rw [div_eq_iff hp0, ← pow_succ, Nat.sub_add_cancel hk1]
    rw [e]
    exact isInt_natPow_p _
  · intro j hj
    by_cases hcj : c j = 0
    · rw [hcj, mul_zero]; exact isIntegral_zero
    · have e : (c j / c j0) * (l * c j0) = l * c j := by
        rw [mul_comm l (c j0), ← mul_assoc, div_mul_cancel₀ _ hx0, mul_comm]
      exact e ▸ (hdiv j hj hcj).mul hlxi
  · rintro ⟨m, hm, hsm⟩
    apply not_isInt_inv_p h
    have hz : l * c j0 ≠ 0 := by
      intro e0
      rw [e0, zero_pow hb.ne', eq_comm, div_eq_zero_iff] at hlx
      rcases hlx with h0 | h0
      · exact hx0 (pow_eq_zero_iff hb.ne' |>.1 h0)
      · exact zpow_ne_zero _ hp0 h0
    have hinv : (p : Ω) ^ a / c j0 ^ b = ((l * c j0) ^ b)⁻¹ := by rw [hlx, inv_div]
    rw [hinv] at hu'
    obtain ⟨b1, rfl⟩ : ∃ b1, b = b1 + 1 := ⟨b - 1, by omega⟩
    have e : ((p : Ω))⁻¹ = ((l * c j0) ^ m / p) ^ (b1 + 1) * (((l * c j0) ^ (b1 + 1))⁻¹) ^ m *
        (p : Ω) ^ b1 := by
      generalize l * c j0 = z at hz
      rw [div_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm (b1 + 1) m, pow_succ (p : Ω) b1]
      have hzz : z ^ (m * (b1 + 1)) ≠ 0 := pow_ne_zero _ hz
      have hpp : (p : Ω) ^ b1 ≠ 0 := pow_ne_zero _ hp0
      rw [div_mul_eq_mul_div, mul_inv_cancel₀ hzz, div_mul_eq_mul_div, one_mul, mul_comm _ (p : Ω),
        eq_div_iff (mul_ne_zero hp0 hpp), inv_mul_cancel_left₀ hp0]
    rw [e]
    exact ((hsm.pow _).mul (hu'.pow m)).mul (isInt_natPow_p b1)

end GlobalTheory.K5.Orth

namespace GlobalTheory.K5.Orth

theorem orth : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
    IsInt p (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt p (c j) := by
  intro p _ Ω _ _ h T N c hfix hint
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨l, hlalg, ⟨m0, hm0, hlsm⟩, hlint, j0, hj0, hj0ns⟩ :=
    normalize h (GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit p Ω h) (p ^ N) c hne
  choose S hSalg hSmem using fun j => GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp p Ω h (c j) (hfix j)
  let S' : Finset Ω := insert l ((Finset.range (p ^ N)).biUnion S)
  have hS'alg : ∀ s ∈ S', IsAlgZp p s := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hlalg
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hs
      exact hSalg j s hj
  set E := Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S' : Set Ω)) with hE
  have hrange : Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) :=
    fun x hx => Subfield.subset_closure (Or.inl hx)
  have hlE : l ∈ E := Subfield.subset_closure (Or.inr (Finset.mem_insert_self _ _))
  have hcE : ∀ j < p ^ N, c j ∈ E := by
    intro j hj
    refine Subfield.closure_mono ?_ (hSmem j)
    apply Set.union_subset_union_right
    intro s hs
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, hs⟩)
  have hsum : (∑ j ∈ Finset.range (p ^ N), (l * c j) * T.qq N ^ j) =
      l * ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsmall : ∃ m : ℕ, 0 < m ∧
      IsInt p ((∑ j ∈ Finset.range (p ^ N), (l * c j) * T.qq N ^ j) ^ m / (p : Ω)) := by
    refine ⟨m0, hm0, ?_⟩
    rw [hsum, mul_pow, mul_div_right_comm]
    exact hlsm.mul (hint.pow m0)
  have := GlobalTheory.T.residue_tower_powers_linearIndependent p Ω h E hrange (GlobalTheory.T.towerParameter_not_pow_mod_maximalIdeal_adjoin_algebraic p Ω h S' hS'alg) T N (fun j => l * c j)
    (fun j hj => ⟨E.mul_mem hlE (hcE j hj), hlint j hj⟩) hsmall j0 hj0
  exact hj0ns this

end GlobalTheory.K5.Orth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.valuation_pow_apply_div_sub_one_lt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (x : Ω) (hx : x ≠ 0) (i : ℕ) :
    A.valuation ((σ ^ i) x / x - 1) < 1 := by
  induction i with
  | zero => simp [hx]
  | succ i ih =>
    have hy0 : (σ ^ i) x ≠ 0 := (map_ne_zero (σ ^ i)).2 hx
    have hle : A.valuation ((σ ^ i) x / x) ≤ 1 := by
      have e : (σ ^ i) x / x = ((σ ^ i) x / x - 1) + 1 := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le ih.le (by simp))
    have key : (σ ^ (i + 1)) x / x - 1 =
        (σ ((σ ^ i) x) / (σ ^ i) x - 1) * ((σ ^ i) x / x) + ((σ ^ i) x / x - 1) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [key]
    apply Valuation.map_add_lt _ _ ih
    rw [map_mul]
    calc A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * A.valuation ((σ ^ i) x / x)
        ≤ A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * 1 := by gcongr
      _ < 1 := by simpa using hσ _ hy0

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.mem_of_wild_of_pow_mem_open_normal :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ (H : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)), H.Normal → IsOpen (H : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) → ∀ (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) (n : ℕ), ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → σ ^ n ∈ H → σ ∈ H := by
  intro E Ω _ _ _ _ _ A v hA H _ hH σ n hn hσ hpow
  change Ω ≃ₐ[E] Ω at σ
  have hv : A.valuation (n : Ω) = 1 := by
    have h1 : ¬ A.valuation (n : Ω) < 1 := by
      intro h
      apply hn
      rw [← hA]
      simpa using h
    have h2 : A.valuation (n : Ω) ≤ 1 := by
      simpa using A.valuation_le_one (n : A)
    exact le_antisymm h2 (not_lt.1 h1)
  have hn0 : (n : Ω) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨s, hsdef⟩ : ∃ s : Ω → Ω, ∀ z, s z = ∑ i ∈ Finset.range n, (σ ^ i) z :=
    ⟨_, fun _ => rfl⟩
  have hs : ∀ z, (σ ^ n) z = z → σ (s z) = s z := by
    intro z hz
    have e1 := Finset.sum_range_succ (fun i => (σ ^ i) z) n
    have e2 := Finset.sum_range_succ' (fun i => (σ ^ i) z) n
    simp only [hz, pow_zero, AlgEquiv.one_apply] at e1 e2
    rw [hsdef, map_sum]
    have e3 : ∑ i ∈ Finset.range n, σ ((σ ^ i) z) = ∑ i ∈ Finset.range n, (σ ^ (i + 1)) z :=
      Finset.sum_congr rfl fun i _ => by rw [pow_succ', AlgEquiv.mul_apply]
    rw [e3]
    exact add_right_cancel (e2.symm.trans e1)
  have hk : ∀ w, σ w = w → ∀ k : ℕ, (σ ^ k) w = w := by
    intro w hw k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hw]
  have hne : ∀ z, z ≠ 0 → s z ≠ 0 := by
    intro z hz h0
    have hlt : A.valuation (∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero
        (fun i _ => _root_.GlobalTheory.valuation_pow_apply_div_sub_one_lt A σ hσ z hz i)
    have e : ∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1) = s z / z - n := by
      simp [hsdef, Finset.sum_sub_distrib, Finset.sum_div]
    rw [e, h0, zero_div, zero_sub, Valuation.map_neg, hv] at hlt
    exact lt_irrefl _ hlt
  have hfix : ∀ y : Ω, (σ ^ n) y = y → σ y = y := by
    intro y hy
    have hsy := hs y hy
    have h1 : ∀ i, (σ ^ i) ((n : Ω) * y - s y) = n * (σ ^ i) y - s y := fun i => by
      rw [map_sub, map_mul, map_natCast, hk (s y) hsy i]
    have hsz : s ((n : Ω) * y - s y) = 0 := by
      rw [hsdef, Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← hsdef, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
    have hz : (n : Ω) * y - s y = 0 := by
      by_contra h
      exact hne _ h hsz
    have hy' : s y = n * y := (sub_eq_zero.1 hz).symm
    have e := congrArg σ hy'
    rw [hsy, map_mul, map_natCast, hy'] at e
    exact (mul_left_cancel₀ hn0 e).symm
  haveI : IsGalois E Ω := inferInstance
  have hcl : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := H.isClosed_of_isOpen hH
  have hH' := InfiniteGalois.fixingSubgroup_fixedField (⟨H, hcl⟩ : ClosedSubgroup (Ω ≃ₐ[E] Ω))
  have hmem : σ ∈ (IntermediateField.fixedField H).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply hfix
    exact (IntermediateField.mem_fixedField_iff H y).1 hy _ hpow
  rw [hH'] at hmem
  exact hmem

end GlobalTheory
end


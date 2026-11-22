import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0001

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.FiniteDimensionalRoots
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial

namespace UpperTheory.KStar.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_roots {M : ℕ} (hM : M ≠ 0) :
    FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}) := by
  have hfin : ({x : Om l | x ^ M = 1} : Set (Om l)).Finite := by
    apply (Polynomial.nthRootsFinset M (1 : Om l)).finite_toSet.subset
    intro x hx
    simpa [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hM)] using hx
  haveI : Finite ({x : Om l | x ^ M = 1} : Set (Om l)) := hfin.to_subtype
  apply IntermediateField.finiteDimensional_adjoin
  intro x hx
  refine ⟨Polynomial.X ^ M - 1, Polynomial.monic_X_pow_sub_C 1 hM, ?_⟩
  simp [Set.mem_setOf_eq.mp hx]

def rootsExt (l : ℕ) [Fact l.Prime] (M : ℕ) (hM : M ≠ 0) : FinExt l :=
  ⟨IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}, finiteDimensional_roots hM⟩

theorem mem_of_rootsExt_le {M : ℕ} (hM : M ≠ 0) {LL : FinExt l} (h : (rootsExt l M hM).1 ≤ LL.1) (x : Om l)
    (hx : x ^ M = 1) : x ∈ LL.1 :=
  h (IntermediateField.subset_adjoin _ _ hx)

theorem le_roots_of_dense {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (J : H.E →+* Om l) (K : FinExt l) {M : ℕ} (hM : M ≠ 0)
    (hN : H.condN ∣ M) (hdense : (K.1 : Set (Om l)) ⊆ closure (Set.range J)) :
    K.1 ≤ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1} := by
  set A := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1} with hA
  haveI : FiniteDimensional ℚ_[l] A := finiteDimensional_roots hM
  have hrange : Set.range J ⊆ (A : Set (Om l)) := by
    rintro _ ⟨y, rfl⟩
    apply H.image_mem_of_roots J A.toSubfield
    intro z hz
    apply IntermediateField.subset_adjoin
    obtain ⟨k, hk⟩ := hN
    show z ^ M = 1
    rw [hk, pow_mul, hz, one_pow]
  have hclosed : IsClosed (A : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule A.toSubalgebra)
  intro x hx
  exact closure_minimal hrange hclosed (hdense hx)

theorem lcm_ne_zero {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : Nat.lcm l H.condN ≠ 0 :=
  Nat.lcm_ne_zero (Fact.out : l.Prime).ne_zero H.condN_ne_zero

theorem kw_le_roots {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) {Ω : Type} [Field Ω] [Algebra H.E Ω]
    {Gw : Subgroup (Ω ≃ₐ[H.E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l H.E Ω Gw O) :
    B.Kw.1 ≤ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ Nat.lcm l H.condN = 1} :=
  le_roots_of_dense H (B.j.comp (algebraMap H.E Ω)) B.Kw (lcm_ne_zero H) (Nat.dvd_lcm_right _ _) B.j_dense

theorem fix_of_roots {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω)
    (σ : Ω →+* Ω) (h : ∀ t : Ω, t ^ H.condN = 1 → σ t = t) (x : H.E) : σ (J x) = J x :=
  H.image_mem_of_roots J (RingHom.eqLocusField σ (RingHom.id Ω)) h x

theorem root_eq_of_congr {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {m : ℕ}
    (hm : ¬ l ∣ m) {u : Ω} (hu : u ^ m = 1) (h : A.valuation (u - 1) < 1) : u = 1 := by
  by_contra hne
  have hm0 : m ≠ 0 := fun e => hm (e ▸ dvd_zero l)
  have hsum : ∑ i ∈ Finset.range m, u ^ i = 0 := by
    have := mul_geom_sum u m
    rw [hu, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hvu : A.valuation u = 1 := by
    have : A.valuation u ^ m = 1 := by rw [← map_pow, hu, map_one]
    rcases lt_trichotomy (A.valuation u) 1 with h' | h' | h'
    · exact absurd this (pow_lt_one₀ zero_le h' hm0).ne
    · exact h'
    · exact absurd this (one_lt_pow₀ h' hm0).ne'
  have hpow : ∀ i : ℕ, A.valuation (u ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : u ^ (i + 1) - 1 = u ^ i * (u - 1) + (u ^ i - 1) := by ring
      rw [e]
      refine Valuation.map_add_lt _ ?_ ih
      rw [map_mul, map_pow, hvu, one_pow, one_mul]; exact h
  have hmv : A.valuation (m : Ω) < 1 := by
    have e : (m : Ω) = -∑ i ∈ Finset.range m, (u ^ i - 1) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    rw [e, Valuation.map_neg]
    exact Valuation.map_sum_lt _ one_ne_zero fun i _ => hpow i
  have hcop : Nat.Coprime l m := ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
  have e : (a : Ω) * l + b * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have : A.valuation ((a : Ω) * l + b * m) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hint a) zero_le hA
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hint b) zero_le hmv
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem fix_mul {Ω : Type} [Field Ω] (σ : Ω →+* Ω) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ∀ t : Ω, t ^ a = 1 → σ t = t) (hb : ∀ t : Ω, t ^ b = 1 → σ t = t) (h0 : a * b ≠ 0) (t : Ω)
    (ht : t ^ (a * b) = 1) : σ t = t := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow h0] at ht
    exact zero_ne_one ht
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h1 : σ (t ^ b) = t ^ b := ha _ (by rw [← pow_mul, mul_comm, ht])
  have h2 : σ (t ^ a) = t ^ a := hb _ (by rw [← pow_mul, ht])
  have e : t = (t ^ a) ^ x * (t ^ b) ^ y := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ ht0, mul_comm (a : ℤ), mul_comm (b : ℤ), hxy,
      zpow_one]
  rw [e, map_mul, map_zpow₀, map_zpow₀, h1, h2]

end UpperTheory.KStar.Cyc

end
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
section
namespace UpperTheory.Small

open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain

variable {R : Ranks} (H : Host R)

theorem not_dvd_QS {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) : ¬ l ∣ H.QS := fun h =>
  hs (Nat.mem_primeFactors.2 ⟨hl, h, H.QS_pos.ne'⟩)

theorem not_dvd_condN {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) (hq : l ≠ H.q) (hd : l ≠ H.d) : ¬ l ∣ H.condN := by
  intro h
  rcases (Nat.Prime.dvd_mul hl).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hl).1 h1 with h2 | h2
    · exact not_dvd_QS H hl hs h2
    · exact hq ((Nat.prime_dvd_prime_iff_eq hl H.hyp.1).1 h2)
  · exact hd ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).1 h1)

theorem factorization_condN_le {l : ℕ} (hl : l.Prime) :
    H.condN.factorization l ≤ max 1 (H.QS.factorization l) ∧ (l = 2 → H.condN.factorization l ≤ H.QS.factorization l) := by
  have hq := H.hyp.1
  have hd := H.hyp.2.1
  have h8 := H.hyp.2.2.1
  have h16 := H.hyp.2.2.2.1
  have e : H.condN.factorization l = H.QS.factorization l + H.q.factorization l + H.d.factorization l := by
    show (H.QS * H.q * H.d).factorization l = _
    rw [Nat.factorization_mul (mul_ne_zero H.QS_pos.ne' hq.ne_zero) hd.ne_zero,
      Nat.factorization_mul H.QS_pos.ne' hq.ne_zero]
    rfl
  rw [e, hq.factorization, hd.factorization, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h1 : H.q = l
  · have hs := factorization_eq_zero H (h1 ▸ q_not_mem H)
    have h2 : H.d ≠ l := by omega
    rw [if_pos h1, if_neg h2, hs]
    exact ⟨by simp, fun h => by omega⟩
  · by_cases h2 : H.d = l
    · have hs := factorization_eq_zero H (h2 ▸ d_not_mem H)
      rw [if_neg h1, if_pos h2, hs]
      exact ⟨by simp, fun h => by omega⟩
    · rw [if_neg h1, if_neg h2]
      exact ⟨by simp, fun _ => by simp⟩

theorem image_mem_Kur_sup {l : ℕ} [Fact l.Prime] (J : H.E →+* Om l) {s : ℕ} (hs : H.condN.factorization l ≤ s) (x : H.E) :
    J x ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} := by
  have hl : l.Prime := Fact.out
  have hN := H.toHostRaw.condN_ne_zero
  refine H.toHostRaw.image_mem_of_roots J
    (MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}).toSubfield (fun y hy => ?_) x
  set a := l ^ H.condN.factorization l with ha
  set b := H.condN / a with hb
  have hab : a * b = H.condN := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hco : Nat.Coprime a b := (Nat.coprime_ordCompl hl hN).pow_left _
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hy
    exact zero_ne_one hy
  have hbez := Nat.gcd_eq_gcd_ab a b
  rw [hco.gcd_eq_one] at hbez
  have e : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hy0, ← hbez]
    simp
  have h1 : y ^ a ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _
    ⟨b, Nat.ordCompl_pos l hN, Nat.not_dvd_ordCompl hl hN, by rw [← pow_mul, hab, hy]⟩
  have h2 : y ^ b ∈ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} := by
    refine IntermediateField.subset_adjoin _ _ ?_
    obtain ⟨c, hc⟩ := pow_dvd_pow l hs
    show (y ^ b) ^ (l ^ s) = 1
    rw [hc, ← ha, ← pow_mul, ← mul_assoc, mul_comm b a, hab, pow_mul, hy, one_pow]
  show y ∈ MaximalUnramifiedExtension l ⊔ IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1}
  rw [e]
  exact mul_mem (zpow_mem ((le_sup_left : MaximalUnramifiedExtension l ≤ _) h1) _)
    (zpow_mem ((le_sup_right : IntermediateField.adjoin ℚ_[l] {y : Om l | y ^ (l ^ s) = 1} ≤ _) h2) _)

theorem not_mem_of_ramIdx_one {l : ℕ} (hl : l.Prime) (P : HeightOneSpectrum (𝓞 H.E)) (hP : (l : 𝓞 H.E) ∈ P.asIdeal)
    (he : P.asIdeal.ramificationIdx ℤ = 1) : l ∉ H.small := by
  intro hs
  obtain ⟨P, hPp, hP0⟩ := P
  have h2 := H.toHostAx.mem_sq_of_dvd_QS H.QS_exact hl (Nat.dvd_of_mem_primeFactors hs) P hP
  have he' : P.ramificationIdx ℤ = 1 := he
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 H.E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 H.E)) (Ideal.span {(l : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hP
  have : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hPp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) P hb] at he'
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he'
  rw [hmap, Ideal.span_le]
  simpa using h2

theorem zmod_two_quadratic_ne_zero : ∀ v : ZMod 2, v ^ 2 - v + 1 ≠ 0 := by decide

theorem card_quot_ne_two (P : HeightOneSpectrum (𝓞 H.E)) : Nat.card (𝓞 H.E ⧸ P.asIdeal) ≠ 2 := by
  intro hc
  have h8 := H.hyp.2.2.1
  obtain ⟨k, hk⟩ : ∃ k, H.q = 8 * k + 3 := ⟨H.q / 8, by omega⟩
  have hx : ((1 + H.sqq) / 2) ^ 2 - (1 + H.sqq) / 2 + ((2 * k + 1 : ℕ) : H.E) = 0 := by
    have h := H.sqq_sq
    rw [hk] at h
    push_cast at h ⊢
    linear_combination (1 / 4 : H.E) * h
  have hi : IsIntegral ℤ ((1 + H.sqq) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k + 1 : ℕ) : ℤ), by monicity!, ?_⟩
    simpa using hx
  let z : 𝓞 H.E := ⟨_, hi⟩
  have hz : z ^ 2 - z + ((2 * k + 1 : ℕ) : 𝓞 H.E) = 0 := by
    apply RingOfIntegers.ext
    simp only [map_add, map_sub, map_pow, map_natCast, map_zero]
    exact hx
  haveI := P.isPrime
  haveI : Finite (𝓞 H.E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by omega)
  letI := Fintype.ofFinite (𝓞 H.E ⧸ P.asIdeal)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := ZMod.ringEquivOfPrime (𝓞 H.E ⧸ P.asIdeal) Nat.prime_two (Nat.card_eq_fintype_card.symm.trans hc)
  have h := congrArg (fun t => e.symm (Ideal.Quotient.mk P.asIdeal t)) hz
  simp only [map_add, map_sub, map_pow, map_natCast, map_zero] at h
  generalize e.symm (Ideal.Quotient.mk P.asIdeal z) = u at h
  push_cast at h
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_mul, zero_add] at h
  exact zmod_two_quadratic_ne_zero u h

end UpperTheory.Small
end


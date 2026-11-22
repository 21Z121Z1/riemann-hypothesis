import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0010
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PinFld
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.MemOfTameGeneratorFrobenius

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
section
theorem UpperTheory.Zero.LLC.artEx :
    UpperTheory.Zero.LLC.ArtEx := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨a, ha, fun b hb => ?_⟩
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds E Ω
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art hart w
  refine MonoidHom.ext fun σ => hinj ?_
  exact (hb.glob art hart σ).trans (ha.glob art hart σ).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsoUniq
section
open ValuativeRel Filter

private theorem val_natCast_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* k) (hi : Continuous i) :
    valuation k (g : k) < 1 := by
  have h1 : Tendsto (fun m : ℕ => (g : ℚ_[g]) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  have hT : Tendsto (fun m : ℕ => i ((g : ℚ_[g]) ^ m)) atTop (nhds 0) := by
    have := (hi.tendsto 0).comp h1
    rwa [map_zero] at this
  have hopen : IsOpen {x : k | valuation k x < 1} := by
    simpa [Valuation.restrict_lt_one_iff] using (valuation k).isOpen_ball 1
  have hO : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    hopen.mem_nhds (by simp)
  obtain ⟨m, hm, hm0⟩ := ((hT.eventually hO).and (eventually_gt_atTop 0)).exists
  have hm' : valuation k (g : k) ^ m < 1 := by
    have : valuation k (i ((g : ℚ_[g]) ^ m)) < 1 := hm
    rwa [map_pow, map_natCast, map_pow] at this
  by_contra hge
  exact absurd hm' (not_lt.2 (one_le_pow₀ (not_lt.1 hge)))

private theorem val_intCast_le_one {k : Type} [Field k] [ValuativeRel k] (a : ℤ) :
    valuation k (a : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (intCast_mem (valuation k).integer a)

theorem UpperTheory.Zero.LLC.isoUniq :
    UpperTheory.Zero.LLC.IsoUniq := by
  intro k _ _ _ _ _ g g' _ _ i i' hi hi'
  refine ⟨?_, fun i'' hi'' => ?_⟩
  · by_contra hne
    have hc : Nat.Coprime g g' := (Nat.coprime_primes Fact.out Fact.out).2 hne
    have hb : ((1 : ℤ) : k) = (g : k) * (Nat.gcdA g g' : k) + (g' : k) * (Nat.gcdB g g' : k) := by
      have h := Nat.gcd_eq_gcd_ab g g'
      rw [hc.gcd_eq_one] at h
      exact_mod_cast congrArg (Int.cast : ℤ → k) h
    have hv : valuation k (1 : k) < 1 := by
      have h1 : ((1 : ℤ) : k) = 1 := Int.cast_one
      rw [← h1, hb]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le (val_natCast_lt_one g i hi) (val_intCast_le_one _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le (val_natCast_lt_one g' i' hi') (val_intCast_le_one _)
    rw [map_one] at hv
    exact lt_irrefl _ hv
  · have h : (i'' : ℚ_[g] → k) = i :=
      (Padic.denseRange_ratCast g).equalizer hi'' hi (by
        funext q
        simp only [Function.comp_apply, map_ratCast])
    exact DFunLike.coe_injective h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PairCheckThreeTwo
section
open Finset

namespace UpperTheory.Zero.LLC.CharacterSumPairs

private def Reg (g n N t : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, (t * g ^ i) % N = (t * g ^ j) % N → i = j

private def Cl (g n N e t : ℕ) : Prop :=
  ∀ i < n, ∃ j < n, (t * g ^ i + e) % N = (t * g ^ j) % N

private instance (g n N t : ℕ) : Decidable (Reg g n N t) := by
  unfold Reg
  infer_instance

private instance (g n N e t : ℕ) : Decidable (Cl g n N e t) := by
  unfold Cl
  infer_instance

private def Pair (g n N e t t' : ℕ) : Prop :=
  (Reg g n N t ∧ Cl g n N e t) → (Reg g n N t' ∧ Cl g n N e t') → ∃ j < n, t' % N = (t * g ^ j) % N

private instance (g n N e t t' : ℕ) : Decidable (Pair g n N e t t') := by
  unfold Pair
  infer_instance

private theorem pairCheck_two_two : ∀ t < 2 ^ 2 - 1, ∀ t' < 2 ^ 2 - 1, Pair 2 2 (2 ^ 2 - 1) 1 t t' := by
  decide

private theorem pairCheck_three_two : ∀ t < 3 ^ 2 - 1, ∀ t' < 3 ^ 2 - 1, Pair 3 2 (3 ^ 2 - 1) 2 t t' := by
  decide

set_option maxHeartbeats 4000000 in
private theorem pairCheck_two_four : ∀ t < 2 ^ 4 - 1, ∀ t' < 2 ^ 4 - 1, Pair 2 4 (2 ^ 4 - 1) 3 t t' := by
  decide

set_option maxHeartbeats 40000000 in
private theorem pairCheck_two_six : ∀ t < 2 ^ 6 - 1, ∀ t' < 2 ^ 6 - 1, Pair 2 6 (2 ^ 6 - 1) 21 t t' := by
  decide

section

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem card_unitsK [Fintype Kˣ] (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) :
    Fintype.card Kˣ = g ^ n - 1 := by
  rw [Fintype.card_eq_nat_card, Nat.card_units, natCard_K hn hr]

private theorem exc (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (e : ℕ)
    (he : ∀ p ∈ n.primeFactors, (g ^ (n / p) - 1) ∣ e)
    (hcheck : ∀ t < g ^ n - 1, ∀ t' < g ^ n - 1, Pair g n (g ^ n - 1) e t t')
    (θ θ' : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j)
    (hθ' : ∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j)
    (hs : ∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) :
    ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  by_contra hne
  have hdisj := disj_cj hn hr θ θ' hne
  obtain ⟨D, hD1, hD2, -⟩ := exists_D (K := K) (g := g) hn hr
  have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
    intro z hz
    unfold dif
    rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
  obtain ⟨η₀, hgen, hpow⟩ := exists_gen_char (G := Kˣ)
  have hcard := card_unitsK (K := K) (g := g) hn hr
  rw [hcard] at hgen hpow
  have key : ∀ s : ℕ, (∀ i j, i < n → j < n → (η₀ ^ s) ^ g ^ i = (η₀ ^ s) ^ g ^ j → i = j) →
      (∀ ψ ∈ cj g n (η₀ ^ s), ψ * η₀ ^ e ∈ cj g n (η₀ ^ s)) →
      Reg g n (g ^ n - 1) s ∧ Cl g n (g ^ n - 1) e s := by
    intro s hreg hcl
    unfold Reg Cl
    refine ⟨fun i hi j hj hij => hreg i j hi hj ?_, fun i hi => ?_⟩
    · rw [← pow_mul, ← pow_mul, hpow]
      exact hij
    · have hm : (η₀ ^ s) ^ g ^ i ∈ cj g n (η₀ ^ s) := mem_cj.2 ⟨i, hi, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := mem_cj.1 (hcl _ hm)
      refine ⟨j, hj, ?_⟩
      rw [← pow_mul, ← pow_mul, ← pow_add, hpow] at hjeq
      exact hjeq.symm
  have hηD : ∀ z ∈ D, (η₀ ^ e) z = 1 := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := hD2 z hz
    obtain ⟨c, hc⟩ := he p hp
    rw [MonoidHom.pow_apply, ← map_pow, hc, pow_mul, hzp, one_pow, map_one]
  have hmm := mul_mem _ _ hdisj D hdif (η₀ ^ e) hηD
  obtain ⟨t, ht, rfl⟩ := hgen θ
  obtain ⟨t', ht', rfl⟩ := hgen θ'
  have hP := hcheck t ht t' ht'
  unfold Pair at hP
  obtain ⟨j, hj, hjt⟩ := hP (key t hθ (fun ψ hψ => (hmm ψ).1 hψ))
    (key t' hθ' (fun ψ hψ => (hmm ψ).2 hψ))
  exact hne ⟨j, hj, by rw [← pow_mul, hpow]; exact hjt⟩

private theorem main (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j) :
    (∃ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n ∧
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) ≠ 0) ∧
    ∀ θ' : Kˣ →* ℂˣ, (∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j) →
      (∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
        ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) →
      ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hcard := card_unitsK (K := K) (g := g) hn hr
  obtain ⟨D, hD1, hD2, hDb⟩ := exists_D (K := K) (g := g) hn hr
  have hA := card_cj hθ
  refine ⟨?_, ?_⟩
  · by_contra hno
    push_neg at hno
    have hdif : ∀ z ∉ D, dif (cj g n θ) ∅ z = 0 := by
      intro z hz
      unfold dif
      rw [sum_cj hθ, hno z (hD1 z hz)]
      simp
    have hle := card_le (cj g n θ) ∅ (Finset.disjoint_empty_right _) D hdif (by simp [hA, hn])
    rw [hA, hcard] at hle
    simp only [Finset.card_empty, add_zero] at hle
    have h1 := one_bd g n hg2 hn
    have h2 : D.card * n ≤ n * bd g n := by
      rw [mul_comm n]
      exact Nat.mul_le_mul_right n hDb
    omega
  · intro θ' hθ' hs
    by_cases hex : g = 2 ∧ n = 2 ∨ g = 3 ∧ n = 2 ∨ g = 2 ∧ n = 4 ∨ g = 2 ∧ n = 6
    · rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine exc hn hr 1 ?_ pairCheck_two_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 2 ?_ pairCheck_three_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 3 ?_ pairCheck_two_four θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 21 ?_ pairCheck_two_six θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
    · by_contra hne
      have hB := card_cj hθ'
      have hdisj := disj_cj hn hr θ θ' hne
      have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
        intro z hz
        unfold dif
        rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
      have hle := card_le _ _ hdisj D hdif (by rw [hA, hB]; omega)
      rw [hA, hB, hcard] at hle
      have h1 := two_bd g n hg2 hn hex
      have h2 : D.card * (n + n) ≤ 2 * n * bd g n := by
        calc D.card * (n + n) ≤ bd g n * (n + n) := Nat.mul_le_mul_right _ hDb
          _ = 2 * n * bd g n := by ring
      omega

end

end UpperTheory.Zero.LLC.CharacterSumPairs

theorem UpperTheory.Zero.LLC.pin :
    UpperTheory.Zero.LLC.Pin := by
  unfold UpperTheory.Zero.LLC.Pin
  intro g _ n hn K _ _ hr θ hθ
  exact UpperTheory.Zero.LLC.CharacterSumPairs.main hn hr θ hθ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameUniq
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open PositivityTheory.Rg.DzCount

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Fields

variable {g n : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem pow_period (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (z : Kˣ) :
    z ^ g ^ n = z := by
  have h1 : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hr ▸ hn)
  have h2 : Finite K := Module.finite_of_finite (ZMod g)
  have h3 : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod g) (V := K), ZMod.card, hr]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ← hc, FiniteField.pow_card]

private theorem prod_shift {M : Type*} [CommMonoid M] {n : ℕ} (hn : 0 < n) (f : ℕ → M)
    (hf : ∀ i, f (i + n) = f i) (j : ℕ) :
    ∏ i ∈ Finset.range n, f (i + j) = ∏ i ∈ Finset.range n, f i := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← ih, Finset.prod_range_succ (fun i => f (i + (j + 1))),
      Finset.prod_range_succ' (fun i => f (i + j))]
    have e1 : f (m + (j + 1)) = f (0 + j) := by
      have := hf j
      rw [show j + (m + 1) = m + (j + 1) by omega] at this
      simpa using this
    rw [e1]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    omega

private theorem orbit_of_sums (hn : 0 < n) (θ θ' : Kˣ →* ℂˣ)
    (h : ∀ z : Kˣ, ∑ i ∈ Finset.range n, ((θ (z ^ g ^ i) : ℂˣ) : ℂ) =
      ∑ i ∈ Finset.range n, ((θ' (z ^ g ^ i) : ℂˣ) : ℂ)) :
    ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  let v : (Kˣ →* ℂˣ) → (Kˣ → ℂ) := fun χ x => ((χ x : ℂˣ) : ℂ)
  have hv : LinearIndependent ℂ v := by
    have hinj : Function.Injective (fun χ : Kˣ →* ℂˣ => (Units.coeHom ℂ).comp χ) := by
      intro χ χ' e
      ext x
      exact congrArg (fun f : Kˣ →* ℂ => f x) e
    have h0 := (linearIndependent_monoidHom Kˣ ℂ).comp _ hinj
    exact h0
  by_contra hne
  push_neg at hne
  let l1 : (Kˣ →* ℂˣ) →₀ ℂ := ∑ i ∈ Finset.range n, Finsupp.single (θ ^ g ^ i) 1
  let l2 : (Kˣ →* ℂˣ) →₀ ℂ := ∑ i ∈ Finset.range n, Finsupp.single (θ' ^ g ^ i) 1
  have hl : Finsupp.linearCombination ℂ v l1 = Finsupp.linearCombination ℂ v l2 := by
    simp only [l1, l2, map_sum, Finsupp.linearCombination_single, one_smul]
    funext z
    simp only [Finset.sum_apply, v, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    have := h z
    simpa only [map_pow, Units.val_pow_eq_pow_val] using this
  have he : l1 = l2 := hv.finsuppLinearCombination_injective hl
  have h1 : l1 θ' = 0 := by
    simp only [l1, Finsupp.finset_sum_apply, Finsupp.single_apply]
    exact Finset.sum_eq_zero fun i hi => if_neg fun e => hne i (Finset.mem_range.mp hi) e.symm
  have h2 : l2 θ' ≠ 0 := by
    simp only [l2, Finsupp.finset_sum_apply, Finsupp.single_apply]
    rw [Finset.sum_boole]
    have : (Finset.filter (fun i => θ' ^ g ^ i = θ') (Finset.range n)).card ≠ 0 := by
      refine Finset.card_ne_zero.mpr ⟨0, ?_⟩
      simp [hn]
    exact_mod_cast this
  exact h2 (he ▸ h1)

end Fields

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

open TameWeilRepresentationIrreducibility in

private theorem pair_of_gen (φ : Weil h) (hφ : deg φ = -1) : ∃ t₀ : Ine (F := E) A,
    (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)), (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) →
      a.ρ (ineIncl h t₀) * a.ρ φ = a.ρ φ * a.ρ (ineIncl h t₀) ^ normV w ∧
        (a.ρ.IsIrreducible → IrrPair (a.ρ (ineIncl h t₀)) (a.ρ φ))) ∧
    ∀ (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)),
      (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) →
      (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → b.ρ σ = 1) → a.ρ.IsIrreducible → b.ρ.IsIrreducible →
      ∀ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), (∀ v, e (a.ρ (ineIncl h t₀) v) = b.ρ (ineIncl h t₀) (e v)) →
        (∀ v, e (a.ρ φ v) = b.ρ φ (e v)) → a.Iso b := by
  obtain ⟨γ0, hγ⟩ := GlobalTheory.MemTame.exists_tameGenAt E Ω w A h
  have e0 : ineIncl h (⟨γ0, hγ.1⟩ : Ine (F := E) A) = (⟨γ0, Ine_le_Weil h hγ.1⟩ : Weil h) :=
    Subtype.ext rfl
  refine ⟨⟨γ0, hγ.1⟩, ?_, ?_⟩
  · rw [e0]
    intro n a ha
    have hT : a.Tame := fun σ hσ => ha σ (wild_inertia_isWild hσ)
    refine ⟨?_, fun hirr => ?_⟩
    · have hF : deg φ⁻¹ = 1 := by simp [hφ]
      have h1 := hT.conj_eq_pow (γ := ⟨γ0, Ine_le_Weil h hγ.1⟩) (φ := φ⁻¹) hγ.1 hF
      rw [← h1, ← map_mul, ← map_mul]
      congr 1
      group
    · have := irreducible_nontrivial hirr
      refine ⟨inferInstance, fun U hM hG => ?_⟩
      have hinj : ∀ σ, Function.Injective (a.ρ σ) := fun σ =>
        (Representation.apply_bijective a.ρ σ).1
      have hall : ∀ σ, σ ∈ weilStabiliserSubgroup a.ρ U :=
        mem_of_tame_generator_frobenius a.ρ a.smooth (fun σ hσ => ha σ (wild_inertia_isWild hσ)) hγ hφ (weilStabiliserSubgroup a.ρ U)
          (fun σ hσ => mem_weil_stabiliser_iff.mpr fun v => by rw [hσ, Module.End.one_apply])
          (mem_weil_stabiliser_iff.mpr fun v => ⟨hM v, fun hv => mem_of_injective_maps_into (hinj _) hM hv⟩)
          (mem_weil_stabiliser_iff.mpr fun v => ⟨hG v, fun hv => mem_of_injective_maps_into (hinj _) hG hv⟩)
      exact irreducible_stable_bot_or_top hirr U (fun σ v hv => (mem_weil_stabiliser_iff.mp (hall σ) v).mp hv)
  · rw [e0]
    intro n m a b ha hb hirra hirrb e hγe hφe
    have hNa := irreducible_monodromy_zero a hirra
    have hNb := irreducible_monodromy_zero b hirrb
    let f : Weil h →* Module.End ℂ (Fin n → ℂ) × Module.End ℂ (Fin m → ℂ) := MonoidHom.prod a.ρ b.ρ
    have hf : IsSmooth f := IsSmooth.of_le₂ a.smooth b.smooth (fun σ h1 h2 => Prod.ext h1 h2)
    have hall : ∀ σ, σ ∈ weilIntertwiningSubgroup a.ρ b.ρ e :=
      mem_of_tame_generator_frobenius f hf
        (fun σ hσ => Prod.ext (ha σ (wild_inertia_isWild hσ)) (hb σ (wild_inertia_isWild hσ)))
        hγ hφ (weilIntertwiningSubgroup a.ρ b.ρ e)
        (fun σ hσ => mem_weil_intertwining_iff.mpr fun v => by
          have h1 : a.ρ σ = 1 := congrArg Prod.fst hσ
          have h2 : b.ρ σ = 1 := congrArg Prod.snd hσ
          rw [h1, h2, Module.End.one_apply, Module.End.one_apply])
        (mem_weil_intertwining_iff.mpr hγe) (mem_weil_intertwining_iff.mpr hφe)
    show ∃ e' : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), (∀ σ v, e' (a.ρ σ v) = b.ρ σ (e' v)) ∧ ∀ v, e' (a.N v) = b.N (e' v)
    exact ⟨e, fun σ v => mem_weil_intertwining_iff.mp (hall σ) v, fun v => by rw [hNa, hNb]; simp⟩

private theorem charpoly_of_inFor {g n m : ℕ} {K : Type} [Field K] {R : Ine (F := E) A →* Kˣ}
    {θ : Kˣ →* ℂˣ} (a : WDRep h (Fin m → ℂ)) (hV : InFor g n R θ (WD.mk a)) (t : Ine (F := E) A) :
    (a.ρ (ineIncl h t)).charpoly = ∏ j ∈ Finset.range n, (X - C ((θ (R t ^ g ^ j) : ℂˣ) : ℂ)) := by
  have := hV t
  rwa [WD.inePol_of_mem_Ine _ t.2, WD.charPol_mk] at this

private theorem eigenvalue_iff {g n m : ℕ} {K : Type} [Field K] {R : Ine (F := E) A →* Kˣ}
    {θ : Kˣ →* ℂˣ} (a : WDRep h (Fin m → ℂ)) (hV : InFor g n R θ (WD.mk a)) (t : Ine (F := E) A)
    (z : ℂ) : Module.End.HasEigenvalue (a.ρ (ineIncl h t)) z ↔
      ∃ i < n, z = ((θ (R t ^ g ^ i) : ℂˣ) : ℂ) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_of_inFor a hV t, IsRoot.def,
    eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

end UpperTheory.Zero.LLC

open UpperTheory.Zero.LLC in
theorem UpperTheory.Zero.LLC.tameUniq :
    UpperTheory.Zero.LLC.TameUniq := by
  intro E Ω _ _ _ _ _ A w h g _ n K _ _ R hR θ hθ V hV
  have hn := hR.pos
  have hr := hR.rank
  refine ⟨fun j => ?_, fun θ' hθ' => ?_, fun V' hi hi' ht ht' hV' hdet => ?_⟩
  · intro t
    rw [hV t]
    have hf : ∀ i, (X - C ((θ (R t ^ g ^ (i + n)) : ℂˣ) : ℂ) : ℂ[X]) =
        X - C ((θ (R t ^ g ^ i) : ℂˣ) : ℂ) := by
      intro i
      have e : R t ^ g ^ (i + n) = R t ^ g ^ i := by
        rw [add_comm, pow_add, mul_comm, pow_mul, pow_period hn hr]
      rw [e]
    rw [← prod_shift hn (fun i => (X - C ((θ (R t ^ g ^ i) : ℂˣ) : ℂ) : ℂ[X])) hf j]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e : (θ ^ g ^ j) (R t ^ g ^ i) = θ (R t ^ g ^ (i + j)) := by
      rw [MonoidHom.pow_apply, ← map_pow, ← pow_mul, pow_add]
    rw [e]
  · refine orbit_of_sums hn θ θ' fun z => ?_
    obtain ⟨t, rfl⟩ := hR.surj z
    have e := congrArg Polynomial.nextCoeff ((hV t).symm.trans (hθ' t))
    rw [prod_X_sub_C_nextCoeff, prod_X_sub_C_nextCoeff] at e
    exact neg_injective e
  · obtain ⟨φ, hφ⟩ : ∃ φ : Weil h, deg φ = -1 := ⟨(frob h)⁻¹, by simp [deg_frob]⟩
    obtain ⟨t₀, h1, h2⟩ := pair_of_gen φ hφ
    obtain ⟨m, a, rfl, hai, hat⟩ := PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.exists_good hi ht
    obtain ⟨m', a', rfl, hai', hat'⟩ := PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.exists_good hi' ht'
    have hdim : ∀ {m : ℕ} (b : WDRep h (Fin m → ℂ)), InFor g n R θ (WD.mk b) →
        Module.finrank ℂ (Fin m → ℂ) = n := by
      intro m b hb
      have e := congrArg Polynomial.natDegree (charpoly_of_inFor b hb t₀)
      rwa [LinearMap.charpoly_natDegree, natDegree_finset_prod_X_sub_C_eq_card, Finset.card_range] at e
    have hm := hdim a hV
    have hm' := hdim a' hV'
    obtain ⟨hc, hirr⟩ := h1 m a hat
    obtain ⟨hc', -⟩ := h1 m' a' hat'
    rw [hR.normV_eq] at hc hc'
    obtain ⟨z, hz1, hz2⟩ := st1a (Fin m → ℂ) g (a.ρ (ineIncl h t₀)) (a.ρ φ)
      (PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.isUnit_rho a _) (PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.isUnit_rho a _) hc
      (hirr hai)
    rw [hm] at hz2
    obtain ⟨i, hin, hzi⟩ := (eigenvalue_iff a hV t₀ z).mp hz1
    have hz3 : Module.End.HasEigenvalue (a'.ρ (ineIncl h t₀)) (z ^ g ^ (n - i)) := by
      refine (eigenvalue_iff a' hV' t₀ _).mpr ⟨0, hn, ?_⟩
      rw [hzi, ← Units.val_pow_eq_pow_val, ← map_pow, ← pow_mul, ← pow_add,
        Nat.add_sub_of_le hin.le, pow_period hn hr]
      simp
    have hd : LinearMap.det (a.ρ φ) = LinearMap.det (a'.ρ φ) := by
      rw [← PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.eig_prod, ← PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.eig_prod]
      exact hdet φ
    obtain ⟨e, he1, he2⟩ := st1b (Fin m → ℂ) (Fin m' → ℂ) g n (n - i) _ (a.ρ φ) _ (a'.ρ φ) z hn hm hm'
      (PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.isUnit_rho a _) (PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.isUnit_rho a' _) hc hc' hz2 hz1 hz3 hd
    exact (WD.mk_eq_mk.mpr (h2 m m' a a' hat hat' hai hai' e he1 he2)).symm

end
end


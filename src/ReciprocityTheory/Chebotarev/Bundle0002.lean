import Mathlib

-- bundled from ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt
section
namespace ReciprocityTheory.Cheb

open Polynomial NumberField

private theorem setOf_prime_ramified_finite (K : Type*) [Field K] [NumberField K] :
    {p : ℕ | p.Prime ∧ ∃ (P : Ideal (𝓞 K)) (_ : P.IsPrime), (p : 𝓞 K) ∈ P ∧
      ¬ Algebra.IsUnramifiedAt ℤ P}.Finite := by
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hF := Ideal.finite_factors (I := differentIdeal ℤ (𝓞 K)) (by simpa using hD)

  have hsub : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      {p : ℕ | p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal}.Subsingleton := by
    intro v p ⟨hp, hpv⟩ q ⟨hq, hqv⟩
    by_contra hne
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
    have hc : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := by
      have := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 K))
      simpa using this
    obtain ⟨a, b, hab⟩ := hc
    have h1 : (1 : 𝓞 K) ∈ v.asIdeal := hab ▸
      v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpv) (v.asIdeal.mul_mem_left b hqv)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  refine (hF.biUnion (fun v _ => (hsub v).finite)).subset ?_
  rintro p ⟨hp, P, hPp, hpP, hnr⟩
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  exact Set.mem_biUnion (x := ⟨P, hPp, hP0⟩) (dvd_differentIdeal_iff.mpr hnr) ⟨hp, hpP⟩

theorem exists_forall_isUnramifiedAt (K : Type*) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N < p → ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (p : 𝓞 K) ∈ P →
      Algebra.IsUnramifiedAt ℤ P := by
  obtain ⟨N, hN⟩ := (setOf_prime_ramified_finite K).bddAbove
  refine ⟨N, fun p hp hpN P _ hpP => ?_⟩
  by_contra h
  exact absurd (hN ⟨hp, P, inferInstance, hpP, h⟩) (not_le.mpr hpN)

theorem natCast_notMem_sq_of_isUnramifiedAt {K : Type*} [Field K] [NumberField K] {l : ℕ}
    (hl : l.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [Algebra.IsUnramifiedAt ℤ P] : (l : 𝓞 K) ∉ P ^ 2 := by
  intro hl2
  have hlP : (l : 𝓞 K) ∈ P := Ideal.pow_le_self two_ne_zero hl2
  have hl0 : (l : 𝓞 K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hlP
    exact hl0 hlP
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {(l : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa [Ideal.under, Ideal.mem_comap] using hlP
  have hunder : Ideal.span {(l : ℤ)} = P.under ℤ :=
    hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top hle
  haveI : P.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hunder⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hmap0 : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(l : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  have hcount := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {(l : ℤ)}) P hmap0
  rw [Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcount

  have hdvd : P ^ 2 ∣ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(l : ℤ)}) := by
    rw [Ideal.dvd_iff_le, hmap, Ideal.span_le, Set.singleton_subset_iff]
    exact hl2
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using hP0)
  have hnf := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP2
    (by simpa using hmap0)).mp hdvd
  have hc := Multiset.count_le_of_le P hnf
  rw [← hcount, UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 inferInstance).irreducible,
    normalize_eq] at hc
  simp at hc

theorem cyclotomic_irreducible_of_isUnramifiedAt {K : Type*} [Field K] [NumberField K] {l : ℕ}
    (hl : l.Prime) (P : Ideal (𝓞 K)) [P.IsPrime] (hlP : (l : 𝓞 K) ∈ P)
    [Algebra.IsUnramifiedAt ℤ P] : Irreducible (cyclotomic l K) := by
  haveI := Fact.mk hl
  have hl2 := natCast_notMem_sq_of_isUnramifiedAt hl P

  have hE := cyclotomic_comp_X_add_one_isEisensteinAt l
  have hX1 : (X + 1 : ℤ[X]).Monic := by simpa using monic_X_add_C (1 : ℤ)
  have hX1d : (X + 1 : ℤ[X]).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ℤ)
  have hmon : ((cyclotomic l ℤ).comp (X + 1)).Monic :=
    (cyclotomic.monic l ℤ).comp hX1 (by rw [hX1d]; exact one_ne_zero)
  have hg : ((cyclotomic l ℤ).comp (X + 1)).map (Int.castRingHom (𝓞 K)) = (cyclotomic l (𝓞 K)).comp (X + 1) := by
    simp [Polynomial.map_comp, map_cyclotomic]
  have hdeg : (((cyclotomic l ℤ).comp (X + 1)).map (Int.castRingHom (𝓞 K))).natDegree =
      ((cyclotomic l ℤ).comp (X + 1)).natDegree := hmon.natDegree_map _
  have hc0 : ((cyclotomic l ℤ).comp (X + 1)).coeff 0 = l := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp [eval_one_cyclotomic_prime]
  have hE' : ((cyclotomic l (𝓞 K)).comp (X + 1)).IsEisensteinAt P := by
    rw [← hg]
    refine ⟨?_, ?_, ?_⟩
    · rw [(hmon.map _).leadingCoeff]
      exact (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top inferInstance)
    · intro n hn
      rw [hdeg] at hn
      rw [coeff_map]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hE.mem hn)
      rw [← hc, smul_eq_mul, map_mul, map_natCast]
      exact P.mul_mem_left _ hlP
    · rw [coeff_map, hc0, map_natCast]
      exact hl2
  have hpos : 0 < ((cyclotomic l (𝓞 K)).comp (X + 1)).natDegree := by
    rw [← hg, hdeg, natDegree_comp, natDegree_cyclotomic, hX1d, mul_one, Nat.totient_prime hl]
    exact Nat.sub_pos_of_lt hl.one_lt
  have hmon' : ((cyclotomic l (𝓞 K)).comp (X + 1)).Monic := by
    rw [← hg]
    exact hmon.map _
  have hirr1 := hE'.irreducible inferInstance hmon'.isPrimitive hpos
  have hcomp : (algEquivAevalXAddC (1 : 𝓞 K)) (cyclotomic l (𝓞 K)) = (cyclotomic l (𝓞 K)).comp (X + 1) := by
    rw [algEquivAevalXAddC_apply, ← comp_eq_aeval, map_one]
  have hirr2 : Irreducible (cyclotomic l (𝓞 K)) := by
    rw [← hcomp] at hirr1
    exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : 𝓞 K)).toMulEquiv).mp hirr1
  have := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := K)
    (cyclotomic.monic l (𝓞 K))).mp hirr2
  rwa [map_cyclotomic] at this

theorem natCast_mem_of_liesOver {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (P : Ideal (𝓞 K)) [P.LiesOver (Ideal.span {(p : ℤ)})] : (p : 𝓞 K) ∈ P := by
  have h : (p : ℤ) ∈ P.under ℤ := by
    rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)})]
    exact Ideal.mem_span_singleton_self _
  simpa [Ideal.under, Ideal.mem_comap] using h

theorem exists_forall_isUnramifiedAt_of_liesOver (K : Type*) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N < p → ∀ (P : Ideal (𝓞 K)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], Algebra.IsUnramifiedAt ℤ P := by
  obtain ⟨N, hN⟩ := exists_forall_isUnramifiedAt K
  exact ⟨N, fun p hp hpN P _ _ => hN p hp hpN P (natCast_mem_of_liesOver P)⟩

theorem cyclotomic_irreducible_of_forall_isUnramifiedAt {K : Type*} [Field K] [NumberField K]
    {l : ℕ} (hl : l.Prime)
    (h : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (l : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt ℤ P) :
    Irreducible (cyclotomic l K) := by
  have hnu : ¬ IsUnit (l : 𝓞 K) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [show (l : 𝓞 K) = algebraMap ℤ (𝓞 K) (l : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq] at h1
    simp at h1
    exact hl.one_lt.ne' h1
  obtain ⟨M, hM, hlM⟩ := Ideal.exists_le_maximal (Ideal.span {(l : 𝓞 K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hlM' : (l : 𝓞 K) ∈ M := hlM (Ideal.mem_span_singleton_self _)
  haveI := h M hlM'
  exact cyclotomic_irreducible_of_isUnramifiedAt hl M hlM'

theorem exists_forall_cyclotomic_irreducible (K : Type*) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ l : ℕ, l.Prime → N < l → Irreducible (cyclotomic l K) := by
  obtain ⟨N, hN⟩ := exists_forall_isUnramifiedAt K
  exact ⟨N, fun l hl hlN => cyclotomic_irreducible_of_forall_isUnramifiedAt hl
    (fun P _ hP => hN l hl hlN P hP)⟩

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.LatSum
section
open Set

namespace ReciprocityTheory.Cheb

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def latSumEquiv (Λ₀ Λ' : Submodule ℤ V) (hle : Λ' ≤ Λ₀) (reps : Finset V)
    (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂) :
    Λ' × reps ≃ Λ₀ :=
  Equiv.ofBijective (fun p => ⟨(p.1 : V) + (p.2 : V), Λ₀.add_mem (hle p.1.2) (hmem _ p.2.2)⟩) (by
    constructor
    · rintro ⟨l₁, β₁⟩ ⟨l₂, β₂⟩ h
      simp only [Subtype.mk.injEq] at h
      have hβ : (β₁ : V) = β₂ := huniq _ β₁.2 _ β₂.2 (by
        have e : (β₁ : V) - β₂ = l₂ - l₁ := by
          rw [sub_eq_sub_iff_add_eq_add, add_comm (β₁ : V), h]
        rw [e]; exact Λ'.sub_mem l₂.2 l₁.2)
      have hl : (l₁ : V) = l₂ := by rw [hβ] at h; exact add_right_cancel h
      exact Prod.ext (Subtype.ext hl) (Subtype.ext hβ)
    · rintro ⟨α, hα⟩
      obtain ⟨l, hl, β, hβ, rfl⟩ := hcover α hα
      exact ⟨(⟨l, hl⟩, ⟨β, hβ⟩), rfl⟩)

theorem tsum_latSum_eq (Λ₀ Λ' : Submodule ℤ V) (hle : Λ' ≤ Λ₀) (reps : Finset V)
    (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (g : V → ℂ) (hg : Summable fun α : Λ₀ => g α) :
    ∑' α : Λ₀, c' α * g α = ∑' l : Λ', ∑ β ∈ reps, c' β * (g (l + β) - g l) := by
  set e := latSumEquiv Λ₀ Λ' hle reps hmem hcover huniq
  have hc : ∀ α : Λ₀, ‖c' α‖ ≤ ∑ β ∈ reps, ‖c' β‖ := by
    rintro ⟨α, hα⟩
    obtain ⟨l, hl, β, hβ, rfl⟩ := hcover α hα
    rw [hper l hl β hβ]
    exact Finset.single_le_sum (f := fun β => ‖c' β‖) (fun _ _ => norm_nonneg _) hβ
  have hcg : Summable fun α : Λ₀ => c' α * g α := by
    refine summable_norm_iff.mp (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => ?_)
      ((summable_norm_iff.mpr hg).mul_left (∑ β ∈ reps, ‖c' β‖)))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc α) (norm_nonneg _)
  have hs : Summable fun p : Λ' × reps => c' (e p) * g (e p) := (e.summable_iff).mpr hcg
  rw [← e.tsum_eq, hs.tsum_prod]
  refine tsum_congr fun l => ?_
  rw [tsum_fintype]
  have h1 : ∀ β : reps, (fun α : Λ₀ => c' α * g α) (e (l, β)) = c' β * g (l + β) := by
    rintro ⟨β, hβ⟩
    show c' ((l : V) + β) * g ((l : V) + β) = _
    rw [hper l l.2 β hβ]
  simp only [h1]
  rw [Finset.sum_coe_sort reps (fun β => c' β * g (l + β))]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmean, zero_mul, sub_zero]

variable [FiniteDimensional ℝ V]

theorem exists_continuousOn_latticeSum (Λ₀ Λ' : Submodule ℤ V) [DiscreteTopology Λ₀] (hle : Λ' ≤ Λ₀)
    (reps : Finset V) (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (G : ℝ → V → ℂ) (r : ℝ) (hr : r < -(Module.finrank ℤ Λ₀ : ℝ))
    (hdiff : ∃ R₀ C : ℝ, ∀ s ∈ Icc (1 : ℝ) 2, ∀ β ∈ reps, ∀ x ∈ Λ', R₀ ≤ ‖x‖ →
      ‖G s (x + β) - G s x‖ ≤ C * ‖x‖ ^ r)
    (K : ℝ) (hbound : ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ Λ₀, ‖G s x‖ ≤ K)
    (hsum : ∀ s ∈ Ioc (1 : ℝ) 2, Summable fun α : Λ₀ => G s α)
    (hcont : ∀ x ∈ Λ₀, ContinuousOn (fun s => G s x) (Icc 1 2)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2, F s = ∑' α : Λ₀, c' α * G s α := by
  classical
  obtain ⟨R₀, C, hRC⟩ := hdiff
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set A := ∑ β ∈ reps, ‖c' β‖ with hAdef
  have hr0 : r < 0 := lt_of_lt_of_le hr (neg_nonpos.mpr (Nat.cast_nonneg _))
  set X := |C| + 2 * |K| * R ^ (-r) with hXdef
  have hX : 0 ≤ X := by positivity
  let u : Λ' → ℝ := fun l => A * X * ‖(l : V)‖ ^ r + if (l : V) = 0 then A * (2 * |K|) else 0
  have hu : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.mul_left (A * X) ?_
      have h0 := ZLattice.summable_norm_rpow Λ₀ r hr
      have h1 := h0.comp_injective (i := fun l : Λ' => (⟨l, hle l.2⟩ : Λ₀))
        (fun a b h => Subtype.ext (congrArg Subtype.val h :))
      exact h1
    · apply summable_of_ne_finset_zero (s := {0})
      intro l hl
      have : (l : V) ≠ 0 := by simpa using hl
      simp [this]
  refine ⟨fun s => ∑' l : Λ', ∑ β ∈ reps, c' β * (G s (l + β) - G s l), ?_, ?_⟩
  · refine continuousOn_tsum (u := u) (fun l => ?_) hu (fun l s hs => ?_)
    · refine continuousOn_finsetSum _ fun β hβ => ?_
      exact continuousOn_const.mul
        ((hcont _ (Λ₀.add_mem (hle l.2) (hmem β hβ))).sub (hcont _ (hle l.2)))
    · have key : ∀ β ∈ reps, ‖G s (l + β) - G s l‖ ≤
          X * ‖(l : V)‖ ^ r + if (l : V) = 0 then 2 * |K| else 0 := by
        intro β hβ
        have h2K : ‖G s (l + β) - G s l‖ ≤ 2 * |K| := by
          refine (norm_sub_le _ _).trans ?_
          have := hbound s hs _ (Λ₀.add_mem (hle l.2) (hmem β hβ))
          have := hbound s hs _ (hle l.2)
          have := le_abs_self K
          linarith
        have hpow : 0 ≤ ‖(l : V)‖ ^ r := Real.rpow_nonneg (norm_nonneg _) _
        by_cases hl0 : (l : V) = 0
        · rw [if_pos hl0]
          nlinarith
        rw [if_neg hl0, add_zero]
        by_cases hR : R ≤ ‖(l : V)‖
        · have := hRC s hs β hβ l l.2 ((le_max_left _ _).trans hR)
          have hC : C * ‖(l : V)‖ ^ r ≤ |C| * ‖(l : V)‖ ^ r :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hpow
          have : 0 ≤ 2 * |K| * R ^ (-r) * ‖(l : V)‖ ^ r := by positivity
          nlinarith
        · rw [not_le] at hR
          have hlpos : 0 < ‖(l : V)‖ := norm_pos_iff.mpr hl0
          have hRr : R ^ r ≤ ‖(l : V)‖ ^ r := Real.rpow_le_rpow_of_nonpos hlpos hR.le hr0.le
          have hone : R ^ (-r) * R ^ r = 1 := by
            rw [Real.rpow_neg hRpos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hRpos r).ne']
          have hRn : 0 ≤ R ^ (-r) := Real.rpow_nonneg hRpos.le _
          have h3 : 2 * |K| ≤ 2 * |K| * R ^ (-r) * ‖(l : V)‖ ^ r := by
            calc 2 * |K| = 2 * |K| * (R ^ (-r) * R ^ r) := by rw [hone, mul_one]
              _ ≤ 2 * |K| * (R ^ (-r) * ‖(l : V)‖ ^ r) := by gcongr
              _ = _ := by ring
          have : 0 ≤ |C| * ‖(l : V)‖ ^ r := by positivity
          nlinarith
      calc ‖∑ β ∈ reps, c' β * (G s (l + β) - G s l)‖
          ≤ ∑ β ∈ reps, ‖c' β‖ * ‖G s (l + β) - G s l‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp only [norm_mul]
        _ ≤ ∑ β ∈ reps, ‖c' β‖ * (X * ‖(l : V)‖ ^ r + if (l : V) = 0 then 2 * |K| else 0) :=
            Finset.sum_le_sum fun β hβ => mul_le_mul_of_nonneg_left (key β hβ) (norm_nonneg _)
        _ = u l := by
            rw [← Finset.sum_mul]
            simp only [u]
            split_ifs <;> ring
  · intro s hs
    exact (tsum_latSum_eq Λ₀ Λ' hle reps hmem hcover huniq c' hper hmean (G s) (hsum s hs)).symm

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.NZIdeal
section
open NumberField

namespace ReciprocityTheory.Cheb

noncomputable section

abbrev NZIdeal (E : Type) [Field E] [NumberField E] : Type := {a : Ideal (𝓞 E) // a ≠ ⊥}

abbrev Prm (E : Type) [Field E] [NumberField E] : Type := IsDedekindDomain.HeightOneSpectrum (𝓞 E)

def Nrm {E : Type} [Field E] [NumberField E] (q : Prm E) : ℕ := Ideal.absNorm q.asIdeal

def Lser (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' a : NZIdeal E, χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))

def Psum (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' q : Prm E, χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))

def abelian₂ (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' q : Prm E, -Complex.log (1 - χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))

def PE (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-s)

def Pcl (E : Type) [Field E] [NumberField E] (l : ℕ) (a : ZMod l) (s : ℝ) : ℝ :=
  ∑' q : Prm E, if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0

end

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.NoWind
section
namespace ReciprocityTheory.Cheb

open Filter Topology Set Complex

theorem isDiscrete_exp_fiber (c : ℂ) : IsDiscrete {w : ℂ | Complex.exp w = c} := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  refine ⟨Metric.ball y 1, Metric.isOpen_ball, ?_⟩
  ext w
  simp only [mem_inter_iff, Metric.mem_ball, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hw, hwc⟩
    have hexp : Complex.exp w = Complex.exp y := hwc.trans hy.symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      simpa using hn
    have hd : dist w y = |(n : ℝ)| * (2 * Real.pi) := by
      rw [dist_eq_norm, hn, add_sub_cancel_left, norm_mul, Complex.norm_intCast]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
    have := Real.pi_gt_three
    nlinarith
  · rintro rfl
    exact ⟨Metric.mem_ball_self one_pos, hy⟩

theorem bounded_of_tendsto_exp {abelian₂ : ℝ → ℂ} {L1 : ℂ} (hcont : ContinuousOn abelian₂ (Ioc 1 2))
    (hL1 : L1 ≠ 0) (hlim : Tendsto (fun s => Complex.exp (abelian₂ s)) (𝓝[>] 1) (𝓝 L1)) :
    ∃ C, ∀ s ∈ Ioc (1 : ℝ) 2, ‖abelian₂ s‖ ≤ C := by

  have hslitB : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2), z ∈ slitPlane := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    exact mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_le.mp (this.trans hz)).1]))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (f := Complex.log) (fun z hz => (continuousAt_clog (hslitB z hz)).continuousWithinAt)

  have hlim' : Tendsto (fun s => Complex.exp (abelian₂ s) / L1) (𝓝[>] 1) (𝓝 1) := by
    simpa [div_self hL1] using hlim.div_const L1
  have hev := hlim'.eventually (Metric.closedBall_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu1 : (1 : ℝ) < u := hu1
  set t : ℝ := min ((1 + u) / 2) 2 with ht
  have ht1 : 1 < t := lt_min (by linarith) (by norm_num)
  have htu : t < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : t ≤ 2 := min_le_right _ _
  have hSsub : Ioc 1 t ⊆ Ioc (1 : ℝ) 2 := Ioc_subset_Ioc_right ht2
  have hball : ∀ s ∈ Ioc 1 t, Complex.exp (abelian₂ s) / L1 ∈ Metric.closedBall (1 : ℂ) (1 / 2) :=
    fun s hs => hu ⟨hs.1, lt_of_le_of_lt hs.2 htu⟩

  set g : ℝ → ℂ := fun s => abelian₂ s - Complex.log (Complex.exp (abelian₂ s) / L1) with hg
  have hgc : ContinuousOn g (Ioc 1 t) := by
    intro s hs
    have h1 : ContinuousWithinAt abelian₂ (Ioc 1 t) s := (hcont s (hSsub hs)).mono hSsub
    have h2 : ContinuousWithinAt (fun s => Complex.exp (abelian₂ s) / L1) (Ioc 1 t) s :=
      (Complex.continuous_exp.continuousAt.comp_continuousWithinAt h1).div_const L1
    have h3 : ContinuousWithinAt (fun s => Complex.log (Complex.exp (abelian₂ s) / L1)) (Ioc 1 t) s :=
      (continuousAt_clog (hslitB _ (hball s hs))).comp_continuousWithinAt
        (f := fun s => Complex.exp (abelian₂ s) / L1) h2
    exact h1.sub h3
  have hmaps : MapsTo g (Ioc 1 t) {w : ℂ | Complex.exp w = L1} := by
    intro s _
    have hne : Complex.exp (abelian₂ s) / L1 ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) hL1
    simp only [mem_ofPred_eq, hg, Complex.exp_sub, Complex.exp_log hne]
    field_simp [Complex.exp_ne_zero]
  obtain ⟨c, -, hc⟩ := isPreconnected_Ioc.eqOn_const_of_mapsTo (isDiscrete_exp_fiber L1) hgc hmaps
    ⟨Complex.log L1, Complex.exp_log hL1⟩

  obtain ⟨C2, hC2⟩ := (isCompact_Icc : IsCompact (Icc t 2)).exists_bound_of_continuousOn
    (hcont.mono (Icc_subset_Ioc_iff ht2 |>.mpr ⟨ht1, le_rfl⟩))
  refine ⟨max (‖c‖ + B) C2, fun s hs => ?_⟩
  rcases le_or_gt s t with hst | hst
  · have hs' : s ∈ Ioc 1 t := ⟨hs.1, hst⟩
    have hgs : g s = c := hc hs'
    have hL : abelian₂ s = c + Complex.log (Complex.exp (abelian₂ s) / L1) := by
      rw [← hgs, hg]; ring
    calc ‖abelian₂ s‖ = ‖c + Complex.log (Complex.exp (abelian₂ s) / L1)‖ := by rw [← hL]
      _ ≤ ‖c‖ + ‖Complex.log (Complex.exp (abelian₂ s) / L1)‖ := norm_add_le _ _
      _ ≤ ‖c‖ + B := by gcongr; exact hB _ (hball s hs')
      _ ≤ _ := le_max_left _ _
  · exact (hC2 s ⟨hst.le, hs.2⟩).trans (le_max_right _ _)

theorem bdd_of_exp_tendsto (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 1)) (L1 : ℂ) (hL : L1 ≠ 0)
    (h : Tendsto (fun s => Complex.exp (f s)) (𝓝[>] 1) (𝓝 L1)) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖f s‖ ≤ C := by
  obtain ⟨C, hC⟩ := bounded_of_tendsto_exp (hf.mono Set.Ioc_subset_Ioi_self) hL h
  exact ⟨C, Filter.mem_of_superset (Ioc_mem_nhdsGT one_lt_two) hC⟩

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.NormCongr
section
namespace ReciprocityTheory.Cheb

open Module

theorem norm_modEq_of_sub_mem_span {S : Type*} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (m : ℤ) {α α' : S} (h : α - α' ∈ Ideal.span {(m : S)}) :
    Algebra.norm ℤ α ≡ Algebra.norm ℤ α' [ZMOD m] := by
  classical
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.mp h
  have hα : α = α' + algebraMap ℤ S m * β := by
    rw [algebraMap_int_eq, eq_intCast, mul_comm, hβ]; ring
  rw [Int.modEq_iff_dvd, ← Int.natAbs_dvd, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
  symm
  let b := Module.Free.chooseBasis ℤ S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, hα, map_add, map_mul,
    AlgHom.commutes]
  have key : ∀ M : Matrix (Module.Free.ChooseBasisIndex ℤ S) (Module.Free.ChooseBasisIndex ℤ S) ℤ,
      ((Int.castRingHom (ZMod m.natAbs)) M.det : ZMod m.natAbs) = ((Int.castRingHom (ZMod m.natAbs)).mapMatrix M).det :=
    fun M => RingHom.map_det _ M
  simp only [eq_intCast] at key
  rw [key, key]
  congr 1
  have h0 : ((m : ZMod m.natAbs)) = 0 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub 0 m m.natAbs).mpr (by simp)
    simpa using this.symm
  have hM : (Int.castRingHom (ZMod m.natAbs)).mapMatrix
      ((algebraMap ℤ (Matrix (Free.ChooseBasisIndex ℤ S) (Free.ChooseBasisIndex ℤ S) ℤ)) m) = 0 := by
    rw [eq_intCast, map_intCast]
    ext i j
    by_cases hij : i = j <;> simp [hij, h0, Matrix.diagonal, ← Matrix.diagonal_intCast']
  rw [map_add, map_mul, hM, zero_mul, add_zero]

theorem absNorm_dvd_algebraNorm {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] {b : Ideal S} {α : S} (h : α ∈ b) :
    (Ideal.absNorm b : ℤ) ∣ Algebra.norm ℤ α :=
  Ideal.absNorm_dvd_norm_of_mem h

theorem norm_div_absNorm_modEq {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (l : ℤ) {b : Ideal S} {α α' : S} (hα : α ∈ b) (hα' : α' ∈ b)
    (h : α - α' ∈ Ideal.span {((l * (Ideal.absNorm b : ℤ) : ℤ) : S)}) :
    Algebra.norm ℤ α / (Ideal.absNorm b : ℤ) ≡ Algebra.norm ℤ α' / (Ideal.absNorm b : ℤ) [ZMOD l] := by
  have hm := norm_modEq_of_sub_mem_span _ h
  obtain ⟨a, ha⟩ := absNorm_dvd_algebraNorm hα
  obtain ⟨c, hc⟩ := absNorm_dvd_algebraNorm hα'
  rw [ha, hc] at hm ⊢
  by_cases hN : (Ideal.absNorm b : ℤ) = 0
  · rw [hN, Int.ediv_zero, Int.ediv_zero]
  rw [Int.mul_ediv_cancel_left _ hN, Int.mul_ediv_cancel_left _ hN]
  rw [mul_comm l] at hm
  exact Int.ModEq.mul_left_cancel' hN hm

example {E : Type*} [Field E] [NumberField E] (m : ℤ) {α α' : NumberField.RingOfIntegers E}
    (h : α - α' ∈ Ideal.span {(m : NumberField.RingOfIntegers E)}) :
    Algebra.norm ℤ α ≡ Algebra.norm ℤ α' [ZMOD m] := norm_modEq_of_sub_mem_span m h

example {E : Type*} [Field E] [NumberField E] (l : ℤ) {b : Ideal (NumberField.RingOfIntegers E)}
    {α α' : NumberField.RingOfIntegers E} (hα : α ∈ b) (hα' : α' ∈ b)
    (h : α - α' ∈ Ideal.span {((l * (Ideal.absNorm b : ℤ) : ℤ) : NumberField.RingOfIntegers E)}) :
    Algebra.norm ℤ α / (Ideal.absNorm b : ℤ) ≡ Algebra.norm ℤ α' / (Ideal.absNorm b : ℤ) [ZMOD l] :=
  norm_div_absNorm_modEq l hα hα' h

end ReciprocityTheory.Cheb
end


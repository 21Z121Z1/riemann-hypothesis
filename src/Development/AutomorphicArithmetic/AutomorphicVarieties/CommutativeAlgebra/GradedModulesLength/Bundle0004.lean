import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.OzTwoMulEqPow
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

private theorem absR {w a b c : ℤ} {z f : A} (hz : z ∈ 𝒜 w) (hf : f ∈ 𝒜 a * 𝒜 b) (hc : c = w + b) :
    z * f ∈ 𝒜 a * 𝒜 c := by
  subst hc
  refine Submodule.mul_induction_on hf (fun p hp q hq => ?_) (fun p q hp hq => ?_)
  · rw [mul_left_comm]
    exact Submodule.mul_mem_mul hp (SetLike.GradedMul.mul_mem hz hq)
  · rw [mul_add]; exact add_mem hp hq

private theorem absL {w a b c d : ℤ} {z f : A} (hz : z ∈ 𝒜 w) (hf : f ∈ 𝒜 a * 𝒜 b) (hc : c = w + a) (hd : d = b) :
    z * f ∈ 𝒜 c * 𝒜 d := by
  subst hd
  rw [mul_comm (𝒜 a)] at hf
  rw [mul_comm (𝒜 c)]
  exact absR 𝒜 hz hf hc

private def dec (ε j : ℤ) : Submodule O A where
  carrier := {f | f ∈ 𝒜 j ∧ (1 ≤ ε * j → f ∈ 𝒜 ε * 𝒜 (j - ε) ⊔ 𝒜 (2 * ε) * 𝒜 (j - 2 * ε)) ∧
    (2 ≤ ε * j → f ∈ 𝒜 (2 * ε) * 𝒜 (j - 2 * ε))}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, fun h => add_mem (ha.2.1 h) (hb.2.1 h), fun h => add_mem (ha.2.2 h) (hb.2.2 h)⟩
  zero_mem' := ⟨zero_mem _, fun _ => zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ ha := ⟨Submodule.smul_mem _ c ha.1, fun h => Submodule.smul_mem _ c (ha.2.1 h),
    fun h => Submodule.smul_mem _ c (ha.2.2 h)⟩

private theorem dec_mul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {w j : ℤ} (hw : -2 ≤ w ∧ w ≤ 2) {z f : A} (hz : z ∈ 𝒜 w)
    (hf : f ∈ dec 𝒜 ε j) : z * f ∈ dec 𝒜 ε (w + j) := by
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨SetLike.GradedMul.mul_mem hz h0, ?_⟩
  by_cases c2 : w = 2 * ε
  · subst c2
    have : z * f ∈ 𝒜 (2 * ε) * 𝒜 (2 * ε + j - 2 * ε) := by
      rw [add_sub_cancel_left]; exact Submodule.mul_mem_mul hz h0
    exact ⟨fun _ => Submodule.mem_sup_right this, fun _ => this⟩
  by_cases c1 : w = ε
  · subst c1
    refine ⟨fun _ => Submodule.mem_sup_left ?_, fun h => ?_⟩
    · rw [add_sub_cancel_left]; exact Submodule.mul_mem_mul hz h0
    · obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))
      rw [mul_add]
      exact add_mem (absL 𝒜 hz hp (by ring) (by ring)) (absR 𝒜 hz hq (by ring))
  refine ⟨fun h => ?_, fun h => absR 𝒜 hz (h2 (by rcases hε with rfl | rfl <;> omega)) (by ring)⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))
  rw [mul_add]
  exact add_mem (Submodule.mem_sup_left (absR 𝒜 hz hp (by ring))) (Submodule.mem_sup_right (absR 𝒜 hz hq (by ring)))

private theorem dec_all [IsLocalRing O] {x : A →ₐ[O] O} (hx : IsWRing 𝒜 x) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {j : ℤ} {f : A} (hf : f ∈ 𝒜 j) : f ∈ dec 𝒜 ε j := by
  obtain ⟨s, hs, htop⟩ := hx.gen
  have gen : ∀ (w : ℤ), (-2 ≤ w ∧ w ≤ 2) → ∀ z ∈ 𝒜 w, ∀ g ∈ ⨆ i, dec 𝒜 ε i, z * g ∈ ⨆ i, dec 𝒜 ε i := by
    intro w hw z hz g hg
    refine Submodule.iSup_induction (motive := fun g => z * g ∈ ⨆ i, dec 𝒜 ε i) _ hg (fun i g hg => ?_) (by simp)
      (fun a b ha hb => by rw [mul_add]; exact add_mem ha hb)
    exact Submodule.mem_iSup_of_mem _ (dec_mul 𝒜 hε hw hz hg)
  have key : ∀ a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ s), ∀ g ∈ ⨆ i, dec 𝒜 ε i, a * g ∈ ⨆ i, dec 𝒜 ε i := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · exact gen 0 (by omega) a ha
      · rcases hs a ha with h | h | h | h <;> exact gen _ (by omega) a h
    | algebraMap c =>
      intro g hg
      rw [← Algebra.smul_def]; exact Submodule.smul_mem _ c hg
    | add a b _ _ ha hb =>
      intro g hg
      rw [add_mul]; exact add_mem (ha g hg) (hb g hg)
    | mul a b _ _ ha hb =>
      intro g hg
      rw [mul_assoc]; exact ha _ (hb g hg)
  have h1 : (1 : A) ∈ dec 𝒜 ε 0 := ⟨SetLike.GradedOne.one_mem, fun h => by omega, fun h => by omega⟩
  have h2 := key f (htop ▸ Algebra.mem_top) 1 (Submodule.mem_iSup_of_mem _ h1)
  rw [mul_one] at h2
  have h3 : ∀ g ∈ ⨆ i, dec 𝒜 ε i, (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j := by
    intro g hg
    refine Submodule.iSup_induction (motive := fun g => (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j) _ hg
      (fun i g hg => ?_) (by simp) (fun a b ha hb => ?_)
    · by_cases hi : i = j
      · subst hi
        rwa [DirectSum.decompose_of_mem_same 𝒜 hg.1]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 hg.1 hi]; exact zero_mem _
    · simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem ha hb
  have h4 := h3 f h2
  rwa [DirectSum.decompose_of_mem_same 𝒜 hf] at h4

private theorem pow_eps [IsLocalRing O] {x : A →ₐ[O] O} (hx : IsWRing 𝒜 x) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (n : ℕ) : oz 𝒜 (2 * ε * n) = oz 𝒜 (2 * ε) ^ n := by
  induction n with
  | zero =>
    ext f
    simp only [Nat.cast_zero, mul_zero, pow_zero, mem_oz, Submodule.mem_one]
    exact ⟨fun h => ⟨⟨f, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩
  | succ n ih =>
    rw [pow_succ, mul_comm (_ ^ n), ← ih]
    apply le_antisymm
    · intro f hf
      have h := (dec_all 𝒜 hx hε hf).2.2 (by rcases hε with rfl | rfl <;> push_cast <;> omega)
      have e : 2 * ε * ((n + 1 : ℕ) : ℤ) - 2 * ε = 2 * ε * n := by push_cast; ring
      rw [e] at h
      clear hf
      refine Submodule.mul_induction_on h (fun p hp q hq => ?_) (fun p q hp hq => add_mem hp hq)
      exact Submodule.mul_mem_mul hp hq
    · refine Submodule.mul_le.2 fun p hp q hq => ?_
      have e : 2 * ε * ((n + 1 : ℕ) : ℤ) = 2 * ε + 2 * ε * n := by push_cast; ring
      rw [mem_oz, e]
      exact SetLike.GradedMul.mul_mem (A := 𝒜) hp hq

end SlopeTestRemainingChoices

theorem UpperTheory.V.Alg.M.oz_two_mul_eq_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx n
  have h1 := pow_eps 𝒜 hx (Or.inr rfl) n
  have h2 := pow_eps 𝒜 hx (Or.inl rfl) n
  have e : (2 * -1 * n : ℤ) = -(2 * n) := by ring
  rw [e] at h1
  rw [mul_one] at h2
  exact ⟨h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.PrimeMaximalOrKernel
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem prime_maximal_or_kernel (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (P : Ideal B) [hP : P.IsPrime]
    [Module.Finite O (B ⧸ P)] :
    P = maximalIdeal B ∨ ((∀ c : O, c ≠ 0 → algebraMap O B c ∉ P) ∧ ∃ σ : B →ₐ[O] K, RingHom.ker σ = P) := by
  classical
  haveI : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)
  have hcomap : ∀ a : O, algebraMap O (B ⧸ P) a = 0 ↔ algebraMap O B a ∈ P := by
    intro a
    rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  by_cases hc : ∃ c : O, c ≠ 0 ∧ algebraMap O B c ∈ P
  · obtain ⟨c, hc0, hcP⟩ := hc
    left
    apply IsLocalRing.eq_maximalIdeal
    have hQ : (P.comap (algebraMap O B)).IsMaximal := by
      apply Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _)
      intro h
      have hmem : c ∈ P.comap (algebraMap O B) := hcP
      rw [h] at hmem
      exact hc0 ((Submodule.mem_bot O).1 hmem)
    have hbot : (⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P)) = P.comap (algebraMap O B) := by
      ext a
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap, hcomap]
    haveI : (⊥ : Ideal (B ⧸ P)).IsPrime := Ideal.bot_prime
    have hmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) (⊥ : Ideal (B ⧸ P)) (hbot ▸ hQ)
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact Ring.isField_iff_maximal_bot.2 hmax
  · push_neg at hc
    right
    refine ⟨hc, ?_⟩
    have hinj : Function.Injective (algebraMap O (B ⧸ P)) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h0
      exact hc a h0 ((hcomap a).1 ha)
    haveI : Module.IsTorsionFree O (B ⧸ P) := NoZeroSMulDivisors.iff_algebraMap_injective.2 hinj
    haveI : Module.IsTorsionFree O K :=
      NoZeroSMulDivisors.iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective O K)
    haveI : Algebra.IsAlgebraic O (B ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let τ : (B ⧸ P) →ₐ[O] K := IsAlgClosed.lift
    refine ⟨τ.comp (Ideal.Quotient.mkₐ O P), ?_⟩
    have hτ : RingHom.ker (τ : (B ⧸ P) →+* K) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O)
      ext a
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      change τ (algebraMap O (B ⧸ P) a) = 0 ↔ a = 0
      rw [AlgHom.commutes]
      constructor
      · intro h
        exact FaithfulSMul.algebraMap_injective O K (h.trans (map_zero _).symm)
      · intro h
        rw [h, map_zero]
    have hτi : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot (τ : (B ⧸ P) →+* K)).2 hτ
    ext b
    rw [RingHom.mem_ker]
    change τ (Ideal.Quotient.mk P b) = 0 ↔ b ∈ P
    rw [map_eq_zero_iff τ hτi, Ideal.Quotient.eq_zero_iff_mem]

theorem UpperTheory.V.Alg.M.emb_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I →
    ∀ P : Ideal (𝒜 0), P.IsPrime → (∀ b : 𝒜 0, (b : A) ∈ I → b ∈ P) →
      (P = maximalIdeal (𝒜 0) ∨ ((∀ c : O, c ≠ 0 → algebraMap O (𝒜 0) c ∉ P) ∧ ∃ σ : 𝒜 0 →ₐ[O] K, RingHom.ker σ = P)) := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x I hM P hP hIP
  let φ : 𝒜 0 →ₗ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ (𝒜 0).subtype
  have hr : (LinearMap.range φ).FG := by
    have : LinearMap.range φ = (𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [this]; exact hM
  haveI : Module.Finite O (LinearMap.range φ) := Module.Finite.iff_fg.2 hr
  haveI : Module.Finite O (𝒜 0 ⧸ LinearMap.ker φ) := Module.Finite.equiv φ.quotKerEquivRange.symm
  let ψ : 𝒜 0 →ₗ[O] (𝒜 0 ⧸ P) := (Ideal.Quotient.mkₐ O P).toLinearMap
  have hk : LinearMap.ker φ ≤ LinearMap.ker ψ := fun b hb =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hIP b (Ideal.Quotient.eq_zero_iff_mem.1 hb))
  haveI : Module.Finite O (𝒜 0 ⧸ P) := by
    refine Module.Finite.of_surjective ((LinearMap.ker φ).liftQ ψ hk) fun y => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  exact prime_maximal_or_kernel O K (𝒜 0) P
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Satfil
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem satfil_wt {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    Finsupp.weight wt ν = (Finsupp.weight (posW wt) ν : ℤ) - (Finsupp.weight (negW wt) ν : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [posW, negW, nsmul_eq_mul, smul_eq_mul]
  push_cast
  rw [← mul_sub, Int.toNat_sub_toNat_neg]

private theorem satfil_deg {τ : Type} (wt : τ → ℤ) (h : ∀ i, wt i ≠ 0) (ν : τ →₀ ℕ) :
    Finsupp.degree ν ≤ Finsupp.weight (posW wt) ν + Finsupp.weight (negW wt) ν := by
  change (∑ i ∈ ν.support, ν i) ≤ _
  simp only [Finsupp.weight_apply, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : 1 ≤ posW wt i + negW wt i := by
    simp only [posW, negW]
    have := h i
    omega
  simp only [smul_eq_mul]
  nlinarith

theorem UpperTheory.V.Alg.M.satfil_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
      (∀ f ∈ 𝒜 (-1), f ∈ satSq x → φ f ∈ fil (FractionRing O) wt 2) ∧ ∀ b ∈ 𝒜 0, x b = 0 → φ b ∈ fil (FractionRing O) wt 1 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx τ _ wt φ hφ
  have hnz : ∀ i, wt i ≠ 0 := by
    intro i
    rcases hφ.wts i with h | h | h | h <;> omega
  have hlow : ∀ y ∈ RingHom.ker x ^ 2, ∀ ν : τ →₀ ℕ, Finsupp.degree ν ≤ 1 →
      MvPowerSeries.coeff ν (φ y) = 0 := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm n hn ν hν
      classical
      rw [map_mul, MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hd : Finsupp.degree p.1 + Finsupp.degree p.2 ≤ 1 := by
        rw [← map_add, hp]
        exact hν
      have hm0 : MvPowerSeries.coeff 0 (φ m) = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, RingHom.mem_ker.mp hm, map_zero]
      have hn0 : MvPowerSeries.coeff 0 (φ n) = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, RingHom.mem_ker.mp hn, map_zero]
      by_cases h1 : Finsupp.degree p.1 = 0
      · rw [(Finsupp.degree_eq_zero_iff _).mp h1, hm0, zero_mul]
      · have h2 : Finsupp.degree p.2 = 0 := by omega
        rw [(Finsupp.degree_eq_zero_iff _).mp h2, hn0, mul_zero]
    · intro a b ha hb ν hν
      rw [map_add, map_add, ha ν hν, hb ν hν, add_zero]
  refine ⟨?_, ?_⟩
  · intro f hf hsat ν hν
    obtain ⟨c, hc, hcf⟩ := hsat
    by_contra hne
    have hw : Finsupp.weight wt ν = -1 := by
      by_contra h'
      exact hne (hφ.graded (-1) f hf ν h')
    have e := satfil_wt wt ν
    have hdeg := satfil_deg wt hnz ν
    have hd1 : Finsupp.degree ν ≤ 1 := by omega
    have h0 := hlow _ hcf ν hd1
    rw [map_smul, ← algebraMap_smul (FractionRing O) c (φ f), map_smul, smul_eq_mul] at h0
    have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
      intro hz
      exact hc (IsFractionRing.injective O (FractionRing O) (by rw [hz, map_zero]))
    exact hne ((mul_eq_zero.mp h0).resolve_left hc')
  · intro b hb hxb ν hν
    by_contra hne
    have hw : Finsupp.weight wt ν = 0 := by
      by_contra h'
      exact hne (hφ.graded 0 b hb ν h')
    have e := satfil_wt wt ν
    have hdeg := satfil_deg wt hnz ν
    have hd : Finsupp.degree ν = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).mp hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, hxb,
      map_zero] at hne
    exact hne rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SmHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem sm_smith {O P : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup P]
    [Module O P] [Module.Finite O P] [Module.IsTorsionFree O P] {r : ℕ} (hr : Module.finrank O P = r)
    (N : Submodule O P) (hN : Module.finrank O N = Module.finrank O P) (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ (y : Fin r → P) (c : Fin r → ℕ), Submodule.span O (Set.range fun i => ϖ ^ c i • y i) = N ∧
      Module.length O (P ⧸ N) = ((∑ i, c i : ℕ) : ℕ∞) := by
  classical
  let b := Module.finBasisOfFinrankEq O P hr
  have ha := fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (Submodule.smithNormalFormCoeffs_ne_zero b hN i) hϖ
  choose c u hu using ha
  refine ⟨fun i => (u i : O) • Submodule.smithNormalFormTopBasis b hN i, c, ?_, ?_⟩
  · have h1 : (fun i => ϖ ^ c i • (u i : O) • Submodule.smithNormalFormTopBasis b hN i) =
        N.subtype ∘ Submodule.smithNormalFormBotBasis b hN := by
      funext i
      simp only [Function.comp, Submodule.subtype_apply]
      rw [Submodule.smithNormalFormBotBasis_def, hu i, smul_smul, mul_comm]
    rw [h1, Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
  · rw [(N.quotientEquivPiSpan b hN).length_eq, Module.length_pi_of_fintype, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Ideal.span {Submodule.smithNormalFormCoeffs b hN i} = maximalIdeal O ^ c i := by
      rw [hu i, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit (u i).isUnit]
    rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

private theorem sm_lift {O P : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup P]
    [Module O P] {r : ℕ} (φ : (Fin (r + 1) → O) →ₗ[O] P) (hr : Module.finrank O (LinearMap.range φ) = r)
    (n : Fin r → P) (hn : Submodule.span O (Set.range n) = LinearMap.range φ) :
    ∃ v : Fin (r + 1) → (Fin (r + 1) → O), Submodule.span O (Set.range v) = ⊤ ∧
      (∀ i : Fin r, φ (v i.castSucc) = n i) ∧ φ (v (Fin.last r)) = 0 := by
  have hw : ∀ i, ∃ w, φ w = n i := fun i => by
    have : n i ∈ LinearMap.range φ := hn ▸ Submodule.subset_span ⟨i, rfl⟩
    exact this
  choose w hw using hw
  have hk : Module.finrank O (LinearMap.ker φ) = 1 := by
    have h1 := (LinearMap.ker φ).finrank_quotient_add_finrank
    rw [φ.quotKerEquivRange.finrank_eq, hr, Module.finrank_fin_fun] at h1
    omega
  let b := Module.finBasisOfFinrankEq O (LinearMap.ker φ) hk
  refine ⟨Fin.snoc (α := fun _ => Fin (r + 1) → O) w (b 0 : Fin (r + 1) → O), ?_, fun i => by simp [hw], by simp⟩
  rw [eq_top_iff]
  intro u _
  have h1 : φ u ∈ Submodule.span O (Set.range n) := hn ▸ LinearMap.mem_range_self φ u
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
  have h2 : u - ∑ i, a i • w i ∈ LinearMap.ker φ := by
    simp [LinearMap.mem_ker, map_sum, hw, ha]
  have h3 := congrArg Subtype.val (b.sum_repr ⟨_, h2⟩)
  simp only [Fin.sum_univ_one, Submodule.coe_smul] at h3
  rw [← sub_add_cancel u (∑ i, a i • w i), ← h3]
  refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last r, by simp⟩)) ?_
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, by simp⟩)

theorem UpperTheory.V.Alg.M.sm_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [CommRing A] [Algebra O A]
      (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O), (∀ f ∈ 𝒜 (-1), x f = 0) → ∀ (r : ℕ) (F : Fin (r + 1) → A), (∀ i, F i ∈ 𝒜 (-1)) →
      Module.Finite O (cotLat x 𝒜 (-1)) → Module.finrank O (cotLat x 𝒜 (-1)) = r → SpansCot x 𝒜 (-1) F →
      ∀ ϖ : O, Irreducible ϖ → ∃ (F' : Fin (r + 1) → A) (y : Fin r → A) (c : Fin r → ℕ),
        Submodule.span O (Set.range F') = Submodule.span O (Set.range F) ∧
        (∀ i, y i ∈ 𝒜 (-1) ∧ F' i.castSucc - ϖ ^ c i • y i ∈ satSq x) ∧ F' (Fin.last r) ∈ satSq x ∧
        cotLen x 𝒜 (-1) F = ((∑ i, c i : ℕ) : ℕ∞) := by
  intro O _ _ _ A _ _ 𝒜 x hx r F hF hfin hr hs ϖ hϖ
  classical
  haveI : Module.IsTorsionFree O (A ⧸ satSq x) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c p h => ?_
    obtain ⟨f, rfl⟩ := (satSq x).mkQ_surjective p
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨d, hd, h⟩ := h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩
  have hle : cotSpan x F ≤ cotLat x 𝒜 (-1) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨F i, ⟨hF i, hx _ (hF i)⟩, rfl⟩
  set N := (cotSpan x F).comap (cotLat x 𝒜 (-1)).subtype with hNdef
  have hN : Module.finrank O N = Module.finrank O (cotLat x 𝒜 (-1)) := by
    have h1 := N.finrank_quotient_add_finrank
    have h2 : Module.finrank O (cotLat x 𝒜 (-1) ⧸ N) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro q
      obtain ⟨p, rfl⟩ := N.mkQ_surjective q
      obtain ⟨c, hc, hp⟩ := hs p.1 p.2
      refine ⟨c, hc, ?_⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hp
    omega
  obtain ⟨y, c, hy, hlen⟩ := sm_smith hr N hN ϖ hϖ
  let ψ : (Fin (r + 1) → O) →ₗ[O] A := Fintype.linearCombination O F
  have hψ : LinearMap.range ψ = Submodule.span O (Set.range F) := Fintype.range_linearCombination O F
  have hφ : LinearMap.range ((satSq x).mkQ ∘ₗ ψ) = cotSpan x F := by
    rw [LinearMap.range_comp, hψ, Submodule.map_span, ← Set.range_comp]
    rfl
  have hmap : N.map (cotLat x 𝒜 (-1)).subtype = cotSpan x F := by
    rw [hNdef, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  obtain ⟨v, hv, hv1, hv2⟩ := sm_lift ((satSq x).mkQ ∘ₗ ψ)
    (by rw [hφ]; exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.symm.trans (hN.trans hr))
    (fun i => ϖ ^ c i • (y i : A ⧸ satSq x))
    (by rw [hφ, ← hmap, ← hy, Submodule.map_span, ← Set.range_comp]; rfl)
  have hz : ∀ i, ∃ z ∈ 𝒜 (-1), (satSq x).mkQ z = y i := fun i => by
    obtain ⟨z, hz, h⟩ := (y i).2
    exact ⟨z, hz.1, h⟩
  choose z hz hz' using hz
  refine ⟨ψ ∘ v, z, c, ?_, fun i => ⟨hz i, ?_⟩, ?_, hlen⟩
  · rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top, hψ]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, hz', sub_eq_zero]
    exact hv1 i
  · rw [← Submodule.Quotient.mk_eq_zero]
    exact hv2
end


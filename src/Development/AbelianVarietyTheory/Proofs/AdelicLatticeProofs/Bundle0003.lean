import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNsmulMem
section
open NumberField

namespace GlobalTheory.IntegralMultipleOfVectors

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ (e : ℕ) (b : RingOfIntegers E), 0 < e ∧ (e : E) * a = algebraMap (RingOfIntegers E) E b := by
  have h : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  have hi' : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rcases Int.natAbs_eq y with h1 | h1
    · have : (y.natAbs : E) * a = y • a := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi
    · have : (y.natAbs : E) * a = -(y • a) := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi.neg
  exact ⟨y.natAbs, ⟨_, hi'⟩, Int.natAbs_pos.mpr hy, rfl⟩

theorem exists_nsmul_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx e
    · rw [mul_smul]; exact nsmul_mem hy d
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, b, he, hb⟩ := exists_nat_mul_integral a
    refine ⟨e * d, Nat.mul_pos he hd, ?_⟩
    have : (e * d) • a • x = b • d • x := by
      rw [← algebraMap_smul E b, ← hb]
      ext i
      simp
      ring
    rw [this]
    exact L.smul_mem b hx

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • M.mulVec v ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hfg
  choose f hf hmem using fun v => exists_nsmul_mem L hL (M.mulVec v)
  refine ⟨∏ v ∈ s, f v, Finset.prod_pos fun v _ => hf v, fun v hv => ?_⟩
  have hv' : v ∈ Submodule.span (RingOfIntegers E) (s : Set (Fin n → E)) := by
    rw [hs]; exact hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s f (Finset.mem_coe.mp hx), mul_smul]
    exact nsmul_mem (hmem x) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul E a, Matrix.mulVec_smul, algebraMap_smul, smul_comm]
    exact L.smul_mem a hx

end GlobalTheory.IntegralMultipleOfVectors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNsmulMulVecMem
section
namespace GlobalTheory.IntegralMultipleClearDenominators

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ K : ℕ, 0 < K ∧ IsIntegral ℤ ((K : E) * c) := by
  have h : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := h.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h1 | h1
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h1]
      exact (Int.cast_natCast _).symm
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h1]
      rw [Int.cast_neg, neg_neg]
      exact (Int.cast_natCast _).symm
    rw [this, neg_mul]; exact hint.neg

theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (↑L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hxa b
    · rw [mul_smul]; exact nsmul_mem hyb a
  | smul c x _ hx =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨K, hK, hint⟩ := exists_nat_mul_integral c
    refine ⟨K * a, Nat.mul_pos hK ha, ?_⟩
    have h := L.smul_mem (⟨(K : E) * c, hint⟩ : RingOfIntegers E) hxa
    convert h using 1
    ext i
    change _ = ((K : E) * c) * (a • x i)
    simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • Matrix.mulVec M v ∈ L := by
  obtain ⟨s, hs⟩ := hfg
  choose f hf0 hf using exists_nsmul_mem L hL
  refine ⟨∏ x ∈ s, f (M.mulVec x), Finset.prod_pos fun x _ => hf0 _, ?_⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec x)) (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) k
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul c x _ hx =>
    rw [Matrix.mulVec_smul, smul_comm]
    exact L.smul_mem c hx

end GlobalTheory.IntegralMultipleClearDenominators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeInvolutionOfRingInvolution
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_primeInvolution_of_ringInvolution {R : Type} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] (s : R ≃+* R) (hs : ∀ x, s (s x) = x) :
    ∃ c : HeightOneSpectrum R ≃ HeightOneSpectrum R, (∀ P, c (c P) = P) ∧
      (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2) := by
  have hm : ∀ (I : Ideal R) (x : R), s x ∈ I.map s ↔ x ∈ I := by
    intro I x
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, h⟩
      rwa [← s.injective h]
    · intro h
      exact ⟨x, h, rfl⟩
  let f : HeightOneSpectrum R → HeightOneSpectrum R := fun P =>
    { asIdeal := P.asIdeal.map s
      isPrime := by
        have := P.isPrime
        exact Ideal.map_isPrime_of_equiv s
      ne_bot := by
        intro h
        apply P.ne_bot
        rw [eq_bot_iff]
        intro x hx
        have h1 := (hm _ x).2 hx
        rw [h, Ideal.mem_bot] at h1
        rw [Ideal.mem_bot]
        exact s.injective (by simpa using h1) }
  have hf : Function.Involutive f := by
    intro P
    ext x
    show x ∈ (P.asIdeal.map s).map s ↔ _
    rw [← hm P.asIdeal x, ← hm _ (s x), hs]
  refine ⟨hf.toPerm f, hf, ?_, ?_, ?_⟩
  · intro P
    show Ideal.absNorm (P.asIdeal.map s) = _
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (P.asIdeal.map s) s rfl).toEquiv).symm
  · intro P x
    exact hm _ x
  · intro P x
    show s x ∈ (P.asIdeal.map s) ^ 2 ↔ _
    rw [← Ideal.map_pow, hm]

theorem cmConjugation_on_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → (∀ x, σ (σ x) = x) ∧ ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧ (∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ ∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hσ, hσ, star_star]
  have hfix : ∀ x, σ x = x → ∃ a : F, algebraMap F E a = x := by
    intro x hx
    have := Subalgebra.isSimpleOrder_of_finrank h2
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have hx' : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
      rw [h] at hx'
      exact hx'
    · exfalso
      apply IsTotallyComplex.complexEmbedding_not_isReal τ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      have hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      have hy' : σ y = y := hy
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := hσ τ y
      rw [hy'] at this
      exact this.symm
  let e : E ≃+* E :=
    { toFun := σ, invFun := σ, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul σ, map_add' := map_add σ }
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv e
  have hs : ∀ x : 𝓞 E, ((s x : 𝓞 E) : E) = σ x := fun x => rfl
  have hss : ∀ x, s (s x) = x := by
    intro x
    apply RingOfIntegers.ext
    rw [hs, hs, hinv]
  have hsF : ∀ a : 𝓞 F, s (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hs]
    exact σ.commutes (a : F)
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_primeInvolution_of_ringInvolution s hss
  refine ⟨hinv, c, hc1, hc2, fun x => ⟨s x, hs x⟩, ?_, ?_⟩
  · intro P x y hy
    have : y = s x := RingOfIntegers.ext (by rw [hy, hs])
    subst this
    exact ⟨hc3 P x, hc4 P x⟩
  · intro P Q
    have hu : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 F),
        a ∈ (P.under (𝓞 F)).asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := fun P a => Iff.rfl
    constructor
    · intro h
      by_contra hne
      push Not at hne
      have hnot : ¬ ((Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (c P).asIdeal) := by
        rw [Ideal.subset_union]
        rintro (h' | h')
        · exact hne.1 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h'))
        · exact hne.2 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (c P).isPrime.ne_top h'))
      rw [Set.not_subset] at hnot
      obtain ⟨x, hxQ, hx⟩ := hnot
      simp only [Set.mem_union, SetLike.mem_coe, not_or] at hx hxQ
      obtain ⟨a, ha⟩ := hfix ((x * s x : 𝓞 E) : E) (by
        rw [← hs, map_mul, hss, mul_comm])
      have hai : IsIntegral ℤ a := by
        have h1 : IsIntegral ℤ (algebraMap F E a) := by
          rw [ha]; exact RingOfIntegers.isIntegral_coe _
        exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h1
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = x * s x :=
        ⟨⟨a, hai⟩, RingOfIntegers.ext ha⟩
      have h1 : b ∈ (Q.under (𝓞 F)).asIdeal := by
        rw [hu, hb]; exact Ideal.mul_mem_right _ _ hxQ
      rw [← h, hu, hb] at h1
      rcases P.isPrime.mem_or_mem h1 with h3 | h3
      · exact hx.1 h3
      · apply hx.2
        have := (hc3 P _).2 h3
        rwa [hss] at this
    · rintro (rfl | rfl)
      · rfl
      · ext a
        rw [hu, hu, ← hc3 P, hsF]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatBilinForm
section
namespace GlobalTheory.RationalValueRealScalar

theorem map_rat_smul_real {U : Type} [AddCommGroup U] [Module ℝ U] {V : Type} [AddCommGroup V]
    [Module ℚ V] (p : V →+ U) (c : ℚ) (x : V) : p (c • x) = (c : ℝ) • p x := by
  have h1 : (c.den : ℤ) • (c • x) = c.num • x := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [Int.cast_natCast, mul_comm, Rat.mul_den_eq_num]
  have h2 : (c.den : ℝ) • p (c • x) = (c.num : ℝ) • p x := by
    rw [← Int.cast_natCast, Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ, ← map_zsmul, ← map_zsmul, h1]
  have hd : (c.den : ℝ) ≠ 0 := by positivity
  calc p (c • x) = ((c.den : ℝ)⁻¹ * c.den) • p (c • x) := by rw [inv_mul_cancel₀ hd, one_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.den : ℝ) • p (c • x)) := by rw [smul_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.num : ℝ) • p x) := by rw [h2]
    _ = (c : ℝ) • p x := by rw [smul_smul, Rat.cast_def, inv_mul_eq_div]

theorem exists_rat_value {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) (u v : V) :
    ∃ q : ℚ, (q : ℝ) = -(om (p u) (p v)) := by
  obtain ⟨N, hN, hNu⟩ := hL u
  obtain ⟨M, hM, hMv⟩ := hL v
  obtain ⟨k, hk⟩ := hint _ hNu _ hMv
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hk
  refine ⟨-(k / (N * M) : ℚ), ?_⟩
  have hNM : (N : ℝ) * M ≠ 0 := by positivity
  push_cast
  rw [neg_inj, div_eq_iff hNM, ← hk]
  ring

theorem exists_rat_bilinForm {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] [Module ℚ V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ u v : V, ((B u v : ℚ) : ℝ) = -(om (p u) (p v)) := by
  choose q hq using exists_rat_value om p L hL hint
  refine ⟨LinearMap.mk₂ ℚ q ?_ ?_ ?_ ?_, fun u v => hq u v⟩
  · intro u1 u2 v
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add, LinearMap.map_add, LinearMap.add_apply]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro u v1 v2
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add, LinearMap.map_add]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, smul_eq_mul]
    ring

end GlobalTheory.RationalValueRealScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExpSeriesContDiffAndHasDerivAt
section
open scoped ContDiff

namespace GlobalTheory

section ExpSeries

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {I : Type}

end ExpSeries

open scoped ContDiff in
private lemma norm_smulRight_le_opNorm_mul_norm {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (L : V →L[ℝ] ℂ) (w : E) :
    ‖L.smulRight w‖ ≤ ‖L‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖L h‖ * ‖w‖ ≤ ‖L‖ * ‖h‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (L.le_opNorm h) (norm_nonneg _)
    _ = ‖L‖ * ‖w‖ * ‖h‖ := by ring

open scoped ContDiff in
private lemma mul_exp_mul_le_exp_add_one_mul (r R : ℝ) :
    r * Real.exp (R * r) ≤ Real.exp ((R + 1) * r) := by
  calc r * Real.exp (R * r) ≤ Real.exp r * Real.exp (R * r) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp r]) (Real.exp_pos _).le
    _ = Real.exp ((R + 1) * r) := by rw [← Real.exp_add]; ring_nf

open scoped ContDiff in
private lemma summable_norm_smulRight_mul_exp {V E I : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (R : ℝ) :
    Summable fun i => ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hw (R + 1))
  calc ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖)
      ≤ ‖m i‖ * ‖w i‖ * Real.exp (R * ‖m i‖) :=
        mul_le_mul_of_nonneg_right (norm_smulRight_le_opNorm_mul_norm _ _) (Real.exp_pos _).le
    _ = ‖w i‖ * (‖m i‖ * Real.exp (R * ‖m i‖)) := by ring
    _ ≤ ‖w i‖ * Real.exp ((R + 1) * ‖m i‖) :=
        mul_le_mul_of_nonneg_left (mul_exp_mul_le_exp_add_one_mul _ _) (norm_nonneg _)

open scoped ContDiff in
private lemma norm_cexp_le_exp_mul_opNorm_of_norm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℂ) {y : V} {r : ℝ} (hy : ‖y‖ ≤ r) :
    ‖Complex.exp (L y)‖ ≤ Real.exp (r * ‖L‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  calc (L y).re ≤ ‖L y‖ := Complex.re_le_norm _
    _ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
    _ ≤ r * ‖L‖ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)

open scoped ContDiff in
private lemma hasFDerivAt_tsum_cexp_smul_of_summable_exp {V E I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (x : V) :
    HasFDerivAt (fun v => ∑' i, Complex.exp (m i v) • w i)
      (∑' i, Complex.exp (m i x) • (m i).smulRight (w i)) x := by
  set r := ‖x‖ + 1
  have hx : x ∈ Metric.ball (0 : V) r := by rw [mem_ball_zero_iff]; simp [r]
  refine hasFDerivAt_tsum_of_isPreconnected (u := fun i => ‖(m i).smulRight (w i)‖ *
      Real.exp (r * ‖m i‖)) (f := fun i v => Complex.exp (m i v) • w i)
    (f' := fun i y => Complex.exp (m i y) • (m i).smulRight (w i))
    (summable_norm_smulRight_mul_exp m w hw r) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected ?_ ?_ hx ?_ hx
  · intro i y _
    refine (((m i).hasFDerivAt.cexp).smul_const (w i)).congr_fderiv ?_
    ext h
    simp [smul_smul]
  · intro i y hy
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by rw [mem_ball_zero_iff] at hy; exact hy.le)) (norm_nonneg _)
  · refine Summable.of_norm_bounded (hw r) fun i => ?_
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by simp [r])) (norm_nonneg _)

open scoped ContDiff in
private lemma contDiff_tsum_cexp_smul_of_summable_exp {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : I → V →L[ℝ] ℂ) (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (w : I → E),
      (∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ n (fun v => ∑' i, Complex.exp (m i v) • w i) := by
  induction n with
  | zero =>
    intro E _ _ _ w hw
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x).continuousAt)
  | succ n ih =>
    intro E _ _ _ w hw
    have hd := fun x => hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x
    push_cast
    refine contDiff_succ_iff_fderiv.2 ⟨fun x => (hd x).differentiableAt, fun h => by simp at h, ?_⟩
    have hfd : fderiv ℝ (fun v => ∑' i, Complex.exp (m i v) • w i) =
        fun x => ∑' i, Complex.exp (m i x) • (m i).smulRight (w i) :=
      funext fun x => (hd x).fderiv
    rw [hfd]
    exact ih (V →L[ℝ] E) (fun i => (m i).smulRight (w i))
      (summable_norm_smulRight_mul_exp m w hw)

open scoped ContDiff in

theorem _root_.GlobalTheory.expSeries_contDiff_and_hasDerivAt :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (I : Type) (c : I → ℂ)
      (m : I → V →L[ℝ] ℂ), (∀ R : ℝ, Summable fun i => ‖c i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ ∞ (fun v : V => ∑' i, c i * Complex.exp (m i v)) ∧
        ∀ z : V, Summable (fun i => c i * m i z) ∧
          HasDerivAt (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z)))
            (∑' i, c i * m i z) 0 := by
  intro V _ _ I c m hc
  have hfun : (fun v : V => ∑' i, c i * Complex.exp (m i v)) =
      fun v => ∑' i, Complex.exp (m i v) • c i :=
    funext fun v => tsum_congr fun i => by rw [smul_eq_mul, mul_comm]
  have hz : ∀ z : V, Summable fun i => c i * m i z := by
    intro z
    refine Summable.of_norm_bounded ((hc 1).mul_left ‖z‖) fun i => ?_
    rw [norm_mul, one_mul]
    have h1 : 0 ≤ ‖c i‖ * ‖z‖ * (Real.exp ‖m i‖ - ‖m i‖) :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (by linarith [Real.add_one_le_exp ‖m i‖])
    have h2 : ‖c i‖ * ‖m i z‖ ≤ ‖c i‖ * (‖m i‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((m i).le_opNorm z) (norm_nonneg _)
    nlinarith
  refine ⟨?_, fun z => ⟨hz z, ?_⟩⟩
  · rw [hfun]
    exact contDiff_infty.2 fun n => contDiff_tsum_cexp_smul_of_summable_exp m n ℂ c hc
  · have hF := hasFDerivAt_tsum_cexp_smul_of_summable_exp m c hc (0 : V)
    have hl := (hasDerivAt_id (0 : ℝ)).smul_const z
    have h := hF.comp_hasDerivAt_of_eq (0 : ℝ) hl (zero_smul ℝ z).symm
    have hS : Summable fun i => (m i).smulRight (c i) := by
      refine Summable.of_norm ?_
      simpa using summable_norm_smulRight_mul_exp m c hc 0
    have hS' : Summable fun i => Complex.exp (m i 0) • (m i).smulRight (c i) := by
      simpa using hS
    have hfeq : (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z))) =
        ((fun v => ∑' i, Complex.exp (m i v) • c i) ∘ fun y => id y • z) :=
      funext fun t => tsum_congr fun i => by simp [mul_comm]
    rw [hfeq]
    refine h.congr_deriv ?_
    have happ := (hS'.hasSum.mapL (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ) • z))).tsum_eq
    simp only [ContinuousLinearMap.apply_apply] at happ
    rw [← happ]
    exact tsum_congr fun i => by simp [mul_comm]

end GlobalTheory
end


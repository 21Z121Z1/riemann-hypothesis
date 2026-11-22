import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfLocallyFractionOnGenerisations
section
namespace GlobalTheory

theorem exists_eq_of_locally_fraction_on_generisations
    (K : Type) [Field K] (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra K R]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (R →ₐ[K] k) → k)
    (hW : ∀ (q : Ideal R) [q.IsPrime], ∃ a : Localization.AtPrime q,
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : Localization.AtPrime q →ₐ[K] k),
        W k (φ.comp (IsScalarTower.toAlgHom K R (Localization.AtPrime q))) = φ a) :
    ∃ r : R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k),
      W k φ = φ r := by
  classical
  have h1 : ∀ (q : Ideal R) [q.IsPrime], ∃ g ∉ q, ∃ a : R,
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k),
        RingHom.ker φ ≤ q → φ g * W k φ = φ a := by
    intro q _
    obtain ⟨b, hb⟩ := hW q
    obtain ⟨⟨a, g⟩, hg⟩ := IsLocalization.surj q.primeCompl b
    refine ⟨g, g.2, a, fun k _ _ _ φ hφ => ?_⟩
    have hu : ∀ y : q.primeCompl, IsUnit (φ y) := fun y =>
      IsUnit.mk0 _ fun h => y.2 (hφ h)
    let ψ : Localization.AtPrime q →ₐ[K] k := IsLocalization.liftAlgHom (M := q.primeCompl) hu
    have hψ : ∀ x : R, ψ (algebraMap R _ x) = φ x := fun x => by
      simp [ψ, IsLocalization.liftAlgHom_apply]
    have hc : ψ.comp (IsScalarTower.toAlgHom K R (Localization.AtPrime q)) = φ := by
      ext x; simpa using hψ x
    have h2 := hb k ψ
    rw [hc] at h2
    have h3 := congrArg ψ hg
    simp only [map_mul, hψ] at h3
    rw [h2, mul_comm]; exact h3
  let I : Ideal R :=
    { carrier := {g | ∃ a : R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k]
        (φ : R →ₐ[K] k), RingHom.ker φ ∈ minimalPrimes R → φ g * W k φ = φ a}
      zero_mem' := ⟨0, fun k _ _ _ φ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', fun k _ _ _ φ h => by
          rw [map_add, map_add, add_mul, ha k φ h, ha' k φ h]⟩
      smul_mem' := by
        rintro c g ⟨a, ha⟩
        exact ⟨c * a, fun k _ _ _ φ h => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, ha k φ h]⟩ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hne
    haveI := hq.isPrime
    obtain ⟨g, hg, a, ha⟩ := h1 q
    have hfin := minimalPrimes.finite_of_isNoetherianRing R
    let S : Finset (Ideal R) := hfin.toFinset.filter fun m => ¬ m ≤ q
    have hS : ¬ S.inf id ≤ q := by
      rw [Ideal.IsPrime.inf_le' inferInstance]
      rintro ⟨m, hm, hmq⟩
      exact (Finset.mem_filter.1 hm).2 hmq
    obtain ⟨h, hh, hhq⟩ := Set.not_subset.1 hS
    have hmem : h * g ∈ I := by
      refine ⟨h * a, fun k _ _ _ φ hφ => ?_⟩
      by_cases hle : RingHom.ker φ ≤ q
      · rw [map_mul, map_mul, mul_assoc, ha k φ hle]
      · have hm : RingHom.ker φ ∈ S := Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hφ, hle⟩
        have h0 : φ h = 0 := (Finset.inf_le (f := id) hm : S.inf id ≤ RingHom.ker φ) hh
        simp [h0]
    rcases hq.isPrime.mem_or_mem (hIq hmem) with h' | h'
    · exact hhq h'
    · exact hg h'
  obtain ⟨r, hr⟩ : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  refine ⟨r, fun k _ _ _ φ => ?_⟩
  haveI hp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨g, hg, a, ha⟩ := h1 (RingHom.ker φ)
  obtain ⟨m, hm, hmq⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
    (J := RingHom.ker φ) bot_le
  haveI : m.IsPrime := hm.1.1
  let k' := AlgebraicClosure (FractionRing (R ⧸ m))
  let ψ : R →ₐ[K] k' := (IsScalarTower.toAlgHom K (R ⧸ m) k').comp (Ideal.Quotient.mkₐ K m)
  have hinj : Function.Injective (algebraMap (R ⧸ m) k') := by
    rw [IsScalarTower.algebraMap_eq (R ⧸ m) (FractionRing (R ⧸ m)) k']
    exact (algebraMap (FractionRing (R ⧸ m)) k').injective.comp (IsFractionRing.injective _ _)
  have hker : RingHom.ker ψ = m := by
    ext x
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff _ hinj]
    rfl
  have e1 := hr k' ψ (by rw [hker]; exact hm)
  have e2 := ha k' ψ (by rw [hker]; exact hmq)
  have e3 : g * r - a ∈ m := by
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, ← e1, ← e2, map_one, one_mul, sub_self]
  have e4 : φ (g * r - a) = 0 := hmq e3
  have e5 := ha k φ le_rfl
  rw [map_sub, map_mul, ← e5, sub_eq_zero] at e4
  exact (mul_left_cancel₀ hg e4).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionCapitulationComplex
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

theorem exists_pow_eq_span_singleton_of_fg (E : Type) [Field E] [NumberField E]
    (I : Submodule (𝓞 E) E) (hI : I.FG) :
    ∃ n : ℕ, ∃ β : E, I ^ (n + 1) = Submodule.span (𝓞 E) {β} := by
  classical
  by_cases h0 : I = ⊥
  · exact ⟨0, 0, by simp [h0]⟩
  let F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  have hF : F ≠ 0 := by
    intro h
    apply h0
    have := congrArg (fun G : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (G : Submodule (𝓞 E) E)) h
    simpa [F] using this
  let u := Units.mk0 F hF
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card (ClassGroup (𝓞 E)) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h1 : ClassGroup.mk E (u ^ (n + 1)) = 1 := by
    rw [map_pow, ← hn, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨β, hβ⟩ := h1
  refine ⟨n, β, ?_⟩
  rw [← hβ, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

theorem span_image_eq_span_root {E M : Type} [Field E] [Field M] (ψ : E →+* M)
    (I : Submodule (𝓞 E) E) (n : ℕ) (β : E) (hβ : I ^ (n + 1) = Submodule.span (𝓞 E) {β})
    (γ : M) (hγ : γ ^ (n + 1) = ψ β) :
    Submodule.span (𝓞 M) (ψ '' I) = Submodule.span (𝓞 M) {γ} := by
  set J := Submodule.span (𝓞 M) (ψ '' I) with hJ
  have hint : ∀ c : 𝓞 E, IsIntegral ℤ (ψ c) := fun c =>
    map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe c)
  have hle : J ≤ Submodule.span (𝓞 M) {γ} := by
    rw [hJ, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ^ (n + 1) ∈ Submodule.span (𝓞 E) {β} := hβ ▸ Submodule.pow_mem_pow I hx (n + 1)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxn
    have hc' : ψ x ^ (n + 1) = ψ c * γ ^ (n + 1) := by
      rw [hγ, ← map_pow, ← hc, ← map_mul]; rfl
    by_cases hγ0 : γ = 0
    · have : ψ x = 0 := by
        rw [hγ0] at hc'
        simpa using hc'
      rw [this]; exact Submodule.zero_mem _
    · have hi : IsIntegral ℤ (ψ x / γ) := by
        apply IsIntegral.of_pow (Nat.succ_pos n)
        rw [div_pow, hc', mul_div_assoc, div_self (pow_ne_zero _ hγ0), mul_one]
        exact hint c
      refine Submodule.mem_span_singleton.mpr ⟨⟨ψ x / γ, hi⟩, ?_⟩
      change (ψ x / γ) * γ = ψ x
      exact div_mul_cancel₀ _ hγ0
  have hpow : ∀ k : ℕ, ∀ y ∈ I ^ k, ψ y ∈ J ^ k := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [pow_zero, Submodule.mem_one] at hy ⊢
      obtain ⟨c, rfl⟩ := hy
      exact ⟨⟨ψ c, hint c⟩, rfl⟩
    | succ k ih =>
      intro y hy
      rw [pow_succ] at hy ⊢
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Submodule.mul_mem_mul (ih a ha) (Submodule.subset_span ⟨b, hb, rfl⟩)
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
  refine le_antisymm hle ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  by_cases hγ0 : γ = 0
  · rw [hγ0]; exact Submodule.zero_mem _
  have h1 : γ ^ (n + 1) ∈ J ^ (n + 1) := by
    rw [hγ]; apply hpow; rw [hβ]; exact Submodule.mem_span_singleton_self β
  have h2 : J ^ (n + 1) ≤ J * Submodule.span (𝓞 M) {γ ^ n} := by
    rw [pow_succ']
    refine mul_le_mul_right ?_ _
    rw [← Set.singleton_pow, ← Submodule.span_pow]
    exact pow_le_pow_left' hle n
  obtain ⟨z, hz, hz'⟩ := Submodule.mem_mul_span_singleton.mp (h2 h1)
  rw [pow_succ'] at hz'
  have : z = γ := mul_right_cancel₀ (pow_ne_zero n hγ0) hz'
  exact this ▸ hz

theorem exists_finite_extension_capitulation :
    ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (ι : Type) [Finite ι] (I : ι → Submodule (𝓞 E) E), (∀ τ, (I τ).FG) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ x, φ x ∈ M) ∧ ∀ τ, ∃ s : M, Submodule.span (𝓞 M) {y : M | ∃ x ∈ I τ, (y : ℂ) = φ x} = Submodule.span (𝓞 M) {s} := by
  intro E _ _ φ ι _ I hI
  choose n β hβ using fun τ => exists_pow_eq_span_singleton_of_fg E (I τ) (hI τ)
  choose γ hγ using fun τ => IsAlgClosed.exists_pow_nat_eq (φ (β τ)) (Nat.succ_pos (n τ))
  let φ' : E →ₐ[ℚ] ℂ := φ.toRatAlgHom
  let K : IntermediateField ℚ ℂ := φ'.fieldRange
  haveI hK : FiniteDimensional ℚ K :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ').toLinearEquiv
  haveI : Finite (Set.range γ) := Set.finite_range γ
  haveI hL : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range γ)) := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨τ, rfl⟩
    apply IsIntegral.of_pow (Nat.succ_pos (n τ))
    rw [hγ]
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) (β τ)).map φ'
  let M : IntermediateField ℚ ℂ := K ⊔ IntermediateField.adjoin ℚ (Set.range γ)
  have hM : ∀ x, φ x ∈ M := fun x => (le_sup_left : K ≤ M) ⟨x, rfl⟩
  refine ⟨M, IntermediateField.finiteDimensional_sup _ _, hM, fun τ => ?_⟩
  have hγM : γ τ ∈ M := (le_sup_right : _ ≤ M) (IntermediateField.subset_adjoin ℚ _ ⟨τ, rfl⟩)
  let ψ : E →+* M := φ.codRestrict M.toSubfield hM
  refine ⟨⟨γ τ, hγM⟩, ?_⟩
  rw [← span_image_eq_span_root ψ (I τ) (n τ) (β τ) (hβ τ) ⟨γ τ, hγM⟩ (Subtype.ext (hγ τ))]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, Subtype.ext h.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteTypeSubalgebraValuationLeOne
section
namespace GlobalTheory.FractionalParts

def fracs {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (C : Subalgebra A B) :
    Subalgebra A B where
  carrier := {b | ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a}
  mul_mem' := by
    rintro x y ⟨a, ha, s, hs, hu, h⟩ ⟨a', ha', s', hs', hu', h'⟩
    exact ⟨a * a', C.mul_mem ha ha', s * s', C.mul_mem hs hs', hu.mul hu', by
      rw [← h, ← h']; ring⟩
  add_mem' := by
    rintro x y ⟨a, ha, s, hs, hu, h⟩ ⟨a', ha', s', hs', hu', h'⟩
    exact ⟨s' * a + s * a', C.add_mem (C.mul_mem hs' ha) (C.mul_mem hs ha'), s * s',
      C.mul_mem hs hs', hu.mul hu', by rw [← h, ← h']; ring⟩
  algebraMap_mem' r := ⟨algebraMap A B r, C.algebraMap_mem r, 1, C.one_mem, isUnit_one, one_mul _⟩

theorem exists_finiteType_subalgebra_valuation_le_one (A B k : Type) [CommRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k)
    (V : ValuationSubring k) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal B)
    (hA : ∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) :
    ∃ C : Subalgebra A B, Algebra.FiniteType A C ∧ (∀ c ∈ C, V.valuation (φ c) ≤ 1) ∧
      ∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a := by
  classical
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff A B).mp inferInstance
  have key : ∀ x : B, ∃ y : B, φ y ∈ V ∧ (y = x ∨ y * x = 1) := by
    intro x
    by_cases hx : φ x ∈ V
    · exact ⟨x, hx, Or.inl rfl⟩
    · have hne : φ x ≠ 0 := fun h => hx (h ▸ V.zero_mem)
      have hu : IsUnit x := by
        by_contra hnu
        have : x ∈ RingHom.ker φ := by
          rw [hker]; exact (IsLocalRing.mem_maximalIdeal x).mpr hnu
        exact hne this
      obtain ⟨y, hy⟩ := hu.exists_left_inv
      refine ⟨y, ?_, Or.inr hy⟩
      have h1 : φ y * φ x = 1 := by rw [← map_mul, hy, map_one]
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (V.mem_or_inv_mem (φ x)).resolve_left hx
  choose f hfV hf using key
  let C : Subalgebra A B := Algebra.adjoin A ((σ.image f : Finset B) : Set B)
  have hfC : ∀ x ∈ σ, f x ∈ C := fun x hx =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem f hx))
  refine ⟨C, ?_, ?_, ?_⟩
  · exact (Subalgebra.fg_iff_finiteType C).mp (Subalgebra.fg_adjoin_finset _)
  · intro c hc
    rw [ValuationSubring.valuation_le_one_iff]
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact hfV z
    | algebraMap r => exact (V.valuation_le_one_iff _).mp (hA r)
    | add x y _ _ hx hy => rw [map_add]; exact V.add_mem _ _ hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact V.mul_mem _ _ hx hy
  · have hle : Algebra.adjoin A (σ : Set B) ≤ fracs C := by
      refine Algebra.adjoin_le ?_
      intro x hx
      have hx' := hfC x (Finset.mem_coe.mp hx)
      rcases hf x with h | h
      · exact ⟨x, h ▸ hx', 1, C.one_mem, isUnit_one, one_mul _⟩
      · exact ⟨1, C.one_mem, f x, hx', IsUnit.of_mul_eq_one _ h, h⟩
    intro b
    obtain ⟨t, ht, htu, hbt⟩ := hσ b
    obtain ⟨a1, ha1, s1, hs1, hu1, h1⟩ := hle ht
    obtain ⟨a2, ha2, s2, hs2, hu2, h2⟩ := hle hbt
    refine ⟨s1 * a2, C.mul_mem hs1 ha2, s2 * a1, C.mul_mem hs2 ha1,
      hu2.mul (h1 ▸ hu1.mul htu), ?_⟩
    rw [← h1, ← h2]; ring

end GlobalTheory.FractionalParts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorSqEqOfSqMemZpowers
section
namespace GlobalTheory

theorem exists_generator_sq_eq_of_sq_mem_zpowers :
    ∀ (p : ℕ), p.Prime → ∀ a : (ZMod p)ˣ,
      (∀ b : (ZMod p)ˣ, b ^ 2 ∈ Subgroup.zpowers (a ^ 2)) →
      ∃ γ : (ZMod p)ˣ, Subgroup.zpowers γ = ⊤ ∧ γ ^ 2 = a ^ 2 := by
  intro p hp a ha
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hgn : orderOf g = Nat.card (ZMod p)ˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hn0 : 0 < Nat.card (ZMod p)ˣ := Nat.card_pos
  have gen : ∀ γ : (ZMod p)ˣ, orderOf γ = Nat.card (ZMod p)ˣ → Subgroup.zpowers γ = ⊤ :=
    fun γ h => Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h])
  have hdn : orderOf a ∣ Nat.card (ZMod p)ˣ := orderOf_dvd_natCard a
  have hd0 : 0 < orderOf a := orderOf_pos a
  have key : orderOf (g ^ 2) ∣ orderOf (a ^ 2) := orderOf_dvd_of_mem_zpowers (ha g)
  rw [orderOf_pow' g two_ne_zero, orderOf_pow' a two_ne_zero, hgn] at key
  generalize Nat.card (ZMod p)ˣ = n at *
  generalize hd : orderOf a = d at *
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hn_odd
  · rcases Nat.even_or_odd d with ⟨e, he⟩ | hd_odd
    · refine ⟨a, gen a ?_, rfl⟩
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      have h2 : d.gcd 2 = 2 := Nat.gcd_eq_right ⟨e, by omega⟩
      rw [h1, h2, show n / 2 = m by omega, show d / 2 = e by omega] at key
      have h3 : e ∣ m := by
        rw [he, hm, ← two_mul, ← two_mul] at hdn
        exact Nat.dvd_of_mul_dvd_mul_left two_pos hdn
      have := Nat.dvd_antisymm key h3
      omega
    · have hcop : d.Coprime 2 := Nat.coprime_two_right.mpr hd_odd
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      rw [h1, hcop.gcd_eq_one, Nat.div_one, show n / 2 = m by omega] at key
      have h3 : d ∣ m := hcop.dvd_of_dvd_mul_left (by rw [hm] at hdn; rwa [two_mul])
      have hdm : d = m := Nat.dvd_antisymm h3 key
      have hgm : orderOf (g ^ m) = 2 := by
        have := orderOf_pow_orderOf_div (x := g) (by omega) (show 2 ∣ orderOf g from ⟨m, by omega⟩)
        rwa [show orderOf g / 2 = m by omega] at this
      refine ⟨a * g ^ m, gen _ ?_, ?_⟩
      · rw [(Commute.all a (g ^ m)).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hd, hgm]; exact hcop), hgm, hd]
        omega
      · have hg1 : g ^ n = 1 := hgn ▸ pow_orderOf_eq_one g
        rw [mul_pow, ← pow_mul, show m * 2 = n by omega, hg1, mul_one]
  · have hd_odd : Odd d := hn_odd.of_dvd_nat hdn
    refine ⟨a, gen a ?_, rfl⟩
    rw [(Nat.coprime_two_right.mpr hn_odd).gcd_eq_one, (Nat.coprime_two_right.mpr hd_odd).gcd_eq_one,
      Nat.div_one, Nat.div_one] at key
    rw [hd]
    exact Nat.dvd_antisymm hdn key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHenselRootResidue
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem residue_eval_map_comm {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (q : A[X]) (f : A →+* B) (h : B →+* C) (x : B) :
    h ((q.map f).eval x) = (q.map (h.comp f)).eval (h x) := by
  rw [eval_map, eval_map, hom_eval₂]

theorem exists_root_lift_of_residue_map :
    ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V]
      [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V)
      (σ : ResidueField R →+* ResidueField V),
      (∀ a, σ (residue R (φ a)) = residue V (α a)) → ∀ (θ : R) (q : Polynomial A), q.Monic →
      (q.map φ).eval θ = 0 → IsUnit ((q.derivative.map φ).eval θ) →
      ∃ η : V, (q.map α).eval η = 0 ∧ residue V η = σ (residue R θ) := by
  intro A R V _ _ _ _ _ _ _ φ α σ hσ θ q hq h0 hu
  obtain ⟨η₀, hη₀⟩ := residue_surjective (σ (residue R θ))
  have hcomp : (residue V).comp α = σ.comp ((residue R).comp φ) := by
    ext a; simp [hσ]
  have key : ∀ p : A[X], residue V ((p.map α).eval η₀) = σ (residue R ((p.map φ).eval θ)) := by
    intro p
    rw [residue_eval_map_comm, hcomp, hη₀, residue_eval_map_comm p φ (residue R),
      residue_eval_map_comm _ _ σ]
  have hm : (q.map α).Monic := hq.map α
  have h1 : (q.map α).eval η₀ ∈ maximalIdeal V := by
    rw [← residue_eq_zero_iff, key, h0, map_zero, map_zero]
  have h2 : IsUnit (Ideal.Quotient.mk (maximalIdeal V) ((q.map α).derivative.eval η₀)) := by
    have : (Ideal.Quotient.mk (maximalIdeal V) ((q.map α).derivative.eval η₀)) =
        σ (residue R ((q.derivative.map φ).eval θ)) := by
      rw [derivative_map]; exact key _
    rw [this]
    exact (hu.map (residue R)).map σ
  obtain ⟨η, hη, hηm⟩ := HenselianRing.is_henselian (I := maximalIdeal V) _ hm η₀ h1 h2
  refine ⟨η, hη, ?_⟩
  rw [← hη₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hηm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveAdicCompletionMapOfFinite
section
open IsLocalRing

namespace GlobalTheory

theorem adicCompletion_evalₐ_of_val {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {n : ℕ} (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) d := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), AdicCompletion.eval_apply]
  erw [hd]
  rfl

theorem adicCompletion_val_of_le {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {m n : ℕ} (hmn : m ≤ n) (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    x.val m = Submodule.Quotient.mk d := by
  rw [← x.prop hmn, hd]
  rfl

theorem adicCompletion_injective_ringHom_of_finite
    (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N]
    [Module.Finite D N] (hinj : Function.Injective (algebraMap D N)) (J : Ideal D) :
    ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N,
      Function.Injective f := by
  set φ := algebraMap D N with hφ
  have hle : ∀ n : ℕ, J ^ n ≤ ((J.map φ) ^ n).comap φ := fun n => by
    rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  let g : (n : ℕ) → AdicCompletion J D →+* N ⧸ (J.map φ) ^ n := fun n =>
    (Ideal.quotientMap ((J.map φ) ^ n) φ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (J.map φ) hmn).comp (g n) = g m := by
    intro m n hmn
    ext x
    obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    have hn := adicCompletion_evalₐ_of_val J x d hd.symm
    have hm := adicCompletion_evalₐ_of_val J x d (adicCompletion_val_of_le J x hmn d hd.symm)
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hn, hm,
      Ideal.quotientMap_mk]
    rfl
  refine ⟨AdicCompletion.liftRingHom _ g hg, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmap := AdicCompletion.map_injective J (f := Algebra.linearMap D N) hinj
  apply hmap
  rw [map_zero]
  apply AdicCompletion.ext
  intro n
  obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have h1 := adicCompletion_evalₐ_of_val J x d hd.symm
  have h2 := congrArg (AdicCompletion.evalₐ (J.map φ) n) hx
  rw [AdicCompletion.evalₐ_liftRingHom, map_zero] at h2
  simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1,
    Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  rw [AdicCompletion.map_val_apply]
  erw [← hd]
  rw [LinearMap.reduceModIdeal_apply]
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).trans rfl
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsotropicDualOfSkewMatrix
section
open Matrix

namespace GlobalTheory

theorem exists_isotropic_dual_of_skew {V : Type*} [AddCommGroup V] [Module ℚ V] {g : ℕ}
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (ε ψ : Fin g → V) (hB : ∀ x y, B x y = -B y x)
    (hε : ∀ i j, B (ε i) (ε j) = 0)
    (hψ : ∀ i j, B (ψ j) (ε i) = if i = j then 1 else 0) :
    ∃ φ : Fin g → V, (∀ i j, B (φ i) (φ j) = 0) ∧
      (∀ i j, B (φ j) (ε i) = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  classical
  have h1 : ∀ k l, B (ψ l) (ε k) = if k = l then 1 else 0 := fun k l => hψ k l
  have h2 : ∀ k l, B (ε k) (ψ l) = -(if k = l then 1 else 0) := fun k l => by
    rw [hB, h1]
  refine ⟨fun j => ψ j + ∑ k, (B (ψ j) (ψ k) / 2) • ε k, ?_, ?_, ?_⟩
  · intro i j
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, h2, mul_zero,
      Finset.sum_const_zero, add_zero, mul_ite, mul_one, mul_neg, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [hB (ψ i) (ψ j)]
  · intro i j
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, mul_zero,
      Finset.sum_const_zero, add_zero]
  · intro j
    simp only [add_sub_cancel_left]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem exists_isotropic_dual_of_skew_matrix (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ)
    (ε ψ : Fin g → Fin r → ℚ) (hM : Mqᵀ = -Mq) (hε : ∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0)
    (hψ : ∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) :
    ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧
      (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  obtain ⟨φ, h₁, h₂, h₃⟩ := exists_isotropic_dual_of_skew (Matrix.toLinearMap₂' ℚ Mq) ε ψ
    (fun x y => by
      simp only [Matrix.toLinearMap₂'_apply']
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, Matrix.neg_mulVec,
        neg_dotProduct, dotProduct_comm])
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hε i j)
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hψ i j)
  exact ⟨φ, fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₁ i j,
    fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₂ i j, h₃⟩

end GlobalTheory
end


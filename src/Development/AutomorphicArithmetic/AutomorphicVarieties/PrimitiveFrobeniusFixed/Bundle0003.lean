import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ThDist
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem modSum (q b c : ℕ) (hq : q.Prime) (hb0 : b ≠ 0) (hb : b < q) :
    ∑ i ∈ Finset.range q, (c + i * b) % q = ∑ i ∈ Finset.range q, i := by
  have hinj : Set.InjOn (fun i => (c + i * b) % q) (Finset.range q : Set ℕ) := by
    intro i hi j hj h
    have h1 : c + i * b ≡ c + j * b [MOD q] := h
    have h2 : i * b ≡ j * b [MOD q] := Nat.ModEq.add_left_cancel' c h1
    have hc : Nat.gcd q b = 1 := (Nat.coprime_of_lt_prime hb0 hb hq)
    have h3 : i ≡ j [MOD q] := Nat.ModEq.cancel_right_of_coprime hc h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 (by simpa using hi) (by simpa using hj)
  have him : (Finset.range q).image (fun i => (c + i * b) % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hq.pos)
    · rw [Finset.card_image_of_injOn hinj]
  have := Finset.sum_image (f := fun x : ℕ => x) hinj
  rw [him] at this
  exact this.symm

private theorem divSum (q b c : ℕ) (hq : q.Prime) (hb0 : b ≠ 0) (hb : b < q) :
    ∑ i ∈ Finset.range q, (c + i * b) / q = c + ∑ i ∈ Finset.range q, (i * b) / q := by
  have key : ∀ c : ℕ, q * ∑ i ∈ Finset.range q, (c + i * b) / q + ∑ i ∈ Finset.range q, i
      = q * c + ∑ i ∈ Finset.range q, i * b := by
    intro c
    rw [← modSum q b c hq hb0 hb, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [Nat.div_add_mod]
    rw [Finset.sum_add_distrib]
    simp
  have h1 := key c
  have h2 := key 0
  simp only [zero_add, mul_zero] at h2
  apply Nat.eq_of_mul_eq_mul_left hq.pos
  rw [mul_add]
  omega

private theorem divSum' (M q b a : ℕ) (hM : 0 < M) (hq : q.Prime) (hb : b < q) :
    ∑ i ∈ Finset.range q, (a + i * M) * b / (q * M) = a * b / M + ∑ i ∈ Finset.range q, (i * b) / q := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  rw [← divSum q b _ hq hb0 hb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm q M, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [show (a + i * M) * b = a * b + i * b * M by ring, Nat.add_mul_div_right _ _ hM]

private theorem classSum (M q a : ℕ) (ha : a < M) (g : ℕ → ℕ) :
    ∑ n ∈ (Finset.range (q * M)).filter (fun n => n % M = a), g n = ∑ i ∈ Finset.range q, g (a + i * M) := by
  have hM : 0 < M := by omega
  symm
  refine Finset.sum_nbij' (fun i => a + i * M) (fun n => n / M) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_filter] at hi ⊢
    refine ⟨by nlinarith, by simp [Nat.mod_eq_of_lt ha]⟩
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter] at hn ⊢
    exact (Nat.div_lt_iff_lt_mul hM).2 hn.1
  · intro i _
    rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt ha, zero_add]
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter] at hn ⊢
    rw [← hn.2, mul_comm]
    exact Nat.mod_add_div n M
  · intro i _
    rfl

private theorem unitSum (M q : ℕ) [NeZero M] [NeZero (q * M)] (hq : q.Prime) (u : (ZMod M)ˣ) (hu : (u : ZMod M) = q)
    (t : (ZMod M)ˣ) (g : ℕ → ℕ) :
    ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t),
      g (t' : ZMod (q * M)).val + g (q * ((u⁻¹ * t : (ZMod M)ˣ) : ZMod M).val)
      = ∑ i ∈ Finset.range q, g ((t : ZMod M).val + i * M) := by
  rw [← classSum M q _ (ZMod.val_lt _) g]
  set s : (ZMod M)ˣ := u⁻¹ * t with hs
  have hst : (q : ZMod M) * s = t := by
    rw [← hu, hs, ← Units.val_mul, mul_inv_cancel_left]
  have hmod : ∀ n : ℕ, n % M = (t : ZMod M).val ↔ (n : ZMod M) = t := by
    intro n
    rw [← ZMod.val_natCast]
    exact (ZMod.val_injective M).eq_iff
  have hmem : q * (s : ZMod M).val ∈ (Finset.range (q * M)).filter (fun n => n % M = (t : ZMod M).val) := by
    simp only [Finset.mem_range, Finset.mem_filter]
    refine ⟨Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hq.pos, ?_⟩
    rw [hmod]
    push_cast
    rw [ZMod.natCast_zmod_val, hst]
  rw [← Finset.sum_erase_add _ _ hmem]
  congr 1
  refine Finset.sum_bij (fun t' _ => (t' : ZMod (q * M)).val) ?_ ?_ ?_ ?_
  · intro t' ht'
    simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at ht' ⊢
    refine ⟨?_, ZMod.val_lt _, ?_⟩
    · intro h
      have hc := ZMod.val_coe_unit_coprime t'
      rw [h] at hc
      exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hc) (Dvd.intro _ rfl))
    · rw [hmod, ← ht', ZMod.unitsMap_val, ZMod.natCast_val]
  · intro x _ y _ h
    exact Units.ext (ZMod.val_injective _ h)
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_erase] at hn
    obtain ⟨h1, h2, h3⟩ := hn
    rw [hmod] at h3
    have hcM : n.Coprime M := by
      rw [← ZMod.isUnit_iff_coprime, h3]
      exact t.isUnit
    have hcq : n.Coprime q := by
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
      rintro ⟨k, rfl⟩
      apply h1
      congr 1
      have hk : k < M := Nat.lt_of_mul_lt_mul_left h2
      have : (k : ZMod M) = s := by
        apply u.isUnit.mul_left_cancel
        rw [hu, hst, ← h3]
        push_cast
        rfl
      rw [← this, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
    have hv : ((ZMod.unitOfCoprime n (Nat.Coprime.mul_right hcq hcM) : (ZMod (q * M))ˣ) : ZMod (q * M)).val = n := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt h2]
    refine ⟨ZMod.unitOfCoprime n (Nat.Coprime.mul_right hcq hcM), ?_, hv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Units.ext
    rw [ZMod.unitsMap_val, ← ZMod.natCast_val, hv, h3]
  · intro _ _
    rfl

private theorem halfSum (M q b : ℕ) [NeZero M] [NeZero (q * M)] (hq : q.Prime) (hb : b < q) (u : (ZMod M)ˣ)
    (hu : (u : ZMod M) = q) (t : (ZMod M)ˣ) :
    ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t),
      (((t' : ZMod (q * M)).val * b / (q * M) : ℕ) : ℤ) + ((((u⁻¹ * t : (ZMod M)ˣ) : ZMod M).val * b / M : ℕ) : ℤ)
      = (((t : ZMod M).val * b / M : ℕ) : ℤ) + ((∑ i ∈ Finset.range q, (i * b) / q : ℕ) : ℤ) := by
  have h := unitSum M q hq u hu t (fun n => n * b / (q * M))
  rw [divSum' M q b _ (Nat.pos_of_ne_zero (NeZero.ne M)) hq hb, mul_assoc, Nat.mul_div_mul_left _ _ hq.pos] at h
  rw [← Nat.cast_sum, ← Nat.cast_add, h, Nat.cast_add]

theorem UpperTheory.V.ML.thDist :
    ∀ (M q b : ℕ) [NeZero M] [NeZero (q * M)], q.Prime → b < q → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ t : (ZMod M)ˣ,
    ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t), th (q * M) b t' = th M b t - th M b (u⁻¹ * t : (ZMod M)ˣ) := by
  intro M q b _ _ hq hb u hu t
  have h1 := halfSum M q b hq hb u hu t
  have h2 := halfSum M q b hq hb u hu (-t)
  have hneg : ∀ x : (ZMod (q * M))ˣ, ZMod.unitsMap (Dvd.intro_left q rfl) (-x) = -ZMod.unitsMap (Dvd.intro_left q rfl) x := by
    intro x
    apply Units.ext
    rw [Units.val_neg, ZMod.unitsMap_val, ZMod.unitsMap_val, Units.val_neg, ZMod.cast_neg (Dvd.intro_left q rfl)]
  have h3 : ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t),
      (((-(t' : ZMod (q * M))).val * b / (q * M) : ℕ) : ℤ) =
      ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = -t),
      (((t' : ZMod (q * M)).val * b / (q * M) : ℕ) : ℤ) := by
    refine Finset.sum_equiv (Equiv.neg _) ?_ ?_
    · intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.neg_apply, hneg, neg_inj]
    · intro x _
      simp only [Equiv.neg_apply, Units.val_neg]
  rw [mul_neg, Units.val_neg, Units.val_neg] at h2
  simp only [th]
  rw [Finset.sum_sub_distrib, h3]
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationComapIsEquivOfLtOneIffMemPrime
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

theorem UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] (ι : K →+* Ω) (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), (∀ y : 𝓞 K, A.valuation (ι (y : K)) < 1 ↔ y ∈ w.asIdeal) → (A.valuation.comap ι).IsEquiv (w.valuation K) := by
  intro K Ω _ _ _ ι A w h
  have hle : ∀ y : 𝓞 K, A.valuation (ι (y : K)) ≤ 1 := fun y =>
    int_le A (y.isIntegral_coe.map ι.toIntAlgHom)
  have key : ∀ x : K, w.valuation K x ≤ 1 → ∃ a s : 𝓞 K, s ∉ w.asIdeal ∧ x * (s : K) = (a : K) ∧
      A.valuation (ι x) = A.valuation (ι (a : K)) := by
    intro x hx
    obtain ⟨a, s, hs⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hs' : (s : 𝓞 K) ∉ w.asIdeal := s.2
    have hs2 : x * ((s : 𝓞 K) : K) = (a : K) := hs
    refine ⟨a, s, hs', hs2, ?_⟩
    have h1 : A.valuation (ι ((s : 𝓞 K) : K)) = 1 :=
      le_antisymm (hle _) (not_lt.1 fun hh => hs' ((h _).1 hh))
    rw [← hs2, map_mul, map_mul, h1, mul_one]
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [Valuation.comap_apply]
  constructor
  · intro hx
    by_contra hw
    have hw' : 1 < w.valuation K x := not_le.1 hw
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hw'
    have hinv : w.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hw'
    obtain ⟨a, s, -, hs2, he⟩ := key x⁻¹ hinv.le
    have ha : w.valuation K (a : K) < 1 := by
      rw [← hs2, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hinv (w.valuation_le_one s)
    have ha' : a ∈ w.asIdeal := (w.valuation_lt_one_iff_mem a).1 ha
    have h2 : A.valuation (ι x⁻¹) < 1 := he ▸ (h a).2 ha'
    have h3 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h2 hx
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx0, map_one, map_one] at h3
    exact lt_irrefl _ h3
  · intro hx
    obtain ⟨a, s, -, -, he⟩ := key x hx
    rw [he]
    exact hle a
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationKummerElementEqOneOfNotOver
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_count_int {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    v.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))) := by
  have h1 : v.valuation K (a : K) = v.intValuation a := v.valuation_of_algebraMap a
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
      = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_span_singleton a).symm
  rw [h1, h2, v.intValuation_if_neg ha, FractionalIdeal.count_coe K v (by simpa using ha)]

private theorem val_count {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simp [← e]
  have e' : x * (b : K) = (a : K) := by
    rw [← e]; exact div_mul_cancel₀ _ hbK
  have h1 := val_count_int v a ha0
  have h2 := val_count_int v b hb0
  rw [← e', map_mul, h2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbK), neg_add, WithZero.exp_add] at h1
  exact mul_right_cancel₀ WithZero.exp_ne_zero h1

theorem UpperTheory.valuation_kummerElement_eq_one_of_not_over :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b r : ℕ) (v w : HeightOneSpectrum (𝓞 K)) (X : K), IsX M K b v.asIdeal X → (r : 𝓞 K) ∈ v.asIdeal → (r : 𝓞 K) ∉ w.asIdeal → w.valuation K X = 1 := by
  intro M _ K _ _ _ b r v w X hX hv hw
  have hX0 : X ≠ 0 := left_ne_zero_of_mul_eq_one hX.1
  let P : (ZMod M)ˣ → HeightOneSpectrum (𝓞 K) := fun t =>
    HeightOneSpectrum.comap (sgO M K t : 𝓞 K →+* 𝓞 K) (sgO M K t).surjective v
  have hP : ∀ t, (P t).asIdeal = conjI M K v.asIdeal t := fun t => rfl
  have hne : ∀ t, P t ≠ w := by
    intro t h
    apply hw
    rw [← h, hP, mem_conjI, map_natCast]
    exact hv
  rw [val_count w X hX0, hX.2, FractionalIdeal.count_prod]
  · rw [Finset.sum_eq_zero, neg_zero, WithZero.exp_zero]
    intro t _
    rw [FractionalIdeal.count_zpow, ← hP, FractionalIdeal.count_maximal_coprime K w (hne t), mul_zero]
  · intro t _
    apply zpow_ne_zero
    rw [← hP]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (P t).ne_bot
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XMulConjIMul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section aux

variable (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]

private theorem xMul_conjI_eq (P : Ideal (𝓞 K)) (t : (ZMod M)ˣ) :
    conjI M K P t = P.map (sgO M K t).symm := (Ideal.map_symm (sgO M K t)).symm

private theorem xMul_conjI_mul (P Q : Ideal (𝓞 K)) (t : (ZMod M)ˣ) :
    conjI M K (P * Q) t = conjI M K P t * conjI M K Q t := by
  simp only [xMul_conjI_eq, Ideal.map_mul]

private theorem xMul_conjI_pow (P : Ideal (𝓞 K)) (n : ℕ) (t : (ZMod M)ˣ) :
    conjI M K (P ^ n) t = conjI M K P t ^ n := by
  simp only [xMul_conjI_eq, Ideal.map_pow]

private theorem xMul_conj (φ : K →+* ℂ) (x : K) : φ (sg M K (-1) x) = (starRingEnd ℂ) (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  set ζ := IsCyclotomicExtension.zeta M ℚ K
  have h : φ.toRatAlgHom.comp (sg M K (-1) : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    have h1 : sg M K (-1) ζ * ζ = 1 := by
      rw [sg_apply M K _ hζ.pow_eq_one, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
      simp
    have h2 : (φ ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have h3 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 (NeZero.ne M)
    have h4 : φ (sg M K (-1) ζ) * φ ζ = 1 := by rw [← map_mul, h1, map_one]
    change φ (sg M K (-1) ζ) = (starRingEnd ℂ) (φ ζ)
    rw [eq_inv_of_mul_eq_one_left h4, Complex.inv_eq_conj h3]
  exact DFunLike.congr_fun h x

private theorem xMul_root (ζ : K) (k : ℕ) (hk : k ≠ 0) (h : ζ ^ k = 1) : ζ * sg M K (-1) ζ = 1 := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply φ.injective
  have h2 : (φ ζ) ^ k = 1 := by rw [← map_pow, h, map_one]
  have h3 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 hk
  have h0 : φ ζ ≠ 0 := by
    intro h0
    simp [h0] at h3
  rw [map_mul, xMul_conj, map_one, ← Complex.inv_eq_conj h3, mul_inv_cancel₀ h0]

private noncomputable def xMul_sp : K →*₀ FractionalIdeal (𝓞 K)⁰ K where
  toFun x := FractionalIdeal.spanSingleton (𝓞 K)⁰ x
  map_zero' := FractionalIdeal.spanSingleton_zero
  map_one' := FractionalIdeal.spanSingleton_one
  map_mul' x y := (FractionalIdeal.spanSingleton_mul_spanSingleton x y).symm

private theorem xMul_sp_eq (x : K) : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = xMul_sp K x := rfl

end aux

theorem UpperTheory.V.ML.xMul :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ),
    (∀ (𝔞 𝔟 : Ideal (𝓞 K)) (X Y : K), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsX M K b 𝔞 X → IsX M K b 𝔟 Y → IsX M K b (𝔞 * 𝔟) (X * Y)) ∧
    (∀ (𝔞 𝔟 : Ideal (𝓞 K)) (Z Y : K), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsX M K b (𝔞 * 𝔟) Z → IsX M K b 𝔟 Y → IsX M K b 𝔞 (Z / Y)) ∧
    (∀ (𝔞 : Ideal (𝓞 K)) (X : K) (n : ℕ), 𝔞 ≠ ⊥ → IsX M K b 𝔞 X → IsX M K b (𝔞 ^ n) (X ^ n)) ∧
    (∀ (𝔞 : Ideal (𝓞 K)) (X ζ : K) (k : ℕ), k ≠ 0 → ζ ^ k = 1 → IsX M K b 𝔞 X → IsX M K b 𝔞 (ζ * X)) ∧
    ∀ y : 𝓞 K, y ≠ 0 → IsX M K b (Ideal.span {y}) (∏ t : (ZMod M)ˣ, (sg M K t)⁻¹ (y : K) ^ th M b t) := by
  intro M _ K _ _ _ b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro 𝔞 𝔟 X Y - - ⟨hX, hX'⟩ ⟨hY, hY'⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul, mul_mul_mul_comm, hX, hY, one_mul]
    · rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, hX', hY', ← Finset.prod_mul_distrib]
      simp only [xMul_conjI_mul, FractionalIdeal.coeIdeal_mul, mul_zpow]
  · rintro 𝔞 𝔟 Z Y - - ⟨hZ, hZ'⟩ ⟨hY, hY'⟩
    have hY0 : Y ≠ 0 := by
      rintro rfl
      simp at hY
    refine ⟨?_, ?_⟩
    · rw [map_div₀, div_mul_div_comm, hZ, hY, div_one]
    · have h0 : xMul_sp K Y ≠ 0 := (map_ne_zero _).2 hY0
      rw [xMul_sp_eq] at hZ' hY' ⊢
      rw [map_div₀, div_eq_iff h0, hZ', hY', ← Finset.prod_mul_distrib]
      simp only [xMul_conjI_mul, FractionalIdeal.coeIdeal_mul, mul_zpow]
  · rintro 𝔞 X n - ⟨hX, hX'⟩
    refine ⟨?_, ?_⟩
    · rw [map_pow, ← mul_pow, hX, one_pow]
    · rw [xMul_sp_eq] at hX' ⊢
      rw [map_pow, hX', ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [xMul_conjI_pow, FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  · rintro 𝔞 X ζ k hk hζ ⟨hX, hX'⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul, mul_mul_mul_comm, hX, xMul_root M K ζ k hk hζ, one_mul]
    · rw [← hX', eq_comm, FractionalIdeal.spanSingleton_eq_spanSingleton]
      have hi : IsIntegral ℤ ζ := IsIntegral.of_pow (Nat.pos_of_ne_zero hk) (hζ ▸ isIntegral_one)
      obtain ⟨z, rfl⟩ : ∃ z : 𝓞 K, (z : K) = ζ := ⟨⟨ζ, hi⟩, rfl⟩
      have hu : IsUnit z := IsUnit.of_pow_eq_one (n := k) (Subtype.ext hζ) hk
      obtain ⟨u, rfl⟩ := hu
      refine ⟨u, ?_⟩
      rw [Units.smul_def, Algebra.smul_def]
  · intro y hy
    have hy' : (y : K) ≠ 0 := by exact_mod_cast hy
    refine ⟨?_, ?_⟩
    · rw [map_prod, ← Equiv.prod_comp (Equiv.neg (ZMod M)ˣ) (fun t => sg M K (-1) ((sg M K t)⁻¹ (y : K) ^ th M b t)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun t _ => ?_
      have h1 : sg M K (-1) ((sg M K (-t))⁻¹ (y : K)) = (sg M K t)⁻¹ (y : K) := by
        rw [← AlgEquiv.mul_apply, ← map_inv, ← map_inv, ← map_mul]
        congr 2
        simp [inv_neg]
      have h2 : (sg M K t)⁻¹ (y : K) ≠ 0 := (map_ne_zero _).2 hy'
      rw [Equiv.neg_apply, map_zpow₀, h1, Units.val_neg, th_neg, zpow_neg]
      exact mul_inv_cancel₀ (zpow_ne_zero _ h2)
    · rw [xMul_sp_eq, map_prod]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [map_zpow₀, xMul_conjI_eq, Ideal.map_span, Set.image_singleton, FractionalIdeal.coeIdeal_span_singleton]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XUniqConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem UpperTheory.V.ML.xUniq_conj (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] (φ : K →+* ℂ) (x : K) : φ (sg M K (-1) x) = starRingEnd ℂ (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  set ζ := IsCyclotomicExtension.zeta M ℚ K
  have hz : (φ ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have key : φ (sg M K (-1) ζ) = starRingEnd ℂ (φ ζ) := by
    rw [sg_apply M K (-1) hζ.pow_eq_one, map_pow]
    have hM : M ∣ ((-1 : (ZMod M)ˣ) : ZMod M).val + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simp
    have hnorm : ‖φ ζ‖ = 1 := by
      have h1 := congrArg norm hz
      rw [norm_pow, norm_one] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne M)).mp h1
    have hinv : starRingEnd ℂ (φ ζ) = (φ ζ)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
      simp
    rw [hinv]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    obtain ⟨k, hk⟩ := hM
    rw [hk, pow_mul, hz, one_pow]
  have hext := AlgHom.ext_of_adjoin_eq_top (R := ℚ)
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
    (φ₁ := (φ.comp (sg M K (-1)).toAlgHom.toRingHom).toRatAlgHom)
    (φ₂ := ((starRingEnd ℂ).comp φ).toRatAlgHom)
    (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact key)
  have h2 := DFunLike.congr_fun hext x
  simpa using h2

theorem UpperTheory.V.ML.xUniq :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ) (𝔞 : Ideal (𝓞 K)) (X X' : K), 𝔞 ≠ ⊥ → IsX M K b 𝔞 X → IsX M K b 𝔞 X' → ∃ ζ : K, ζ ^ (2 * M) = 1 ∧ X' = ζ * X := by
  intro M _ K _ _ _ b 𝔞 X X' _ hX hX'
  obtain ⟨z, hz⟩ := (FractionalIdeal.spanSingleton_eq_spanSingleton).mp (hX.2.trans hX'.2.symm)
  set w : K := ((z : 𝓞 K) : K) with hw
  have hX'eq : X' = w * X := by
    rw [← hz, Units.smul_def, Algebra.smul_def]
  have hww : w * sg M K (-1) w = 1 := by
    have h1 := hX'.1
    rw [hX'eq, map_mul] at h1
    have h2 := hX.1
    calc w * sg M K (-1) w = w * sg M K (-1) w * (X * sg M K (-1) X) := by rw [h2, mul_one]
      _ = 1 := by rw [← h1]; ring
  have hnorm : ∀ φ : K →+* ℂ, ‖φ w‖ = 1 := by
    intro φ
    have h3 : φ w * starRingEnd ℂ (φ w) = 1 := by
      rw [← UpperTheory.V.ML.xUniq_conj M K φ w, ← map_mul, hww, map_one]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h3
    have h4 : ‖φ w‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h4
  obtain ⟨n, hn, hwn⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ
    (RingOfIntegers.isIntegral_coe (z : 𝓞 K)) hnorm
  have hzt : z ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hn, ?_⟩
    apply Units.ext
    apply RingOfIntegers.coe_injective
    simpa using hwn
  have hpow : w ^ NumberField.Units.torsionOrder K = 1 := by
    have h5 := pow_card_eq_one' (x := (⟨z, hzt⟩ : NumberField.Units.torsion K))
    have h6 : z ^ Nat.card (NumberField.Units.torsion K) = 1 := by
      have h7 := congrArg Subtype.val h5
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h7
    have h8 := congrArg (fun t : (𝓞 K)ˣ => ((t : 𝓞 K) : K)) h6
    simp only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] at h8
    exact h8
  refine ⟨w, ?_, hX'eq⟩
  have hdvd : NumberField.Units.torsionOrder K ∣ 2 * M := by
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := M)]
    split_ifs with he
    · exact dvd_mul_left M 2
    · exact dvd_rfl
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul, hpow, one_pow]
end


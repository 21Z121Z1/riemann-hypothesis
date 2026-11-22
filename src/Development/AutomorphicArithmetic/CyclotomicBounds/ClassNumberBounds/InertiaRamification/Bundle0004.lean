import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0003
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0002

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bounds
section
namespace KStar.Ram

open DirichletCharacter

section PrimePower

variable {l v : ℕ} [hl : Fact l.Prime]

private instance bounds_neZero : NeZero (l ^ v) := ⟨pow_ne_zero _ hl.out.ne_zero⟩

private def boundsSub (m d : ℕ) [NeZero m] : Subgroup (DirichletCharacter ℂ m) where
  carrier := {θ | θ.conductor ∣ d}
  mul_mem' {a b} ha hb := (conductor_mul_dvd_lcm_conductor a b).trans (Nat.lcm_dvd ha hb)
  one_mem' := by simp [conductor_one]
  inv_mem' {a} ha := by simpa [conductor_inv] using ha

end PrimePower

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDvd
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N]

private theorem mem_conductorDvd_iff (m : ℕ) (ψ : DirichletCharacter ℂ N) :
    ψ ∈ condDvd N m ↔ ψ.conductor ∣ m := by
  have h1 : ψ ∈ condDvd N m ↔ ψ.FactorsThrough (Nat.gcd N m) := by
    rw [factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_left N m), condDvd, mem_annihilator_iff]
    refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
    · rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
      exact h x hx
    · have := h hx
      rwa [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at this
  rw [h1, ← mem_conductorSet_iff, mem_conductorSet_iff_conductor_dvd _ (Nat.gcd_dvd_left N m),
    Nat.dvd_gcd_iff]
  exact ⟨fun h => h.2, fun h => ⟨ψ.conductor_dvd_level, h⟩⟩

private theorem fieldConductor_dvd_iff (X : Subgroup (DirichletCharacter ℂ N)) (m : ℕ) :
    fieldCond X ∣ m ↔ X ≤ condDvd N m := by
  rw [fieldCond, Finset.lcm_dvd_iff]
  refine ⟨fun h ψ hψ => (mem_conductorDvd_iff m ψ).2 (h ψ ?_), fun h ψ hψ =>
    (mem_conductorDvd_iff m ψ).1 (h ?_)⟩
  · simpa using hψ
  · simpa using hψ

theorem mem_condDvd_iff (m : ℕ) (ψ : DirichletCharacter ℂ N) :
    (ψ ∈ condDvd N m ↔ ψ.conductor ∣ m) ∧ (m ∣ N → Nat.card (condDvd N m) = Nat.totient m) := by
  refine ⟨mem_conductorDvd_iff m ψ, fun hm => ?_⟩
  have : NeZero m := ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hm))⟩
  have h : condDvd N m = (changeLevel (R := ℂ) hm).range := by
    ext χ
    rw [mem_conductorDvd_iff, ← mem_conductorSet_iff_conductor_dvd _ hm, mem_conductorSet_iff,
      MonoidHom.mem_range]
    refine ⟨fun ⟨_, χ₀, h⟩ => ⟨χ₀, h.symm⟩, fun ⟨χ₀, h⟩ => ⟨hm, χ₀, h.symm⟩⟩
  rw [h, ← card_eq_totient_of_hasEnoughRootsOfUnity ℂ m]
  exact (Nat.card_congr (MonoidHom.ofInjective (changeLevel_injective hm)).toEquiv).symm

theorem card_evenPart (X : Subgroup (DirichletCharacter ℂ N)) :
    (∀ ψ, ψ ∈ evenPart X ↔ ψ ∈ X ∧ ψ.Even) ∧
      ((∃ ψ ∈ X, ψ.Odd) → Nat.card X = 2 * Nat.card (evenPart X)) := by
  have hmem : ∀ ψ, ψ ∈ evenPart X ↔ ψ ∈ X ∧ ψ.Even := by
    intro ψ
    rw [evenPart, Subgroup.mem_inf, mem_annihilator_iff]
    simp [DirichletCharacter.Even]
  refine ⟨hmem, ?_⟩
  rintro ⟨ψ, hψ, hodd⟩
  have hle : evenPart X ≤ X := inf_le_left
  have hidx : ((evenPart X).subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨ψ, hψ⟩, fun b => ?_⟩
    have hψ' : ψ (-1) = -1 := hodd
    have e1 : b * ⟨ψ, hψ⟩ ∈ (evenPart X).subgroupOf X ↔ (b : DirichletCharacter ℂ N).Odd := by
      rw [Subgroup.mem_subgroupOf, hmem]
      simp only [SetLike.coe_mem, true_and, DirichletCharacter.Even, DirichletCharacter.Odd]
      rw [Subgroup.coe_mul, MulChar.mul_apply, hψ', mul_neg, mul_one, neg_eq_iff_eq_neg]
    have e2 : b ∈ (evenPart X).subgroupOf X ↔ (b : DirichletCharacter ℂ N).Even := by
      rw [Subgroup.mem_subgroupOf, hmem]
      simp
    rw [e1, e2]
    rcases (b : DirichletCharacter ℂ N).even_or_odd with h | h
    · exact Or.inr ⟨h, h.not_odd⟩
    · exact Or.inl ⟨h, h.not_even⟩
  rw [← Subgroup.index_mul_card ((evenPart X).subgroupOf X), hidx,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem fieldCond_sup (X Y : Subgroup (DirichletCharacter ℂ N)) (χ : DirichletCharacter ℂ N) :
    fieldCond (X ⊔ Y) = Nat.lcm (fieldCond X) (fieldCond Y) ∧
      fieldCond (Subgroup.zpowers χ) = χ.conductor ∧
      ∀ m, fieldCond X ∣ m ↔ X ≤ condDvd N m := by
  refine ⟨?_, ?_, fieldConductor_dvd_iff X⟩
  · refine Nat.dvd_antisymm ?_ ?_
    · rw [fieldConductor_dvd_iff, sup_le_iff, ← fieldConductor_dvd_iff, ← fieldConductor_dvd_iff]
      exact ⟨Nat.dvd_lcm_left _ _, Nat.dvd_lcm_right _ _⟩
    · rw [Nat.lcm_dvd_iff, fieldConductor_dvd_iff, fieldConductor_dvd_iff, ← sup_le_iff,
        ← fieldConductor_dvd_iff]
  · refine Nat.dvd_antisymm ?_ ?_
    · rw [fieldConductor_dvd_iff, Subgroup.zpowers_le, mem_conductorDvd_iff]
    · rw [← mem_conductorDvd_iff, ← Subgroup.zpowers_le, ← fieldConductor_dvd_iff]

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycDifferent
section
namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

open Polynomial in
private theorem minpoly_map_eq_prod_gal {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (x : L) (hx : Algebra.adjoin F {x} = ⊤) :
    (minpoly F x).map (algebraMap F L) = ∏ σ : Gal(L/F), (X - C (σ x)) := by
  classical
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hinj : Function.Injective (fun σ : Gal(L/F) => σ x) := by
    intro σ τ h
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top hx
    rintro y rfl
    exact h
  have hm : (∏ σ : Gal(L/F), (X - C (σ x))).Monic :=
    monic_prod_of_monic _ _ fun σ _ => monic_X_sub_C _
  have hdvd : (∏ σ : Gal(L/F), (X - C (σ x))) ∣ (minpoly F x).map (algebraMap F L) := by
    apply Finset.prod_dvd_of_coprime
    · intro σ _ τ _ hne
      exact pairwise_coprime_X_sub_C hinj hne
    · intro σ _
      rw [dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap, aeval_algEquiv]
      simp
  refine eq_of_monic_of_dvd_of_natDegree_le hm ((minpoly.monic hint).map _) hdvd ?_
  rw [natDegree_map, natDegree_prod_of_monic _ _ (fun σ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  exact minpoly.natDegree_le x

open Polynomial Classical in
private theorem aeval_derivative_minpoly_eq_prod_gal {F L : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (x : L)
    (hx : Algebra.adjoin F {x} = ⊤) :
    aeval x (derivative (minpoly F x)) = ∏ σ ∈ (Finset.univ : Finset Gal(L/F)).erase 1, (x - σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map, minpoly_map_eq_prod_gal x hx,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : Gal(L/F))), derivative_mul]
  simp [eval_prod]

open Polynomial Classical in
private theorem differentIdeal_eq_span_of_prod (A F : Type*) {L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field F] [Field L] [NumberField L] [Algebra A F] [IsFractionRing A F]
    [Algebra F L] [Algebra A L] [Algebra A (𝓞 L)] [IsScalarTower A F L] [IsScalarTower A (𝓞 L) L]
    [IsIntegralClosure (𝓞 L) A L] [Module.IsTorsionFree A (𝓞 L)]
    [FiniteDimensional F L] [IsGalois F L] (x y : 𝓞 L)
    (hx : Algebra.adjoin A {x} = ⊤) (hx' : Algebra.adjoin F {algebraMap (𝓞 L) L x} = ⊤)
    (hy : algebraMap (𝓞 L) L y = ∏ σ ∈ (Finset.univ : Finset Gal(L/F)).erase 1,
      (algebraMap (𝓞 L) L x - σ (algebraMap (𝓞 L) L x))) :
    differentIdeal A (𝓞 L) = Ideal.span {y} := by
  have h := conductor_mul_differentIdeal A F L x hx'
  rw [conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul] at h
  rw [h]
  congr 2
  apply IsFractionRing.injective (𝓞 L) L
  have hint : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  rw [hy, ← aeval_derivative_minpoly_eq_prod_gal _ hx',
    minpoly.isIntegrallyClosed_eq_field_fractions F L hint, derivative_map, aeval_map_algebraMap,
    aeval_algebraMap_apply]

private theorem adjoin_root_eq_top (E : Type*) [Field E] [Algebra ℚ E] [Algebra E K]
    [IsScalarTower ℚ E K] {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    Algebra.adjoin E {ζ} = ⊤ := by
  have h := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ) hζ
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Algebra.adjoin ℚ {ζ} := h ▸ Algebra.mem_top
  have : Algebra.adjoin ℚ {ζ} ≤ (Algebra.adjoin E {ζ}).restrictScalars ℚ :=
    Algebra.adjoin_le (by simp)
  exact this hy

private theorem adjoin_toInteger_eq_top (A : Type*) [CommRing A] [Algebra A (𝓞 K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    Algebra.adjoin A {hζ.toInteger} = ⊤ := by
  have h := adjoin_singleton_eq_top hζ
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Algebra.adjoin ℤ {hζ.toInteger} := h ▸ Algebra.mem_top
  have : Algebra.adjoin ℤ {hζ.toInteger} ≤ (Algebra.adjoin A {hζ.toInteger}).restrictScalars ℤ :=
    Algebra.adjoin_le (by simp)
  exact this hy

open Classical in

theorem relDifferent_eq_span_prod (E : IntermediateField ℚ K) {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    differentIdeal (𝓞 E) (𝓞 K) = Ideal.span
      {∏ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∈ E.fixingSubgroup ∧ σ ≠ 1),
        (hζ.toInteger - σ • hζ.toInteger)} := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  refine differentIdeal_eq_span_of_prod (𝓞 E) E hζ.toInteger _
    (adjoin_toInteger_eq_top _ hζ) (adjoin_root_eq_top E hζ) ?_
  rw [map_prod]
  symm
  refine Finset.prod_bij (fun σ _ => σ.restrictScalars ℚ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    · intro h
      apply (Finset.mem_erase.mp hσ).1
      ext x
      exact DFunLike.congr_fun h x
  · intro σ _ τ _ h
    ext x
    exact DFunLike.congr_fun h x
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨E.fixingSubgroupEquiv ⟨σ, hσ.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro h
      apply hσ.2
      ext x
      exact DFunLike.congr_fun h x
    · rfl
  · intro σ _
    rfl

open Classical in

theorem map_differentIdeal_eq_span_prod (E : IntermediateField ℚ K) {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) :
    (differentIdeal ℤ (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 K)) = Ideal.span
      {∏ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
        (hζ.toInteger - σ • hζ.toInteger)} := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have h1 : differentIdeal ℤ (𝓞 K) = Ideal.span
      {∏ σ ∈ (Finset.univ : Finset Gal(K/ℚ)).erase 1, (hζ.toInteger - σ • hζ.toInteger)} := by
    refine differentIdeal_eq_span_of_prod ℤ ℚ hζ.toInteger _
      (adjoin_toInteger_eq_top _ hζ) (adjoin_root_eq_top ℚ hζ) ?_
    rw [map_prod]
    rfl
  have h2 := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 K)
  have h3 : differentIdeal (𝓞 E) (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  apply mul_left_cancel₀ h3
  rw [← h2, h1, relDifferent_eq_span_prod E hζ, Ideal.span_singleton_mul_span_singleton,
    ← Finset.prod_filter_mul_prod_filter_not _ (fun σ : Gal(K/ℚ) => σ ∈ E.fixingSubgroup)]
  congr 4
  · ext σ
    simp [and_comm]
  · ext σ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and,
      and_iff_right_iff_imp]
    rintro h rfl
    exact h (one_mem _)

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
section
namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

private theorem cycInertia_card_comap (l : ℕ) [hl : Fact l.Prime]
    (H : Subgroup (ZMod (ordCompl[l] N))ˣ) :
    Nat.card (H.comap (ZMod.unitsMap (Nat.ordCompl_dvd N l))) =
      Nat.totient (ordProj[l] N) * Nat.card H := by
  have hne : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩
  have h1 := Subgroup.card_mul_index (H.comap (ZMod.unitsMap (Nat.ordCompl_dvd N l)))
  have h2 := Subgroup.card_mul_index H
  rw [Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective _)] at h1
  rw [Nat.card_eq_fintype_card (α := (ZMod N)ˣ), ZMod.card_units_eq_totient] at h1
  rw [Nat.card_eq_fintype_card (α := (ZMod (ordCompl[l] N))ˣ), ZMod.card_units_eq_totient] at h2
  have h3 : Nat.totient N = Nat.totient (ordProj[l] N) * Nat.totient (ordCompl[l] N) := by
    rw [← Nat.totient_mul (Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))),
      Nat.ordProj_mul_ordCompl_eq_self]
  have h4 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4)
  rw [h1, h3, ← h2, mul_assoc]

private theorem cycInertia_ef (l : ℕ) [hl : Fact l.Prime] :
    (Ideal.span {(l : ℤ)}).ramificationIdxIn (𝓞 K) = Nat.totient (ordProj[l] N) ∧
      (Ideal.span {(l : ℤ)}).inertiaDegIn (𝓞 K) = orderOf (l : ZMod (ordCompl[l] N)) := by
  have h := (Nat.ordProj_mul_ordCompl_eq_self N l).symm
  have hm : ¬ l ∣ ordCompl[l] N := Nat.not_dvd_ordCompl hl.out (NeZero.ne N)
  generalize ordCompl[l] N = m at h hm ⊢
  generalize N.factorization l = v at h ⊢
  cases v with
  | zero =>
    rw [pow_zero, one_mul] at h
    subst h
    exact ⟨by simpa using ramificationIdxIn_eq_of_not_dvd l K hm, inertiaDegIn_eq_of_not_dvd l K hm⟩
  | succ k =>
    exact ⟨by rw [ramificationIdxIn_eq N K h hm, Nat.totient_prime_pow_succ hl.out],
      inertiaDegIn_eq N K h hm⟩

private theorem cycInertia_key (l : ℕ) [hl : Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] (σ : Gal(K/ℚ)) (i : ℕ)
    (h : ∀ x : 𝓞 K, Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ l ^ i) :
    ZMod.unitsMap (Nat.ordCompl_dvd N l) (galEquivZMod N K σ) =
      ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl.out (NeZero.ne N)) ^ i := by
  have hne : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩
  have hζ := (IsCyclotomicExtension.zeta_spec N ℚ K).toInteger_isPrimitiveRoot
  have hη := hζ.pow (NeZero.pos N) (Nat.ordProj_mul_ordCompl_eq_self N l).symm
  set η := (IsCyclotomicExtension.zeta_spec N ℚ K).toInteger ^ (ordProj[l] N)
  have h₀ : IsPrimitiveRoot (Ideal.Quotient.mk P η) (ordCompl[l] N) := by
    refine hη.idealQuotient_mk
      (by simpa using Ideal.IsPrime.ne_top inferInstance) ?_
    rw [← Ideal.pow_inertiaDeg l]
    exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))
  have hi := h η
  rw [galEquivZMod_smul_of_pow_eq N _ _
    ((hη.pow_eq_one_iff_dvd _).mpr (Nat.ordCompl_dvd N l)), map_pow,
    (h₀.isOfFinOrder (NeZero.ne _)).pow_inj_mod,
    ← h₀.eq_orderOf, ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow] at hi
  ext
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← hi, ZMod.natCast_val]
  rfl

private theorem cycInertia_card_map (H : Subgroup Gal(K/ℚ)) :
    Nat.card (H.map (galEquivZMod N K).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (galEquivZMod N K).injective

theorem map_inertia_eq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] :
    (P.inertia Gal(K/ℚ)).map (galEquivZMod N K).toMonoidHom = inertiaUnits N l := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨σ, hσ, rfl⟩
    have := cycInertia_key (N := N) l P σ 0 (fun x => by
      rw [pow_zero, pow_one, Ideal.Quotient.eq]
      exact hσ x)
    rw [pow_zero] at this
    exact this
  · rw [cycInertia_card_map, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(l : ℤ)}),
      (cycInertia_ef (N := N) l).1, inertiaUnits, ← MonoidHom.comap_bot, cycInertia_card_comap]
    simp

attribute [local instance] Ideal.Quotient.field in

theorem map_stabilizer_eq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] :
    (MulAction.stabilizer Gal(K/ℚ) P).map (galEquivZMod N K).toMonoidHom = decompUnits N l := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(l : ℤ)})
    (by simpa using (Fact.out : l.Prime).ne_zero) P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨σ, hσ, rfl⟩
    let τ := IsFractionRing.stabilizerHom Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P
      (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩
    have : CharP (ℤ ⧸ Ideal.span {(l : ℤ)}) l := ringChar.of_eq <| Int.ringChar_idealQuot l
    have : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    obtain ⟨i, hi⟩ :=
      FiniteField.exists_forall_apply_eq_pow (ℤ ⧸ Ideal.span {(l : ℤ)}) l (𝓞 K ⧸ P) τ
    have := cycInertia_key (N := N) l P σ i (fun x => by
      have h₁ := IsFractionRing.stabilizerHom_apply_apply_mk Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P
        (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩ x
      simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at h₁
      have h2 := hi (Ideal.Quotient.mk P x)
      rwa [h₁, Int.card_ideal_quot] at h2)
    exact ⟨i, by simpa using this.symm⟩
  · rw [cycInertia_card_map, Ideal.card_stabilizer_eq (Ideal.span {(l : ℤ)}),
      (cycInertia_ef (N := N) l).1, (cycInertia_ef (N := N) l).2, decompUnits,
      cycInertia_card_comap, Nat.card_zpowers, ← orderOf_injective _ Units.coeHom_injective,
      Units.coeHom_apply, ZMod.coe_unitOfCoprime]

private theorem cycInertia_conj (σ : Gal(K/ℚ)) (hσ : galEquivZMod N K σ = -1) (φ : K →+* ℂ)
    (x : K) : φ (σ x) = starRingEnd ℂ (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have key : φ.toRatAlgHom.comp (σ : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    change φ (σ _) = starRingEnd ℂ (φ _)
    have h1 : ‖φ (IsCyclotomicExtension.zeta N ℚ K)‖ = 1 :=
      (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne N)
    rw [← Complex.inv_eq_conj h1, ← map_inv₀, galEquivZMod_apply_of_pow_eq N K σ hζ.pow_eq_one, hσ]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    simp
  exact DFunLike.congr_fun key x

theorem card_fieldChars (E : IntermediateField ℚ K) :
    Nat.card (fieldChars N E) = Module.finrank ℚ E ∧
      (IsTotallyReal E ↔ ∀ ψ ∈ fieldChars N E, ψ.Even) := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N} ℚ K
  have hmem : ∀ ψ, ψ ∈ fieldChars N E ↔
      ∀ σ ∈ E.fixingSubgroup, ψ (galEquivZMod N K σ) = 1 := by
    intro ψ
    rw [fieldChars, mem_annihilator_iff]
    constructor
    · intro h σ hσ
      exact h _ ⟨σ, hσ, rfl⟩
    · rintro h _ ⟨σ, hσ, rfl⟩
      exact h σ hσ
  have heq : fieldChars N E = intermediateFieldEquivSubgroupChar N K ℂ E := by
    ext ψ
    rw [hmem, mem_intermediateFieldEquivSubgroupChar_iff]
  refine ⟨by rw [heq, card_intermediateFieldEquivSubgroupChar], ?_⟩
  obtain ⟨σ, hσ⟩ := (galEquivZMod N K).surjective (-1)
  have heq2 : fieldChars N E = (subgroupGalEquivSubgroupChar N K ℂ E.fixingSubgroup).ofDual := by
    ext ψ
    rw [hmem, mem_subgroupGalEquivSubgroupChar_iff]
  clear hmem heq
  generalize fieldChars N E = X at heq2 ⊢
  have h1 : σ ∈ E.fixingSubgroup ↔ ∀ ψ ∈ X, ψ.Even := by
    have := mem_subgroupGalEquivSubgroupChar_symm_iff N K ℂ σ X
    rw [hσ] at this
    conv_lhs at this => rw [heq2, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply]
    simpa [DirichletCharacter.Even] using this
  rw [← h1, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    apply φ.injective
    rw [cycInertia_conj σ hσ]
    have := IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap E K))
    rw [ComplexEmbedding.isReal_iff] at this
    exact RingHom.congr_fun this ⟨x, hx⟩
  · intro h
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← ComplexEmbedding.lift_algebraMap_apply K w.embedding,
      ← cycInertia_conj σ hσ]
    congr 1
    exact h x x.2

end KStar.Ram
end


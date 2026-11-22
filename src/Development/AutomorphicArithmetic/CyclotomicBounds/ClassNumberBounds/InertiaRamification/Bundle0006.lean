import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0004
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0005
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Filtration
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0003

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDisc
section
namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

private theorem isPrimitiveRoot_pow_val {R : Type*} [CommRing R] {z : R}
    (hz : IsPrimitiveRoot z N) (a : ZMod N) : IsPrimitiveRoot (z ^ a.val) (addOrderOf a) := by
  have h1 : addOrderOf a = orderOf (z ^ a.val) := by
    have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨N, NeZero.pos N, hz.pow_eq_one⟩
    rw [hfin.orderOf_pow, ← hz.eq_orderOf, ← ZMod.addOrderOf_coe _ (NeZero.ne N),
      ZMod.natCast_zmod_val]
  rw [h1]
  exact IsPrimitiveRoot.orderOf _

private theorem span_sub_smul {z : 𝓞 K} (hz : IsPrimitiveRoot z N) (σ : Gal(K/ℚ)) :
    Ideal.span {z - σ • z} =
      Ideal.span {1 - z ^ ((galEquivZMod N K σ : ZMod N) - 1).val} := by
  rw [galEquivZMod_smul_of_pow_eq N K σ hz.pow_eq_one]
  have h : z ^ (galEquivZMod N K σ).val.val =
      z ^ (1 + ((galEquivZMod N K σ : ZMod N) - 1).val) := by
    refine pow_eq_pow_of_modEq ?_ hz.pow_eq_one
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  rw [h, pow_add, pow_one, ← mul_one_sub]
  exact Ideal.span_singleton_mul_left_unit (hz.isUnit (NeZero.ne N)) _

private theorem padicValNat_prod {ι : Type*} (l : ℕ) [Fact l.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValNat l (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat l (f i) := by
  have hl : l.Prime := Fact.out
  simp only [← Nat.factorization_def _ hl]
  rw [Nat.factorization_prod hf, Finsupp.finsetSum_apply]

private theorem vdField_eq_avg (E : IntermediateField ℚ K) (l : ℕ) [Fact l.Prime] :
    vdField E l = avgCondExp l (fieldChars N E) := by
  classical
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have hz := hζ.toInteger_isPrimitiveRoot
  have h := congrArg Ideal.absNorm (map_differentIdeal_eq_span_prod E hζ)
  rw [Ideal.absNorm_algebraMap, absNorm_differentIdeal E,
    ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K, ← Ideal.prod_span_singleton, map_prod] at h
  have hne : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hne' := h ▸ pow_ne_zero (Module.finrank E K) hne
  have h2 := congrArg (padicValNat l) h
  rw [padicValNat.pow, padicValNat_prod l _ _ (Finset.prod_ne_zero_iff.1 hne')] at h2
  have h3 := congrArg (Nat.cast : ℕ → ℚ) h2
  push_cast at h3
  have h4 : ∀ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
      (padicValNat l (Ideal.absNorm (Ideal.span {hζ.toInteger - σ • hζ.toInteger})) : ℚ) =
        Module.finrank ℚ K * rootWeight l (addOrderOf ((galEquivZMod N K σ : ZMod N) - 1)) := by
    intro σ hσ
    rw [span_sub_smul hz σ]
    refine padicValNat_absNorm_one_sub l ?_ (isPrimitiveRoot_pow_val hz _)
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      exact (Finset.mem_filter.1 hσ).2 (one_mem _)
    have hpos := addOrderOf_pos ((galEquivZMod N K σ : ZMod N) - 1)
    have hne1 : addOrderOf ((galEquivZMod N K σ : ZMod N) - 1) ≠ 1 := by
      rw [Ne, AddMonoid.addOrderOf_eq_one_iff, sub_eq_zero, Units.val_eq_one,
        map_eq_one_iff _ (galEquivZMod N K).injective]
      exact hσ1
    omega
  rw [Finset.sum_congr rfl h4, ← Finset.mul_sum] at h3
  have h5 : ∑ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
      rootWeight l (addOrderOf ((galEquivZMod N K σ : ZMod N) - 1)) =
      avgCondExp l (fieldChars N E) := by
    rw [fieldChars, ← sum_rootWeight_eq_avgCondExp]
    refine Finset.sum_equiv (galEquivZMod N K).toEquiv ?_ (fun _ _ => rfl)
    intro σ
    rw [Finset.mem_filter_univ, Finset.mem_filter_univ, fieldUnits]
    exact not_congr (Subgroup.mem_map_iff_mem (f := (galEquivZMod N K).toMonoidHom)
      (galEquivZMod N K).injective).symm
  rw [h5, ← Module.finrank_mul_finrank ℚ E K] at h3
  have p1 : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have p2 : (Module.finrank E K : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [vdField, padicValInt, div_eq_iff p1]
  push_cast at h3
  apply mul_left_cancel₀ p2
  rw [h3]; ring

theorem natAbs_discr_eq_finprod_conductor (E : IntermediateField ℚ K) :
    (discr E).natAbs = ∏ᶠ ψ : fieldChars N E, (ψ : DirichletCharacter ℂ N).conductor ∧
      Real.log (rootDiscr E) = logRootDiscChar (fieldChars N E) ∧
      (discr E).natAbs.primeFactors = (fieldCond (fieldChars N E)).primeFactors := by
  classical
  have := Fintype.ofFinite (fieldChars N E)
  have hne : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hc : ∀ ψ : DirichletCharacter ℂ N, ψ.conductor ≠ 0 := fun ψ => conductor_ne_zero ψ
  have p1 : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hcard := (card_fieldChars (N := N) E).1
  have h1 : (discr E).natAbs = ∏ ψ : fieldChars N E, (ψ : DirichletCharacter ℂ N).conductor := by
    refine Nat.eq_of_factorization_eq hne (Finset.prod_ne_zero_iff.2 fun ψ _ => hc _) fun l => ?_
    by_cases hl : l.Prime
    · have : Fact l.Prime := ⟨hl⟩
      have h := vdField_eq_avg (N := N) E l
      rw [vdField, avgCondExp, hcard, div_left_inj' p1, finsum_eq_sum_of_fintype, padicValInt] at h
      rw [Nat.factorization_prod fun ψ _ => hc _, Finsupp.finsetSum_apply,
        Nat.factorization_def _ hl]
      exact_mod_cast h
    · simp [Nat.factorization_eq_zero_of_not_prime _ hl]
  refine ⟨by rw [finprod_eq_prod_of_fintype, h1], ?_, ?_⟩
  · have habs : ((|discr E| : ℤ) : ℝ) = ((discr E).natAbs : ℝ) := by
      rw [← Int.natCast_natAbs, Int.cast_natCast]
    rw [rootDiscr_def, logRootDiscChar, hcard, finsum_eq_sum_of_fintype, habs,
      Real.log_rpow (by exact_mod_cast Nat.pos_of_ne_zero hne), h1, Nat.cast_prod,
      Real.log_prod (fun ψ _ => by exact_mod_cast hc _), div_eq_inv_mul]
  · have hf : fieldCond (fieldChars N E) ≠ 0 := by
      rw [fieldCond, Ne, Finset.lcm_eq_zero_iff]
      rintro ⟨ψ, -, h⟩
      exact hc ψ h
    ext l
    rw [Nat.mem_primeFactors_of_ne_zero hne, Nat.mem_primeFactors_of_ne_zero hf]
    refine and_congr_right fun hl => ?_
    have : Fact l.Prime := ⟨hl⟩
    obtain ⟨a, b, -⟩ := ramIdx_eq_one_iff l (fieldChars N E)
    rw [h1, hl.prime.dvd_finsetProd_iff, ← not_iff_not, ← b, a]
    simp

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Places
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

omit [NeZero N] in
private theorem mem_ker_toUnitHom_iff (ψ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    u ∈ (MulChar.toUnitHom ψ).ker ↔ ψ (u : ZMod N) = 1 := by
  rw [MonoidHom.mem_ker, ← Units.val_eq_one, MulChar.coe_toUnitHom]

omit [NeZero N] in
private theorem charKer_le_ker {X : Subgroup (DirichletCharacter ℂ N)}
    {ψ : DirichletCharacter ℂ N} (h : ψ ∈ X) : charKer X ≤ (MulChar.toUnitHom ψ).ker :=
  iInf₂_le (f := fun (φ : DirichletCharacter ℂ N) (_ : φ ∈ X) => (MulChar.toUnitHom φ).ker) ψ h

omit [NeZero N] in
private theorem neg_one_notMem_ker {ψ : DirichletCharacter ℂ N} (o : ψ.Odd) :
    (-1 : (ZMod N)ˣ) ∉ (MulChar.toUnitHom ψ).ker := by
  rw [mem_ker_toUnitHom_iff]
  have h : ψ (-1) = -1 := o
  simp only [Units.val_neg, Units.val_one, h]
  norm_num

omit [NeZero N] in
private theorem not_conjIn_of_trivial {X : Subgroup (DirichletCharacter ℂ N)}
    {ψ : DirichletCharacter ℂ N} (h : ψ ∈ X) (o : ψ.Odd) {D : Subgroup (ZMod N)ˣ}
    (hD : ∀ u ∈ D, ψ (u : ZMod N) = 1) :
    D ⊔ charKer X ≤ (MulChar.toUnitHom ψ).ker ∧ ¬ ConjIn X D := by
  have hle : D ⊔ charKer X ≤ (MulChar.toUnitHom ψ).ker :=
    sup_le (fun u hu => (mem_ker_toUnitHom_iff ψ u).2 (hD u hu)) (charKer_le_ker h)
  exact ⟨hle, fun hc => neg_one_notMem_ker o (hle hc)⟩

theorem split_of_splitsFor (X : Subgroup (DirichletCharacter ℂ N)) {ch : DirichletCharacter ℂ N}
    (hch : ch ∈ X) (hodd : ch.Odd) (hs : SplitsFor l ch) :
    decompUnits N l ⊔ charKer X ≤ (MulChar.toUnitHom ch).ker ∧ ¬ ConjIn X (decompUnits N l) ∧
      numPlaces l X = 2 * numPlaces l (evenPart X) ∧
      ∀ σ τ : (ZMod N)ˣ, σ⁻¹ * τ ∈ decompUnits N l ⊔ charKer X →
        ch (σ : ZMod N) = ch (τ : ZMod N) := by
  obtain ⟨hle, hc⟩ := not_conjIn_of_trivial hch hodd ((splitsFor_iff l ch).2.1 hs)
  refine ⟨hle, hc, (conjIn_iff l X).1.2 hc, fun σ τ h => ?_⟩
  have h1 := (mem_ker_toUnitHom_iff ch _).1 (hle h)
  have h2 : (τ : ZMod N) = σ * ((σ⁻¹ * τ : (ZMod N)ˣ) : ZMod N) := by
    rw [← Units.val_mul, mul_inv_cancel_left]
  rw [h2, map_mul, h1, mul_one]

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.QuadraticCharacterLegendreSymbol
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N]

private lemma quad_gen {d : ℕ} [Fact d.Prime] {g : (ZMod d)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {χ : MulChar (ZMod d) ℂ} (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) : χ g = -1 := by
  have hs : χ g ^ 2 = 1 := by
    rw [← MulChar.pow_apply_coe, h2, MulChar.one_apply_coe]
  rcases sq_eq_one_iff.mp hs with h | h
  · exact absurd ((MulChar.eq_iff hg χ 1).mpr (by rw [h, MulChar.one_apply_coe])) h1
  · exact h

private noncomputable def quadC (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

private lemma quadC_sq (d : ℕ) [Fact d.Prime] : quadC d ^ 2 = 1 := by
  ext a
  rw [MulChar.pow_apply_coe, quadC, MulChar.ringHomComp_apply, ← map_pow,
    quadraticChar_sq_one a.ne_zero, map_one, MulChar.one_apply_coe]

private lemma quadC_ne (d : ℕ) [Fact d.Prime] (h : d ≠ 2) : quadC d ≠ 1 := by
  rw [quadC, Ne, MulChar.ringHomComp_eq_one_iff (by exact Int.cast_injective)]
  exact quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact h)

private lemma quad_unique {d : ℕ} [Fact d.Prime] {χ : DirichletCharacter ℂ d} (h2 : χ ^ 2 = 1)
    (h1 : χ ≠ 1) : χ = quadC d := by
  have hd : d ≠ 2 := by
    rintro rfl
    apply h1
    ext x
    rw [Subsingleton.elim x 1]
    simp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod d)ˣ)
  refine (MulChar.eq_iff hg _ _).mpr ?_
  rw [quad_gen hg h2 h1, quad_gen hg (quadC_sq d) (quadC_ne d hd)]

private lemma sub_smul_mul_sub_smul_eq_zero_of_quadratic {d c : ℕ} [Fact d.Prime] (hc : c = d) {χ : DirichletCharacter ℂ c}
    (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) (m : ℕ) : χ (m : ZMod c) = (legendreSym d m : ℂ) := by
  subst hc
  rw [quad_unique h2 h1]
  simp [quadC, legendreSym]

theorem exists_isImagQuad {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) (hN : d ∣ N) :
    ∃ ψ : DirichletCharacter ℂ N, IsImagQuad ψ d := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hd2 : d ≠ 2 := by
    rintro rfl
    norm_num at h4
  refine ⟨changeLevel hN (quadC d), ?_, ?_, ?_⟩
  · rw [← map_pow, quadC_sq, map_one]
  · show changeLevel hN (quadC d) (-1) = -1
    have hc := changeLevel_eq_cast_of_dvd' (quadC d) hN (a := -1)
      (by simpa using (isCoprime_one_left (x := (N : ℤ))).neg_left)
    push_cast at hc
    rw [hc, quadC, MulChar.ringHomComp_apply,
      quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; exact hd2), ZMod.card,
      ZMod.χ₄_nat_three_mod_four h4]
    simp
  · rw [conductor_changeLevel]
    rcases hd.eq_one_or_self_of_dvd _ (quadC d).conductor_dvd_level with h1 | h1
    · exact absurd (eq_one_iff_conductor_eq_one.mpr h1) (quadC_ne d hd2)
    · exact h1

theorem IsImagQuad.primitiveCharacter_eq {d : ℕ} [Fact d.Prime] {ψ : DirichletCharacter ℂ N}
    (h : IsImagQuad ψ d) (m : ℕ) :
    ψ.primitiveCharacter (m : ZMod ψ.conductor) = (legendreSym d m : ℂ) := by
  obtain ⟨h2, hodd, hc⟩ := h
  refine sub_smul_mul_sub_smul_eq_zero_of_quadratic hc ?_ ?_ m
  · apply changeLevel_injective ψ.conductor_dvd_level
    rw [map_pow, changeLevel_primitiveCharacter, h2, map_one]
  · intro h1
    have := changeLevel_primitiveCharacter ψ
    rw [h1, map_one] at this
    have h3 : ψ.conductor = 1 := eq_one_iff_conductor_eq_one.mp this.symm
    exact (Fact.out : d.Prime).one_lt.ne' (hc ▸ h3)

theorem IsImagQuad.values {d q₁ : ℕ} (hd : d.Prime) (hq : q₁.Prime) (hd8 : d % 8 = 7)
    (hq8 : q₁ % 8 = 3) {ch ps : DirichletCharacter ℂ N} (hch : IsImagQuad ch d)
    (hps : IsImagQuad ps q₁) :
    SplitsFor 2 ch ∧ ps.primitiveCharacter ((2 : ℕ) : ZMod ps.conductor) = -1 ∧
      (SplitsFor q₁ ch → ps.primitiveCharacter (d : ZMod ps.conductor) = -1) := by
  have : Fact d.Prime := ⟨hd⟩
  have : Fact q₁.Prime := ⟨hq⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold SplitsFor
    rw [hch.primitiveCharacter_eq]
    have : legendreSym d ((2 : ℕ) : ℤ) = 1 := by
      rw [Nat.cast_ofNat, legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight,
        if_neg (by omega), if_pos (by omega)]
    rw [this]; simp
  · rw [hps.primitiveCharacter_eq]
    have : legendreSym q₁ ((2 : ℕ) : ℤ) = -1 := by
      rw [Nat.cast_ofNat, legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight,
        if_neg (by omega), if_neg (by omega)]
    rw [this]; simp
  · unfold SplitsFor
    rw [hch.primitiveCharacter_eq, hps.primitiveCharacter_eq]
    intro h
    rw [legendreSym.quadratic_reciprocity_three_mod_four (p := d) (q := q₁) (by omega) (by omega)]
    push_cast
    rw [h]

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ResDeg
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

private theorem relIndex_zpowers_dvd_iff {G : Type*} [CommGroup G] (K : Subgroup G) (u : G)
    (k : ℕ) : K.relIndex (Subgroup.zpowers u ⊔ K) ∣ k ↔ u ^ k ∈ K := by
  have h : K.relIndex (Subgroup.zpowers u) = orderOf (QuotientGroup.mk' K u) := by
    rw [← Nat.card_zpowers, ← MonoidHom.map_zpowers, ← Subgroup.relIndex_ker,
      QuotientGroup.ker_mk']
  rw [Subgroup.relIndex_sup_right, h, orderOf_dvd_iff_pow_eq_one, ← map_pow,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [NeZero N] in
private theorem mem_charKer_iff' (X : Subgroup (DirichletCharacter ℂ N)) (u : (ZMod N)ˣ) :
    u ∈ charKer X ↔ ∀ ψ ∈ X, ψ (u : ZMod N) = 1 := by
  simp only [charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, ← Units.val_eq_one,
    MulChar.coe_toUnitHom]

private theorem mem_annihilator_inertia_sup (X : Subgroup (DirichletCharacter ℂ N))
    (ψ : DirichletCharacter ℂ N) :
    ψ ∈ annihilator ℂ ((inertiaUnits N l ⊔ charKer X : Subgroup (ZMod N)ˣ) : Set (ZMod N)ˣ) ↔
      ψ ∈ X ∧ ¬ l ∣ ψ.conductor := by
  obtain ⟨h1, h2⟩ := localPart_eq_one_iff l ψ
  rw [← h2, h1, mem_annihilator_iff]
  constructor
  · intro h
    refine ⟨?_, fun u hu => h u (Subgroup.mem_sup_left hu)⟩
    rw [← (annihilator_charKer X ⊥).1, mem_annihilator_iff]
    exact fun u hu => h u (Subgroup.mem_sup_right hu)
  · rintro ⟨hX, hI⟩ u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    rw [Units.val_mul, map_mul, hI a ha, (mem_charKer_iff' X b).1 hb ψ hX, one_mul]

private theorem exists_frobUnit :
    ∃ u : (ZMod N)ˣ, decompUnits N l = Subgroup.zpowers u ⊔ inertiaUnits N l ∧
      ∀ ψ : DirichletCharacter ℂ N, ¬ l ∣ ψ.conductor →
        ψ (u : ZMod N) = ψ.primitiveCharacter (l : ZMod ψ.conductor) := by
  have hl : l.Prime := Fact.out
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Nat.ordCompl_dvd N l)
    (ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl (NeZero.ne N)))
  refine ⟨u, ?_, fun ψ hψ => ?_⟩
  · unfold decompUnits inertiaUnits
    rw [← hu, ← MonoidHom.map_zpowers, Subgroup.comap_map_eq]
  · have hc : ψ.conductor ∣ ordCompl[l] N :=
      Nat.dvd_ordCompl_of_dvd_not_dvd ψ.conductor_dvd_level hψ
    have hu' : (ZMod.cast (u : ZMod N) : ZMod (ordCompl[l] N)) = (l : ZMod (ordCompl[l] N)) := by
      have := congrArg Units.val hu
      rwa [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at this
    have h2 : (ZMod.cast (u : ZMod N) : ZMod ψ.conductor) = (l : ZMod ψ.conductor) := by
      have e := congrArg (fun f : ZMod N →+* ZMod ψ.conductor => f (u : ZMod N))
        (ZMod.castHom_comp hc (Nat.ordCompl_dvd N l))
      simp only [RingHom.comp_apply] at e
      rw [ZMod.castHom_apply (h := Nat.ordCompl_dvd N l), hu', map_natCast,
        ZMod.castHom_apply] at e
      exact e.symm
    rw [← h2, ← changeLevel_eq_cast_of_dvd _ ψ.conductor_dvd_level, changeLevel_primitiveCharacter]

private theorem resDeg_dvd_iff_unit {u : (ZMod N)ˣ}
    (hu : decompUnits N l = Subgroup.zpowers u ⊔ inertiaUnits N l)
    (X : Subgroup (DirichletCharacter ℂ N)) (k : ℕ) :
    resDeg l X ∣ k ↔ ∀ ψ ∈ X, ¬ l ∣ ψ.conductor → ψ (u : ZMod N) ^ k = 1 := by
  unfold resDeg
  rw [hu, sup_assoc, relIndex_zpowers_dvd_iff,
    ← (annihilator_charKer ⊥ (inertiaUnits N l ⊔ charKer X)).2.1, mem_charKer_iff']
  simp only [mem_annihilator_inertia_sup, Units.val_pow_eq_pow_val, map_pow, and_imp]

theorem resDeg_sup (X Y : Subgroup (DirichletCharacter ℂ N)) (hX : ∀ ψ ∈ X, ¬ l ∣ ψ.conductor) :
    resDeg l (X ⊔ Y) = Nat.lcm (resDeg l X) (resDeg l Y) ∧ ramIdx l (X ⊔ Y) = ramIdx l Y ∧
      vd l (X ⊔ Y) = vd l Y := by
  have hX1 : ∀ ψ ∈ X, localPart N l ψ = 1 := fun ψ h => (localPart_eq_one_iff l ψ).2.2 (hX ψ h)
  have hmap : (X ⊔ Y).map (localPart N l) = Y.map (localPart N l) := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff X).2 (fun ψ h => hX1 ψ h), bot_sup_eq]
  refine ⟨?_, by unfold ramIdx; rw [hmap], by unfold vd; rw [hmap]⟩
  obtain ⟨u, hu, -⟩ := exists_frobUnit (N := N) l
  have key : ∀ k, resDeg l (X ⊔ Y) ∣ k ↔ Nat.lcm (resDeg l X) (resDeg l Y) ∣ k := by
    intro k
    rw [Nat.lcm_dvd_iff, resDeg_dvd_iff_unit l hu, resDeg_dvd_iff_unit l hu,
      resDeg_dvd_iff_unit l hu]
    constructor
    · exact fun h => ⟨fun ψ hψ => h ψ (Subgroup.mem_sup_left hψ),
        fun ψ hψ => h ψ (Subgroup.mem_sup_right hψ)⟩
    · rintro ⟨h1, h2⟩ ψ hψ hc
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hψ
      have hb' : ¬ l ∣ b.conductor := by
        have := (localPart_eq_one_iff l (a * b)).2.2 hc
        rw [map_mul, hX1 a ha, one_mul] at this
        exact (localPart_eq_one_iff l b).2.1 this
      rw [MulChar.mul_apply, mul_pow, h1 a ha (hX a ha), h2 b hb hb', one_mul]
  exact Nat.dvd_antisymm ((key _).2 dvd_rfl) ((key _).1 dvd_rfl)

theorem resDeg_zpowers (χ : DirichletCharacter ℂ N) (hχ : ¬ l ∣ χ.conductor) :
    resDeg l (Subgroup.zpowers χ) = orderOf (χ.primitiveCharacter (l : ZMod χ.conductor)) := by
  obtain ⟨u, hu, hv⟩ := exists_frobUnit (N := N) l
  have key : ∀ k, resDeg l (Subgroup.zpowers χ) ∣ k ↔ orderOf (χ (u : ZMod N)) ∣ k := by
    intro k
    rw [resDeg_dvd_iff_unit l hu, orderOf_dvd_iff_pow_eq_one]
    constructor
    · exact fun h => h χ (Subgroup.mem_zpowers χ) hχ
    · intro h ψ hψ _
      obtain ⟨m, rfl⟩ := mem_powers_iff_mem_zpowers.2 hψ
      show (χ ^ m) (u : ZMod N) ^ k = 1
      rw [MulChar.pow_apply_coe, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  rw [← hv χ hχ]
  exact Nat.dvd_antisymm ((key _).2 dvd_rfl) ((key _).1 dvd_rfl)

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.TwoPower
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N]

private theorem twoPower_exists_odd {k : ℕ} (hk : 2 ^ k ∣ N) (h2 : 2 ≤ k) :
    ∃ ψ ∈ condDvd N (2 ^ k), ψ.Odd := by
  have h4 : 4 ∣ 2 ^ k := (pow_dvd_pow 2 h2 : 2 ^ 2 ∣ 2 ^ k)
  have h4N : 4 ∣ N := h4.trans hk
  let χ : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
  refine ⟨changeLevel h4N χ, ?_, ?_⟩
  · rw [(mem_condDvd_iff _ _).1]
    exact (conductor_dvd_of_mem_conductorSet _ (changeLevel_factorsThrough χ h4N)).trans h4
  · have h := changeLevel_eq_cast_of_dvd' χ h4N (a := -1) (isCoprime_one_left.neg_left)
    have h' : ZMod.χ₄ (-1) = -1 := by decide
    unfold DirichletCharacter.Odd
    push_cast at h
    rw [h]
    simp [χ, h']

theorem card_evenPart_condDvd_two_pow {k : ℕ} (hk : 2 ^ k ∣ N) :
    Nat.card (evenPart (condDvd N (2 ^ k))) = 2 ^ (k - 2) := by
  have hc : Nat.card (condDvd N (2 ^ k)) = Nat.totient (2 ^ k) :=
    (mem_condDvd_iff (2 ^ k) 1).2 hk
  rcases Nat.lt_or_ge k 2 with h | h
  · have h1 : Nat.totient (2 ^ k) = 1 := by
      interval_cases k <;> simp
    have hle : Nat.card (evenPart (condDvd N (2 ^ k))) ≤ Nat.card (condDvd N (2 ^ k)) :=
      Subgroup.card_le_of_le inf_le_left
    have hpos : 0 < Nat.card (evenPart (condDvd N (2 ^ k))) := Nat.card_pos
    rw [show k - 2 = 0 by omega, pow_zero]
    omega
  · have h2 := (card_evenPart (condDvd N (2 ^ k))).2 (twoPower_exists_odd hk h)
    rw [hc, Nat.totient_prime_pow Nat.prime_two (by omega),
      show k - 1 = (k - 2) + 1 by omega, pow_succ] at h2
    omega

theorem fieldCond_evenPart_condDvd_two_pow {k : ℕ} (hk : 2 ^ k ∣ N) (h3 : 3 ≤ k) :
    fieldCond (evenPart (condDvd N (2 ^ k))) = 2 ^ k ∧
      ramIdx 2 (evenPart (condDvd N (2 ^ k))) = 2 ^ (k - 2) ∧
      resDeg 2 (evenPart (condDvd N (2 ^ k))) = 1 := by
  have hcard := card_evenPart_condDvd_two_pow hk
  set X := evenPart (condDvd N (2 ^ k)) with hX
  have hXle : X ≤ condDvd N (2 ^ k) := inf_le_left
  have hF := (fieldCond_sup X X 1).2.2
  have hram : ramIdx 2 X = Nat.card X := by
    have hbot : (localPart N 2).ker ⊓ X = ⊥ := by
      rw [eq_bot_iff]
      rintro ψ ⟨h1, h2⟩
      have h1' : ¬ 2 ∣ ψ.conductor := (localPart_eq_one_iff 2 ψ).2.1 h1
      have h2' : ψ.conductor ∣ 2 ^ k := (mem_condDvd_iff _ _).1.1 (hXle h2)
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2'
      rw [Subgroup.mem_bot, eq_one_iff_conductor_eq_one, hj]
      rcases j with _ | j
      · rfl
      · exact absurd (hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)) h1'
    unfold ramIdx
    rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, hbot, Subgroup.relIndex_bot_left]
  refine ⟨?_, hram.trans hcard, ?_⟩
  · obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 ((hF _).2 hXle)
    rw [hj]
    rcases hjk.eq_or_lt with rfl | hlt
    · rfl
    · exfalso
      have hle : X ≤ condDvd N (2 ^ (k - 1)) :=
        (hF _).1 (hj ▸ pow_dvd_pow 2 (by omega))
      have hle' : X ≤ evenPart (condDvd N (2 ^ (k - 1))) := le_inf hle inf_le_right
      have h := Subgroup.card_le_of_le hle'
      rw [hcard, card_evenPart_condDvd_two_pow ((pow_dvd_pow 2 (Nat.sub_le k 1)).trans hk)] at h
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
      omega
  · have e2 : ramIdxUnits 2 (charKer X) * (inertiaUnits N 2 ⊔ charKer X).index =
        (charKer X).index := by
      unfold ramIdxUnits
      rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← Subgroup.relIndex_sup_right,
        Subgroup.relIndex_mul_index le_sup_right]
    rw [← ramIdx_eq_ramIdxUnits, hram, ← (annihilator_charKer X ⊥).2.2] at e2
    have hpos : 0 < Nat.card X := Nat.card_pos
    have h1 : (inertiaUnits N 2 ⊔ charKer X).index = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [e2, mul_one])
    unfold resDeg
    rw [Subgroup.index_eq_one.1 h1, Subgroup.relIndex_top_left]

end KStar.Ram
end


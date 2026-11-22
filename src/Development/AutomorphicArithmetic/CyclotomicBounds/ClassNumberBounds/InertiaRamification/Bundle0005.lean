import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0003

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Decomp
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

private lemma inertia_le_decomp : inertiaUnits N l ≤ decompUnits N l := by
  intro u hu
  unfold inertiaUnits at hu
  unfold decompUnits
  rw [MonoidHom.mem_ker] at hu
  rw [Subgroup.mem_comap, hu]
  exact Subgroup.one_mem _

private lemma relIndex_sup_zpowers_of_mem {G : Type*} [CommGroup G] (A : Subgroup G) (c : G)
    (h : c ∈ A) : A.relIndex (A ⊔ Subgroup.zpowers c) = 1 := by
  rw [Subgroup.relIndex_eq_one]
  exact sup_le le_rfl ((Subgroup.zpowers_le).2 h)

private lemma relIndex_sup_zpowers_of_notMem {G : Type*} [CommGroup G] (A : Subgroup G) (c : G)
    (hc : c * c = 1) (h : c ∉ A) : A.relIndex (A ⊔ Subgroup.zpowers c) = 2 := by
  rw [Subgroup.relIndex_sup_left, Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨c, Subgroup.mem_zpowers c, h, ?_⟩
  rintro b ⟨k, rfl⟩
  have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two, hc]
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · right
    simp only [zpow_mul, h2, one_zpow]
    exact A.one_mem
  · left
    simp only [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one, hc]
    exact A.one_mem

omit [NeZero N] in
private lemma mem_charKer_iff' (X : Subgroup (DirichletCharacter ℂ N)) (u : (ZMod N)ˣ) :
    u ∈ charKer X ↔ ∀ ψ ∈ X, ψ (u : ZMod N) = 1 := by
  unfold charKer
  simp only [Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
    Units.val_one]

private lemma charKer_evenPart' (X : Subgroup (DirichletCharacter ℂ N)) :
    charKer (evenPart X) = charKer X ⊔ Subgroup.zpowers (-1) := by
  have key : evenPart X =
      annihilator ℂ ((charKer X ⊔ Subgroup.zpowers (-1) : Subgroup (ZMod N)ˣ) : Set (ZMod N)ˣ) := by
    ext ψ
    have h1 : ψ ∈ X ↔ charKer X ≤ (MulChar.toUnitHom ψ).ker := by
      conv_lhs => rw [← (annihilator_charKer X ⊥).1]
      rw [mem_annihilator_iff]
      refine forall_congr' fun u => ?_
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
        Units.val_one]
    have h2 : ∀ K : Subgroup (ZMod N)ˣ, ψ ∈ annihilator ℂ (K : Set (ZMod N)ˣ) ↔
        K ≤ (MulChar.toUnitHom ψ).ker := by
      intro K
      rw [mem_annihilator_iff]
      refine forall_congr' fun u => ?_
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
        Units.val_one]
    unfold evenPart
    rw [h2, sup_le_iff, Subgroup.mem_inf, h1, Subgroup.zpowers_le, mem_annihilator_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  rw [key]
  exact (annihilator_charKer X _).2.1

private lemma ramIdx_eq_relIndex' (X : Subgroup (DirichletCharacter ℂ N)) :
    ramIdx l X = (charKer X).relIndex (inertiaUnits N l ⊔ charKer X) := by
  rw [ramIdx_eq_ramIdxUnits, ramIdxUnits, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk',
    Subgroup.relIndex_sup_right]

theorem splitsFor_iff (ψ : DirichletCharacter ℂ N) :
    inertiaUnits N l ≤ decompUnits N l ∧
      (SplitsFor l ψ ↔ ∀ u ∈ decompUnits N l, ψ (u : ZMod N) = 1) := by
  refine ⟨inertia_le_decomp l, ?_⟩
  unfold SplitsFor
  rw [← mem_subgroupOfPrimitiveMapToOne_iff]
  simp only [subgroupOfPrimitiveMapToOne, Subgroup.mem_map, mem_annihilator_iff,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨χ, hχ, rfl⟩ u hu
    unfold decompUnits at hu
    rw [Subgroup.mem_comap] at hu
    obtain ⟨k, hk⟩ := hu
    have h1 : MulChar.toUnitHom χ (ZMod.unitOfCoprime l
        (Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N))) = 1 := by
      rw [Units.ext_iff, MulChar.coe_toUnitHom, hχ, Units.val_one]
    rw [← MulChar.coe_toUnitHom, changeLevel_toUnitHom, MonoidHom.comp_apply, ← hk]
    simp only [map_zpow, h1, one_zpow, Units.val_one]
  · intro h
    have hf : ψ.FactorsThrough (ordCompl[l] N) := by
      rw [factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N l)]
      intro u hu
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
      exact h u (inertia_le_decomp l hu)
    obtain ⟨hd, χ, rfl⟩ := hf
    refine ⟨χ, ?_, rfl⟩
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd (ZMod.unitOfCoprime l
        (Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)))
    have hmem : u ∈ decompUnits N l := by
      unfold decompUnits
      rw [Subgroup.mem_comap, hu]
      exact Subgroup.mem_zpowers _
    have := h u hmem
    rw [← MulChar.coe_toUnitHom, changeLevel_toUnitHom, MonoidHom.comp_apply, hu,
      MulChar.coe_toUnitHom] at this
    exact this

theorem ramIdx_mul_resDeg_mul_numPlaces (X : Subgroup (DirichletCharacter ℂ N)) :
    ramIdx l X * resDeg l X * numPlaces l X = Nat.card X := by
  have h : inertiaUnits N l ⊔ charKer X ≤ decompUnits N l ⊔ charKer X :=
    sup_le_sup_right (inertia_le_decomp l) _
  rw [ramIdx_eq_relIndex', resDeg, numPlaces,
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right h,
    Subgroup.relIndex_mul_index le_sup_right, (annihilator_charKer X ⊥).2.2]

theorem conjIn_iff (X : Subgroup (DirichletCharacter ℂ N)) :
    (numPlaces l X = 2 * numPlaces l (evenPart X) ↔ ¬ ConjIn X (decompUnits N l)) ∧
      ((∃ ψ ∈ X, ψ.Odd) →
        (ramIdx l X = ramIdx l (evenPart X) ↔ ¬ ConjIn X (inertiaUnits N l))) := by
  have hc : (-1 : (ZMod N)ˣ) * (-1) = 1 := by simp
  constructor
  · unfold numPlaces ConjIn
    rw [charKer_evenPart', ← sup_assoc]
    set A := decompUnits N l ⊔ charKer X
    have h1 := Subgroup.relIndex_mul_index (le_sup_left : A ≤ A ⊔ Subgroup.zpowers (-1))
    have h0 : (A ⊔ Subgroup.zpowers (-1)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_cases h : (-1 : (ZMod N)ˣ) ∈ A
    · rw [relIndex_sup_zpowers_of_mem A _ h] at h1
      simp only [h, not_true_eq_false, iff_false]
      omega
    · rw [relIndex_sup_zpowers_of_notMem A _ hc h] at h1
      simp only [h, not_false_eq_true, iff_true]
      omega
  · rintro ⟨ψ, hψ, hodd⟩
    have hH : (-1 : (ZMod N)ˣ) ∉ charKer X := by
      intro h
      have := (mem_charKer_iff' X _).1 h ψ hψ
      refine ψ.not_even_and_odd ⟨?_, hodd⟩
      simpa [DirichletCharacter.Even] using this
    unfold ConjIn
    rw [ramIdx_eq_relIndex', ramIdx_eq_relIndex', charKer_evenPart', ← sup_assoc]
    set H := charKer X
    set A := inertiaUnits N l ⊔ H with hA
    have hHA : H ≤ A := le_sup_right
    have h1 := Subgroup.relIndex_mul_relIndex H A (A ⊔ Subgroup.zpowers (-1)) hHA le_sup_left
    have h2 := Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers (-1))
      (A ⊔ Subgroup.zpowers (-1)) le_sup_left (sup_le_sup_right hHA _)
    rw [relIndex_sup_zpowers_of_notMem H _ hc hH] at h2
    have h0 : (H ⊔ Subgroup.zpowers (-1)).relIndex (A ⊔ Subgroup.zpowers (-1)) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    by_cases h : (-1 : (ZMod N)ˣ) ∈ A
    · rw [relIndex_sup_zpowers_of_mem A _ h] at h1
      simp only [h, not_true_eq_false, iff_false]
      omega
    · rw [relIndex_sup_zpowers_of_notMem A _ hc h] at h1
      simp only [h, not_false_eq_true, iff_true]
      omega

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.RootNorm
section
namespace KStar.Ram

open NumberField

private theorem rootNorm_powerBasis {F : Type*} [Field F] [Algebra ℚ F] (pb : PowerBasis ℚ F) :
    Algebra.norm ℚ (1 - pb.gen) = (minpoly ℚ pb.gen).eval 1 := by
  classical
  rw [← charpoly_leftMulMatrix, Matrix.eval_charpoly, Algebra.norm_eq_matrix_det pb.basis,
    map_sub, map_one, map_one]

private theorem rootNorm_field {K : Type*} [Field K] [NumberField K] (x : K) :
    ∃ k : ℕ, Module.finrank ℚ K = (minpoly ℚ x).natDegree * k ∧
      Algebra.norm ℚ (1 - x) = ((minpoly ℚ x).eval 1) ^ k := by
  have hx : IsIntegral ℚ x := .of_finite ℚ x
  refine ⟨Module.finrank (IntermediateField.adjoin ℚ {x}) K, ?_, ?_⟩
  · rw [← IntermediateField.adjoin.finrank hx, Module.finrank_mul_finrank]
  · have h1 : (1 - x : K) = algebraMap (IntermediateField.adjoin ℚ {x}) K
        (1 - IntermediateField.AdjoinSimple.gen ℚ x) := by
      simp
    have h2 := rootNorm_powerBasis (IntermediateField.adjoin.powerBasis hx)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h2
    rw [h1, ← Algebra.norm_norm (S := IntermediateField.adjoin ℚ {x}), Algebra.norm_algebraMap, map_pow]
    exact congrArg (· ^ Module.finrank (IntermediateField.adjoin ℚ {x}) K) h2

theorem padicValNat_absNorm_one_sub {K : Type*} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime]
    {m : ℕ} (hm : 2 ≤ m) {η : 𝓞 K} (hη : IsPrimitiveRoot η m) :
    (padicValNat l (Ideal.absNorm (Ideal.span {1 - η})) : ℚ) =
      Module.finrank ℚ K * rootWeight l m := by
  haveI : NeZero m := ⟨by omega⟩
  have hηK : IsPrimitiveRoot (η : K) m :=
    hη.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  obtain ⟨k, hk, hnorm⟩ := rootNorm_field (η : K)
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega), Polynomial.natDegree_cyclotomic] at hk
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega)] at hnorm
  have hcQ : (Polynomial.cyclotomic m ℚ).eval 1 = (((Polynomial.cyclotomic m ℤ).eval 1 : ℤ) : ℚ) := by
    rw [← Polynomial.map_cyclotomic_int, ← Int.cast_one, Polynomial.eval_intCast_map, eq_intCast,
      Int.cast_one]
  have hnormZ : Algebra.norm ℤ (1 - η) = ((Polynomial.cyclotomic m ℤ).eval 1) ^ k := by
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, Int.cast_pow, ← hcQ, ← hnorm]
    push_cast
    rfl
  have hv : (padicValNat l ((Polynomial.cyclotomic m ℤ).eval 1).natAbs : ℚ) =
      m.totient * rootWeight l m := by
    by_cases hpp : ∃ p j, p.Prime ∧ m = p ^ (j + 1)
    · obtain ⟨p, j, hp, rfl⟩ := hpp
      haveI := Fact.mk hp
      rw [Polynomial.eval_one_cyclotomic_prime_pow, Int.natAbs_natCast]
      have hne : p ^ (j + 1) ≠ 1 := fun h => by rw [h] at hm; norm_num at hm
      by_cases hpl : p = l
      · subst hpl
        rw [padicValNat_self, rootWeight, if_pos ⟨hne, j + 1, rfl⟩]
        have ht : ((p ^ (j + 1)).totient : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr (by positivity)).ne'
        rw [Nat.cast_one, mul_one_div, div_self ht]
      · rw [padicValNat_primes (Ne.symm hpl), rootWeight, if_neg]
        · simp
        · rintro ⟨-, s, hs⟩
          apply hpl
          rcases s with _ | s
          · rw [pow_zero] at hs
            exact absurd hs hne
          · have hd : p ∣ l ^ (s + 1) := by
              rw [← hs]
              exact dvd_pow_self p (Nat.succ_ne_zero j)
            exact (Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp (hp.dvd_of_dvd_pow hd)
    · have h1 : Polynomial.eval 1 (Polynomial.cyclotomic m ℤ) = 1 := by
        apply Polynomial.eval_one_cyclotomic_not_prime_pow
        intro p hp j hj
        rcases j with _ | j
        · rw [pow_zero] at hj
          omega
        · exact hpp ⟨p, j, hp, hj.symm⟩
      rw [h1, rootWeight, if_neg]
      · simp
      · rintro ⟨-, s, hs⟩
        rcases s with _ | s
        · rw [pow_zero] at hs
          omega
        · exact hpp ⟨l, s, Fact.out, hs⟩
  rw [Ideal.absNorm_span_singleton, hnormZ, Int.natAbs_pow, padicValNat.pow, hk]
  push_cast
  rw [hv]
  ring

end KStar.Ram
end


import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvEntryNormLeOfSubSmulOnePosSemidef
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem inv_entry_norm_le_of_sub_posSemidef (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ)
    (hc : 0 < c) (hY : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) (i j : Fin g) :
    ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by

  have hq : ∀ x : Fin g → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Y *ᵥ x) := by
    intro x
    have h := hY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at h
    linarith

  have hdet : IsUnit Y.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hYv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have h1 := hq v
    rw [hYv, dotProduct_zero] at h1
    have h2 : v ⬝ᵥ v = 0 := le_antisymm (by nlinarith [dotProduct_self_star_nonneg v]) (by
      simpa using dotProduct_self_star_nonneg v)
    exact hv (by simpa using h2)
  have hYinv : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hdet

  have hmap : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [show Y.map Complex.ofReal = Y.map Complex.ofRealHom from rfl,
      show Y⁻¹.map Complex.ofReal = Y⁻¹.map Complex.ofRealHom from rfl, ← Matrix.map_mul, hYinv]
    simp
  rw [hmap, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]

  set w : Fin g → ℝ := Y⁻¹ *ᵥ Pi.single j 1 with hw
  have hYw : Y *ᵥ w = Pi.single j 1 := by
    rw [hw, mulVec_mulVec, hYinv, one_mulVec]
  have hwi : ∀ k, w k = Y⁻¹ k j := by
    intro k; simp [hw, mulVec_single_one]
  have hqw : c * (w ⬝ᵥ w) ≤ w j := by
    have := hq w
    rw [hYw, dotProduct_single, mul_one] at this
    exact this
  have hsq : ∀ k, w k ^ 2 ≤ w ⬝ᵥ w := by
    intro k
    rw [dotProduct]
    have := Finset.single_le_sum (f := fun l => w l * w l) (fun l _ => mul_self_nonneg (w l))
      (Finset.mem_univ k)
    simpa [sq] using this
  have hj1 := hsq j
  have hi1 := hsq i
  have hwj0 : 0 ≤ w j := by nlinarith [sq_nonneg (w j)]
  have hcwj : c * w j ≤ 1 := by
    rcases hwj0.lt_or_eq with h | h
    · nlinarith
    · rw [← h]; linarith
  have hci1 : c * w i ^ 2 ≤ w j := le_trans (mul_le_mul_of_nonneg_left hi1 hc.le) hqw
  have hci : (c * w i) ^ 2 ≤ 1 := by
    calc (c * w i) ^ 2 = c * (c * w i ^ 2) := by ring
      _ ≤ c * w j := mul_le_mul_of_nonneg_left hci1 hc.le
      _ ≤ 1 := hcwj
  have habs : |c * w i| ≤ 1 := sq_le_one_iff_abs_le_one _ |>.1 hci
  rw [← hwi i, le_div_iff₀ hc]
  rw [abs_mul, abs_of_pos hc] at habs
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfValued
section
open IsDedekindDomain NumberField
namespace GlobalTheory
namespace DegreeOneUniformiser

open IsDedekindDomain NumberField in
private theorem adicCompletionIntegers_integers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers F) :=
  ⟨Subtype.val_injective, fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2,
    fun x hx => ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mpr hx⟩, rfl⟩⟩

open IsDedekindDomain NumberField in

theorem _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F)
    (h : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  have hI := adicCompletionIntegers_integers v
  have hunit : ∀ x : v.adicCompletionIntegers F, IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
    fun x => hI.isUnit_iff_valuation_eq_one
  have hle : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) ≤ 1 :=
    fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := (hunit π).mp hu
    rw [h] at this
    exact absurd this (by decide)
  · have hv : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
        WithZero.exp (-1 : ℤ) := by
      rw [← h, hab, Subring.coe_mul, map_mul]
    have ha0 : Valued.v (a : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
    have hb0 : Valued.v (b : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (a : v.adicCompletion F) = WithZero.exp m :=
      ⟨_, (WithZero.exp_log ha0).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (b : v.adicCompletion F) = WithZero.exp n :=
      ⟨_, (WithZero.exp_log hb0).symm⟩
    have ha := hle a
    have hb := hle b
    rw [hm, hn, ← WithZero.exp_add, WithZero.exp_inj] at hv
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb
    rw [hunit, hunit, hm, hn, ← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega

open IsDedekindDomain NumberField in

theorem _root_.GlobalTheory.DegreeOneUniformiser.exists_irreducible_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (ψ : E →+* v.adicCompletion F), (∀ a : F, ψ (algebraMap F E a) = algebraMap F (v.adicCompletion F) a) → (∀ x : 𝓞 E, ψ (x : E) ∈ v.adicCompletionIntegers F) → (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ψ ((x : E)⁻¹) ∉ v.adicCompletionIntegers F)) → ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ π : v.adicCompletionIntegers F, Irreducible π ∧ (π : v.adicCompletion F) = ψ (ϖ : E) := by
  intro F E _ _ _ _ _ v P ψ hψ hint hP ϖ hϖP hϖP2
  have hle : ∀ x : 𝓞 E, Valued.v (ψ (x : E)) ≤ 1 := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hint x)
  have hne : ∀ x : 𝓞 E, x ≠ 0 → Valued.v (ψ (x : E)) ≠ 0 := by
    intro x hx
    rw [Valuation.ne_zero_iff, map_ne_zero_iff _ ψ.injective]
    exact_mod_cast hx
  have hone : ∀ x : 𝓞 E, x ∉ P.asIdeal → Valued.v (ψ (x : E)) = 1 := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => hx (h ▸ P.asIdeal.zero_mem)
    have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp
      (not_not.mp (mt (hP x hx0).mpr hx))
    rw [map_inv₀, map_inv₀] at h1
    exact le_antisymm (hle x) ((inv_le_one₀ (zero_lt_iff.mpr (hne x hx0))).mp h1)
  have hϖ0 : ϖ ≠ 0 := fun h => hϖP2 (h ▸ Ideal.zero_mem _)
  have hlt : Valued.v (ψ (ϖ : E)) < 1 := by
    have h1 := (hP ϖ hϖ0).mp hϖP
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀] at h1
    exact (one_lt_inv₀ (zero_lt_iff.mpr (hne ϖ hϖ0))).mp h1
  obtain ⟨u, hu⟩ := v.intValuation_exists_uniformizer
  let f : 𝓞 E := ⟨algebraMap F E (u : F), (RingOfIntegers.isIntegral_coe u).algebraMap⟩
  have hf : Valued.v (ψ (f : E)) = WithZero.exp (-1 : ℤ) := by
    show Valued.v (ψ (algebraMap F E (u : F))) = _
    rw [hψ, ← hu, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (u : F)
  have hf0 : f ≠ 0 := fun h => by
    rw [h] at hf
    simp only [ZeroMemClass.coe_zero, map_zero] at hf
    exact WithZero.exp_ne_zero hf.symm
  have hfP : f ∈ P.asIdeal := by
    rw [hP f hf0, HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀, hf,
      ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem _).mpr hϖP : Ideal.span {ϖ} ≤ P.asIdeal)
  have hJP : ¬ J ≤ P.asIdeal := fun hJP => hϖP2 (by
    have hmem : ϖ ∈ Ideal.span {ϖ} := Ideal.mem_span_singleton_self ϖ
    rw [hJ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hJP hmem)
  obtain ⟨t, htJ, htP⟩ := Set.not_subset.mp hJP
  have hft : f * t ∈ Ideal.span {ϖ} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hfP htJ
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hft
  have hval := congrArg (fun x : 𝓞 E => Valued.v (ψ (x : E))) hs
  simp only [MulMemClass.coe_mul, map_mul] at hval
  rw [hone t htP, mul_one, hf] at hval
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v (ψ (ϖ : E)) := by
    rw [← hval]
    calc Valued.v (ψ (s : E)) * Valued.v (ψ (ϖ : E)) ≤ 1 * Valued.v (ψ (ϖ : E)) :=
          mul_le_mul' (hle s) le_rfl
      _ = Valued.v (ψ (ϖ : E)) := one_mul _
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (ψ (ϖ : E)) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log (hne ϖ hϖ0)).symm⟩
  rw [hm, WithZero.exp_le_exp] at hge
  rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  have hm1 : m = -1 := by omega
  refine ⟨⟨ψ (ϖ : E), hint ϖ⟩, _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued v _ ?_, rfl⟩
  rw [← hm1]
  exact hm

end DegreeOneUniformiser
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDomainOfIsIntegrallyClosedOfIsReduced
section
open IsLocalRing

namespace GlobalTheory

theorem eq_zero_of_mem_minimalPrimes {R : Type} [CommRing R] [IsReduced R] {y : R}
    (hy : ∀ P ∈ minimalPrimes R, y ∈ P) : y = 0 := by
  have : y ∈ nilradical R := by
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    intro J hJ
    haveI : Ideal.IsPrime J := hJ
    obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := J) bot_le
    exact hpJ (hy p hp)
  rw [nilradical_eq_zero] at this
  simpa using this

theorem isDomain_of_isIntegrallyClosed_of_isReduced :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R],
      IsIntegrallyClosed R → IsDomain R := by
  intro R _ _ _ _ hic
  classical
  suffices hbot : (⊥ : Ideal R).IsPrime by
    haveI : NoZeroDivisors R := ⟨fun {x y} h => by
      have : x * y ∈ (⊥ : Ideal R) := by simp [h]
      simpa using hbot.mem_or_mem this⟩
    exact NoZeroDivisors.to_isDomain R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  obtain ⟨P, hP⟩ : ∃ P, P ∈ minimalPrimes R := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
      (J := IsLocalRing.maximalIdeal R) bot_le
    exact ⟨p, hp⟩
  have hPprime : P.IsPrime := hP.1.1
  have minle : ∀ {A B : Ideal R}, A ∈ minimalPrimes R → B ∈ minimalPrimes R → A ≤ B → A = B :=
    fun {A B} hA hB hAB => le_antisymm hAB (hB.2 hA.1 hAB)
  set T : Finset (Ideal R) := hfin.toFinset with hT
  have memT : ∀ Q, Q ∈ T ↔ Q ∈ minimalPrimes R := fun Q => by simp [T]
  set Q : Ideal R := (T.erase P).inf id with hQ
  have hQle : ∀ P' ∈ T.erase P, Q ≤ P' := fun P' h => Finset.inf_le (f := id) h
  by_cases hone : T.erase P = ∅
  ·
    have hPbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
        by_cases h : P' = P
        · exact h ▸ hy
        · have : P' ∈ T.erase P := Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩
          simp [hone] at this)
      simp [this]
    exact hPbot ▸ hPprime
  exfalso
  obtain ⟨P₂, hP₂⟩ := Finset.nonempty_iff_ne_empty.2 hone

  have hnot : ¬ ((P ⊔ Q : Ideal R) : Set R) ⊆ ⋃ i ∈ (↑T : Set (Ideal R)), (i : Set R) := by
    intro hsub
    obtain ⟨P', hP'T, hle⟩ := (Ideal.subset_union_prime (f := id) P P
      (fun i hi _ _ => ((memT i).1 hi).1.1)).1 hsub
    have hle' : P ⊔ Q ≤ P' := hle
    have h1 : P = P' := minle hP ((memT P').1 hP'T) (le_sup_left.trans hle')
    have hQP : Q ≤ P := by
      have h2 : Q ≤ P' := le_sup_right.trans hle'
      rw [← h1] at h2
      exact h2
    obtain ⟨P'', hP''e, hP''le⟩ := (Ideal.IsPrime.inf_le' (s := T.erase P) (f := id) hPprime).1 hQP
    have : P'' = P := minle ((memT P'').1 (Finset.mem_of_mem_erase hP''e)) hP hP''le
    exact Finset.ne_of_mem_erase hP''e this
  obtain ⟨s, hsPQ, hsout⟩ := Set.not_subset.1 hnot
  have hsnot : ∀ P' ∈ minimalPrimes R, s ∉ P' := fun P' hP' hs =>
    hsout (Set.mem_biUnion (x := P') (by simpa [memT] using hP') hs)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hsPQ
  have hsnzd : ∀ y : R, y * s = 0 → y = 0 := fun y hy =>
    eq_zero_of_mem_minimalPrimes (fun P' hP' => by
      have : y * s ∈ P' := by simp [hy]
      exact (hP'.1.1.mem_or_mem this).resolve_right (hsnot P' hP'))
  have hab0 : a * b = 0 := eq_zero_of_mem_minimalPrimes (fun P' hP' => by
    by_cases h : P' = P
    · exact h ▸ P.mul_mem_right b ha
    · exact P'.mul_mem_left a (hQle P' (Finset.mem_erase.2 ⟨h, (memT P').2 hP'⟩) hb))
  have hs : s ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_right.2 hsnzd
  let K := FractionRing R
  set e : K := IsLocalization.mk' K a ⟨s, hs⟩ with he_def
  have hspec : e * algebraMap R K s = algebraMap R K a := IsLocalization.mk'_spec K a ⟨s, hs⟩
  have ht : IsUnit (algebraMap R K s) := IsLocalization.map_units K (⟨s, hs⟩ : nonZeroDivisors R)
  have has : a * s = a * a := by rw [← hab, mul_add, hab0, add_zero]
  have hee : e * e = e := by
    refine (ht.mul ht).mul_left_inj.1 ?_
    calc e * e * (algebraMap R K s * algebraMap R K s)
        = (e * algebraMap R K s) * (e * algebraMap R K s) := by ring
      _ = algebraMap R K (a * a) := by rw [hspec, map_mul]
      _ = algebraMap R K (a * s) := by rw [has]
      _ = (e * algebraMap R K s) * algebraMap R K s := by rw [hspec, map_mul]
      _ = e * (algebraMap R K s * algebraMap R K s) := by ring
  have hint : IsIntegral R e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
    · simp [Polynomial.eval₂_sub, sq, hee]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj := IsFractionRing.injective R K
  have hrr : r * r = r := hinj (by rw [map_mul, hr, hee])
  have hrs : r * s = a := hinj (by rw [map_mul, hr, hspec])
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hu | hu
  · have hr1 : r = 1 := hu.mul_left_cancel (by rw [hrr, mul_one])
    rw [hr1, one_mul] at hrs

    exact hsnot P hP (hrs ▸ ha)
  · have hr0 : r = 0 := by
      have : (1 - r) * r = 0 := by rw [sub_mul, one_mul, hrr, sub_self]
      exact (hu.mul_right_eq_zero).1 this
    rw [hr0, zero_mul] at hrs

    have hsb : s = b := by rw [← hab, ← hrs, zero_add]
    exact hsnot P₂ ((memT P₂).1 (Finset.mem_of_mem_erase hP₂)) (hsb ▸ hQle P₂ hP₂ hb)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFractionRingStalkGeneric
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem residueField_isFractionRing_of_generic : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x),
    IsDomain (X.presheaf.stalk x) → (∀ y, y ⤳ ξ → y = ξ) →
    @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _
      (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) := by
  intro X x ξ e hd hgen

  have hnil : ∀ s : X.presheaf.stalk ξ, X.residue ξ s = 0 → IsNilpotent s := by
    intro s hs
    have hs' : s ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.residue_eq_zero_iff s).mp hs
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    let q : PrimeSpectrum (X.presheaf.stalk ξ) := ⟨J, hJ⟩
    have h1 : X.fromSpecStalk ξ q ⤳ ξ := by
      have : X.fromSpecStalk ξ q ∈ Set.range (X.fromSpecStalk ξ) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h2 : q = IsLocalRing.closedPoint _ :=
      (X.fromSpecStalk ξ).isEmbedding.injective
        ((hgen _ h1).trans Scheme.fromSpecStalk_closedPoint.symm)
    have h3 : J = IsLocalRing.maximalIdeal _ := congrArg PrimeSpectrum.asIdeal h2
    rw [h3]; exact hs'
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hξU : ξ ∈ U := e.mem_open U.2 hxU
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨ξ, hξU⟩ : U)
  haveI hLx := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI hLξ := hU.isLocalization_stalk ⟨ξ, hξU⟩
  have hsp : ∀ a : Γ(X, U), X.presheaf.stalkSpecializes e (X.presheaf.germ U x hxU a) =
      X.presheaf.germ U ξ hξU a :=
    fun a => X.presheaf.germ_stalkSpecializes_apply hxU e a
  have hunitξ : ∀ b ∈ (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl,
      IsUnit (X.presheaf.germ U ξ hξU b) :=
    fun b hb => IsLocalization.map_units (X.presheaf.stalk (⟨ξ, hξU⟩ : U))
      (⟨b, hb⟩ : (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl)
  have hne : ∀ b ∈ (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl,
      X.presheaf.germ U x hxU b ≠ 0 := by
    intro b hb h0
    have h' := congrArg (X.presheaf.stalkSpecializes e) h0
    rw [hsp, map_zero] at h'
    exact (hunitξ b hb).ne_zero h'
  have hinj : ∀ r : X.presheaf.stalk x,
      X.residue ξ (X.presheaf.stalkSpecializes e r) = 0 → r = 0 := by
    intro r hr
    obtain ⟨⟨a, d⟩, hrad⟩ := IsLocalization.surj (S := X.presheaf.stalk (⟨x, hxU⟩ : U))
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl r
    change r * X.presheaf.germ U x hxU d = X.presheaf.germ U x hxU a at hrad
    have hres : X.residue ξ (X.presheaf.germ U ξ hξU a) = 0 := by
      rw [← hsp, ← hrad, map_mul, map_mul, hr, zero_mul]
    obtain ⟨n, hn⟩ := hnil _ hres
    have hn' : algebraMap Γ(X, U) (X.presheaf.stalk (⟨ξ, hξU⟩ : U)) (a ^ n) = 0 := by
      rw [map_pow]; exact hn
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff
      (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl _ _).mp hn'
    have hc' : X.presheaf.germ U x hxU c * (X.presheaf.germ U x hxU a) ^ n = 0 := by
      rw [← map_pow, ← map_mul, hc, map_zero]
    have ha0 : X.presheaf.germ U x hxU a = 0 :=
      IsNilpotent.eq_zero ⟨n, (mul_eq_zero.mp hc').resolve_left (hne c c.2)⟩
    rw [ha0] at hrad
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units
      (X.presheaf.stalk (⟨x, hxU⟩ : U)) d)).mp hrad
  letI alg := RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom
  have halg : ∀ r, algebraMap (X.presheaf.stalk x) (X.residueField ξ) r =
      X.residue ξ (X.presheaf.stalkSpecializes e r) := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero, halg]
    exact fun h => nonZeroDivisors.ne_zero y.2 (hinj _ h)
  · intro z
    obtain ⟨s, rfl⟩ := X.residue_surjective ξ z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (S := X.presheaf.stalk (⟨ξ, hξU⟩ : U))
      (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl s
    change s * X.presheaf.germ U ξ hξU b = X.presheaf.germ U ξ hξU a at hab
    refine ⟨⟨X.presheaf.germ U x hxU a,
      ⟨X.presheaf.germ U x hxU b, mem_nonZeroDivisors_of_ne_zero (hne b b.2)⟩⟩, ?_⟩
    change X.residue ξ s * algebraMap _ _ (X.presheaf.germ U x hxU b) =
      algebraMap _ _ (X.presheaf.germ U x hxU a)
    rw [halg, halg, hsp, hsp, ← map_mul, hab]
  · intro r t h
    refine ⟨1, ?_⟩
    have h0 := hinj (r - t) (by rw [map_sub, map_sub, ← halg, ← halg, h, sub_self])
    rw [sub_eq_zero.mp h0]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralDetOfPreservesLattice
section
open Polynomial

namespace GlobalTheory.IsIntegralDetLattice

theorem isIntegral_of_isRoot_charpoly {R K : Type} [CommRing R] [Field K] [Algebra R K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) (hA : IsIntegral R A) (x : K) (hx : A.charpoly.IsRoot x) :
    IsIntegral R x := by
  obtain ⟨p, hp, hpA⟩ := hA

  have hmem : x ∈ spectrum K A := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hx
  have h2 := spectrum.subset_polynomial_aeval A (p.map (algebraMap R K)) ⟨x, hmem, rfl⟩
  rw [aeval_map_algebraMap, aeval_def, hpA, spectrum.mem_iff, sub_zero] at h2
  refine ⟨p, hp, ?_⟩
  rw [eval₂_eq_eval_map]
  by_contra hne
  exact h2 ((Ne.isUnit hne).map (algebraMap K (Matrix (Fin N) (Fin N) K)))

theorem isIntegral_det {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) E) (hA : IsIntegral R A) : IsIntegral R A.det := by

  let φ : E →ₐ[R] AlgebraicClosure E := IsScalarTower.toAlgHom R E (AlgebraicClosure E)
  have hA' : IsIntegral R (A.map (algebraMap E (AlgebraicClosure E))) := by
    exact hA.map (φ.mapMatrix (m := Fin N))
  have hdet : (A.map (algebraMap E (AlgebraicClosure E))).det = algebraMap E (AlgebraicClosure E) A.det := by
    rw [RingHom.map_det]; rfl
  rw [← isIntegral_algHom_iff φ (algebraMap E (AlgebraicClosure E)).injective]
  show IsIntegral R (algebraMap E (AlgebraicClosure E) A.det)
  rw [← hdet, Matrix.det_eq_prod_roots_charpoly]
  exact multiset_prod_mem (S := integralClosure R (AlgebraicClosure E)) _
    fun r hr => isIntegral_of_isRoot_charpoly _ hA' r (Polynomial.isRoot_of_mem_roots hr)

theorem isIntegral_of_preserves {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (L : Submodule R (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ := by
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hL

  let f : Module.End R L := ((Matrix.mulVecLin γ).restrictScalars R).restrict hγ
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  have hpow : ∀ (n : ℕ) (v : Fin N → E) (hv : v ∈ L),
      (γ ^ n).mulVec v = ((f ^ n) ⟨v, hv⟩ : Fin N → E) := by
    intro n
    induction n with
    | zero => intro v hv; simp
    | succ n ih =>
      intro v hv
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih v hv, Module.End.mul_apply]
      rfl
  have key : ∀ (q : R[X]) (v : Fin N → E) (hv : v ∈ L),
      (aeval γ q).mulVec v = ((aeval f q) ⟨v, hv⟩ : Fin N → E) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v hv; simp [Matrix.add_mulVec, hp v hv, hq v hv]
    | monomial n a =>
      intro v hv
      simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, hpow n v hv]
  have hz : Matrix.toLin' (aeval γ p) = 0 := by
    refine LinearMap.ext_on hs fun v hv => ?_
    simp [Matrix.toLin'_apply, key p v hv, hpf]
  exact ⟨p, hp, by rw [← aeval_def]; exact Matrix.toLin'.map_eq_zero_iff.mp hz⟩

theorem isIntegral_det_of_preserves_lattice {E : Type} [Field E] [NumberField E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det := by
  exact isIntegral_trans _ (isIntegral_det γ (isIntegral_of_preserves L hL hs γ hγ))

end GlobalTheory.IsIntegralDetLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LaurentMonomialOfMultiplicative
section
open Matrix

namespace GlobalTheory

theorem laurentMonomial_of_multiplicative :
    ∀ (n : ℕ) (χ : (Fin n → ℂ) → ℂ), χ 1 = 1 →
      (∀ s t : Fin n → ℂ, (∀ i, s i ≠ 0) → (∀ i, t i ≠ 0) → χ (s * t) = χ s * χ t) →
      (∀ i : Fin n, ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ (Pi.mulSingle i t) = t ^ k) →
      ∃ μ : Fin n → ℤ, ∀ d : Fin n → ℂ, (∀ i, d i ≠ 0) → χ d = ∏ i, d i ^ μ i := by
  intro n χ h1 hmul hk
  choose k hk using hk
  refine ⟨k, fun d hd => ?_⟩
  have hne : ∀ (s : Finset (Fin n)) (i : Fin n), (∏ j ∈ s, Pi.mulSingle j (d j)) i ≠ 0 := by
    intro s i
    rw [Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    rw [Pi.mulSingle_apply]
    split_ifs with h
    · subst h; exact hd _
    · exact one_ne_zero
  have key : ∀ s : Finset (Fin n), χ (∏ i ∈ s, Pi.mulSingle i (d i)) = ∏ i ∈ s, d i ^ k i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using h1
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.prod_insert ha, hmul _ _ ?_ (hne s), hk a (d a) (hd a), ih]
      intro i
      rw [Pi.mulSingle_apply]
      split_ifs with h
      · subst h; exact hd _
      · exact one_ne_zero
  have := key Finset.univ
  rwa [Finset.univ_prod_mulSingle] at this

end GlobalTheory
end


import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0006
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0019
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.VanPairs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.PolySupp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecAlg

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryInertOddPrime
section
open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.CertificateRingHomMap (Plc)

namespace UpperTheory.Gal.Spc.EntrywiseClass

private theorem exists_root (tr nm : ℤ) (h : tr ^ 2 - 4 * nm < 0) (b : ℕ) :
    ∃ q : ℕ, q.Prime ∧ b < q ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm := by
  have hnm : 0 < nm := by nlinarith [sq_nonneg tr]
  set c : ℕ := (b + tr.natAbs + 1).factorial with hc
  have hcge : b + tr.natAbs + 1 ≤ c := Nat.self_le_factorial _
  have hcZ : (tr.natAbs : ℤ) + 1 ≤ (c : ℤ) := by omega
  have htr : tr ≤ tr.natAbs := by omega
  set g : ℤ := nm * (c : ℤ) ^ 2 - tr * c + 1 with hg
  have hcpos : (0 : ℤ) < c := by omega
  have hg1 : 1 < g := by
    have h1 : (c : ℤ) ≤ nm * c := by nlinarith
    have h2 : 0 < nm * c - tr := by omega
    have : 0 < (c : ℤ) * (nm * c - tr) := mul_pos hcpos h2
    rw [hg]; nlinarith
  have hne : g.natAbs ≠ 1 := by omega
  refine ⟨g.natAbs.minFac, Nat.minFac_prime hne, ?_, nm * c, ?_⟩
  · by_contra hle
    have hq := Nat.minFac_prime hne
    have hqc : g.natAbs.minFac ∣ c := (hq.dvd_factorial).2 (by omega)
    have hqg : (g.natAbs.minFac : ℤ) ∣ g := Int.natCast_dvd.2 (Nat.minFac_dvd _)
    have hqc' : (g.natAbs.minFac : ℤ) ∣ (c : ℤ) := by exact_mod_cast hqc
    have h1 : (g.natAbs.minFac : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = g - c * (nm * c - tr) := by rw [hg]; ring
      rw [e]; exact dvd_sub hqg (Dvd.dvd.mul_right hqc' _)
    have := Int.eq_one_of_dvd_one (by omega) h1
    have h2 := hq.one_lt
    omega
  · have hqg : (g.natAbs.minFac : ℤ) ∣ g := Int.natCast_dvd.2 (Nat.minFac_dvd _)
    have e : (nm * c) ^ 2 - tr * (nm * c) + nm = nm * g := by rw [hg]; ring
    rw [e]; exact Dvd.dvd.mul_left hqg _

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem not_both (u : Plc E) {a b : ℕ} (h : a.Coprime b) (ha : (a : 𝓞 E) ∈ u.asIdeal) (hb : (b : 𝓞 E) ∈ u.asIdeal) : False := by
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (1 : 𝓞 E) = (s : 𝓞 E) * (a : 𝓞 E) + (t : 𝓞 E) * (b : 𝓞 E) := by
    exact_mod_cast (congrArg (Int.cast : ℤ → 𝓞 E) hst).symm
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [e]
  exact u.asIdeal.add_mem (u.asIdeal.mul_mem_left _ ha) (u.asIdeal.mul_mem_left _ hb)

private theorem exists_place (q : ℕ) (hq : q.Prime) : ∃ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.ExistsPlace.exists_place q hq

private theorem finite_above (q : ℕ) (hq : q.Prime) : {w : Plc E | (q : 𝓞 E) ∈ w.asIdeal}.Finite := by
  have hq0 : (q : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  refine (Ideal.finite_factors (I := Ideal.span {(q : 𝓞 E)}) (by simpa using hq0)).subset fun w hw => ?_
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hw)

private theorem cj_cj (A : Arith E) (u : Plc E) : CertificateRingHomMap.cj (CertificateRingHomMap.cj u) = u := by
  apply HeightOneSpectrum.ext
  ext y
  rw [UpperTheory.Gal.G1.pCjMem E A, UpperTheory.Gal.G1.pCjMem E A, A.bar_bar]

private theorem eq_or_cj (A : Arith E) (w u : Plc E)
    (h : w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))) : u = w ∨ u = CertificateRingHomMap.cj w := by
  have hsub : (u.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ ((CertificateRingHomMap.cj w).asIdeal : Set (𝓞 E)) := by
    intro y hy
    have hy' : y ∈ u.asIdeal := hy
    have ht : IsCMField.complexConj E ((y * A.bar y : 𝓞 E) : E) = ((y * A.bar y : 𝓞 E) : E) := by
      rw [← A.bar_eq, map_mul, A.bar_bar, mul_comm]
    have hmem : ((y * A.bar y : 𝓞 E) : E) ∈ maximalRealSubfield E := (IsCMField.complexConj_eq_self_iff E _).1 ht
    have hint : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield E) :=
      (isIntegral_algebraMap_iff (A := maximalRealSubfield E) (B := E) (algebraMap (maximalRealSubfield E) E).injective).1
        (RingOfIntegers.isIntegral_coe (y * A.bar y))
    let z : 𝓞 (maximalRealSubfield E) := ⟨⟨_, hmem⟩, hint⟩
    have hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) z = y * A.bar y := RingOfIntegers.ext rfl
    have h1 : z ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, hz]
      exact u.asIdeal.mul_mem_right _ hy'
    rw [← h, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, hz] at h1
    rcases w.isPrime.mem_or_mem h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ((UpperTheory.Gal.G1.pCjMem E A w y).2 h2)
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top h1))
  · exact Or.inr (HeightOneSpectrum.ext (u.isMaximal.eq_of_le (CertificateRingHomMap.cj w).isPrime.ne_top h1))

end UpperTheory.Gal.Spc.EntrywiseClass

theorem UpperTheory.Gal.Spc.auxiliary_prime_holds :
    UpperTheory.Gal.Spc.AuxiliaryInertOddPrime := by
  intro E _ _ _ A n p _ S x U w₀ Up V hG X
  obtain ⟨e, he, hperf⟩ := pPerfCof E A
  obtain ⟨q, hq, hb, r, hr⟩ := UpperTheory.Gal.Spc.EntrywiseClass.exists_root A.tr A.nm A.disc_neg
    (X.sup id + p + e + (A.tr ^ 2 - 4 * A.nm).natAbs + V.S.sup fun u => Ideal.absNorm u.asIdeal)
  have hX : q ∉ X := fun h => by
    have h1 := Finset.le_sup (f := id) h
    simp only [id] at h1
    omega
  have hqp : q ≠ p := by omega
  have hcop : ∀ a : ℕ, 0 < a → a < q → a.Coprime q := fun a h0 h1 =>
    ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => absurd (Nat.le_of_dvd h0 h) (by omega)).symm
  have hD : ¬ (q : ℤ) ∣ A.tr ^ 2 - 4 * A.nm := fun h => by
    have h1 : q ∣ (A.tr ^ 2 - 4 * A.nm).natAbs := Int.natCast_dvd.1 h
    have h2 : 0 < (A.tr ^ 2 - 4 * A.nm).natAbs := by have := A.disc_neg; omega
    have := Nat.le_of_dvd h2 h1
    omega
  have hs : A.SplitK q := ⟨hD, r, hr⟩
  have hgood : A.Good q := ⟨hs, hperf q (hcop e he (by omega))⟩
  have hoff : ∀ u ∈ V.S, (q : 𝓞 E) ∉ u.asIdeal := fun u hu h => by
    have h1 : Ideal.absNorm u.asIdeal ≤ V.S.sup fun u => Ideal.absNorm u.asIdeal :=
      Finset.le_sup (f := fun u : Plc E => Ideal.absNorm u.asIdeal) hu
    have h2 : 0 < Ideal.absNorm u.asIdeal := Nat.pos_of_ne_zero fun h0 => u.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact UpperTheory.Gal.Spc.EntrywiseClass.not_both u (hcop _ h2 (by omega)).symm h (Ideal.absNorm_mem u.asIdeal)
  obtain ⟨w₁, hw₁⟩ := UpperTheory.Gal.Spc.EntrywiseClass.exists_place (E := E) q hq
  have SD := fun (w : Plc E) (hw : (q : 𝓞 E) ∈ w.asIdeal) => Pl.sides_holds E A x hG q hq hs w hw
  obtain ⟨ρ, -, hρ⟩ := (SD w₁ hw₁).2.2.2.2.2.1
  have hiff := (SD w₁ hw₁).2.2.2.2.2.2 ρ hρ
  have hpo : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → (p : 𝓞 E) ∉ u.asIdeal := fun u hu hp =>
    UpperTheory.Gal.Spc.EntrywiseClass.not_both u ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp) hu hp
  have hT : {w : UpperTheory.Gal.Spc.Spl E p | (q : 𝓞 E) ∈ w.1.asIdeal ∧ A.ω - (ρ : 𝓞 E) ∈ w.1.asIdeal}.Finite :=
    ((UpperTheory.Gal.Spc.EntrywiseClass.finite_above (E := E) q hq).preimage (f := fun w : UpperTheory.Gal.Spc.Spl E p => w.1)
      (fun _ _ _ _ h => Subtype.ext h)).subset fun w hw => hw.1
  have hmk : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → A.ω - (ρ : 𝓞 E) ∈ u.asIdeal →
      ∃ w ∈ hT.toFinset, w.1 = u := fun u h1 h2 =>
    ⟨⟨u, (SD u h1).2.1, hpo u h1⟩, hT.mem_toFinset.2 ⟨h1, h2⟩, rfl⟩
  refine ⟨q, hT.toFinset, hX, hq, hqp, hgood, hoff, ⟨fun w hw => (hT.mem_toFinset.1 hw).1, fun u hu => ?_, fun w hw w' hw' hne heq => ?_⟩, ?_⟩
  · rcases (SD w₁ hw₁).2.2.1 u hu with h | h
    · obtain ⟨h1, h2⟩ := (hiff u).1 h
      obtain ⟨w, hw, e⟩ := hmk u h1 h2
      exact ⟨w, hw, Or.inl e⟩
    · obtain ⟨h1, h2⟩ := (hiff _).1 h
      obtain ⟨w, hw, e⟩ := hmk _ h1 h2
      exact ⟨w, hw, Or.inr (by rw [e]; exact UpperTheory.Gal.Spc.EntrywiseClass.cj_cj A u)⟩
  · have m := hT.mem_toFinset.1 hw
    have m' := hT.mem_toFinset.1 hw'
    rcases UpperTheory.Gal.Spc.EntrywiseClass.eq_or_cj A w.1 w'.1 heq with h | h
    · exact hne (Subtype.ext h.symm)
    · refine (SD w.1 m.1).1 (((SD w.1 m.1).2.2.2.2.2.2 ρ m.2 _).2 ?_)
      rw [← h]
      exact m'
  · obtain ⟨w, hw, -⟩ := hmk w₁ hw₁ hρ
    exact ⟨w, hw⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecOfF
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.CertificateRingHomMap (wop wmul)
open UpperTheory.Gal.LocalSmoothExtension
open Formalism.UG (Hecke)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Abstract

variable {H : Type} [Group H] {K : Subgroup H} {M : Type} [AddCommGroup M] [Module ℂ M]
  {T : (H → ℂ) → Module.End ℂ M} {J : Type}

private theorem polyFn_single (ψ : J → H → ℂ) (w : List J) (c : ℂ) (f : H → ℂ) :
    polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f :=
  Finsupp.sum_single_index (zero_smul _ _)

private theorem polyFn_zero (ψ : J → H → ℂ) (f : H → ℂ) : polyFn K ψ 0 f = 0 :=
  Finsupp.sum_zero_index

private theorem polyFn_add (ψ : J → H → ℂ) (s t : List J →₀ ℂ) (f : H → ℂ) :
    polyFn K ψ (s + t) f = polyFn K ψ s f + polyFn K ψ t f :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

private theorem word_mem (ψ : J → H → ℂ) (f : H → ℂ) (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K) (w : List J) :
    wordFn K ψ w f ∈ Hecke ℂ K := by
  have h := hmem (Finsupp.single w 1)
  rwa [polyFn_single, one_smul] at h

private theorem T_word (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hmem : ∀ w, wordFn K ψ w f ∈ Hecke ℂ K) (w : List J) :
    T (wordFn K ψ w f) = (w.map fun j => T (ψ j)).prod * T f := by
  induction w with
  | nil => simp [wordFn]
  | cons j w ih =>
    have h : wordFn K ψ (j :: w) f = Formalism.UG.conv K (ψ j) (wordFn K ψ w f) := rfl
    rw [h, hmul _ (hψ j) _ (hmem w), ih, List.map_cons, List.prod_cons, mul_assoc]

private theorem T_poly (hT0 : T 0 = 0) (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (hlin : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, ∀ c : ℂ, T (c • f + f') = c • T f + T f')
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K)
    (s : List J →₀ ℂ) : T (polyFn K ψ s f) = wop (fun j => T (ψ j)) s * T f := by
  induction s using Finsupp.induction_linear with
  | zero => rw [polyFn_zero, hT0, UpperTheory.Gal.CertificateRingHomMap.wop_zero, zero_mul]
  | add s t hs ht =>
    have h : polyFn K ψ (s + t) f = (1 : ℂ) • polyFn K ψ s f + polyFn K ψ t f := by
      rw [one_smul, polyFn_add]
    rw [h, hlin _ (hmem s) _ (hmem t), one_smul, hs, ht, UpperTheory.Gal.CertificateRingHomMap.wop_add, add_mul]
  | single w c =>
    have h : polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f + 0 := by
      rw [polyFn_single, add_zero]
    rw [h, hlin _ (word_mem ψ f hmem w) _ (Submodule.zero_mem _), hT0, add_zero,
      T_word hmul ψ hψ f (word_mem ψ f hmem) w, UpperTheory.Gal.CertificateRingHomMap.wop_single, smul_mul_assoc]

private theorem T_pow (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (u e : H → ℂ) (hu : u ∈ Hecke ℂ K) (hmem : ∀ n, powFn K u e n ∈ Hecke ℂ K) (n : ℕ) :
    T (powFn K u e n) = T u ^ n * T e := by
  induction n with
  | zero => simp [powFn]
  | succ n ih =>
    have h : powFn K u e (n + 1) = Formalism.UG.conv K u (powFn K u e n) := Function.iterate_succ_apply' _ _ _
    rw [h, hmul _ hu _ (hmem n), ih, pow_succ', mul_assoc]

private theorem C_pow {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f))
    (u e : H → ℂ) (hu : u ∈ Hecke ℂ K) (he : C e) (hmem : ∀ n, powFn K u e n ∈ Hecke ℂ K) (n : ℕ) :
    C (powFn K u e n) := by
  induction n with
  | zero => exact he
  | succ n ih =>
    have h : powFn K u e (n + 1) = Formalism.UG.conv K u (powFn K u e n) := Function.iterate_succ_apply' _ _ _
    rw [h]
    exact hid _ hu _ (hmem n) ih

private theorem C_word {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f))
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hf : C f)
    (hmem : ∀ w, wordFn K ψ w f ∈ Hecke ℂ K) (w : List J) : C (wordFn K ψ w f) := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact hid _ (hψ j) _ (hmem w) ih

private theorem C_poly {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f)) (h0 : C 0)
    (hlin : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, ∀ c : ℂ, C f → C f' → C (c • f + f'))
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hf : C f)
    (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K) (s : List J →₀ ℂ) : C (polyFn K ψ s f) := by
  induction s using Finsupp.induction_linear with
  | zero => rw [polyFn_zero]; exact h0
  | add s t hs ht =>
    have h : polyFn K ψ (s + t) f = (1 : ℂ) • polyFn K ψ s f + polyFn K ψ t f := by
      rw [one_smul, polyFn_add]
    rw [h]
    exact hlin _ (hmem s) _ (hmem t) _ hs ht
  | single w c =>
    have h : polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f + 0 := by
      rw [polyFn_single, add_zero]
    rw [h]
    exact hlin _ (word_mem ψ f hmem w) _ (Submodule.zero_mem _) _
      (C_word hid ψ hψ f hf (word_mem ψ f hmem) w) h0

private theorem hecke_relation_image (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (ψ : J → H → ℂ) (e u u' : H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K) (hu : u ∈ Hecke ℂ K)
    (hu' : u' ∈ Hecke ℂ K) (hrel : Rel (Formalism.UG.conv K) ψ e u u') (hB : Formalism.UG.conv K u e ∈ Hecke ℂ K)
    (hA : ∀ j, Formalism.UG.conv K (ψ j) e ∈ Hecke ℂ K) :
    Rel (· * ·) (fun j => T (ψ j)) (T e) (T u) (T u') := by
  refine ⟨?_, fun j => ?_, ?_, fun j j' => ?_, fun j => ?_, ?_⟩
  · have h := congrArg T hrel.idem
    rwa [hmul _ he _ he] at h
  · have h := congrArg T (hrel.eT j)
    rwa [hmul _ he _ (hA j), hmul _ (hψ j) _ he] at h
  · have h := congrArg T hrel.eu
    rwa [hmul _ he _ hB, hmul _ hu _ he] at h
  · have h := congrArg T (hrel.TT j j')
    rwa [hmul _ (hψ j) _ (hA j'), hmul _ (hψ j') _ he, hmul _ (hψ j') _ (hA j), hmul _ (hψ j) _ he] at h
  · have h := congrArg T (hrel.uT j)
    rwa [hmul _ hu _ (hA j), hmul _ (hψ j) _ he, hmul _ (hψ j) _ hB, hmul _ hu _ he] at h
  · have h := congrArg T hrel.inv
    rwa [hmul _ hu' _ hB, hmul _ hu _ he] at h

end Abstract

private theorem forms_fin {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V)
    (hf : Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H))) :
    FiniteDimensional ℂ (HeckeTraceForms.forms ι K ξ) := by
  haveI := hf
  obtain ⟨r, hr⟩ : ∃ r : DoubleCoset.Quotient (ι.range : Set H) (K : Set H) → H, ∀ g : H,
      ∃ γ : Γ, ∃ k ∈ K, g = ι γ * r (DoubleCoset.mk ι.range K g) * k := by
    refine ⟨fun q => Quotient.out q, fun g => ?_⟩
    obtain ⟨h, ⟨γ, rfl⟩, k, hk, e⟩ := (DoubleCoset.eq ι.range K _ _).1
      (DoubleCoset.out_eq' ι.range K (DoubleCoset.mk ι.range K g))
    exact ⟨γ, k, hk, e⟩
  let L : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] (DoubleCoset.Quotient (ι.range : Set H) (K : Set H) → V) :=
    { toFun := fun φ q => (φ : H → V) (r q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective L ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  apply Subtype.ext
  funext g
  have h0 : (φ : H → V) (r (DoubleCoset.mk ι.range K g)) = 0 :=
    congrFun hφ (DoubleCoset.mk ι.range K g)
  obtain ⟨γ, k, hk, e⟩ := hr g
  have h1 : (φ : H → V) g = ξ γ ((φ : H → V) (r (DoubleCoset.mk ι.range K g))) := by
    conv_lhs => rw [e]
    rw [φ.2.2 k hk, φ.2.1]
  rw [h1, h0, map_zero]
  rfl

def SpecOfF : Prop := ForPlaces fun p _ G Lv C R => Finite (DFCls G) →
  ∀ (D : Datum p) (L : GlobalTheory.LKGeo.Link D G) (lam : (D.F →+* ℂ) → Fin G.n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V), IsWt L lam ξ →
    ∀ (J : Type) (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (e u u' : G.GAf → ℂ),
    (∀ j, ψ j ∈ Hecke ℂ Lv.K.toSubgroup) → e ∈ Hecke ℂ Lv.K.toSubgroup → u ∈ Hecke ℂ Lv.K.toSubgroup →
    u' ∈ Hecke ℂ Lv.K.toSubgroup → Rel (Formalism.UG.conv Lv.K.toSubgroup) ψ e u u' → C e →
    (∀ n : ℕ, 1 ≤ n → ∃ A : Set G.GAf, (∀ g ∈ A, R g ∧ RegAf G g) ∧ (∀ j a, ψ j a ≠ 0 → ∀ g ∈ A, a * g ∈ A) ∧
      ∀ g, powFn Lv.K.toSubgroup u e n g ≠ 0 → g ∈ A) →
    HasEig G ξ Lv.K.toSubgroup ψ θ e → ∃ n : ℕ, 1 ≤ n ∧ Spec L lam Lv.K.toSubgroup ψ θ (powFn Lv.K.toSubgroup u e n)

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.specOfF :
    UpperTheory.Gal.Spc.SpecOfF := by
  intro p _ G hGa Lv k _ _ _ _ _ _ _ P H _ _ _ _ S k₁ _ _ P₁ hfin D L lam V _ _ _ ξ hwt J ψ θ e u u' hψ he hu hu' hrel hCe hA hEig
  have hW := words p G Lv J ψ e u u' hψ he hu hrel
  have hp : ∀ n, powFn Lv.K.toSubgroup u e n ∈ Hecke ℂ Lv.K.toSubgroup := fun n => (hW n).1
  have hpoly : ∀ n s, polyFn Lv.K.toSubgroup ψ s (powFn Lv.K.toSubgroup u e n) ∈ Hecke ℂ Lv.K.toSubgroup :=
    fun n => (hW n).2.1
  obtain ⟨hCi, hC0, hCl⟩ := cuspIdeal p G hGa Lv k P H S k₁ P₁
  obtain ⟨q₀, Φ₀, hΦ₀, hne, hΦe, hΦψ⟩ := clsMove p G V ξ Lv.K.toSubgroup J ψ θ e hEig
  letI : Fintype (DFCls G) := Fintype.ofFinite _
  have hop := fun q : DFCls G => opAlg p G Lv V ξ (Quot.out q)
  choose T hT0 hT using hop
  haveI hfd' : ∀ q : DFCls G, FiniteDimensional ℂ (HeckeTraceForms.forms (Quot.out q).emb (Lv.K.toSubgroup.prod (Kp G))
      (ξ.comp (grp G (Quot.out q).β).subtype)) := fun q =>
    forms_fin (Quot.out q).emb _ _ (GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level p G hGa Lv (Kp G) (Subgroup.Commensurable.refl _) (Quot.out q))
  have hmul : ∀ q, ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup,
      T q (Formalism.UG.conv Lv.K.toSubgroup f f') = T q f * T q f' := fun q f hf f' hf' => ((hT q f hf).2.2 f' hf').1
  have hlin : ∀ q, ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup, ∀ c : ℂ,
      T q (c • f + f') = c • T q f + T q f' := fun q f hf f' hf' => ((hT q f hf).2.2 f' hf').2
  have hB : Formalism.UG.conv Lv.K.toSubgroup u e ∈ Hecke ℂ Lv.K.toSubgroup := hp 1
  have hAj : ∀ j, Formalism.UG.conv Lv.K.toSubgroup (ψ j) e ∈ Hecke ℂ Lv.K.toSubgroup := fun j =>
    word_mem ψ _ (hpoly 0) [j]
  have key := specAlg (DFCls G) J
    (fun q => HeckeTraceForms.forms (Quot.out q).emb (Lv.K.toSubgroup.prod (Kp G)) (ξ.comp (grp G (Quot.out q).β).subtype))
    (fun q j => T q (ψ j)) (fun q => T q e) (fun q => T q u) (fun q => T q u') θ
    (fun q => hecke_relation_image (hmul q) ψ e u u' hψ he hu hu' hrel hB hAj)
    ⟨q₀, ⟨Φ₀, hΦ₀⟩, fun h => hne (congrArg Subtype.val h),
      Subtype.ext (((hT q₀ e he).1 ⟨Φ₀, hΦ₀⟩).trans hΦe),
      fun j => Subtype.ext (((hT q₀ (ψ j) (hψ j)).1 ⟨Φ₀, hΦ₀⟩).trans (hΦψ j))⟩
  obtain ⟨n, hn, a, ha⟩ := key
  refine ⟨n, hn, (hW n).2.2.1, V, inferInstance, inferInstance, inferInstance, ξ, hwt, fun s hs => ⟨a, ?_, ?_⟩⟩
  · obtain ⟨A, hAR, hAψ, hAp⟩ := hA n hn
    have hsup := (hW n).2.2.2 A hAψ hAp
    have hCF : S.Cusp (polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n)) :=
      C_poly hCi hC0 hCl ψ hψ _ (C_pow hCi u e hu hCe hp n) (hpoly n) _
    have hR : ∀ g, polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n) g ≠ 0 →
        (P₁.at g).charpoly.Separable := fun g hg => (hAR g (hsup _ g hg)).1
    exact ⟨fun g hg => (hAR g (hsup _ g hg)).2,
      vanPairs p G hGa Lv k P H S k₁ P₁ _ (hpoly n _) hCF hR,
      vanForms p G hGa Lv k P H S k₁ P₁ _ (hpoly n _) hCF hR⟩
  · have hq : ∀ q : DFCls G, (Quot.out q).trace ξ Lv.K.toSubgroup
        (polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n)) (Kp G) (oneP G) =
        LinearMap.trace ℂ _ (wop (fun j => T q (ψ j)) (wmul a s) * (T q u ^ n * T q e)) := fun q => by
      rw [(hT q _ (hpoly n _)).2.1, T_poly (hT0 q) (hmul q) (hlin q) ψ hψ _ (hpoly n),
        T_pow (hmul q) u e hu hp n]
    unfold dTrace
    rw [finsum_eq_sum_of_fintype]
    simp only [hq]
    exact ha s hs
end
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0686
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfIsotypicCommutingSubgroups
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

theorem exists_multilinearMap_of_isotypic_commuting :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
      (H : ι → Type) [∀ v, Group (H v)] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)]
      [∀ v, Module ℂ (Wv v)] [∀ v, FiniteDimensional ℂ (Wv v)] (ρ : Representation ℂ G V)
      (s : ∀ v, H v →* G) (σ : ∀ v, Representation ℂ (H v) (Wv v)),
      Nontrivial V → (∀ v, (σ v).IsIrreducible) →
      (∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b)) →
      (∀ v, (⨆ f : (σ v).IntertwiningMap (ρ.comp (s v)), LinearMap.range f.toLinearMap) = ⊤) →
      ∃ F : MultilinearMap ℂ Wv V, F ≠ 0 ∧ ∀ v (h : H v) (x : ∀ u, Wv u),
        ρ (s v h) (F x) = F (Function.update x v (σ v h (x v))) := by
  intro ι _ _ G V _ _ _ H _ Wv _ _ _ ρ s σ hV hirr hcomm hspan
  have hfac : ∀ v, ∃ Φ : Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V,
      (∀ h, Φ (σ v h) = ρ (s v h)) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ (s v h))) → ∀ A, Commute T (Φ A) :=
    fun v => GlobalTheory.T.exists_algHom_endomorphism_of_span_intertwiners (H v) (Wv v) V (σ v) (ρ.comp (s v)) (hirr v) (hspan v)
  choose Φ hΦσ hΦc using hfac
  have hΦcomm : ∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B) := by
    intro u v huv A B
    have h1 : ∀ b, Commute (ρ (s v b)) (Φ u A) := by
      intro b
      refine hΦc u _ (fun a => ?_) A
      exact ((hcomm v u (Ne.symm huv) b a).map ρ)
    exact hΦc v (Φ u A) (fun b => (h1 b).symm) B
  have hnt : ∀ v, Nontrivial (Wv v) := fun v => ((GlobalTheory.CuspRep.isIrreducible_iff _).1 (hirr v)).1
  have hw : ∀ v, ∃ w : Wv v, w ≠ 0 := fun v => exists_ne 0
  choose w hw0 using hw
  have hl : ∀ v, ∃ ℓ : Module.Dual ℂ (Wv v), ℓ (w v) = 1 := by
    intro v
    have hn : w v ∉ (⊥ : Submodule ℂ (Wv v)) := by simpa using hw0 v
    obtain ⟨f, hf, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
    exact ⟨(f (w v))⁻¹ • f, by simp [hf]⟩
  choose ℓ hℓ using hl
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.T.exists_ne_zero_fixed_by_commuting_rankOne_images ι Wv V Φ w ℓ hV hℓ hΦcomm
  obtain ⟨F, hFw, hF⟩ := GlobalTheory.T.exists_multilinearMap_of_commuting_endAlgHom ι Wv V Φ w ℓ y hΦcomm hy
  refine ⟨F, fun h0 => hy0 ?_, fun v h x => ?_⟩
  · rw [← hFw, h0]; rfl
  · rw [← hΦσ v h]
    exact hF v (σ v h) x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrobTeich

variable {Ω : Type} [Field Ω]

theorem eq_of_pow_eq_self_of_cong (A : ValuationSubring Ω) {N : ℕ} (hN : A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = a) (hb : b ^ N = b) (hab : A.valuation (a - b) < 1) : a = b := by
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · interval_cases N
    · rw [pow_zero] at ha hb; rw [← ha, ← hb]
    · simp at hN
  have hle : ∀ c : Ω, c ^ N = c → A.valuation c ≤ 1 := by
    intro c hc
    by_contra hc1
    have h1 : 1 < A.valuation c := not_le.mp hc1
    have h2 : A.valuation c ^ 1 < A.valuation c ^ N := pow_lt_pow_right₀ h1 (by omega)
    rw [← map_pow, ← map_pow, hc, pow_one] at h2
    exact lt_irrefl _ h2
  have ha1 := hle a ha
  have hb1 := hle b hb
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  set S := ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i) with hS
  have hS1 : S = 1 := by
    have h1 : S * (a - b) = a - b := by rw [hS, geom_sum₂_mul, ha, hb]
    have h2 : (S - 1) * (a - b) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hsub
  have hdiff : A.valuation (S - ∑ i ∈ Finset.range N, a ^ i * a ^ (N - 1 - i)) < 1 := by
    rw [hS, ← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [← mul_sub, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (GlobalTheory.WeilDeligne.val_pow_le_one ha1 i))
      (GlobalTheory.WeilDeligne.cong_pow hb1 ha1 (GlobalTheory.WeilDeligne.cong_symm hab) _)
  rw [geom_sum₂_self] at hdiff
  have hNa : A.valuation ((N : Ω) * a ^ (N - 1)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (GlobalTheory.WeilDeligne.val_pow_le_one ha1 _)) hN
  have hS' : A.valuation S < 1 := by
    have e : S = (S - (N : Ω) * a ^ (N - 1)) + (N : Ω) * a ^ (N - 1) := by ring
    rw [e]; exact Valuation.map_add_lt _ hdiff hNa
  rw [hS1, map_one] at hS'
  exact lt_irrefl _ hS'

open Polynomial in

theorem exists_pow_eq_self_cong [IsAlgClosed Ω] (A : ValuationSubring Ω) {N : ℕ} (hN : 2 ≤ N)
    {x : Ω} (hx : A.valuation (x ^ N - x) < 1) : ∃ ζ : Ω, ζ ^ N = ζ ∧ A.valuation (x - ζ) < 1 := by
  set P : Polynomial Ω := X ^ N - X with hP
  have hdeg : P.natDegree = N := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp; omega
  have hmon : P.Monic := by
    rw [hP]; exact monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by omega : 1 < N))
  have hsplit : P = (P.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [IsAlgClosed.card_roots_eq_natDegree])).symm
  have hev : x ^ N - x = (P.roots.map fun a => x - a).prod := by
    have := congrArg (eval x) hsplit
    rw [eval_multiset_prod, Multiset.map_map] at this
    simpa [hP, Function.comp_def] using this
  by_contra hno
  push_neg at hno
  have hge : ∀ a ∈ P.roots, 1 ≤ A.valuation (x - a) := by
    intro a ha
    refine hno a ?_
    have := (mem_roots hmon.ne_zero).mp ha
    simpa [hP, sub_eq_zero] using this
  have h1 : 1 ≤ A.valuation (x ^ N - x) := by
    rw [hev, map_multiset_prod]
    refine Multiset.prod_induction (fun c => 1 ≤ c) _ (fun a b ha hb => ?_) le_rfl ?_
    · simpa using mul_le_mul' ha hb
    · intro c hc
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hc
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
      exact hge a ha
  exact absurd hx (not_lt.mpr h1)

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem exists_prime_pow_normV (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) : ∃ p f : ℕ, p.Prime ∧ 0 < f ∧ normV w = p ^ f ∧ A.valuation (p : Ω) < 1 := by
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  set p := ringChar (𝓞 E ⧸ w.asIdeal) with hp_def
  obtain ⟨n, hp, hn⟩ := FiniteField.card (𝓞 E ⧸ w.asIdeal) p
  have hpw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  refine ⟨p, n, hp, n.pos, ?_, ?_⟩
  · show Nat.card (𝓞 E ⧸ w.asIdeal) = p ^ (n : ℕ)
    rw [Nat.card_eq_fintype_card, hn]
  · have := (h _).mpr hpw
    simpa using this

theorem exists_pow_char_pow_eq_self {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (P : Polynomial ℤ) (hP : P.map (Int.castRingHom k) ≠ 0) {y : k}
    (hy : P.eval₂ (Int.castRingHom k) y = 0) : ∃ r : ℕ, 0 < r ∧ y ^ p ^ r = y := by
  have hroot : ∀ i : ℕ, y ^ p ^ i ∈ {z : k | (P.map (Int.castRingHom k)).IsRoot z} := by
    intro i
    show (P.map (Int.castRingHom k)).eval (y ^ p ^ i) = 0
    rw [Polynomial.eval_map, ← iterateFrobenius_def (R := k) p i,
      ← RingHom.ext_int ((iterateFrobenius k p i).comp (Int.castRingHom k)) (Int.castRingHom k),
      ← Polynomial.hom_eval₂, hy, map_zero]
  obtain ⟨i, j, hij, heq⟩ := (Polynomial.finite_setOf_isRoot hP).exists_lt_map_eq_of_forall_mem hroot
  refine ⟨j - i, by omega, ?_⟩
  apply (iterateFrobenius k p i).injective
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
  exact heq.symm

theorem exists_pow_prime_pow_cong [CharZero Ω] (A : ValuationSubring Ω) {x : Ω}
    (halg : IsAlgebraic ℤ x) (hx : A.valuation x ≤ 1) {p : ℕ} (hp : p.Prime)
    (hpA : A.valuation (p : Ω) < 1) : ∃ r : ℕ, 0 < r ∧ A.valuation (x ^ p ^ r - x) < 1 := by
  obtain ⟨P, hP0, hPx⟩ := halg
  set Q := P.primPart with hQ
  have hQprim : Q.IsPrimitive := P.isPrimitive_primPart
  have hQx : Polynomial.aeval x Q = 0 := by
    have e := congrArg (Polynomial.aeval x) P.eq_C_content_mul_primPart
    rw [hPx, map_mul, Polynomial.aeval_C] at e
    have hc : (algebraMap ℤ Ω) P.content ≠ 0 := by
      rw [eq_intCast, Int.cast_ne_zero]; exact (Polynomial.content_eq_zero_iff.not).mpr hP0
    exact (mul_eq_zero.mp e.symm).resolve_left hc
  haveI : Fact p.Prime := ⟨hp⟩
  set k := IsLocalRing.ResidueField A
  set y : A := ⟨x, (A.valuation_le_one_iff x).mp hx⟩ with hy_def
  haveI : CharP k p := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    simpa using hpA
  have hmap : Q.map (Int.castRingHom k) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ Q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun g => Polynomial.coeff g i) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
      exact (CharP.intCast_eq_zero_iff k p _).mp this
    have hu := hQprim (p : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    rcases hu with hu | hu <;> omega
  have hyA : Q.eval₂ (Int.castRingHom A) y = 0 := by
    apply Subtype.ext
    have e := Polynomial.hom_eval₂ Q (Int.castRingHom A) A.subtype y
    rw [RingHom.ext_int (A.subtype.comp (Int.castRingHom A)) (algebraMap ℤ Ω)] at e
    change A.subtype _ = A.subtype 0
    rw [e, map_zero]; exact hQx
  have hyk : Q.eval₂ (Int.castRingHom k) (IsLocalRing.residue A y) = 0 := by
    rw [← RingHom.ext_int ((IsLocalRing.residue A).comp (Int.castRingHom A)) (Int.castRingHom k),
      ← Polynomial.hom_eval₂, hyA, map_zero]
  obtain ⟨r, hr, hyr⟩ := exists_pow_char_pow_eq_self p Q hmap hyk
  refine ⟨r, hr, ?_⟩
  have hmem : y ^ p ^ r - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hyr, sub_self]
  have := (A.valuation_lt_one_iff _).mp hmem
  simpa [hy_def] using this

theorem exists_pow_normV_pow_cong [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ A.valuation (x ^ normV w ^ m - x) < 1 := by
  obtain ⟨p, f, hp, hf, hq, hpA⟩ := exists_prime_pow_normV A w h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨r, hr, hxr⟩ := exists_pow_prime_pow_cong A halg hx hp hpA
  refine ⟨r, hr, ?_⟩
  have key : ∀ j : ℕ, A.valuation (x ^ (p ^ r) ^ j - x) < 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := GlobalTheory.WeilDeligne.cong_pow (GlobalTheory.WeilDeligne.val_pow_le_one hx _) hx ih (p ^ r)
      rw [← pow_mul, ← pow_succ] at h1
      exact GlobalTheory.WeilDeligne.cong_trans h1 hxr
  have e : normV w ^ r = (p ^ r) ^ f := by rw [hq, ← pow_mul, ← pow_mul, mul_comm]
  rw [e]; exact key f

end GlobalTheory.FrobTeich

open GlobalTheory.FrobTeich in
theorem GlobalTheory.FrobTeich.isFrob_iff_teichmuller : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (σ : G E Ω), IsFrob (F := E) A (normV w) σ ↔ σ ∈ Dec (F := E) A ∧ ∀ (ζ : Ω) (m : ℕ), 0 < m → ζ ^ normV w ^ m = ζ → σ ζ = ζ ^ normV w := by
  intro E Ω _ _ _ _ _ A w h σ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨p, f, hp, hf, hq, hpA⟩ := exists_prime_pow_normV A w h
  set q := normV w with hq_def
  have hqA : A.valuation (q : Ω) < 1 := by
    rw [hq, Nat.cast_pow, map_pow]; exact pow_lt_one₀ zero_le hpA hf.ne'
  have hq2 : 2 ≤ q := by rw [hq]; exact le_trans hp.two_le (Nat.le_self_pow hf.ne' p)
  constructor
  · rintro ⟨hD, hc⟩
    refine ⟨hD, fun ζ m hm hζ => ?_⟩
    have hNA : A.valuation ((q ^ m : ℕ) : Ω) < 1 := by
      rw [Nat.cast_pow, map_pow]; exact pow_lt_one₀ zero_le hqA hm.ne'
    have hζ1 : A.valuation ζ ≤ 1 := by
      by_contra hc1
      have h1 : 1 < A.valuation ζ := not_le.mp hc1
      have h2 : A.valuation ζ ^ 1 < A.valuation ζ ^ (q ^ m) :=
        pow_lt_pow_right₀ h1 (Nat.one_lt_pow hm.ne' (by omega))
      rw [← map_pow, ← map_pow, hζ, pow_one] at h2
      exact lt_irrefl _ h2
    refine eq_of_pow_eq_self_of_cong A hNA ?_ ?_ (hc ζ hζ1)
    · rw [← map_pow, hζ]
    · rw [← pow_mul, mul_comm, pow_mul, hζ]
  · rintro ⟨hD, hT⟩
    refine ⟨hD, fun x hx => ?_⟩
    obtain ⟨m, hm, hxm⟩ := exists_pow_normV_pow_cong A w h hx
    obtain ⟨ζ, hζ, hxζ⟩ := exists_pow_eq_self_cong A
      (le_trans hq2 (Nat.le_self_pow hm.ne' q)) hxm
    have hσζ := hT ζ m hm hζ
    have hζ1 : A.valuation ζ ≤ 1 := by
      have e : ζ = x - (x - ζ) := by ring
      rw [e]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hx hxζ.le)
    have e : σ x - x ^ q = σ (x - ζ) + (ζ ^ q - x ^ q) := by
      rw [map_sub, hσζ]; ring
    rw [e]
    refine Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hD _).mpr hxζ) ?_
    exact GlobalTheory.WeilDeligne.cong_pow hζ1 hx (GlobalTheory.WeilDeligne.cong_symm hxζ) q
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SmoothCharNorm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finite_image_units (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (χ '' {x : kˣ | valuation k (x : k) = 1}).Finite := by
  have hS := GlobalTheory.SmGL.UnramFixed.isCompact_unitsO k
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun z : kˣ => (fun y => z⁻¹ * y) ⁻¹' (χ.ker : Set kˣ))
    (fun z => (continuous_const.mul continuous_id).isOpen_preimage _ hχ)
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine (t.finite_toSet.image χ).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨i, hi, ?_⟩
  have : χ (i⁻¹ * y) = 1 := hyi
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

theorem norm_eq_one_of_valuation_eq_one (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : kˣ)
    (hu : valuation k (u : k) = 1) : ‖(χ u : ℂ)‖ = 1 := by
  by_contra hne
  have hpos : 0 < ‖(χ u : ℂ)‖ := norm_pos_iff.2 (χ u).ne_zero
  have hinj := pow_right_injective₀ hpos hne
  have hinf := Set.infinite_range_of_injective hinj
  apply hinf
  refine ((finite_image_units χ hχ).image (fun w : ℂˣ => ‖(w : ℂ)‖)).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨χ (u ^ n), ⟨u ^ n, ?_, rfl⟩, ?_⟩
  · simp [Units.val_pow_eq_pow_val, map_pow, hu]
  · simp [map_pow, Units.val_pow_eq_pow_val, norm_pow]

noncomputable def ordHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord k x)
  map_one' := by
    have : ord k (1 : kˣ) = 0 := ord_eq_zero_iff.2 (by simp)
    simp [this]
  map_mul' x y := by simp [ord_mul, ofAdd_add]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  have := congrArg Multiplicative.toAdd (map_zpow (ordHom k) x n)
  simpa [ordHom, toAdd_zpow, smul_eq_mul] using this

end GlobalTheory.SmoothCharNorm

theorem GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ), IsSmoothChar χ → ∃ s : ℝ, ∀ z : kˣ, ‖(χ z : ℂ)‖ = nabs k z ^ s := by
  intro k _ _ _ _ χ hχ
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hord : ord k ϖ = 1 := ord_eq_one hϖ
  have ha : 0 < ‖(χ ϖ : ℂ)‖ := norm_pos_iff.2 (χ ϖ).ne_zero
  have hq : (1 : ℝ) < (resCard k : ℝ) := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  have hlq : Real.log (resCard k : ℝ) ≠ 0 := (Real.log_pos hq).ne'
  refine ⟨-Real.log ‖(χ ϖ : ℂ)‖ / Real.log (resCard k : ℝ), fun z => ?_⟩
  have hz : ‖(χ z : ℂ)‖ = ‖(χ ϖ : ℂ)‖ ^ ord k z := by
    have hw : valuation k ((ϖ ^ (-ord k z) * z : kˣ) : k) = 1 := by
      rw [← ord_eq_zero_iff, ord_mul, GlobalTheory.SmoothCharNorm.ord_zpow, hord]; ring
    have hdec : z = ϖ ^ (ord k z) * (ϖ ^ (-ord k z) * z) := by group
    conv_lhs => rw [hdec]
    rw [map_mul, Units.val_mul, norm_mul,
      GlobalTheory.SmoothCharNorm.norm_eq_one_of_valuation_eq_one χ hχ _ hw, mul_one, map_zpow,
      Units.val_zpow_eq_zpow_val, norm_zpow]
  rw [hz, GlobalTheory.LGrp.nabs_eq_zpow, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (by positivity), Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos (by positivity)]
  congr 1
  push_cast
  field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStableIsCompl
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp

theorem exists_stable_isCompl : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (S : Submodule ℂ V), (∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) → ∃ T : Submodule ℂ V, IsCompl S T ∧ ∀ σ, ∀ v ∈ T, a.ρ σ v ∈ T := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a S hS
  haveI := isSemisimpleRepresentation_of_isSmooth a.ρ a.smooth a.semisimple
  obtain ⟨T, hT⟩ := exists_isCompl (⟨S, fun σ v hv => hS σ v hv⟩ : Subrepresentation a.ρ)
  refine ⟨T.toSubmodule, ?_, fun σ v hv => T.apply_mem_toSubmodule σ hv⟩
  exact IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hT.inf_eq_bot)
    (congrArg Subrepresentation.toSubmodule hT.sup_eq_top)

end GlobalTheory.WeilDeligne.PrimDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (ChrEq)
open Formalism.L2.Host (HChar)
open scoped TensorProduct

namespace GlobalTheory.TowerCharRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

theorem exists_thetaChrTied (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch)
    (X : ThetaX D) (T : ThetaTied D X) (hR : ChrRead T C Tp.xi) :
    ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, ChrEq (T.eChr c) (H.eChr c) := by
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.ChrEqUnique.chrEq_unique D
  have hc : ∀ c, IsHeckeChar D (T.eChr c) ∧ ∀ τ, ∃ a, HasInfExp D (T.eChr c) τ a := fun c => by
    have : T.eChr c ∈ Set.range T.eChr := ⟨c, rfl⟩
    rwa [T.eChr_range] at this
  choose e he using fun c => GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D (T.eChr c) (hc c).1
  have hmul : ∀ a b, e (a * b) = e a * e b := fun a b =>
    u1 _ _ _ (he (a * b)) (by rw [map_mul]; exact chrEq_mul (he a) (he b))
  have hinf : ∀ c, (e c).HasInfQ (Formalism.L2.Host.embTau D) (X.infTy c) := fun c =>
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ (he c)).1 (T.infTy c)
  refine ⟨⟨MonoidHom.mk' e hmul, fun a b hab => T.eChr_inj (u2 _ _ _ (he a) ?_), fun χ => ⟨?_, ?_⟩, hinf,
    fun μ j => u1 _ _ _ (he _) (hR.chr μ j), u1 _ _ _ (he _) hR.eta⟩, he⟩
  · have hab' : e a = e b := hab
    rw [hab']
    exact he b
  · rintro ⟨c, rfl⟩
    exact ⟨u3 _ _ (he c), _, hinf c⟩
  · rintro ⟨hu, a, ha⟩
    obtain ⟨c, hcχ⟩ := GlobalTheory.CharTransport.exists_chrEq D χ hu
    have hm : c ∈ Set.range T.eChr := by
      rw [T.eChr_range]
      exact ⟨hcχ.1, fun τ => ⟨a τ, (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ hcχ).2 ha τ⟩⟩
    obtain ⟨x, rfl⟩ := hm
    exact ⟨x, u1 _ _ _ (he x) hcχ⟩

end GlobalTheory.TowerCharRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tupleUnitaryForms_equiv_periodRowForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), ∀ (u : B.Word) (a : I.ι), ∃ g : MtCx I a ≃ₗ[ℂ] (I.per l u a).Mt, ∀ F, SameForm I l u a F (g F) := by
  first | exact @GlobalTheory.Mem.Df.mtCx_equiv_per | exact GlobalTheory.Mem.Df.mtCx_equiv_per | (intros; apply GlobalTheory.Mem.Df.mtCx_equiv_per <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfBoundedKorbitDimensionStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ), (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) → FiniteDimensional ℂ U := by
  first | exact @GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits | exact GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits | (intros; apply GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizer
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finite_image_of_isOpen_stabilizer (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (hH : IsOpen {g : G | ρ g v = v})
    (S : Set G) (hS : IsCompact S) : ((fun g => ρ g v) '' S).Finite := by
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun s : G => (fun x => s⁻¹ * x) ⁻¹' {g : G | ρ g v = v})
    (fun s => hH.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ((t : Set G).toFinite.image (fun g => ρ g v)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx)
  refine ⟨s, hs, ?_⟩
  have h1 : ρ (s⁻¹ * x) v = v := hxs
  have hx' : x = s * (s⁻¹ * x) := by group
  show ρ s v = ρ x v
  conv_rhs => rw [hx', map_mul, Module.End.mul_apply, h1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankCoefficientSpaceEqProdRealModelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_coefficient_space_eq_prod_real_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Module.finrank ℂ R.cX.W = ∏ τ, Module.finrank ℂ (R.MX.H τ) := by
  first | exact @GlobalTheory.CoefDim.finrank_coef_eq_prod | exact GlobalTheory.CoefDim.finrank_coef_eq_prod | (intros; apply GlobalTheory.CoefDim.finrank_coef_eq_prod <;> assumption)
end


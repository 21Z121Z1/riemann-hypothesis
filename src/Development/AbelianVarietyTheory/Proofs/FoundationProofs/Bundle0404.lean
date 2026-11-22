import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomPadicIntTrivialOfIrreducibleCompactRep
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTransportsKaehlerRelationsOverInvariants
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0400
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0381
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0401
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomPadicIntTrivialOfIrreducibleCompactRepStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_padicInt_trivial_of_irreducible_compact_rep : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → (∀ g, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det ^ 2 = 1) → IsIrr r → Continuous lam → r.ker ≤ lam.ker → lam = 1 := by
  first | exact @GlobalTheory.Ord2.hom_padicInt_trivial | exact GlobalTheory.Ord2.hom_padicInt_trivial | (intros; apply GlobalTheory.Ord2.hom_padicInt_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HtPresNu7MonoLoss
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ

theorem htPresNu7_mono_loss : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
  (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₂ c' : ℕ) (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l),
  HTPresNuOfPolys A c m c₂ Z ζ P o → c₂ ≤ c' → HTPresNuOfPolys A c m c' Z ζ P o := by
  intro l _ Ω _ _ _ A c Z m c₂ c' ζ ι _ P o h hc
  obtain ⟨hζ, hco, hoO, hne, hK⟩ := h
  obtain ⟨hζ₂, -, hu, ho, hs⟩ := hK
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    have : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hl.pos i).ne'⟩
    infer_instance
  set n' := m - c' with hn'
  set d := (m - c₂) - n' with hd
  have hdn : d + n' = m - c₂ := by omega
  have hpow : (ζ ^ l ^ c₂) ^ l ^ d = ζ ^ l ^ c' := by
    rw [← pow_mul, ← pow_add]
    rcases Nat.lt_or_ge m c' with h | h
    swap
    · congr 2; omega
    · have e1 : m ≤ c₂ + d := by omega
      rw [(hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l e1), (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l h.le)]
  have hζ' : IsPrimitiveRoot (ζ ^ l ^ c') (l ^ n') := by
    rw [← hpow]
    exact hζ₂.pow (pow_pos hl.pos _) (by rw [← pow_add, hdn])
  refine ⟨hζ, hco, hoO, hne, hζ', by omega, hu, ho, ?_⟩
  intro s hsI hcyc _
  have hfix : s (ζ ^ l ^ c₂) = ζ ^ l ^ c₂ := by
    refine GlobalTheory.Col.fix_of_cycMod (le_refl m) hcyc ?_
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨k, hkv, hcg⟩ := hs s hsI hcyc hfix
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hkv i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, hdn, hv], ?_⟩
    rw [ZMod.val_natCast, map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, hpow,
      ← pow_eq_pow_mod _ hζ'.pow_eq_one]
  · have hN : ∀ a : ℕ, ‖(a : Qbar l)‖ ≤ 1 := fun a => IsUltrametricDist.norm_natCast_le_one _ a
    have key : ∀ i, ‖o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      intro i
      have e : (((k i).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (((k i).val / l ^ n' : ℕ) : Qbar l) + (((k i).val % l ^ n' : ℕ) : Qbar l) := by
        exact_mod_cast (Nat.div_add_mod (k i).val (l ^ n')).symm
      have e2 : o i * ((k i).val : Qbar l) - o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (o i * (((k i).val / l ^ n' : ℕ) : Qbar l)) := by
        rw [ZMod.val_natCast]
        linear_combination (o i) * e
      rw [e2, norm_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (ho i) (norm_nonneg _) (hN _))
    have h1 : ‖Z m s 1 - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine le_trans hcg ?_
      rw [norm_pow, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (hN l) (by omega)
    have h2 : ‖∑ i, (o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => key i)
    have h3 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    rw [Finset.sum_sub_distrib, sub_add_sub_cancel] at h3
    exact h3

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory.InertiaFixedValue

open GlobalTheory.Published.AbVarRed IsLocalRing

theorem valuation_intCast_lt_one_iff {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    (h : OverL l A) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (l : ℤ) ∣ n := by
  obtain ⟨v, hv, hl⟩ := h
  have hlZ : ((l : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by rw [Int.cast_natCast]; exact hl
  have hiff : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ (l : ℤ) ∣ n := by
    constructor
    · intro hn
      by_contra hnd
      have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)
      obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd
      apply v.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : ((a * l + b * n : ℤ) : 𝓞 ℚ) = 1 := by rw [hab, Int.cast_one]
      rw [← e]
      push_cast
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hlZ) (v.asIdeal.mul_mem_left _ hn)
    · rintro ⟨m, rfl⟩
      push_cast
      exact v.asIdeal.mul_mem_right _ (by exact_mod_cast hlZ)
  rw [← hiff, ← hv (n : 𝓞 ℚ)]
  simp

private theorem valuation_intCast_eq_one_of_not_dvd {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {A : ValuationSubring Ω} (h : OverL l A) (z : ℤ) (hz : ¬ (l : ℤ) ∣ z) : A.valuation (z : Ω) = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A z))
    (not_lt.1 fun hlt => hz ((valuation_intCast_lt_one_iff h z).1 hlt))

private theorem not_dvd_den_of_valuation_le_one {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {A : ValuationSubring Ω} (h : OverL l A) (q : ℚ) (hq : A.valuation (algebraMap ℚ Ω q) ≤ 1) :
    ¬ (l : ℤ) ∣ (q.den : ℤ) := by
  intro hd

  have hn : ¬ (l : ℤ) ∣ q.num := by
    intro hn
    have h1 : l ∣ q.num.natAbs := Int.ofNat_dvd_left.1 hn
    have h2 : l ∣ q.den := by exact_mod_cast hd
    have h3 : l ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [Nat.Coprime.gcd_eq_one q.reduced] at this
    exact (Fact.out : l.Prime).ne_one (Nat.dvd_one.1 h3)
  have e0 : algebraMap ℚ Ω q * ((q.den : ℤ) : Ω) = (q.num : Ω) := by
    rw [← map_intCast (algebraMap ℚ Ω) (q.den : ℤ), ← map_intCast (algebraMap ℚ Ω) q.num, ← map_mul]
    congr 1
    rw [Int.cast_natCast]
    exact Rat.mul_den_eq_num q
  have e : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) = 1 := by
    rw [← map_mul, e0, valuation_intCast_eq_one_of_not_dvd h _ hn]
  have hlt : A.valuation ((q.den : ℤ) : Ω) < 1 := (valuation_intCast_lt_one_iff h _).2 hd
  have hlt1 : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) < 1 :=
    calc A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω)
        ≤ 1 * A.valuation ((q.den : ℤ) : Ω) := by gcongr
      _ = A.valuation ((q.den : ℤ) : Ω) := one_mul _
      _ < 1 := hlt
  rw [e] at hlt1
  exact lt_irrefl _ hlt1

theorem isAbove_of_overL {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    (h : OverL l A) (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [Algebra ℤ R] [(Ideal.span {(l : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(l : ℤ)})] :
    IsAbove R ℚ A.toSubring := by
  unfold IsAbove
  have hcast : ∀ z : ℤ, algebraMap R ℚ (algebraMap ℤ R z) = z := fun z =>
    eq_intCast ((algebraMap R ℚ).comp (algebraMap ℤ R)) z
  have hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ) := fun s hd =>
    Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)
  have hmk : ∀ (a : ℤ) (s : (Ideal.span {(l : ℤ)}).primeCompl),
      algebraMap R ℚ (IsLocalization.mk' R a s) = (a : ℚ) / ((s : ℤ) : ℚ) := by
    intro a s
    have hne : ((s : ℤ) : ℚ) ≠ 0 := by
      have : (s : ℤ) ≠ 0 := fun h0 => hs0 s (h0 ▸ dvd_zero _)
      exact_mod_cast this
    rw [eq_div_iff hne, ← hcast a, ← hcast (s : ℤ), ← map_mul, IsLocalization.mk'_spec]
  ext x
  rw [Subring.mem_comap, RingHom.mem_range]
  change algebraMap ℚ Ω x ∈ A ↔ _
  rw [← A.valuation_le_one_iff]
  constructor
  · intro hx
    have hden := not_dvd_den_of_valuation_le_one h x hx
    refine ⟨IsLocalization.mk' R x.num
      ⟨(x.den : ℤ), Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩, ?_⟩
    rw [hmk]
    push_cast
    exact Rat.num_div_den x
  · rintro ⟨r, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(l : ℤ)}).primeCompl r
    rw [hmk, map_div₀, map_intCast, map_intCast, map_div₀, valuation_intCast_eq_one_of_not_dvd h _ (hs0 s),
      div_one]
    exact (A.valuation_le_one_iff _).2 (intCast_mem A a)

theorem valuation_eq_zpow_of_fixed {R K Ω : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) {π : R} (hπ : Irreducible π)
    {c : Ω} (hc0 : c ≠ 0) (hc : c ∈ IntermediateField.fixedField (inertia K V)) :
    ∃ k : ℤ, V.valuation c = V.valuation (algebraMap K Ω (algebraMap R K π)) ^ k := by
  set p : Ω := algebraMap K Ω (algebraMap R K π) with hp
  have hpF : p ∈ IntermediateField.fixedField (inertia K V) := IntermediateField.algebraMap_mem _ _
  have hp0 : p ≠ 0 := by
    rw [hp, Ne, map_eq_zero_iff _ (algebraMap K Ω).injective,
      map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero

  have hstep : ∀ n : ℕ, ∀ x : Ω, x ∈ IntermediateField.fixedField (inertia K V) → x ≠ 0 → x ∈ V →
      x / p ^ n ∉ V → ∃ k : ℕ, V.valuation x = V.valuation p ^ k := by
    intro n
    induction n with
    | zero =>
      intro x _ _ hxV hn
      rw [pow_zero, div_one] at hn
      exact absurd hxV hn
    | succ n ih =>
      intro x hxF hx0 hxV hn
      by_cases hxu : x ∈ V.nonunits
      · have hd : x / p ∈ V := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ x hxF hxu
        have hdn : x / p / p ^ n ∉ V := by rwa [div_div, ← pow_succ']
        obtain ⟨k, hk⟩ := ih (x / p) (div_mem hxF hpF) (div_ne_zero hx0 hp0) hd hdn
        refine ⟨k + 1, ?_⟩
        calc V.valuation x = V.valuation (x / p * p) := by rw [div_mul_cancel₀ x hp0]
          _ = V.valuation p ^ (k + 1) := by rw [map_mul, hk, pow_succ]
      · refine ⟨0, ?_⟩
        rw [pow_zero]
        exact le_antisymm ((V.valuation_le_one_iff x).2 hxV)
          (not_lt.1 fun hlt => hxu (V.mem_nonunits_iff.2 hlt))
  by_cases hcV : c ∈ V
  · obtain ⟨n, hn⟩ := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c hc0
    obtain ⟨k, hk⟩ := hstep n c hc hc0 hcV hn
    exact ⟨k, by rw [hk, zpow_natCast]⟩
  · have hi : c⁻¹ ∈ V := (V.mem_or_inv_mem c).resolve_left hcV
    obtain ⟨n, hn⟩ := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c⁻¹ (inv_ne_zero hc0)
    obtain ⟨k, hk⟩ := hstep n c⁻¹ (inv_mem hc) (inv_ne_zero hc0) hi hn
    refine ⟨-(k : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, ← hk, map_inv₀, inv_inv]

theorem valuation_eq_zpow_of_ine_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ c : Ω, c ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s c = c) →
    ∃ k : ℤ, A.valuation c = A.valuation (l : Ω) ^ k := by
  intro l _ Ω _ _ _ A hA c hc0 hc
  have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)
  have hne : Ideal.span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hM : (Ideal.span {(l : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpr.irreducible
  have hP : (Ideal.span {(l : ℤ)}).IsPrime := hM.isPrime

  set B := A.comap (algebraMap ℚ Ω) with hB
  have hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ) := fun s hd =>
    Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)
  have hloc : IsLocalization.AtPrime B (Ideal.span {(l : ℤ)}) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro s
      have hs' := hs0 s
      have hsq : ((s : ℤ) : ℚ) ≠ 0 := by
        have : (s : ℤ) ≠ 0 := fun h0 => hs' (h0 ▸ dvd_zero _)
        exact_mod_cast this
      have hinv : ((s : ℤ) : ℚ)⁻¹ ∈ B := by
        rw [hB, ValuationSubring.mem_comap, ← A.valuation_le_one_iff, map_inv₀, map_intCast, map_inv₀,
          valuation_intCast_eq_one_of_not_dvd hA _ hs', inv_one]
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      simp [hsq]
    · intro z
      have hz : A.valuation (algebraMap ℚ Ω (z : ℚ)) ≤ 1 :=
        (A.valuation_le_one_iff _).2 (ValuationSubring.mem_comap.1 z.2)
      have hden := not_dvd_den_of_valuation_le_one hA _ hz
      refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ),
        Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩⟩, Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul, eq_intCast, SubringClass.coe_intCast, Int.cast_natCast]
      exact Rat.mul_den_eq_num _
    · intro x y hxy
      refine ⟨1, ?_⟩
      have hq : (x : ℚ) = y := by
        have := congrArg (fun b : B => (b : ℚ)) hxy
        simpa using this
      simp only [OneMemClass.coe_one, one_mul]
      exact_mod_cast hq
  have : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hne B
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have : Finite (ℤ ⧸ Ideal.span {(l : ℤ)}) := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod l).symm.toEquiv
  have : Finite (ResidueField B) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal (Ideal.span {(l : ℤ)}) B).toEquiv
  have hAb : IsAbove B ℚ A.toSubring := isAbove_of_overL hA B
  have hirr : Irreducible (algebraMap ℤ B l) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(l : ℤ)}) B, Ideal.map_span,
      Set.image_singleton]

  have hs : ∀ σ ∈ inertia ℚ A, σ ∈ Ine (F := ℚ) A := by
    intro σ hσ
    rw [mem_Ine]
    unfold inertia at hσ
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hσ
    refine ⟨τ.2, fun x hx => ?_⟩
    set a : A := ⟨x, (A.valuation_le_one_iff x).1 hx⟩
    have hfix : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := by
      have := congrArg (fun f => f (IsLocalRing.residue A a)) (MonoidHom.mem_ker.1 hτ)
      simpa using this
    have h0 : IsLocalRing.residue A (τ • a - a) = 0 := by
      rw [map_sub, IsLocalRing.ResidueField.residue_smul, hfix, sub_self]
    have hm : τ • a - a ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq_zero_iff_mem.1 h0
    exact (A.valuation_lt_one_iff _).1 hm
  have hfixc : c ∈ IntermediateField.fixedField (inertia ℚ A) :=
    (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => hc σ (hs σ hσ)
  obtain ⟨k, hk⟩ := valuation_eq_zpow_of_fixed A hAb hirr hc0 hfixc
  refine ⟨k, ?_⟩
  rw [hk]
  simp

end GlobalTheory.InertiaFixedValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTransportsKaehlerRelationsOverInvariantsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_transports_kaehler_relations_over_invariants : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω), s ∈ Ine (F := ℚ) A → ∀ a b a' b' c d c' d' : A, (c : Ω) = s a → (d : Ω) = s b → (c' : Ω) = s a' → (d' : Ω) = s b' → a • dA A b = a' • dA A b' → c • dA A d = c' • dA A d' := by
  first | (exact @GlobalTheory.RecOne.transp_rel) | (exact GlobalTheory.RecOne.transp_rel) | (intros; apply GlobalTheory.RecOne.transp_rel  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernelStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_inertia_cyclotomic_kernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) (m : ℕ), IsClosed ((Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  first | exact @GlobalTheory.isClosed_Ine_inf_ker_cycMod | exact GlobalTheory.isClosed_Ine_inf_ker_cycMod | (intros; apply GlobalTheory.isClosed_Ine_inf_ker_cycMod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalDualityCharacterOrthogonalClassesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_duality_character_orthogonal_classes : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' a b : G ℚ Ω → Qbar l), OverL l A → ContinuousOn k (Dec (F := ℚ) A) → ContinuousOn k' (Dec (F := ℚ) A) → ContinuousOn a (Dec (F := ℚ) A) → ContinuousOn b (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ a s ∈ c.O ∧ b s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t ∧ k' (s * t) = k' s * k' t ∧ b (s * t) = b s + k s * b t ∧ a (s * t) = a s + k' s * a t) → (∃ s ∈ Dec (F := ℚ) A, k s ≠ 1) → (∃ s ∈ Dec (F := ℚ) A, k' s ≠ 1) → (∀ n : ℕ, Cob2 c n (Dec (F := ℚ) A) (fun s t => b s * (k' s * a t))) → (∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, b s = k s * x - x) ∨ ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x := by
  first | exact @GlobalTheory.Ord2.localDuality_char | exact GlobalTheory.Ord2.localDuality_char | (intros; apply GlobalTheory.Ord2.localDuality_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroOrdinaryClassOfCompatibleCocyclesModPowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_ordinary_class_of_compatible_cocycles_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) → (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (a (n + 1) s) (a n s)) → (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) → (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) → (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) → (¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y)) → ¬ GrZero W A := by
  first | exact @GlobalTheory.Ord2.limit_nonzero_ordinary_class | exact GlobalTheory.Ord2.limit_nonzero_ordinary_class | (intros; apply GlobalTheory.Ord2.limit_nonzero_ordinary_class <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory.AmiceDist

variable {l : ℕ} [Fact l.Prime]

theorem sum_level (μ : ∀ r : ℕ, ZMod (l ^ r) → Qbar l)
    (hμ : ∀ r (x : ZMod (l ^ r)), μ r x = ∑ x' ∈ Finset.univ.filter
      (fun x' : ZMod (l ^ (r + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x), μ (r + 1) x')
    {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) (R : ℕ) (hR : r ≤ R) :
    ∑ x : ZMod (l ^ R), μ R x * z ^ x.val = ∑ x : ZMod (l ^ r), μ r x * z ^ x.val := by
  induction R, hR using Nat.le_induction with
  | base => rfl
  | succ R hR ih =>
    rw [← ih]
    have hzR : z ^ (l ^ R) = 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hR
      rw [pow_add, pow_mul, hz, one_pow]
    rw [← Finset.sum_fiberwise Finset.univ
      (fun x' : ZMod (l ^ (R + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ R)) (ZMod (l ^ R)) x')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hμ R x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    rw [← (Finset.mem_filter.1 hx').2, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
      ← pow_eq_pow_mod _ hzR]

theorem norm_trunc_binomial {w : Qbar l} (hw : ‖w‖ ≤ 1) (N k : ℕ) :
    ‖∑ n ∈ Finset.range N, (k.choose n : Qbar l) * w ^ n - (w + 1) ^ k‖ ≤ ‖w‖ ^ N := by
  have h1 : (w + 1) ^ k = ∑ n ∈ Finset.range (N + (k + 1)), (k.choose n : Qbar l) * w ^ n := by
    rw [add_pow]
    simp only [one_pow, mul_one]
    simp_rw [mul_comm (w ^ _)]
    refine Finset.sum_subset (Finset.range_mono (Nat.le_add_left _ _)) fun n _ hn => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hn)]
    simp
  rw [h1, Finset.sum_range_add, sub_add_cancel_left, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hw (Nat.le_add_right _ _))

theorem norm_sub_one_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) : ‖z - 1‖ ≤ 1 := by
  have h : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h1
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  simp [h]

theorem norm_sub_one_pow_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) : ‖z - 1‖ ^ (l ^ r) ≤ ‖((l : ℕ) : Qbar l)‖ := by
  have hw := norm_sub_one_le hz
  have h := (Commute.all (z - 1) 1).add_pow_prime_pow_eq (Fact.out : l.Prime) r
  rw [sub_add_cancel, hz] at h
  simp only [one_pow, mul_one] at h
  have h2 : (z - 1) ^ (l ^ r) = -((l : Qbar l) * (z - 1) *
      ∑ k ∈ Finset.Ioo 0 (l ^ r), (z - 1) ^ (k - 1) * (((l ^ r).choose k / l : ℕ) : Qbar l)) := by
    linear_combination -h
  rw [← norm_pow, h2, norm_neg, norm_mul, norm_mul]
  have h3 : ‖∑ k ∈ Finset.Ioo 0 (l ^ r), (z - 1) ^ (k - 1) * (((l ^ r).choose k / l : ℕ) : Qbar l)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hw) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  calc _ ≤ ‖((l : ℕ) : Qbar l)‖ * 1 * 1 := by gcongr
    _ = _ := by ring

theorem norm_sub_one_pow_three_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) :
    ‖z - 1‖ ^ (l ^ (3 * r)) ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  rw [show 3 * r = r + 2 * r by ring, pow_add, pow_mul, norm_pow]
  refine (pow_le_pow_left₀ (by positivity) (norm_sub_one_pow_le hz) _).trans ?_
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le

theorem amice : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (μ : ∀ r : ℕ, ZMod (l ^ r) → Qbar l), (∀ r x, μ r x ∈ c.O) →
    (∀ r (x : ZMod (l ^ r)), μ r x = ∑ x' ∈ Finset.univ.filter
      (fun x' : ZMod (l ^ (r + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x), μ (r + 1) x') →
    ∃ L : PowerSeries (Qbar l), (∀ n, L.coeff n ∈ c.O) ∧ ∀ r, 1 ≤ r → ∀ z : Qbar l, z ^ (l ^ r) = 1 →
      Cg (2 * r) (tval L (l ^ (3 * r)) z) (∑ x : ZMod (l ^ r), μ r x * z ^ x.val) := by
  intro l _ c μ hO hμ
  let a : ℕ → ℕ → Qbar l := fun n R => ∑ x : ZMod (l ^ R), μ R x * (x.val.choose n : Qbar l)
  have ha : ∀ n R, a n R ∈ c.O := fun n R => sum_mem fun x _ => mul_mem (hO R x) (natCast_mem _ _)
  have hlim : ∀ n, ∃ b ∈ c.O, Filter.Tendsto (a n) (Filter.hyperfilter ℕ) (nhds b) := by
    intro n
    obtain ⟨b, hb, h⟩ := (GlobalTheory.Coef.isCompact_O l c).ultrafilter_le_nhds ((Filter.hyperfilter ℕ).map (a n))
      (by
        rw [Filter.le_principal_iff]
        exact Filter.mem_map.2 (Filter.univ_mem' fun R => ha n R))
    exact ⟨b, hb, h⟩
  choose b hb hab using hlim
  refine ⟨PowerSeries.mk b, fun n => by simpa using hb n, fun r _ z hz => ?_⟩
  unfold Cg tval
  simp only [PowerSeries.coeff_mk]
  have ht : Filter.Tendsto (fun R => ‖∑ n ∈ Finset.range (l ^ (3 * r)), a n R * (z - 1) ^ n -
      ∑ x : ZMod (l ^ r), μ r x * z ^ x.val‖) (Filter.hyperfilter ℕ)
      (nhds ‖∑ n ∈ Finset.range (l ^ (3 * r)), b n * (z - 1) ^ n - ∑ x : ZMod (l ^ r), μ r x * z ^ x.val‖) :=
    ((tendsto_finset_sum _ fun n _ => (hab n).mul_const _).sub_const _).norm
  refine le_of_tendsto ht ?_
  have hev : ∀ᶠ R in (Filter.hyperfilter ℕ : Filter ℕ), r ≤ R :=
    Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop r)
  filter_upwards [hev] with R hR
  rw [← sum_level μ hμ hz R hR]
  simp only [a, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (FirstDer.norm_le_one_of_mem c (hO R x))).trans ?_
  have h := norm_trunc_binomial (norm_sub_one_le hz) (l ^ (3 * r)) x.val
  rw [sub_add_cancel] at h
  exact h.trans (norm_sub_one_pow_three_le hz)

end GlobalTheory.AmiceDist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdDualGeneratorPairingModPowNondegenerateStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n), (∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) → b = 0 := by
  first | exact @GlobalTheory.Ord2.SelPerp.pair_nondeg | exact GlobalTheory.Ord2.SelPerp.pair_nondeg | (intros; apply GlobalTheory.Ord2.SelPerp.pair_nondeg <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.tau_mul_dvd | exact GlobalTheory.Ord2.SelPerp.tau_mul_dvd | (intros; apply GlobalTheory.Ord2.SelPerp.tau_mul_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlanePairingEquivariantTwistCartierDualStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.planePairing_equivariant_twist_cartierDual : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (s : G ℚ Ω) (y : Mn c n), GlobalTheory.Ord2.SelPerp.Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ y) = twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) (GlobalTheory.Ord2.SelPerp.Phi c n y) := by
  first | exact @GlobalTheory.Ord2.SelPerp.Phi_equivariant | exact GlobalTheory.Ord2.SelPerp.Phi_equivariant | (intros; apply GlobalTheory.Ord2.SelPerp.Phi_equivariant <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.matQ_det_sq | exact GlobalTheory.Ord2.SelPerp.matQ_det_sq | (intros; apply GlobalTheory.Ord2.SelPerp.matQ_det_sq <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.matQ_dual1_apply | exact GlobalTheory.Ord2.SelPerp.matQ_dual1_apply | (intros; apply GlobalTheory.Ord2.SelPerp.matQ_dual1_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientCharTrivialInertiaCyclotomicTowerStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_char_trivial_inertia_cyclotomic_tower : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → mat W s 1 1 = 1 := by
  first | exact @GlobalTheory.quot_eq_one_of_cycBar_eq_one | exact GlobalTheory.quot_eq_one_of_cycBar_eq_one | (intros; apply GlobalTheory.quot_eq_one_of_cycBar_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedSelmerCochainMemContinuousCocyclesOfContStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_selmer_cochain_mem_continuous_cocycles_of_cont : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ∀ z ∈ divSelCoc c W S A, ∀ y : Fin 2 → Qbar l, VecE c y → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) → descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  first | exact @GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous | exact GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous | (intros; apply GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous <;> assumption)
end


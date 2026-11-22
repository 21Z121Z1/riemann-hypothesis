import Mathlib
import Formalism.CMTypeGalois.StatementField

-- bundled from Formalism.CMTypeGalois.CMTypeFrobenius.HostConj
section
open NumberField

noncomputable section

namespace Formalism.Q3

namespace CMConjugation

variable {q : Fin 3 → ℕ} {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}

lemma q_pos (hq : Hyp3 q) (i : Fin 3) : 0 < q i := (hq.1 i).1.pos

lemma alpha_sq (hα : IsHost q α) (i : Fin 3) : α i ^ 2 = -(q i : E) := by
  rw [hα.1 i]; push_cast; ring

lemma alpha_ne_zero (hq : Hyp3 q) (hα : IsHost q α) (i : Fin 3) : α i ≠ 0 := by
  intro h0
  have h1 := alpha_sq hα i
  rw [h0, zero_pow two_ne_zero, zero_eq_neg] at h1
  exact (q_pos hq i).ne' (by exact_mod_cast h1)

lemma sigma_alpha (hα : IsHost q α) (σ : Gal(E/ℚ)) (i : Fin 3) :
    σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i := by
  have hsq : σ (α i) ^ 2 = α i ^ 2 := by
    rw [← map_pow, hα.1 i, map_intCast]
  unfold galSign
  split_ifs with hc
  · simp [hc]
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
    · exact absurd h1 hc
    · simp [h1]

lemma galSign_eq_cc_iff (hq : Hyp3 q) (hα : IsHost q α) (σ : Gal(E/ℚ)) :
    galSign α σ = cc ↔ ∀ i, σ (α i) = -α i := by
  constructor
  · intro h i
    rw [sigma_alpha hα σ i, h]
    simp [cc]
  · intro h
    funext i
    unfold galSign cc
    rw [if_neg]
    rw [h i]
    intro h2
    have h3 : (2 : E) * α i = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact alpha_ne_zero hq hα i h4

lemma algAdjoin_eq_top (hα : IsHost q α) : Algebra.adjoin ℚ (Set.range α) = ⊤ := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hα.2]
  rfl

lemma phi_conj (hq : Hyp3 q) (hα : IsHost q α) (φ : E →+* ℂ) (i : Fin 3) :
    starRingEnd ℂ (φ (α i)) = -φ (α i) := by
  set z := φ (α i) with hzdef
  have hz : z ^ 2 = -(q i : ℂ) := by
    rw [hzdef, ← map_pow, alpha_sq hα i, map_neg, map_natCast]
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exfalso
    have hre := Complex.conj_eq_iff_re.1 h2
    have h3 : ((z.re ^ 2 : ℝ) : ℂ) = ((-(q i : ℝ) : ℝ) : ℂ) := by
      push_cast; rw [hre]; exact hz
    have h4 := Complex.ofReal_injective h3
    have h5 : (0 : ℝ) < q i := by exact_mod_cast q_pos hq i
    nlinarith [sq_nonneg z.re]
  · exact h2

lemma phi_alpha_ne_zero (hq : Hyp3 q) (hα : IsHost q α) (φ : E →+* ℂ) (i : Fin 3) :
    φ (α i) ≠ 0 := by
  rw [map_ne_zero]; exact alpha_ne_zero hq hα i

lemma part1 (hq : Hyp3 q) (hα : IsHost q α) (φ : E →+* ℂ) (σ : Gal(E/ℚ)) :
    (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galSign α σ = cc := by
  rw [galSign_eq_cc_iff hq hα]
  constructor
  · intro h i
    apply φ.injective
    rw [h, map_neg, phi_conj hq hα]
  · intro h
    have heq : (φ.comp (σ : E →+* E)).toRatAlgHom = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top (algAdjoin_eq_top hα)
      rintro _ ⟨i, rfl⟩
      simp only [RingHom.toRatAlgHom_apply, RingHom.coe_comp, Function.comp_apply]
      change φ (σ (α i)) = starRingEnd ℂ (φ (α i))
      rw [h i, map_neg, phi_conj hq hα]
    intro x
    have := congrArg (fun f => f x) heq
    simpa using this

lemma not_sq_mul (p m : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m) : ¬ IsSquare (p * m) := by
  rintro ⟨r, hr⟩
  have h1 : p ∣ r * r := ⟨m, hr.symm⟩
  have h2 : p ∣ r := (hp.dvd_mul.1 h1).elim id id
  obtain ⟨s, rfl⟩ := h2
  apply hm
  have h3 : p * m = p * (s * (p * s)) := by rw [hr]; ring
  rw [Nat.eq_of_mul_eq_mul_left hp.pos h3]
  exact Dvd.intro (s * s) (by ring)

end CMConjugation

open CMConjugation

theorem hostConj_of (hH : HostGalois) (hK : MQKummer) : HostConj := by
  intro q hq E _ _ α hα
  obtain ⟨hGal, hfin, hbij, _hmul⟩ := hH q hq E α hα
  have h1 : ∀ (φ : E →+* ℂ) (σ : Gal(E/ℚ)),
      (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galSign α σ = cc := part1 hq hα
  obtain ⟨σc, hσc⟩ := hbij.2 cc
  have hTC : IsTotallyComplex E := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro h
    have h2 := RingHom.congr_fun h (α 0)
    rw [ComplexEmbedding.conjugate_coe_eq, phi_conj hq hα] at h2
    have h3 : (2 : ℂ) * w.embedding (α 0) = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact phi_alpha_ne_zero hq hα _ 0 h4
  have hCM : IsCMField E := by
    refine IsCMField.of_forall_isConj E (σ := σc) (fun φ => ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact ((h1 φ σc).2 hσc x).symm
  have h5 : ∀ x : E, x ∈ maximalRealSubfield E ↔ ∀ σ : Gal(E/ℚ), galSign α σ = cc → σ x = x := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx σ hσ
      let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
      apply φ.injective
      rw [(h1 φ σ).2 hσ x]
      exact hx φ
    · intro h φ
      have := (h1 φ σc).2 hσc x
      rw [h σc hσc] at this
      exact this.symm
  have h4 : Module.finrank ℚ (maximalRealSubfield E) = 4 := by
    have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, hfin] at h
    omega
  refine ⟨h1, hCM, ?_, h4, h5, ?_⟩
  · intro _
    let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    apply (h1 φ _).1
    intro x
    rw [AlgEquiv.restrictScalars_apply, IsCMField.complexEmbedding_complexConj]
  · have hcc : ∀ σ : Gal(E/ℚ), galSign α σ = cc → ∀ i, σ (α i) = -α i :=
      fun σ hσ => (galSign_eq_cc_iff hq hα σ).1 hσ
    set K := IntermediateField.adjoin ℚ ({α 0 * α 1, α 1 * α 2} : Set E) with hKdef
    let L : IntermediateField ℚ E := (maximalRealSubfield E).toIntermediateField
      (fun r => (h5 _).2 (fun σ _ => σ.commutes r))
    have hKL : K ≤ L := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      show x ∈ maximalRealSubfield E
      rw [h5]
      intro σ hσ
      rcases hx with rfl | rfl
      · rw [map_mul, hcc σ hσ, hcc σ hσ]; ring
      · rw [map_mul, hcc σ hσ, hcc σ hσ]; ring
    have hp := fun i => (hq.1 i).1
    have hndvd : ∀ i j, i ≠ j → ¬ q i ∣ q j := fun i j hij h =>
      hq.2.ne hij ((Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).1 h)
    have key : ∀ n : ℕ, ¬ IsSquare n → ¬ IsSquare (n : ℚ) := fun n h => by
      rwa [Rat.isSquare_natCast_iff]
    have hKfin : Module.finrank ℚ K = 4 := by
      let β : Fin 2 → K := ![⟨α 0 * α 1, IntermediateField.subset_adjoin ℚ _ (by simp)⟩,
        ⟨α 1 * α 2, IntermediateField.subset_adjoin ℚ _ (by simp)⟩]
      let a : Fin 2 → ℤ := ![((q 0 * q 1 : ℕ) : ℤ), ((q 1 * q 2 : ℕ) : ℤ)]
      have hmq' : @IsMQ 2 K _ K.algebra' a β := by
        refine ⟨?_, ?_⟩
        · intro i
          apply Subtype.ext
          fin_cases i
          · simp [β, a, mul_pow, alpha_sq hα]
          · simp [β, a, mul_pow, alpha_sq hα]
        · apply IntermediateField.map_injective K.val
          rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
            IntermediateField.fieldRange_val]
          show _ = IntermediateField.adjoin ℚ ({α 0 * α 1, α 1 * α 2} : Set E)
          congr 1
          ext x
          simp only [Set.mem_image, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
            fin_cases i
            · left; rfl
            · right; rfl
          · rintro (rfl | rfl)
            · exact ⟨β 0, ⟨0, rfl⟩, rfl⟩
            · exact ⟨β 1, ⟨1, rfl⟩, rfl⟩
      have hmq : IsMQ a β := by convert hmq'; exact Subsingleton.elim _ _
      have hns : ∀ S : Finset (Fin 2), S.Nonempty → ¬ IsSquare (∏ i ∈ S, (a i : ℚ)) := by
        intro S hS
        have hS' : S = {0} ∨ S = {1} ∨ S = Finset.univ := by
          revert S; decide
        rcases hS' with rfl | rfl | rfl
        · have e : (∏ i ∈ ({0} : Finset (Fin 2)), (a i : ℚ)) = ((q 0 * q 1 : ℕ) : ℚ) := by
            simp [a]
          rw [e]; exact key _ (not_sq_mul _ _ (hp 0) (hndvd 0 1 (by decide)))
        · have e : (∏ i ∈ ({1} : Finset (Fin 2)), (a i : ℚ)) = ((q 1 * q 2 : ℕ) : ℚ) := by
            simp [a]
          rw [e]; exact key _ (not_sq_mul _ _ (hp 1) (hndvd 1 2 (by decide)))
        · have e : (∏ i ∈ (Finset.univ : Finset (Fin 2)), (a i : ℚ)) =
              ((q 0 * (q 1 * q 1 * q 2) : ℕ) : ℚ) := by
            simp [a, Fin.prod_univ_two]; ring
          rw [e]
          refine key _ (not_sq_mul _ _ (hp 0) ?_)
          intro h
          rcases (hp 0).dvd_mul.1 h with h | h
          · rcases (hp 0).dvd_mul.1 h with h | h
            · exact hndvd 0 1 (by decide) h
            · exact hndvd 0 1 (by decide) h
          · exact hndvd 0 2 (by decide) h
      have := (hK 2 K a β hmq hns).1
      convert this using 1
      norm_num
    have hLfin : Module.finrank ℚ L = 4 := h4
    have hKL' := IntermediateField.eq_of_le_of_finrank_eq hKL (hKfin.trans hLfin.symm)
    rw [hKL']
    rfl

end Formalism.Q3
end
end

-- bundled from Formalism.CMTypeGalois.CMTypeFrobenius.HostEmb
section
open NumberField Finset

noncomputable section

namespace Formalism.Q3

open Classical in
theorem hostEmb_of (hC : HostConj) (hH : HostGalois) : HostEmb := by
  intro q hq E _ _ α hα φ₀
  obtain ⟨hGal, hfin, hbij, hmul⟩ := hH q hq E α hα
  have := hGal
  have hconj := (hC q hq E α hα).1
  set F : Gal(E/ℚ) → (E →+* ℂ) := fun σ => φ₀.comp σ.toAlgHom.toRingHom with hF
  have hinj : Function.Injective F := by
    intro σ τ h
    apply AlgEquiv.ext
    intro x
    have := congrArg (fun f : E →+* ℂ => f x) h
    exact φ₀.injective this
  have hcard : Fintype.card Gal(E/ℚ) = Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  have hFbij : Function.Bijective F :=
    (Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, hcard⟩
  have hcc : ∀ σ τ : Gal(E/ℚ), galSign α τ = cc →
      F (τ * σ) = ComplexEmbedding.conjugate (F σ) := by
    intro σ τ hτ
    have h1 := (hconj φ₀ τ).mpr hτ
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact h1 (σ y)
  refine ⟨hFbij, hcc, ?_⟩
  intro Φ
  obtain ⟨τc, hτc⟩ := hbij.2 cc
  have hmem : ∀ σ, F σ ∈ (univ.filter (fun σ : Gal(E/ℚ) => galSign α σ ∈ Φ)).image F ↔
      galSign α σ ∈ Φ := by
    intro σ
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨s, hs, he⟩
      rwa [← hinj he]
    · intro h
      exact ⟨σ, h, rfl⟩
  constructor
  · intro hΦ ψ
    obtain ⟨σ, rfl⟩ := hFbij.2 ψ
    rw [← hcc σ τc hτc, hmem, hmem, hmul, hτc]
    exact hΦ _
  · intro hT g
    obtain ⟨σ, rfl⟩ := hbij.2 g
    have := hT (F σ)
    rw [← hcc σ τc hτc, hmem, hmem, hmul, hτc] at this
    exact this

end Formalism.Q3
end
end

-- bundled from Formalism.CMTypeGalois.CMTypeFrobenius.HostFrob
section
open NumberField Ideal

noncomputable section

namespace Formalism.Q3

theorem hostFrob_val (hF : MQFrob) (hK : KroneckerMeaning) (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (p : ℕ) [Fact p.Prime] (hpq : ∀ i, p ≠ q i)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ))
    (H : IsArithFrobAt ℤ σ P) (i : Fin 3) :
    ((galSign α σ i : ℤˣ) : ℤ) = chiQ (q i) p := by
  have hp : p.Prime := Fact.out
  obtain ⟨hqi, hq4⟩ := hq.1 i
  have hne : ∀ j, (-(q j : ℤ)) ≠ 0 := fun j => by
    have := (hq.1 j).1.pos
    omega
  have h := hF 3 E (fun j => -(q j : ℤ)) α hα hne p P σ H i
  by_cases h2 : p = 2
  · subst h2
    have hmod4 : (-(q i : ℤ)) % 4 = 1 := by omega
    have h8 := h.2 rfl hmod4
    have hchi := (hK (q i) hqi hq4).2.1
    have hcop : Int.gcd 2 (q i : ℤ) = 1 := by
      have hodd : Odd (q i) := Nat.odd_iff.mpr (by omega)
      have : Int.gcd ((2 : ℕ) : ℤ) (q i : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact Nat.coprime_two_left.mpr hodd
      exact_mod_cast this
    have hpm : chiQ (q i) 2 = 1 ∨ chiQ (q i) 2 = -1 := by
      unfold chiQ
      exact jacobiSym.eq_one_or_neg_one hcop
    have hc2 : ((2 : ℕ) : ℤ) = 2 := by norm_num
    rw [hc2]
    rcases Int.units_eq_one_or (galSign α σ i) with hs | hs
    · have h7 : q i % 8 = 7 := by
        have := h8.mp hs
        omega
      rw [hs, hchi.mpr h7]
      rfl
    · have h7 : ¬ q i % 8 = 7 := by
        intro h7
        have : galSign α σ i = 1 := h8.mpr (by omega)
        rw [hs] at this
        exact absurd this (by decide)
      have hc : chiQ (q i) 2 = -1 := by
        rcases hpm with hpm | hpm
        · exact absurd (hchi.mp hpm) h7
        · exact hpm
      rw [hs, hc]
      rfl
  · have hnd : ¬ (p : ℤ) ∣ 2 * -(q i : ℤ) := by
      intro hd
      have hd' : p ∣ 2 * q i := by
        have : (p : ℤ) ∣ ((2 * q i : ℕ) : ℤ) := by
          push_cast
          rw [← dvd_neg]
          simpa [mul_neg] using hd
        exact_mod_cast this
      rcases (Nat.Prime.dvd_mul hp).mp hd' with h' | h'
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      · exact hpq i ((Nat.prime_dvd_prime_iff_eq hp hqi).mp h')
    rw [h.1 hnd]
    exact ((hK (q i) hqi hq4).1 p hp h2 (hpq i)).symm

theorem hostFrob_of (hF : MQFrob) (hH : HostGalois) (hK : KroneckerMeaning) : HostFrob := by
  intro q hq E _ _ α hα p _ hpq P _ _
  have hGal := hH q hq E α hα
  have : IsGalois ℚ E := hGal.1
  have : Finite (𝓞 E ⧸ P) := by
    have hpb : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(E/ℚ) P
  refine ⟨⟨τ, hτ⟩, fun σ => ⟨fun H i => hostFrob_val hF hK q hq E α hα p hpq P σ H i,
    fun h => ?_⟩⟩
  have hτv := hostFrob_val hF hK q hq E α hα p hpq P τ hτ
  have : σ = τ := hGal.2.2.1.1 (funext fun i => Units.ext ((h i).trans (hτv i).symm))
  subst this
  exact hτ

end Formalism.Q3
end
end


import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTypePrimeUnderEq
section
open NumberField IsDedekindDomain Formalism.L2.Col

noncomputable section
namespace GlobalTheory.GprimUnder

theorem conjO_conjO (X : Fields) (a : 𝓞 X.E) : X.conjO (X.conjO a) = a := by
  apply RingOfIntegers.ext
  show star (star (a : X.E)) = (a : X.E)
  exact star_star _

theorem conjO_algebraMap (X : Fields) (hX : X.Ok) (x : 𝓞 X.F) :
    X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) x) = algebraMap (𝓞 X.F) (𝓞 X.E) x := by
  apply RingOfIntegers.ext
  show star ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E)
  have : ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = algebraMap X.F X.E (x : X.F) := rfl
  rw [this]
  exact hX.star_F _

theorem mem_divs_iff {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) (P : HeightOneSpectrum A) :
    P ∈ divs a ↔ a ∈ P.asIdeal := by
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h0 : Ideal.span {a} ≠ ⊥ := by simpa using ha
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  unfold divs
  rw [dif_pos hfin, Set.Finite.mem_toFinset]
  rfl

def conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime X.conjO P.asIdeal
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, conjO_conjO]
      exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← conjO_conjO X x, h1, map_zero]

theorem mem_conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) (a : 𝓞 X.E) :
    a ∈ (conjPrime X P).asIdeal ↔ X.conjO a ∈ P.asIdeal := Ideal.mem_comap

theorem under_conjPrime (X : Fields) (hX : X.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime X P).under (𝓞 X.F) = P.under (𝓞 X.F) := by
  apply HeightOneSpectrum.ext
  ext x
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime X P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal
  rw [mem_conjPrime, conjO_algebraMap X hX]

theorem exists_vG_under : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)),
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  intro X Pr hX hPr i P hP
  have hg0 : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hc0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact hg0 h1.symm
  have hvG : ∀ v, v ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ v.asIdeal := fun v => mem_divs_iff hc0 v
  rw [← hPr.piG_norm i] at hP
  rcases P.isPrime.mem_or_mem hP with h | h
  · refine ⟨conjPrime X P, (hvG _).2 ?_, under_conjPrime X hX P⟩
    rw [mem_conjPrime, conjO_conjO]
    exact h
  · exact ⟨P, (hvG P).2 h, rfl⟩

end GlobalTheory.GprimUnder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnimodularLatticeLocalMatch
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace GlobalTheory.GO.SplitGlue

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in

theorem exists_smul_le {N N' : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hN' : Submodule.IsLattice E N') : ∃ a : 𝓞 E, a ≠ 0 ∧ ∀ x ∈ N', a • x ∈ N := by
  classical
  have h0 : ∀ x : Sp E n, ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ N := by
    intro x
    have hx : x ∈ Submodule.span E (N : Set (Sp E n)) := hN.span_eq_top ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (N : Set (Sp E n)) x hx
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  obtain ⟨s, rfl⟩ := hN'.fg
  choose a ha0 ha using h0
  refine ⟨∏ y ∈ s, a y, Finset.prod_ne_zero_iff.mpr fun y _ => ha0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ hy, mul_smul]
    exact N.smul_mem _ (ha y)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact N.smul_mem _ hy

omit [StarRing E] in

theorem mem_of_forall (N : Submodule (𝓞 E) (Sp E n)) {x : Sp E n}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ s ∉ w.asIdeal, s • x ∈ N) : x ∈ N := by
  by_contra hx
  have hI : N.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x) ≠ ⊤ := by
    intro h1
    have : (1 : 𝓞 E) ∈ N.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x) := h1 ▸ Submodule.mem_top
    exact hx (by simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hm0⟩
  exact hs (hle (by simpa using hsx))

omit [StarRing E] in

theorem eq_of_sameAt {N N' : Submodule (𝓞 E) (Sp E n)} (h : ∀ w, SameAt w N N') : N = N' := by
  apply le_antisymm
  · intro x hx
    refine mem_of_forall N' fun w => ?_
    obtain ⟨_, _, a', ha', _, h2⟩ := h w
    exact ⟨a', ha', h2 x hx⟩
  · intro x hx
    refine mem_of_forall N fun w => ?_
    obtain ⟨a, ha, _, _, h1, _⟩ := h w
    exact ⟨a, ha, h1 x hx⟩

omit [NumberField E] [StarRing E] in
theorem sameAt_symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

omit [NumberField E] [StarRing E] in
theorem sameAt_trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', h3, h4⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]; exact h1 _ (h3 x hx)
  · rw [mul_smul]; exact h4 _ (h2 x hx)

theorem conjP_conjP (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

theorem sameAt_dual {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt (conjPrime₂ Q) (dual (hStd E n) N) (dual (hStd E n) N') := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨cO E a', by rwa [mem_conjP, cO_cO], cO E a, by rwa [mem_conjP, cO_cO], fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_dual] at hx ⊢
    intro y hy
    rw [← hStd_osmul_left]
    exact hx _ (h2 y hy)
  · rw [mem_dual] at hx ⊢
    intro y hy
    rw [← hStd_osmul_left]
    exact hx _ (h1 y hy)

theorem exists_glue {L L' : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L')
    (P : HeightOneSpectrum (𝓞 E)) : ∃ L'' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E L'' ∧ SameAt P L' L'' ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q L L'' := by
  classical
  obtain ⟨a, ha0, ha⟩ := exists_smul_le hL hL'
  obtain ⟨b, hb0, hb⟩ := exists_smul_le hL' hL
  have hI : Ideal.span {a * b} ≠ ⊥ := by simpa using ⟨ha0, hb0⟩
  obtain ⟨J, hJ, hdJ⟩ := Ideal.eq_prime_pow_mul_coprime hI P.asIdeal (hpm := P.isMaximal)
  generalize Multiset.count P.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a * b})) = k at hdJ
  have hdvd : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∃ c, r * s = c * (a * b) := by
    intro r hr s hs
    have := Ideal.mul_mem_mul hr hs
    rw [← hdJ, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  have h1 : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∀ x ∈ L, (r * s) • x ∈ L' := by
    intro r hr s hs x hx
    obtain ⟨c, hc⟩ := hdvd r hr s hs
    rw [hc, ← mul_assoc, mul_smul]
    exact L'.smul_mem _ (hb x hx)
  have h2 : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∀ x ∈ L', (r * s) • x ∈ L := by
    intro r hr s hs x hx
    obtain ⟨c, hc⟩ := hdvd r hr s hs
    rw [hc, mul_comm a b, ← mul_assoc, mul_smul]
    exact L.smul_mem _ (ha x hx)
  obtain ⟨s, hsJ, hsP⟩ : ∃ s ∈ J, s ∉ P.asIdeal := by
    by_contra H
    push Not at H
    have : P.asIdeal ⊔ J ≤ P.asIdeal := sup_le le_rfl H
    rw [hJ] at this
    exact P.isPrime.ne_top (top_le_iff.1 this)
  have hs0 : s ≠ 0 := by rintro rfl; exact hsP P.asIdeal.zero_mem
  let L'' : Submodule (𝓞 E) (Sp E n) := J • L' ⊔ (P.asIdeal ^ k) • L
  have hA : ∀ x ∈ L', s • x ∈ L'' := fun x hx => Submodule.mem_sup_left (Submodule.smul_mem_smul hsJ hx)
  have hB : ∀ x ∈ L'', s • x ∈ L' := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine L'.add_mem (L'.smul_mem _ (Submodule.smul_le_right hy)) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul, mul_comm]; exact h1 r hr s hsJ u hu
    · rw [smul_add]; exact L'.add_mem hu hv
  refine ⟨L'', ?_, ⟨s, hsP, s, hsP, hB, hA⟩, fun Q hQ => ?_⟩
  · have hsup : Submodule.IsLattice E (L' ⊔ L) :=
      ⟨hL'.fg.sup hL.fg, by
        rw [eq_top_iff, ← hL.span_eq_top]
        exact Submodule.span_mono (le_sup_right : L ≤ L' ⊔ L)⟩
    exact lattice_of_smul hL' hsup (sup_le_sup Submodule.smul_le_right Submodule.smul_le_right) hs0 hA
  · obtain ⟨t, htP, htQ⟩ := exists_mem_notMem hQ.symm
    have ht : t ^ k ∈ P.asIdeal ^ k := Ideal.pow_mem_pow htP k
    have ht' : t ^ k ∉ Q.asIdeal := fun h => htQ (Q.isPrime.mem_of_pow_mem k h)
    refine ⟨t ^ k, ht', t ^ k, ht', fun x hx => ?_, fun x hx => Submodule.mem_sup_right (Submodule.smul_mem_smul ht hx)⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine L.add_mem ?_ (L.smul_mem _ (Submodule.smul_le_right hz))
    refine Submodule.smul_induction_on hy (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul]; exact h2 _ ht r hr u hu
    · rw [smul_add]; exact L.add_mem hu hv

theorem exists_selfDual_prescribed (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
    (N M : Submodule (𝓞 E) (Sp E n)) (Q : HeightOneSpectrum (𝓞 E)) (hQ : conjPrime₂ Q ≠ Q) (hN : Submodule.IsLattice E N)
    (hu : IsUnimodular (hStd E n) N) (hM : Submodule.IsLattice E M) :
    ∃ N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N' ∧ IsUnimodular (hStd E n) N' ∧
      localization₂ Q.asIdeal N' = localization₂ Q.asIdeal M ∧
      ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q → Q' ≠ conjPrime₂ Q → localization₂ Q'.asIdeal N' = localization₂ Q'.asIdeal N := by
  obtain ⟨L, hL, hLQ, hLo⟩ := exists_glue hN hM Q
  obtain ⟨N', hN', hc, ho⟩ := exists_glue hL (dual_lattice hM) (conjPrime₂ Q)
  have h1 : SameAt Q M N' := sameAt_trans hLQ (ho Q hQ.symm)
  have h2 : ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q → Q' ≠ conjPrime₂ Q → SameAt Q' N N' :=
    fun Q' a b => sameAt_trans (hLo Q' a) (ho Q' b)
  refine ⟨N', hN', ?_, h1.localization_eq, fun Q' a b => (h2 Q' a b).localization_eq⟩
  refine eq_of_sameAt fun w => ?_
  by_cases hw : w = Q
  · subst hw
    have := sameAt_dual hc
    rw [conjP_conjP, dual_dual hM] at this
    exact sameAt_trans (sameAt_symm this) h1
  by_cases hw' : w = conjPrime₂ Q
  · subst hw'
    exact sameAt_trans (sameAt_symm (sameAt_dual h1)) hc
  have := sameAt_dual (h2 (conjPrime₂ w) (fun h => hw' (by rw [← h, conjP_conjP]))
    (fun h => hw (by rw [← conjP_conjP w, h, conjP_conjP])))
  rw [conjP_conjP, show dual (hStd E n) N = N from hu] at this
  exact sameAt_trans (sameAt_symm this) (h2 w hw hw')

end GlobalTheory.GO.SplitGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusDecompositionUnramifiedPrime
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

open scoped Pointwise

namespace GlobalTheory.UnramifiedFrobenius

theorem exists_frobenius : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ), p.Prime → Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) → ∃ (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 ∧ (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) = p ^ orderOf φ ∧ (∀ g : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, g • x ∈ Q.asIdeal ↔ x ∈ Q.asIdeal) ↔ g ∈ Subgroup.zpowers φ) ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ Q'.asIdeal → ∃ g : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, x ∈ Q'.asIdeal ↔ g • x ∈ Q.asIdeal := by
  intro E _ _ _ p hp hunr
  have : Fact p.Prime := ⟨hp⟩
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).2 hpz
  have hover : ∀ R : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ R.asIdeal →
      R.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := fun R hR =>
    (Ideal.liesOver_span_iff R.isPrime.ne_top hpz).mpr (by simpa using hR)
  obtain ⟨Q, hQ⟩ := GlobalTheory.CyclotomicCompletion.exists_place_above E hp
  have := Q.isPrime
  have hQo := hover Q hQ
  have : Finite (𝓞 E ⧸ Q.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) Q.asIdeal
  have he : Q.asIdeal.ramificationIdx ℤ = 1 := hunr.ramificationIdx_eq_one hQo
  have hin : Nat.card (Q.asIdeal.inertia (E ≃ₐ[ℚ] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (Ideal.span {(p : ℤ)}) Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) Q.asIdeal (E ≃ₐ[ℚ] E), he]
  have hbot : Q.asIdeal.inertia (E ≃ₐ[ℚ] E) = ⊥ := Subgroup.eq_bot_of_card_eq _ hin
  have hstab : MulAction.stabilizer (E ≃ₐ[ℚ] E) Q.asIdeal = Subgroup.zpowers φ := by
    refine le_antisymm (fun σ hσ => ?_) (Subgroup.zpowers_le.2 hφ.mem_stabilizer)
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul p Q.asIdeal φ σ hφ hσ
    have h1 : ρ ∈ Q.asIdeal.inertia (E ≃ₐ[ℚ] E) := hρ
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, one_mul]
    exact Subgroup.npow_mem_zpowers φ k
  refine ⟨Q, φ, hQ, ?_, ?_, ?_, ?_, ?_⟩
  · intro h2
    have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) =
        Ideal.span {((p : ℕ) : 𝓞 E)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) Q.asIdeal
      (by simpa using hp.ne_zero)] at he
    refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · rw [hmap]; exact (Ideal.span_singleton_le_iff_mem _).2 hQ
    · rw [hmap]; exact (Ideal.span_singleton_le_iff_mem _).2 h2
  · intro x
    have h1 := hφ x
    rw [Formalism.TwoAdicCyclotomicDecomposition.odd_card_under p Q.asIdeal] at h1
    exact h1
  · have h1 := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := E ≃ₐ[ℚ] E)
      (Ideal.span {(p : ℤ)}) Q.asIdeal
    rw [hin, one_mul, hstab, Nat.card_zpowers] at h1
    rw [h1, Ideal.pow_inertiaDeg p Q.asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro g
    rw [← hstab]
    exact ⟨Formalism.FrobeniusOrbits.Decomp.mem_stab_of g Q.asIdeal,
      Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab g Q.asIdeal⟩
  · intro Q' hQ'
    have := Q'.isPrime
    have := hover Q' hQ'
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) Q'.asIdeal
      Q.asIdeal (E ≃ₐ[ℚ] E)
    refine ⟨g, fun x => ?_⟩
    rw [← hg]
    exact Ideal.smul_mem_pointwise_smul_iff.symm

end GlobalTheory.UnramifiedFrobenius
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisIndexTwoCmConjugation
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem exists_algEquiv_comp_of_normal_rat {E K : Type} [Field E] [Field K] [CharZero E] [CharZero K]
    [Normal ℚ E] (φ ψ : E →+* K) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ψ x = φ (g x) := by
  letI : Algebra E K := φ.toAlgebra
  haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  refine ⟨AlgHom.restrictNormal' ψ.toRatAlgHom E, fun x => ?_⟩
  have := AlgHom.restrictNormal_commutes ψ.toRatAlgHom E x
  exact this.symm

theorem cmType_equiv_fixingSubgroup : ∀ (X : Formalism.L2.Col.Fields), X.Core → IsGalois ℚ X.E → ∃ (τ₀ : X.Tau) (H : Subgroup (X.E ≃ₐ[ℚ] X.E)) (γ : H ≃ X.Tau) (c : X.E ≃ₐ[ℚ] X.E), H.index = 2 ∧ (∀ g ∈ H, ∀ x ∈ X.Kq, g x = x) ∧ (∀ (h : H) (x : X.E), X.emb (γ h) x = X.emb τ₀ (h.1 x)) ∧ (∀ x, c x = star x) ∧ c ∉ H := by
  intro X hX hG
  classical
  have hpos : 0 < Fintype.card X.Tau := by
    rw [hX.card_Tau]; exact Module.finrank_pos
  obtain ⟨τ₀⟩ := Fintype.card_pos_iff.1 hpos
  let L : IntermediateField ℚ X.E := X.Kq.toIntermediateField (fun q => by
    intro τ τ'
    simp)
  have hL : Module.finrank ℚ L = 2 := hX.quad
  let H : Subgroup (X.E ≃ₐ[ℚ] X.E) := L.fixingSubgroup
  have hH : ∀ g, g ∈ H ↔ ∀ x ∈ X.Kq, g x = x := fun g => IntermediateField.mem_fixingSubgroup_iff L g
  have hidx : H.index = 2 := by
    rw [← hL]; exact (IntermediateField.finrank_eq_fixingSubgroup_index X.E L).symm
  have hcardG : Nat.card (X.E ≃ₐ[ℚ] X.E) = Fintype.card X.Tau * 2 := by
    rw [IsGalois.card_aut_eq_finrank, hX.card_Tau, ← hX.rankE, Module.finrank_mul_finrank]
  have hcardH : Nat.card X.Tau = Nat.card H := by
    have := H.card_mul_index
    rw [hidx, hcardG] at this
    rw [Nat.card_eq_fintype_card]
    omega
  choose g hg using fun τ => exists_algEquiv_comp_of_normal_rat (X.emb τ₀) (X.emb τ)
  have hgH : ∀ τ, g τ ∈ H := fun τ => (hH _).2 fun x hx => by
    apply (X.emb τ₀).injective
    rw [← hg]
    exact hx τ τ₀
  let δ : X.Tau → H := fun τ => ⟨g τ, hgH τ⟩
  have hδ : Function.Injective δ := by
    intro τ τ' h
    have h' : g τ = g τ' := congrArg Subtype.val h
    apply hX.emb_inj
    ext x
    rw [hg, hg τ', h']
  have hbij : Function.Bijective δ :=
    (Nat.bijective_iff_injective_and_card δ).2 ⟨hδ, hcardH⟩
  let e : X.Tau ≃ H := Equiv.ofBijective δ hbij
  have hγ : ∀ (h : H) (x : X.E), X.emb (e.symm h) x = X.emb τ₀ (h.1 x) := by
    intro h x
    have : g (e.symm h) = h.1 := congrArg Subtype.val (e.apply_symm_apply h)
    rw [hg, this]
  let c : X.E ≃ₐ[ℚ] X.E := AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut X.E)) (fun q => by simp)
  have hc : ∀ x, c x = star x := fun x => rfl
  refine ⟨τ₀, H, e.symm, c, hidx, fun g hg => (hH g).1 hg, hγ, hc, fun hcH => ?_⟩
  apply hX.emb_ne (e.symm ⟨c, hcH⟩) τ₀
  ext x
  rw [hγ]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapDiagUniformizerElementarySublatticeStatement
section
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glMap_diagUniformizer_elementarySublattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (S : Finset (Fin n)) (d : GL (Fin n) (w.adicCompletion E)), (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i => if i ∈ S then ϖ else 1) → haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) := by
  first | exact @GlobalTheory.DiagElem.glMap_diag_mem_subElem | exact GlobalTheory.DiagElem.glMap_diag_mem_subElem | (intros; apply GlobalTheory.DiagElem.glMap_diag_mem_subElem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapStandardLatticeEqIffMemGLintAdicStatement
section
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)), glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 = (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔ g ∈ GLint (Fin n) (Ov E w) := by
  first | exact @GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint | exact GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint | (intros; apply GlobalTheory.LatHecke.glMap_std_eq_iff_mem_GLint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpWindowOfJumpSets
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

open Formalism.MainNotions.AdmissibleParameterJ in

theorem JJ_finite_ncard {D : D7} (L : SizeData₂ D) (hb : AdmissibleParameterJ.CloudCentreDistance L) (hn : 0 < D.R.nV) (up : Bool) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (ρ : D.what₂.Tau) : (JJ D up j ρ).Finite ∧ (JJ D up j ρ).ncard = D.R.nV := by
  have hc : (Jp D j ρ).ncard = D.R.nV := (hb j h1 h2 ρ).2.2.2.2.2
  have hf : (Jp D j ρ).Finite := Set.finite_of_ncard_pos (by omega)
  cases up with
  | true => simpa [JJ] using And.intro hf hc
  | false =>
    have hinj : Function.Injective (AdmissibleParameterJ.refl D) := by
      intro a b hab
      simp only [AdmissibleParameterJ.refl] at hab
      linarith
    have hEq : Jm D j ρ = AdmissibleParameterJ.refl D '' Jp D j ρ := by
      ext q
      simp only [Jm, reflS, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro h
        exact ⟨_, h, by simp [AdmissibleParameterJ.refl]⟩
      · rintro ⟨u, hu, rfl⟩
        have : AdmissibleParameterJ.refl D (AdmissibleParameterJ.refl D u) = u := by simp [AdmissibleParameterJ.refl]
        rwa [this]
    simp only [JJ, Bool.false_eq_true, if_false]
    rw [hEq]
    exact ⟨hf.image _, by rw [Set.ncard_image_of_injective _ hinj, hc]⟩

theorem jumpWindow_of_jumpSets : ∀ (D : D7) (large₂ : SizeData₂ D), AdmissibleParameterJ.JumpConditions large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ ∧ ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ π : D.nd.X i, GlobalTheory.BlockWindow.JumpWindow D i r π ⌊2 * large₂.sc.b⌋₊ := by
  classical
  intro D large₂ hJ hP
  obtain ⟨⟨ep, hA⟩, hb, -, -, he, -, -⟩ := hJ
  have hn : 0 < D.R.nV := by
    have := D.R.rank_add_five_le
    unfold Ranks.nV; omega
  have hS := large₂.Sc_pos
  have hη := large₂.etaSz_pos
  have hP' : large₂.Sc + large₂.etaSz + (D.R.t : ℝ) + 2 ≤ large₂.sc.b := hP
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨Nat.le_floor (by linarith), ?_⟩
  intro i r hr π w hw CL h τ
  obtain ⟨g, ρ, -, hx, -⟩ := hA i r hr w hw ⟨CL, h⟩ τ
  have hj := D.nd.j_range i
  obtain ⟨hfin, hcard⟩ := JJ_finite_ncard large₂ hb hn (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) hj.1 hj.2 ρ
  have hpre : ((fun a : ℤ => (a : ℚ)) ⁻¹' AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ).Finite :=
    hfin.preimage (Int.cast_injective.injOn)
  refine ⟨hpre.toFinset, ?_, ?_, ?_⟩
  · rw [← hcard, ← Set.ncard_eq_toFinset_card _ hpre,
      ← Set.ncard_image_of_injective _ (Int.cast_injective (α := ℚ))]
    exact Set.ncard_le_ncard (Set.image_preimage_subset _ _) hfin
  · intro u hu
    have hu' : (u : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := by
      simpa using hu
    have hbd := he.1 _ hj.1 hj.2 ρ _ _ hu'
    have hc0 : ((AdmissibleParameterJ.c0 D : ℚ) : ℝ) = ((D.R.t : ℝ) - 1) / 2 := by
      simp [AdmissibleParameterJ.c0]
    rw [hc0] at hbd
    have habs : ((u.natAbs : ℕ) : ℝ) = |((u : ℚ) : ℝ)| := by
      simp [Nat.cast_natAbs]
    have hle : u.natAbs + 1 ≤ ⌊2 * large₂.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      rw [habs]
      linarith
    omega
  · intro a ha
    have : (a : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := (hx π a).1.1 ha
    simpa using this

end GlobalTheory.BlockWindow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThickStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrime_nonthick_letter_no_three_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 3 ≤ H.Lw → φ.1.2 = -1 → ¬ (φ = R.cc ∧ Thick H τ) → NoThree (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) ∧ ∃ i : ZMod (orderOf φ), ¬ Thick H (letter τ φ i) := by
  first | exact @GlobalTheory.HTW.InertWord.inert_nothree_nonthick | exact GlobalTheory.HTW.InertWord.inert_nothree_nonthick | (intros; apply GlobalTheory.HTW.InertWord.inert_nothree_nonthick <;> assumption)
end


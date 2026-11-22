import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
import Lemmata.GeneralBFactRightRest.Imports

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRDivisorDegreeSubSum
section
open Polynomial UniqueFactorizationMonoid

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsSubSum)

theorem exists_le_map_eq {α β : Type*} [DecidableEq β] (f : α → β) (t : Multiset α) :
    ∀ s : Multiset β, s ≤ t.map f → ∃ u ≤ t, u.map f = s := by
  first | exact Bl.general_b_fact_right_rest.goal1 .. | (apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β | exact @Bl.general_b_fact_right_rest.goal1 α

theorem divisor_degree_subsum : DivisorDegreeSubSum := by
  classical
  intro K _ f a hf
  have hdeg : ∀ t : Multiset K[X], t ≤ normalizedFactors f →
      t.prod.natDegree = (t.map natDegree).sum := by
    intro t ht
    apply natDegree_multiset_prod
    intro h0
    exact zero_notMem_normalizedFactors f (Multiset.mem_of_le ht h0)
  constructor
  · rintro ⟨h, hdvd, rfl⟩
    have hh : h ≠ 0 := fun h0 => hf (by rw [h0] at hdvd; exact zero_dvd_iff.mp hdvd)
    have hle : normalizedFactors h ≤ normalizedFactors f :=
      (dvd_iff_normalizedFactors_le_normalizedFactors hh hf).mp hdvd
    refine ⟨(normalizedFactors h).map natDegree, Multiset.map_le_map hle, ?_⟩
    rw [← hdeg _ hle]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hh))
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, hu, rfl⟩ := exists_le_map_eq natDegree _ s hs
    refine ⟨u.prod, ?_, hdeg u hu⟩
    exact (Multiset.prod_dvd_prod_of_le hu).trans (prod_normalizedFactors hf).dvd

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRFrobOrbitIrred
section
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsOrbit)

theorem frobenius_orbit_irreducible : FrobOrbitIrred := by
  unfold FrobOrbitIrred IsOrbit
  intro K L _ _ _ _ _ f hm hirr
  classical
  have hf0 : f ≠ 0 := hm.ne_zero
  have hfL : f.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hf0
  have hmem : ∀ z : L, z ∈ (f.aroots L).toFinset ↔ aeval z f = 0 := by
    intro z
    rw [Multiset.mem_toFinset, mem_aroots]
    exact ⟨fun h => h.2, fun h => ⟨hf0, h⟩⟩
  have hfrob : ∀ z : L, aeval (z ^ Fintype.card K) f = (aeval z f) ^ Fintype.card K := by
    intro z
    rw [← expand_aeval, FiniteField.expand_card, map_pow]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [hmem] at hx ⊢
    show aeval (x ^ Fintype.card K) f = 0
    rw [hfrob, hx, zero_pow Fintype.card_ne_zero]
  · intro x hx y hy
    rw [hmem] at hx hy
    let E : IntermediateField K L := IntermediateField.adjoin K (f.rootSet L)
    have hxE : x ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hx)
    have hyE : y ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hy)
    haveI hSF : IsSplittingField K E f :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    haveI : Normal K E := Normal.of_isSplittingField f
    haveI : FiniteDimensional K E := IsSplittingField.finiteDimensional E f
    haveI : Finite E := Module.finite_of_finite K
    haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    have hmx : minpoly K x = f := (minpoly.eq_of_irreducible_of_monic hirr hx hm).symm
    have hmy : minpoly K y = f := (minpoly.eq_of_irreducible_of_monic hirr hy hm).symm
    have hxy : minpoly K (⟨y, hyE⟩ : E) = minpoly K (⟨x, hxE⟩ : E) := by
      rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
      show minpoly K y = minpoly K x
      rw [hmx, hmy]
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit E).1 hxy
    obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K E).2 σ
    have key : ∀ (m : ℕ) (w : E), (((FiniteField.frobeniusAlgEquivOfAlgebraic K E ^ m) w : E) : L) =
        (fun z : L => z ^ Fintype.card K)^[m] (w : L) := by
      intro m
      induction m with
      | zero => intro w; rfl
      | succ m ih =>
        intro w
        rw [pow_succ, AlgEquiv.mul_apply, ih, Function.iterate_succ_apply]
        congr 1
        all_goals (try rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic])
        all_goals (try simp)
    simp only at hσ
    have h2 : ((σ ⟨x, hxE⟩ : E) : L) = y := by
      rw [← AlgEquiv.smul_def, hσ]
    simp only at hn
    rw [← hn, key] at h2
    exact ⟨_, h2⟩
  · have hsep : f.Separable := by
      first
      | exact PerfectField.separable_of_irreducible hirr
      | (haveI : PerfectField K := PerfectField.ofFinite
         exact PerfectField.separable_of_irreducible hirr)
    rw [Multiset.toFinset_card_of_nodup (nodup_roots (hsep.map (f := algebraMap K L)))]
    show Multiset.card (f.map (algebraMap K L)).roots = f.natDegree
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRGoodDualStable
section
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section
variable {K : Type} [Field K]

theorem rev_natDegree {h : K[X]} (h0 : h.coeff 0 ≠ 0) : h.reverse.natDegree = h.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr h0), Nat.sub_zero]

theorem rev_rev {h : K[X]} (h0 : h.coeff 0 ≠ 0) : h.reverse.reverse = h := by
  ext n
  rw [coeff_reverse, coeff_reverse, rev_natDegree h0, revAt_invol]

variable {L : Type} [Field L] [Algebra K L]

end

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper
section
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

variable {K : Type} [Field K] {N : ℕ}

theorem monicOf_degree_lt (c : Fin N → K) :
    (∑ i : Fin N, C (c i) * X ^ (i : ℕ)).degree < (N : WithBot ℕ) := degree_sum_fin_lt c

theorem monicOf_monic (c : Fin N → K) : (monicOf c).Monic := by
  rw [monicOf]
  exact monic_X_pow_add (monicOf_degree_lt c)

theorem monicOf_natDegree (c : Fin N → K) : (monicOf c).natDegree = N := by
  rw [monicOf, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact monicOf_degree_lt c

theorem monicOf_coeff (c : Fin N → K) (i : Fin N) : (monicOf c).coeff i = c i := by
  rw [monicOf, coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt), zero_add,
    finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h).symm
  · simp

theorem monicOf_injective : Function.Injective (monicOf : (Fin N → K) → K[X]) := by
  intro c d h
  funext i
  rw [← monicOf_coeff c i, ← monicOf_coeff d i, h]

theorem monicOf_coeffs {p : K[X]} (hp : p.Monic) (hN : p.natDegree = N) :
    monicOf (fun i : Fin N => p.coeff i) = p := by
  subst hN
  rw [monicOf, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
  exact hp.as_sum.symm

theorem irreducible_count_upper : IrredCountUpper := by
  intro K _ _ d hd
  classical
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hd0 : d ≠ 0 := by omega
  have hdvd : ∀ f : K[X], Irreducible f → f.natDegree = d → f ∣ X ^ (Fintype.card K ^ d) - X := by
    intro f hf hfd
    haveI := Fact.mk hf
    haveI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
    haveI : Finite (AdjoinRoot f) := Module.finite_of_finite K
    letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
    have hcard : Fintype.card (AdjoinRoot f) = Fintype.card K ^ d := by
      rw [Module.card_fintype (AdjoinRoot.powerBasis hf.ne_zero).basis, Fintype.card_fin,
        AdjoinRoot.powerBasis_dim, hfd]
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard, FiniteField.pow_card,
      sub_self]
  have main : ∀ S : Finset (Fin d → K), (∀ c ∈ S, Irreducible (monicOf c)) →
      d * S.card ≤ Fintype.card K ^ d := by
    intro S hS
    have hcop : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → IsCoprime (monicOf c) (monicOf c') := by
      intro c hc c' hc' hne
      rw [(hS c hc).coprime_iff_not_dvd]
      intro hdv
      apply hne
      apply monicOf_injective
      exact eq_of_monic_of_associated (monicOf_monic c) (monicOf_monic c')
        ((hS c hc).associated_of_dvd (hS c' hc') hdv)
    have hprod : ∏ c ∈ S, monicOf c ∣ X ^ (Fintype.card K ^ d) - X :=
      Finset.prod_dvd_of_coprime (fun c hc c' hc' hne => hcop c hc c' hc' hne)
        (fun c hc => hdvd _ (hS c hc) (monicOf_natDegree c))
    have hdeg : (∏ c ∈ S, monicOf c).natDegree = d * S.card := by
      rw [natDegree_prod_of_monic _ _ (fun c _ => monicOf_monic c),
        Finset.sum_congr rfl (fun c _ => monicOf_natDegree c), Finset.sum_const, smul_eq_mul, mul_comm]
    have hle := natDegree_le_of_dvd hprod (FiniteField.X_pow_card_pow_sub_X_ne_zero K hd0 hq1)
    rw [hdeg, FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hd0 hq1] at hle
    exact hle
  exact main _ (fun c hc => (Finset.mem_filter.mp hc).2)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRJoints
section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem cycleProbSum_of_cycleProbPrime : CycleProbPrime → CycleProbSum := by
  unfold CycleProbPrime CycleProbSum
  intro h N
  classical
  have hdisj : ∀ p ∈ (range (N + 1)).filter (fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N),
      ∀ q ∈ (range (N + 1)).filter (fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N), p ≠ q →
      Disjoint (univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.cycleType)
        (univ.filter fun σ : Equiv.Perm (Fin N) => q ∈ σ.cycleType) := by
    intro p hp q hq hpq
    simp only [mem_filter, mem_range] at hp hq
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    have hq' : q ∈ σ.cycleType.erase p := (Multiset.mem_erase_of_ne hpq.symm).2 h2
    have hsum : σ.cycleType.sum ≤ N := by
      rw [Equiv.Perm.sum_cycleType]
      exact (Finset.card_le_univ _).trans (by simp)
    have hsplit : σ.cycleType.sum = p + (σ.cycleType.erase p).sum := by
      conv_lhs => rw [← Multiset.cons_erase h1]
      rw [Multiset.sum_cons]
    have hle : q ≤ (σ.cycleType.erase p).sum := Multiset.le_sum_of_mem hq'
    omega
  have hset : (univ.filter fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.cycleType, Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N) =
      ((range (N + 1)).filter fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N).biUnion
        (fun p => univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.cycleType) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
    constructor
    · rintro ⟨p, hp, hpr, h2, h3⟩
      exact ⟨p, ⟨by omega, hpr, h2, h3⟩, hp⟩
    · rintro ⟨p, ⟨-, hpr, h2, h3⟩, hp⟩
      exact ⟨p, hp, hpr, h2, h3⟩
  rw [hset, Finset.card_biUnion hdisj, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [mem_filter, mem_range] at hp
  obtain ⟨hpN, hpr, h2, h3⟩ := hp
  have hk := h N p hpr (by omega) h2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpr.ne_zero
  rw [eq_div_iff hp0, ← hk]
  push_cast
  ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRLemmaLWeight
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem torus_bounds (g : ℕ) (hg : 2 ≤ g) (d : Multiset ℕ) : (∀ x ∈ d, 1 ≤ x) →
    0 < (d.map (fun x => (g : ℝ) ^ x - 1)).prod ∧
    (d.map (fun x => (g : ℝ) ^ x - 1)).prod ≤ (g : ℝ) ^ d.sum ∧
    (g : ℝ) ^ d.sum * (1 - (d.card : ℝ) / g) ≤ (d.map (fun x => (g : ℝ) ^ x - 1)).prod := by
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  induction d using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self a s)
    have hga : (g : ℝ) ≤ (g : ℝ) ^ a :=
      calc (g : ℝ) = (g : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (g : ℝ) ^ a := pow_le_pow_right₀ (by linarith) ha
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons,
      pow_add]
    have hG : 0 < (g : ℝ) ^ s.sum := pow_pos (by linarith) _
    generalize (s.map (fun x => (g : ℝ) ^ x - 1)).prod = T at h1 h2 h3 ⊢
    generalize (g : ℝ) ^ s.sum = G at h2 h3 hG ⊢
    generalize (g : ℝ) ^ a = A at hga ⊢
    have hc : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
    push_cast
    generalize (s.card : ℝ) = c at h3 hc ⊢
    refine ⟨mul_pos (by linarith) h1, ?_, ?_⟩
    · calc (A - 1) * T ≤ A * T := by nlinarith [h1]
        _ ≤ A * G := mul_le_mul_of_nonneg_left h2 (by linarith)
    · have hg0 : (g : ℝ) ≠ 0 := by linarith
      have e1 : (A - 1) * (G * (1 - c / g)) - A * G * (1 - (c + 1) / g)
          = G * ((A - g + c) / g) := by
        field_simp; ring
      have e2 : 0 ≤ G * ((A - g + c) / g) :=
        mul_nonneg hG.le (div_nonneg (by linarith) (by linarith))
      calc A * G * (1 - (c + 1) / g) ≤ (A - 1) * (G * (1 - c / g)) := by linarith
        _ ≤ (A - 1) * T := mul_le_mul_of_nonneg_left h3 (by linarith)

theorem lemma_L_weight_holds : LemmaLWeight := by
  intro d g k n hd hg hk hkN hlow hup
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  obtain ⟨hT0, hT1, hT2⟩ := torus_bounds g hg d hd
  set T := (d.map (fun x => (g : ℝ) ^ x - 1)).prod with hTdef
  set N := d.sum with hN
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := pow_pos hg0 k
  have hgN : (0 : ℝ) < (g : ℝ) ^ N := pow_pos hg0 N
  have hk1 : (g : ℝ) ^ k = (g : ℝ) ^ (k - 1) * g := by
    rw [← pow_succ]; congr 1; omega
  constructor
  ·
    have h1 : (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) ≤ n := by
      have : (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) = (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) := by
        rw [hk1]; field_simp
      rw [this]; exact hlow
    have h0 : (0 : ℝ) ≤ 1 - 1 / (g : ℝ) := by
      rw [sub_nonneg, div_le_one hg0]; linarith
    rw [div_le_div_iff₀ hgN (mul_pos hgk hT0)]
    calc (1 - 1 / (g : ℝ)) * ((g : ℝ) ^ k * T) = ((g : ℝ) ^ k * (1 - 1 / (g : ℝ))) * T := by ring
      _ ≤ ((g : ℝ) ^ k * (1 - 1 / (g : ℝ))) * (g : ℝ) ^ N :=
          mul_le_mul_of_nonneg_left hT1 (mul_nonneg hgk.le h0)
      _ ≤ n * (g : ℝ) ^ N := mul_le_mul_of_nonneg_right h1 hgN.le
  · intro h2N
    set t : ℝ := (N : ℝ) / g with ht
    have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hg0.le
    have ht1 : t ≤ 1 / 2 := by
      rw [ht, div_le_iff₀ hg0]
      have : (2 : ℝ) * N ≤ g := by exact_mod_cast h2N
      linarith

    have hsum : ∑ i ∈ Finset.range (k + 1), (N : ℝ) ^ i * (g : ℝ) ^ (k - i)
        = (g : ℝ) ^ k * ∑ i ∈ Finset.range (k + 1), t ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have : (g : ℝ) ^ k = (g : ℝ) ^ (k - i) * (g : ℝ) ^ i := by
        rw [← pow_add]; congr 1; omega
      rw [ht, div_pow, this]
      have hgi : (g : ℝ) ^ i ≠ 0 := (pow_pos hg0 i).ne'
      field_simp
    have hgeom : (∑ i ∈ Finset.range (k + 1), t ^ i) * (1 - t) ≤ 1 := by
      rw [geom_sum_mul_neg]
      have : 0 ≤ t ^ (k + 1) := pow_nonneg ht0 _
      linarith
    have hcard : (d.card : ℝ) ≤ (N : ℝ) := by
      have := Multiset.card_nsmul_le_sum hd
      simp only [smul_eq_mul, mul_one] at this
      exact_mod_cast this
    have hT3 : (g : ℝ) ^ N * (1 - t) ≤ T := by
      refine le_trans ?_ hT2
      apply mul_le_mul_of_nonneg_left _ hgN.le
      have : (d.card : ℝ) / g ≤ t := div_le_div_of_nonneg_right hcard hg0.le
      linarith
    have h1t : (0 : ℝ) < 1 - t := by linarith
    set st := ∑ i ∈ Finset.range (k + 1), t ^ i with hsdef
    have hs0 : 0 ≤ st := Finset.sum_nonneg (fun i _ => pow_nonneg ht0 i)
    have hpoly : 1 ≤ (1 + 6 * t) * (1 - t) ^ 2 := by nlinarith [mul_nonneg ht0 (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * t) (by linarith : (0:ℝ) ≤ 4 - 3 * t))]
    have e6 : 1 + 6 * (N : ℝ) / g = 1 + 6 * t := by rw [ht]; ring
    rw [e6, div_le_div_iff₀ (mul_pos hgk hT0) hgN]
    have hn : n ≤ (g : ℝ) ^ k * st := by rw [← hsum]; exact hup

    have hA : st ≤ (1 + 6 * t) * (1 - t) := by
      have h7 : st * (1 - t) ≤ ((1 + 6 * t) * (1 - t)) * (1 - t) := by
        calc st * (1 - t) ≤ 1 := hgeom
          _ ≤ (1 + 6 * t) * (1 - t) ^ 2 := hpoly
          _ = ((1 + 6 * t) * (1 - t)) * (1 - t) := by ring
      exact le_of_mul_le_mul_right h7 h1t
    calc n * (g : ℝ) ^ N ≤ ((g : ℝ) ^ k * st) * (g : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right hn hgN.le
      _ ≤ ((g : ℝ) ^ k * ((1 + 6 * t) * (1 - t))) * (g : ℝ) ^ N := by
          apply mul_le_mul_of_nonneg_right _ hgN.le
          exact mul_le_mul_of_nonneg_left hA hgk.le
      _ = (1 + 6 * t) * ((g : ℝ) ^ k * ((g : ℝ) ^ N * (1 - t))) := by ring
      _ ≤ (1 + 6 * t) * ((g : ℝ) ^ k * T) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hT3 hgk.le

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartSpec
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem pow_eq_pow_of_modEq_orderOf {M : Type*} [Monoid M] (x : M) {a b : ℕ}
    (h : a ≡ b [MOD orderOf x]) : x ^ a = x ^ b := by
  rw [← pow_mod_orderOf x a, ← pow_mod_orderOf x b, show a % orderOf x = b % orderOf x from h]

theorem gcd_mul_pow_totient {q m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime q m) :
    Nat.gcd (q * m) (q ^ Nat.totient m) = q := by
  have ht : 0 < Nat.totient m := Nat.totient_pos.mpr hm
  obtain ⟨k, hk⟩ : ∃ k, Nat.totient m = k + 1 := ⟨Nat.totient m - 1, by omega⟩
  rw [hk, pow_succ', Nat.gcd_mul_left]
  have : Nat.gcd m (q ^ k) = 1 := (Nat.Coprime.pow_right k hcop.symm)
  rw [this, mul_one]

theorem prime_to_part_spec : PrimeToPartSpec := by
  unfold PrimeToPartSpec
  intro M _ l x hl hx
  set n := orderOf x with hn
  set q := l ^ n.factorization l with hq
  have hnpos : 0 < n := hx.orderOf_pos
  have hqd : q ∣ n := Nat.ordProj_dvd n l
  have hqpos : 0 < q := pow_pos hl.pos _
  have hmpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hnpos hqd) hqpos
  have hcop : Nat.Coprime q (n / q) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hnpos.ne')
  have hnqm : n = q * (n / q) := (Nat.mul_div_cancel' hqd).symm
  unfold primeToPart
  refine ⟨?_, ?_⟩
  · have hg : Nat.gcd n (q ^ Nat.totient (n / q)) = q := by
      have h3 := gcd_mul_pow_totient hmpos hcop
      rwa [← hnqm] at h3
    rw [orderOf_pow' x (pow_pos hqpos _).ne', ← hn, hg]
  · refine ⟨n.factorization l, ?_⟩
    rw [← pow_mul]
    apply pow_eq_pow_of_modEq_orderOf
    rw [← hn]
    have h1 : q ^ Nat.totient (n / q) ≡ 1 [MOD n / q] := Nat.ModEq.pow_totient hcop
    have h2 : q * q ^ Nat.totient (n / q) ≡ q * 1 [MOD q * (n / q)] := Nat.ModEq.mul_left' q h1
    rw [← hnqm, mul_one, mul_comm] at h2
    exact h2.symm

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end


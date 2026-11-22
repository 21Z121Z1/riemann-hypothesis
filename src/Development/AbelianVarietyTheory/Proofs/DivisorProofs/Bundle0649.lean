import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiSh
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem acycF_of_pi_sh : ∀ (R : Type) [CommRing R] (F : Shv R) (ι : Type) [Finite ι] (T : ι → Type)
    [∀ i, CommRing (T i)] (B : Type) [CommRing B], Nonempty (B ≃+* (∀ i, T i)) → (∀ i, SH (T i)) →
    AcycF R (sp B) F := by
  intro R _ F ι _ T _ B _ ⟨e⟩ hT n hn
  obtain ⟨hc⟩ := GlobalTheory.T.spec_pi_cofan_isColimit_of_ringEquiv ι T B e
  have hbij := GlobalTheory.T.etaleSpaceCohomology_coprod_schemes_bijective R F (Spec (CommRingCat.of B)) ι (fun i => Spec (CommRingCat.of (T i)))
    (fun i => Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))) hc n
  have hsub : ∀ i, Subsingleton (H R (sch.obj (Spec (CommRingCat.of (T i)))) F n) :=
    fun i => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf R (T i) (hT i) F n hn
  refine ⟨fun x y => hbij.1 ?_⟩
  funext i
  exact Subsingleton.elim _ _

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddMulLeOfPowLeOfLarge
section
namespace GlobalTheory.VSubArith

theorem sq_le_two_pow_add_one (v : ℕ) : v * v ≤ 2 ^ v + 1 := by
  have key : ∀ k : ℕ, (k + 4) * (k + 4) ≤ 2 ^ (k + 4) ∧ 2 * (k + 4) + 1 ≤ 2 ^ (k + 4) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [show k + 1 + 4 = (k + 4) + 1 by ring, pow_succ]
      constructor <;> nlinarith
  rcases Nat.lt_or_ge v 4 with h | h
  · interval_cases v <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, v = k + 4 := ⟨v - 4, by omega⟩
    exact le_trans (key k).1 (Nat.le_succ _)

theorem two_mul_le_sq_add_sq (v L : ℕ) : 2 * (v * L) ≤ v * v + L * L := by
  have h : (2 * (v * L) : ℤ) ≤ v * v + L * L := by nlinarith [sq_nonneg ((v : ℤ) - L)]
  exact_mod_cast h

theorem add_mul_le_of_pow_le : ∀ (p L m : ℕ), 2 ≤ p → ∃ M0 : ℕ, ∀ n v : ℕ, M0 ≤ n → p ^ v ≤ n → (v + m) * L ≤ n := by
  intro p L m hp
  refine ⟨L * L + 2 * m * L + 1, ?_⟩
  intro n v hn hpv
  have h2 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp v
  have hsq := sq_le_two_pow_add_one v
  have hag := two_mul_le_sq_add_sq v L
  have hx : 2 * ((v + m) * L) ≤ n + n := by nlinarith
  linarith

end GlobalTheory.VSubArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneousStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_formal_group_coboundary_homogeneous : ∀ (R : Type) [CommRing R] (d N : ℕ), (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ (cob1 (addLaw R d) f) = 0) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≠ N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≠ N → coeff γ (cob2 (addLaw R d) c) = 0) ∧ (∀ (c : MvPowerSeries (Fin d ⊕ Fin d) R) (γ : Fin d ⊕ Fin d →₀ ℕ), coeff γ (swap c) = coeff (γ.mapDomain Sum.swap) c) ∧ ∀ (f : MvPowerSeries (Fin d) R) (β : Fin d →₀ ℕ) (i : Fin d), β ≠ 0 → coeff (β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) (cob1 (addLaw R d) f) = ((β i + 1 : ℕ) : R) * coeff (β + Finsupp.single i 1) f := by
  first | exact @GlobalTheory.homog_cob_addLaw | exact GlobalTheory.homog_cob_addLaw | (intros; apply GlobalTheory.homog_cob_addLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTwoCocycleCoeffRelationsOnePair
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.CocRel

variable {R : Type} [CommRing R] {d : ℕ} {τ : Type}

abbrev ex3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single (0 : Fin 3) a + Finsupp.single 1 b + Finsupp.single 2 c

theorem threeVariableMonomialExponent_eq_iff (a b c a' b' c' : ℕ) : ex3 a b c = ex3 a' b' c' ↔ a' = a ∧ b' = b ∧ c' = c := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    have h2 := DFunLike.congr_fun h 2
    simp at h0 h1 h2
    exact ⟨h0.symm, h1.symm, h2.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem coeff_mono3 (a b c i j l : ℕ) (r : ℕ) :
    coeff (R := R) (ex3 i j l) (X 0 ^ a * X 1 ^ b * X 2 ^ c * (r : MvPowerSeries (Fin 3) R)) =
      if a = i ∧ b = j ∧ c = l then (r : R) else 0 := by
  rw [← map_natCast (C : R →+* MvPowerSeries (Fin 3) R), coeff_mul_C, X_pow_eq, X_pow_eq, X_pow_eq,
    monomial_mul_monomial, monomial_mul_monomial, coeff_monomial]
  have := threeVariableMonomialExponent_eq_iff i j l a b c
  by_cases h : a = i ∧ b = j ∧ c = l
  · rw [if_pos (this.2 h), if_pos h]; simp
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h, zero_mul]

theorem coeff_left (p q i j l : ℕ) :
    coeff (ex3 i j l) ((X 0 + X 1) ^ p * X 2 ^ q : MvPowerSeries (Fin 3) R) =
      if p = i + j ∧ q = l then (p.choose i : R) else 0 := by
  rw [add_pow, Finset.sum_mul, map_sum]
  simp only [mul_right_comm _ (_ : MvPowerSeries (Fin 3) R) (X 2 ^ q)]
  have h : ∀ k, coeff (R := R) (ex3 i j l) (X 0 ^ k * X 2 ^ q * X 1 ^ (p - k) * ((p.choose k : ℕ) :
      MvPowerSeries (Fin 3) R)) = if k = i ∧ p - k = j ∧ q = l then (p.choose k : R) else 0 := by
    intro k
    rw [← coeff_mono3, mul_right_comm (X 0 ^ k)]
  simp only [h]
  rw [Finset.sum_eq_single i]
  · by_cases hp : i ≤ p
    · exact if_congr (by omega) rfl rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · intro k _ hk
    exact if_neg fun h' => hk h'.1
  · intro hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]; simp

theorem coeff_right (p q i j l : ℕ) :
    coeff (ex3 i j l) (X 0 ^ p * (X 1 + X 2) ^ q : MvPowerSeries (Fin 3) R) =
      if p = i ∧ q = j + l then (q.choose j : R) else 0 := by
  rw [add_pow, Finset.mul_sum, map_sum]
  simp only [← mul_assoc, coeff_mono3]
  rw [Finset.sum_eq_single j]
  · by_cases hp : j ≤ q
    · exact if_congr (by omega) rfl rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · intro k _ hk
    exact if_neg fun h' => hk h'.2.1
  · intro hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]; simp

theorem coeff_yz (p q i j l : ℕ) :
    coeff (ex3 i j l) (X 1 ^ p * X 2 ^ q : MvPowerSeries (Fin 3) R) =
      if 0 = i ∧ p = j ∧ q = l then 1 else 0 := by
  simpa using coeff_mono3 (R := R) 0 p q i j l 1

theorem coeff_xy (p q i j l : ℕ) :
    coeff (ex3 i j l) (X 0 ^ p * X 1 ^ q : MvPowerSeries (Fin 3) R) =
      if p = i ∧ q = j ∧ 0 = l then 1 else 0 := by
  simpa using coeff_mono3 (R := R) p q 0 i j l 1

theorem coeff_powerSeriesEvalTwoGroups_piSingle (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d)
    {A B : MvPowerSeries τ R} (hA : constantCoeff A = 0) (hB : constantCoeff B = 0)
    (e : τ →₀ ℕ) (p q : ℕ) (h : ∀ p' q', ¬ (p' = p ∧ q' = q) → coeff e (A ^ p' * B ^ q') = 0) :
    coeff e (at2 c (Pi.single m A) (Pi.single m B)) =
      coeff (Finsupp.single (Sum.inl m) p + Finsupp.single (Sum.inr m) q) c *
        coeff e (A ^ p * B ^ q) := by
  have h0 : ∀ {A : MvPowerSeries τ R}, constantCoeff A = 0 → ∀ i,
      constantCoeff ((Pi.single m A : Fin d → MvPowerSeries τ R) i) = 0 := by
    intro A hA i
    by_cases hi : i = m
    · subst hi; simpa using hA
    · simp [hi]
  have hs := SubstCalc.hasSubst_elim (h0 hA) (h0 hB)
  have hprod : ∀ p' q', (Finsupp.single (Sum.inl m) p' + Finsupp.single (Sum.inr m) q' :
      Fin d ⊕ Fin d →₀ ℕ).prod (fun s k => (Sum.elim (Pi.single m A) (Pi.single m B) s :
        MvPowerSeries τ R) ^ k) = A ^ p' * B ^ q' := by
    intro p' q'
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (by exact pow_zero _),
      Finsupp.prod_single_index (by exact pow_zero _)]
    simp
  unfold at2
  rw [coeff_subst hs,
    finsum_eq_single _ (Finsupp.single (Sum.inl m) p + Finsupp.single (Sum.inr m) q), hprod,
    smul_eq_mul]
  intro δ hδ
  by_cases hc : δ = Finsupp.single (Sum.inl m) (δ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (δ (Sum.inr m))
  · rw [congrArg (fun δ' : Fin d ⊕ Fin d →₀ ℕ => δ'.prod _) hc, hprod, h, smul_zero]
    rintro ⟨h1, h2⟩
    rw [h1, h2] at hc
    exact hδ hc
  · obtain ⟨s, hs'⟩ : ∃ s, δ s ≠ (Finsupp.single (Sum.inl m) (δ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (δ (Sum.inr m)) : Fin d ⊕ Fin d →₀ ℕ) s := by
      by_contra hh
      exact hc (Finsupp.ext fun s => by_contra fun h' => hh ⟨s, h'⟩)
    have key : δ s ≠ 0 ∧ (Sum.elim (Pi.single m A) (Pi.single m B) s : MvPowerSeries τ R) = 0 := by
      rcases s with t | t <;> by_cases ht : t = m
      · subst ht; simp at hs'
      · simpa [ht, Finsupp.single_apply, Ne.symm ht] using hs'
      · subst ht; simp at hs'
      · simpa [ht, Finsupp.single_apply, Ne.symm ht] using hs'
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 key.1)
      (by rw [key.2, zero_pow key.1]), map_zero, smul_zero]

theorem cocycle_at (c : MvPowerSeries (Fin d ⊕ Fin d) R) (hc : cob2 (addLaw R d) c = 0)
    {u v t : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (ht : ∀ i, constantCoeff (t i) = 0) :
    at2 c v t - at2 c (u + v) t + at2 c u (v + t) - at2 c u v = 0 := by
  set w : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v t) with hw
  have hw0 : ∀ s, constantCoeff (w s) = 0 := fun s => by
    rcases s with s | s | s <;> simp [hw, hu, hv, ht]
  have hsw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
  have h1 : ∀ i, subst w (x1 (R := R) (d := d) i) = u i := fun i => by
    unfold x1; rw [subst_X hsw]; rfl
  have h2 : ∀ i, subst w (x2 (R := R) (d := d) i) = v i := fun i => by
    unfold x2; rw [subst_X hsw]; rfl
  have h3 : ∀ i, subst w (x3 (R := R) (d := d) i) = t i := fun i => by
    unfold x3; rw [subst_X hsw]; rfl
  have hx0 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx20 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx30 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      op (addLaw R d) a b = a + b := by
    intro a b ha hb
    funext i
    unfold op addLaw at2
    have := SubstCalc.hasSubst_elim ha hb
    rw [subst_add this, subst_X this, subst_X this]
    rfl
  have hop0 : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      ∀ i, constantCoeff ((a + b) i) = 0 := by
    intro a b ha hb i; simp [ha, hb]
  have key := congrArg (subst w) hc
  unfold cob2 at key
  rw [hop _ _ hx0 hx20, hop _ _ hx20 hx30] at key
  rw [subst_sub hsw, subst_add hsw, subst_sub hsw,
    SubstCalc.subst_powerSeriesEvalTwoGroups hx20 hx30 hw0, SubstCalc.subst_powerSeriesEvalTwoGroups (hop0 _ _ hx0 hx20) hx30 hw0,
    SubstCalc.subst_powerSeriesEvalTwoGroups hx0 (hop0 _ _ hx20 hx30) hw0, SubstCalc.subst_powerSeriesEvalTwoGroups hx0 hx20 hw0] at key
  have e : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (fun i => subst w ((a + b) i)) = (fun i => subst w (a i)) + (fun i => subst w (b i)) := by
    intro a b; funext i; simp only [Pi.add_apply]; exact subst_add hsw _ _
  rw [e, e] at key
  simp only [h1, h2, h3] at key
  have e0 : subst w (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := by
    simpa using (subst_sub hsw (0 : MvPowerSeries _ R) 0)
  rw [e0] at key
  convert key using 2

theorem relations : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), cob2 (addLaw R d) c = 0 → ∀ m : Fin d, (∀ n, 0 < n → coeff (Finsupp.single (Sum.inl m) n) c = 0) ∧ ∀ i j l, 0 < i → 0 < j → 0 < l → coeff (Finsupp.single (Sum.inl m) (i + j) + Finsupp.single (Sum.inr m) l) c * ((i + j).choose i : R) = coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (j + l)) c * ((j + l).choose j : R) := by
  intro R _ d c hc m
  have h0 : ∀ (k : Fin 3) i,
      constantCoeff ((Pi.single m (X k) : Fin d → MvPowerSeries (Fin 3) R) i) = 0 := by
    intro k i
    by_cases hi : i = m
    · subst hi; simp
    · simp [hi]
  have hid := cocycle_at c hc (h0 0) (h0 1) (h0 2)
  rw [← Pi.single_add, ← Pi.single_add] at hid
  have key : ∀ i j l : ℕ, 0 < i →
      - coeff (Finsupp.single (Sum.inl m) (i + j) + Finsupp.single (Sum.inr m) l) c *
        ((i + j).choose i : R) +
      coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (j + l)) c *
        ((j + l).choose j : R) -
      coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) j) c *
        (if 0 = l then 1 else 0) = 0 := by
    intro i j l hi
    have h := congrArg (coeff (ex3 i j l)) hid
    rw [map_sub, map_add, map_sub, map_zero,
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ j l
        (fun p q hpq => by rw [coeff_yz, if_neg (by omega)]),
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ (i + j) l
        (fun p q hpq => by rw [coeff_left, if_neg hpq]),
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ i (j + l)
        (fun p q hpq => by rw [coeff_right, if_neg hpq]),
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ i j
        (fun p q hpq => by rw [coeff_xy, if_neg (by omega)]),
      coeff_yz, coeff_left, coeff_right, coeff_xy, if_neg (by omega), if_pos ⟨rfl, rfl⟩,
      if_pos ⟨rfl, rfl⟩] at h
    simp only [true_and] at h
    linear_combination h
  refine ⟨fun n hn => ?_, fun i j l hi _ hl => ?_⟩
  · simpa using key n 0 0 hn
  · have h := key i j l hi
    rw [if_neg (by omega)] at h
    linear_combination -h

end GlobalTheory.Katz.CocRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrobeniusSemilinearEquationExistsUnique
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WSolve

theorem nilp_mod_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)], v.Integers O → ∀ x : O, ¬IsUnit x → IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : O)}) x) := by
  intro p _ C _ _ v O _ _ hp hv x hx
  have hx1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) (fun h => hx (hv.isUnit_iff_valuation_eq_one.2 h))
  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast]
    exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hp0 hx1
  refine ⟨k, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hv.dvd_iff_le, map_pow, map_pow]
  exact hk.le

theorem semilin_nil : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := GlobalTheory.T.frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent

theorem perf_solve : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := GlobalTheory.T.perfection_existsUnique_sub_matrix_frobenius_eq

theorem witt_solve : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)), (∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) → ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := GlobalTheory.T.wittVector_existsUnique_sub_matrix_frobenius_eq

theorem iter_map {T T' : Type} [CommRing T] [CommRing T'] {ι : Type} [Fintype ι] (f : T →+* T')
    (σ : T →+* T) (σ' : T' →+* T') (hf : ∀ x, f (σ x) = σ' (f x)) (M : Matrix ι ι T) (k : ℕ)
    (w : ι → T) :
    (fun u : ι → T' => (M.map f).mulVec fun j => σ' (u j))^[k] (fun j => f (w j)) =
      fun i => f ((fun u : ι → T => M.mulVec fun j => σ (u j))^[k] w i) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    funext i
    simp only [← hf]
    exact (RingHom.map_mulVec f M _ i).symm

theorem coeff_nil {S : Type} [CommRing S] {p : ℕ} [Fact p.Prime] [CharP S p] (y : Perfection S p)
    (h : IsNilpotent (Perfection.coeff S p 0 y)) (n : ℕ) : IsNilpotent (Perfection.coeff S p n y) := by
  have e : ∀ n, Perfection.coeff S p n y ^ (p ^ n) = Perfection.coeff S p 0 y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, Perfection.coeff_pow_p', ih]
  exact IsNilpotent.of_pow (m := p ^ n) (by rw [e]; exact h)

theorem key (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Ainf p O)) (N : ℕ)
    (hN : ∀ j i, IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : O)}) (WittVector.fontaineTheta O p
      ((fun w : ι → Ainf p O => M.mulVec fun k => WittVector.frobenius (w k))^[N] (Pi.single j 1) i)))) :
    ∀ c : ι → Ainf p O, ∃! v : ι → Ainf p O, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by
  apply witt_solve p (PreTilt O p) ι M
  apply perf_solve p (ModP O p) ι (M.map WittVector.constantCoeff)
  intro n
  apply semilin_nil p (ModP O p) ι _ N
  intro j i
  have e1 : (Pi.single j 1 : ι → ModP O p) =
      fun k => Perfection.coeff (ModP O p) p n ((Pi.single j 1 : ι → PreTilt O p) k) := by
    funext k; by_cases h : k = j
    · subst h; simp only [Pi.single_eq_same]; exact (map_one _).symm
    · simp only [Pi.single_eq_of_ne h]; exact (map_zero _).symm
  have e2 : (Pi.single j 1 : ι → PreTilt O p) =
      fun k => WittVector.constantCoeff ((Pi.single j 1 : ι → Ainf p O) k) := by
    funext k; by_cases h : k = j
    · subst h; simp
    · simp [h]
  have h1 := congrFun (iter_map (T := PreTilt O p) (Perfection.coeff (ModP O p) p n)
    (frobenius (PreTilt O p) p) (frobenius (ModP O p) p) (fun x => by rw [frobenius_def, frobenius_def]; exact map_pow (Perfection.coeff (ModP O p) p n) x p)
    (M.map WittVector.constantCoeff) N (Pi.single j 1)) i
  have h2 := iter_map WittVector.constantCoeff WittVector.frobenius
    (frobenius (PreTilt O p) p) (fun x => by simp [frobenius_def, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]) M N (Pi.single j 1)
  rw [e1]
  erw [h1]
  rw [e2, h2]
  apply coeff_nil
  have := hN j i
  rw [WittVector.mk_fontaineTheta] at this
  exact this

theorem frobenius_mu_eq (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) =
      (∑ i ∈ Finset.range p, (WittVector.teichmuller p ε) ^ i) * Sandwich.mu ε := by
  have h : WittVector.frobenius (WittVector.teichmuller p ε) = (WittVector.teichmuller p ε) ^ p := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [Sandwich.mu, map_sub, map_one, h, geom_sum_mul]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (M : Matrix ι ι (Ainf p O)), IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) M → (∀ c : ι → Ainf p O, ∃ v : ι → Ainf p O, ∀ i, v i - M.mulVec (fun j => WittVector.frobenius (v j)) i = c i) ∧ ∀ v : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ v i - M.mulVec (fun j => WittVector.frobenius (v j)) i) → ∀ i, Sandwich.mu ε ∣ v i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε ι _ M hM
  classical
  obtain ⟨N, hN⟩ := hM
  have hK := key p O ι M N (fun j i => nilp_mod_p p C v O hv _ (hN _ i))
  refine ⟨fun c => ?_, ?_⟩
  · obtain ⟨x, hx, -⟩ := hK c
    exact ⟨x, fun i => congrFun hx i⟩
  intro w hw
  choose u hu using hw
  have hφμ := frobenius_mu_eq p O ε
  set s : Ainf p O := ∑ i ∈ Finset.range p, (WittVector.teichmuller p ε) ^ i with hs
  have h1 : ε.untilt = 1 := by simpa [zeta] using hε.zeta_zero
  have hθs : WittVector.fontaineTheta O p s = p := by
    simp [hs, map_sum, map_pow, WittVector.fontaineTheta_teichmuller, h1]
  have hK' := key p O ι (s • M) 1 (fun j i => by
    have e : (fun k => WittVector.frobenius ((Pi.single j 1 : ι → Ainf p O) k)) = Pi.single j 1 := by
      funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [Function.iterate_one, e, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.smul_apply, smul_eq_mul, map_mul, hθs]
    rw [← map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))]
    exact IsNilpotent.zero)
  obtain ⟨w', hw', -⟩ := hK' u
  have hz : (w - Sandwich.mu ε • w') - M.mulVec (fun k => WittVector.frobenius ((w - Sandwich.mu ε • w') k)) = 0 := by
    funext i
    have a := hu i
    have b := congrFun hw' i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.smul_apply,
      map_sub, map_mul, hφμ, Pi.zero_apply] at a b ⊢
    have hsum : ∑ x, M i x * (WittVector.frobenius (w x) - s * Sandwich.mu ε * WittVector.frobenius (w' x)) =
        ∑ x, M i x * WittVector.frobenius (w x) - Sandwich.mu ε * ∑ x, s * M i x * WittVector.frobenius (w' x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsum]
    linear_combination a - Sandwich.mu ε * b
  have h0 : (0 : ι → Ainf p O) - M.mulVec (fun k => WittVector.frobenius ((0 : ι → Ainf p O) k)) = 0 := by
    funext i; simp [Matrix.mulVec, dotProduct]
  have := (hK 0).unique hz h0
  intro i
  refine ⟨w' i, ?_⟩
  have := congrFun this i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.WSolve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingToOrderedCechDegreeTwoMemCocyclesTwoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternatingToOrderedCechDegreeTwo_mem_cocyclesTwo : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2), δ F 2 c = 0 → e2 F c ∈ Z2 F := by
  first | exact @GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | exact GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | (intros; apply GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtlasSectionsMulDivNonvanishingIsOpen
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem sections_prod_quot_open : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), (∀ (la mu : La) (a b : ι → Y → ℂ), A.IsSec la a → A.IsSec mu b → A.IsSec (la + mu) (fun i y => a i y * b i y) ∧ ∀ y, A.nsq (la + mu) (fun i y => a i y * b i y) y = A.nsq la a y * A.nsq mu b y) ∧ (∀ (la : La) (a : ι → Y → ℂ), A.IsSec la a → IsOpen (nz A a)) ∧ (∀ (B la : La) (a b : ι → Y → ℂ) (U : Set Y), A.IsSec (B + la) a → A.IsSec B b → (∀ y ∈ U, a (A.pick y) y ≠ 0 ∧ b (A.pick y) y ≠ 0) → A.IsFrameOn la U (fun i y => a i y / b i y)) := by
  intro n Y _ _ _ _ _ ι La _ A
  refine ⟨?_, ?_, ?_⟩
  · intro la mu a b ha hb
    refine ⟨⟨fun i => ?_, fun i j y _ hi hj => ?_⟩, fun y => ?_⟩
    · exact (ha.1 i).mul (hb.1 i)
    · beta_reduce
      rw [A.g_add la mu i j y hi hj, ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj]
      ring
    · simp only [WeightedAtlas.nsq]
      rw [A.ph_add la mu _ y (A.mem_pick y), norm_mul, mul_pow, neg_add, Real.exp_add]
      ring
  · intro la a ha
    have hc : Continuous (A.nsq la a) := bsA_nsq_cont A ha
    have : nz A a = A.nsq la a ⁻¹' {0}ᶜ := by
      ext y
      simp only [nz, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, WeightedAtlas.nsq]
      constructor
      · intro h
        exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr h)) (Real.exp_pos _).ne'
      · intro h h0
        apply h
        simp [h0]
    rw [this]
    exact isOpen_compl_singleton.preimage hc
  · intro B la a b U ha hb hU
    have hbne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → b i y ≠ 0 := by
      intro i y hy hi
      rw [hb.2 i (A.pick y) y trivial hi (A.mem_pick y)]
      exact mul_ne_zero (A.g_ne B i (A.pick y) y hi (A.mem_pick y)) (hU y hy).2
    refine ⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => div_ne_zero (hU y hy).1 (hU y hy).2⟩
    · have hS : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
          (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, trivial⟩
      have h1 : DifferentiableOn ℂ (a i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (ha.1 i).mono hS
      have h2 : DifferentiableOn ℂ (b i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hb.1 i).mono hS
      have h3 := h1.mul (h2.inv (fun v (hv : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U) =>
        hbne i _ hv.2 ((A.chart i).map_target hv.1)))
      refine h3.congr (fun v _ => ?_)
      simp [div_eq_mul_inv]
    · have hgB := A.g_ne B i j y hi hj
      have hbj := hbne j y hy hj
      beta_reduce
      rw [ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj, A.g_add B la i j y hi hj]
      field_simp

end GlobalTheory.OTY
end


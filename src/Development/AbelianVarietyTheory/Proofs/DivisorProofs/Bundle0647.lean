import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0630
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0614
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferential
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_sub_eq_p_mul_of_constantCoeff_eq {x y : WittVector p k}
    (h : WittVector.constantCoeff x = WittVector.constantCoeff y) : ∃ z, x - y = p * z := by
  by_cases hxy : x - y = 0
  · exact ⟨0, by rw [hxy, mul_zero]⟩
  obtain ⟨m, z, hz, hxyz⟩ := WittVector.exists_eq_pow_p_mul (x - y) hxy
  rcases m with _ | m
  · exfalso; apply hz
    have h1 := congrArg WittVector.constantCoeff hxyz
    rw [map_sub, h, sub_self, pow_zero, one_mul] at h1
    exact h1.symm
  · exact ⟨p ^ m * z, by rw [hxyz, pow_succ]; ring⟩

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem prod_sub_prod_divisible_lemma_2 {σ τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k)
    (U V : σ → MvPowerSeries τ (WittVector p k)) (e : σ → ℕ) (S : Finset σ)
    (h : ∀ i ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (U i ^ e i - V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (∏ i ∈ S, U i ^ e i - ∏ i ∈ S, V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i S hi ih =>
    obtain ⟨Y1, hY1⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨Y2, hY2⟩ := h i (Finset.mem_insert_self i S)
    refine ⟨U i ^ e i * Y1 + Y2 * ∏ j ∈ S, V j ^ e j, ?_⟩
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    simp only [Algebra.smul_def, map_sub, map_mul, map_add, map_pow, map_prod] at hY1 hY2 ⊢
    linear_combination
      (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i)) ^ e i * hY1 +
      (∏ j ∈ S, (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V j)) ^ e j) * hY2

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_choose_mul_p_pow_mul_eq_p_mul (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∃ t : WittVector p k, c * ((n.choose j : _root_.GlobalTheory.Katz.Fr p k) * (p : _root_.GlobalTheory.Katz.Fr p k) ^ j) =
      algebraMap (WittVector p k) _ (p * t) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨e, j', hj', hjeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : j ≠ 0) p hp.ne_one
  have hj'0 : j' ≠ 0 := by rintro rfl; simp at hj'
  have hej : e < j := by
    have h1 : p ^ e ≤ j := by rw [hjeq]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj'0)
    exact lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h1
  obtain ⟨q, rfl⟩ : ∃ q, j = q + e + 1 := ⟨j - e - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hunit : IsUnit (j' : WittVector p k) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have h2 : (j' : WittVector p k).coeff 0 = (j' : k) :=
      map_natCast (WittVector.constantCoeff (p := p) (R := k)) j'
    rw [h2]
    exact (CharP.cast_eq_zero_iff k p j').not.2 hj'
  obtain ⟨s, hs⟩ := hunit.exists_right_inv
  refine ⟨m * (n'.choose (q + e) : WittVector p k) * (p : WittVector p k) ^ q * s, ?_⟩
  set ι := algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)
  have hs' : (j' : _root_.GlobalTheory.Katz.Fr p k) * ι s = 1 := by
    rw [← map_natCast ι, ← map_mul, hs, map_one]
  have hjK : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) = (p : _root_.GlobalTheory.Katz.Fr p k) ^ e * j' := by
    rw [hjeq]; push_cast; ring
  have hchoose : ((n' + 1).choose (q + e + 1) : _root_.GlobalTheory.Katz.Fr p k) * ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) =
      ((n' + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) := by
    have := Nat.add_one_mul_choose_eq n' (q + e)
    rw [← Nat.cast_mul, ← Nat.cast_mul, this]
  have hj0 : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) ≠ 0 := by
    rw [hjK]
    have hinj : Function.Injective ι := IsFractionRing.injective _ _
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 (WittVector.p_nonzero p k)
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 hunit.ne_zero
  apply mul_right_cancel₀ hj0
  simp only [map_mul, map_pow, map_natCast]
  linear_combination (c * (p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1)) * hchoose +
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k)) * hc -
    ((p : _root_.GlobalTheory.Katz.Fr p k) * ι m * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) *
      (p : _root_.GlobalTheory.Katz.Fr p k) ^ q * ι s) * hjK -
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) * ι m) * hs'

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_algebraMap_smul' {τ : Type} (a : WittVector p k) (Y : MvPowerSeries τ (WittVector p k)) :
    MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (a • Y) =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a •
        MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  ext β
  simp only [MvPowerSeries.coeff_map, map_smul, smul_eq_mul, map_mul]

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_add_p_mul_pow_sub_pow_eq_p_smul {τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (V H : MvPowerSeries τ (WittVector p k)) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      ((V + (p : MvPowerSeries τ (WittVector p k)) * H) ^ n - V ^ n) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
    mul_one, add_sub_cancel_right, map_sum, Finset.smul_sum]
  have key : ∀ j ∈ Finset.range n, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨t, ht⟩ := exists_choose_mul_p_pow_mul_eq_p_mul c m hc (n - j) (by omega) (by omega)
    rw [Nat.choose_symm (by omega)] at ht
    refine ⟨t • (V ^ j * H ^ (n - j)), ?_⟩
    have e1 : V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k)) =
        ((n.choose j * p ^ (n - j) : ℕ) : WittVector p k) • (V ^ j * H ^ (n - j)) := by
      rw [Algebra.smul_def, map_natCast]; push_cast; ring
    rw [e1, map_algebraMap_smul', map_algebraMap_smul', smul_smul, smul_smul, map_natCast]
    congr 1
    rw [← map_mul, ← ht]; push_cast; ring
  have hsum : ∀ S : Finset ℕ, (∀ j ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) →
      ∃ Y, ∑ j ∈ S, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro S hS
    classical
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j S hj ih =>
      obtain ⟨Y1, hY1⟩ := ih fun i hi => hS i (Finset.mem_insert_of_mem hi)
      obtain ⟨Y2, hY2⟩ := hS j (Finset.mem_insert_self j S)
      exact ⟨Y2 + Y1, by rw [Finset.sum_insert hj, hY1, hY2, map_add, smul_add]⟩
  exact hsum _ key

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in

theorem _root_.GlobalTheory.Katz.subst_sub_subst_mem_intBy : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries (τ) (_root_.GlobalTheory.Katz.Fr p k)) (w : σ → MvPowerSeries τ k) (f : MvPowerSeries (σ) (_root_.GlobalTheory.Katz.Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, _root_.GlobalTheory.Katz.Red p (u i) (w i)) → (∀ i, _root_.GlobalTheory.Katz.Red p (v i) (w i)) → f ∈ _root_.GlobalTheory.Katz.quasiInt p k σ → subst u f - subst v f ∈ _root_.GlobalTheory.Katz.intBy p k τ p := by
  intro p _ k _ _ _ σ τ _ u v w f hu0 hv0 hu hv hf
  classical
  choose a ha using fun i β => hu i β
  choose b hb using fun i β => hv i β
  choose hh hhh using fun i β =>
    exists_sub_eq_p_mul_of_constantCoeff_eq ((ha i β).2.trans (hb i β).2.symm)
  let U : σ → MvPowerSeries τ (WittVector p k) := fun i β => a i β
  let V : σ → MvPowerSeries τ (WittVector p k) := fun i β => b i β
  let Hs : σ → MvPowerSeries τ (WittVector p k) := fun i β => hh i β
  have hUV : ∀ i, U i = V i + (p : MvPowerSeries τ (WittVector p k)) * Hs i := by
    intro i; refine MvPowerSeries.ext fun β => ?_
    have e : (p : MvPowerSeries τ (WittVector p k)) * Hs i = (p : WittVector p k) • Hs i := by
      rw [Algebra.smul_def, map_natCast]
    rw [e, map_add, map_smul, smul_eq_mul]
    show a i β = b i β + p * hh i β
    rw [← hhh]; ring
  have huM : u = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (ha i β).1
  have hvM : v = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (hb i β).1
  have hf' : ∀ (α : σ →₀ ℕ) (i : σ), ∃ m, ((α i : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * MvPowerSeries.coeff α f =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) m := hf
  have hsu := MvPowerSeries.hasSubst_of_constantCoeff_zero hu0
  have hsv := MvPowerSeries.hasSubst_of_constantCoeff_zero hv0
  unfold _root_.GlobalTheory.Katz.intBy
  refine fun β => ?_
  rw [map_sub, MvPowerSeries.coeff_subst hsu, MvPowerSeries.coeff_subst hsv,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hsu f β)
      (MvPowerSeries.coeff_subst_finite hsv f β)]
  refine finsum_induction (fun x => ∃ w, x = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) (p * w))
    ⟨0, by simp⟩ (fun x y ⟨w1, h1⟩ ⟨w2, h2⟩ => ⟨w1 + w2, by rw [h1, h2, mul_add, map_add]⟩) fun α => ?_
  obtain ⟨Y, hY⟩ := prod_sub_prod_divisible_lemma_2 (MvPowerSeries.coeff α f) U V α α.support fun i _ => by
    obtain ⟨mi, hmi⟩ := hf' α i
    rw [hUV i]
    exact map_add_p_mul_pow_sub_pow_eq_p_smul _ mi hmi (V i) (Hs i)
  refine ⟨MvPowerSeries.coeff β Y, ?_⟩
  rw [huM, hvM]
  simp only [Finsupp.prod, ← map_pow, ← map_prod]
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← map_sub, ← smul_eq_mul, ← map_smul, hY,
    map_smul, MvPowerSeries.coeff_map, smul_eq_mul, map_mul]

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticSimilitudeInvertibleModN
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SympModN

theorem omegaStd_nsmul_left {h : ℕ} (N : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    omegaStd (N • a) b = N * omegaStd a b := by
  unfold omegaStd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

theorem omegaStd_single_inr {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inr i) 1) = a (.inl i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_single_inl {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inl i) 1) = -a (.inr i) := by
  simp [omegaStd, Pi.single_apply]

theorem omegaStd_add_nsmul_modEq {h : ℕ} (N : ℕ) (x y b c : Fin h ⊕ Fin h → ℤ) :
    omegaStd (x + N • b) (y + N • c) ≡ omegaStd x y [ZMOD N] := by
  rw [Int.modEq_iff_dvd]
  unfold omegaStd
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  exact ⟨-(b (.inl i) * y (.inr i) + x (.inl i) * c (.inr i) + N * b (.inl i) * c (.inr i)) +
    (b (.inr i) * y (.inl i) + x (.inr i) * c (.inl i) + N * b (.inr i) * c (.inl i)), by ring⟩

theorem exists_eq_nsmul_iff {ι : Type*} (N : ℕ) (hN : N ≠ 0) (a : ι → ℤ) :
    (∃ b, a = N • b) ↔ ∀ j, (N : ℤ) ∣ a j := by
  constructor
  · rintro ⟨b, rfl⟩ j
    simp [nsmul_eq_mul]
  · intro hd
    refine ⟨fun j => a j / N, funext fun j => ?_⟩
    simp [nsmul_eq_mul, Int.mul_ediv_cancel' (hd j)]

theorem symplecticSimilitude_modN : ∀ (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)), N ≠ 0 →
    m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) →
    (∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b) ∧ (∀ a, ∃ a' b, T a' = a + N • b) ∧
    ∃ T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x, ∃ b, T (T' x) = x + N • b) ∧
      ∀ m' : ℕ, m * m' ≡ 1 [MOD N] → ∀ x y, omegaStd (T' x) (T' y) ≡ m' * omegaStd x y [ZMOD N] := by
  intro h N m T hN hm hT
  have h1 : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b := by
    rintro a ⟨b, hb⟩
    have hd : ∀ y, (N : ℤ) ∣ omegaStd a y := by
      intro y
      have e := hT a y
      rw [hb, omegaStd_nsmul_left] at e
      have hdm : (N : ℤ) ∣ (m : ℤ) * omegaStd a y := by
        have h3 := Int.modEq_iff_dvd.1 e
        have h2 : (N : ℤ) ∣ (N : ℤ) * omegaStd b (T y) := dvd_mul_right _ _
        simpa using dvd_add h3 h2
      exact (Nat.isCoprime_iff_coprime.2 hm.symm).dvd_of_dvd_mul_left hdm
    refine (exists_eq_nsmul_iff N hN a).2 fun j => ?_
    rcases j with i | i
    · simpa [omegaStd_single_inr] using hd (Pi.single (.inr i) 1)
    · simpa [omegaStd_single_inl] using hd (Pi.single (.inl i) 1)
  haveI : NeZero N := ⟨hN⟩
  let red : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ZMod N) := fun a j => (a j : ZMod N)
  let lift : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ℤ) := fun v j => ((v j).val : ℤ)
  have hred0 : ∀ a, red a = 0 ↔ ∃ b, a = N • b := by
    intro a
    rw [exists_eq_nsmul_iff N hN a, funext_iff]
    exact forall_congr' fun j => ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hredlift : ∀ v, red (lift v) = v := by
    intro v; funext j; simp [red, lift]
  have hred_sub : ∀ a a', red (a - a') = red a - red a' := by
    intro a a'; funext j; simp [red]
  have finj : Function.Injective fun v => red (T (lift v)) := by
    intro v w hvw
    have e : red (T (lift v - lift w)) = 0 := by
      rw [map_sub, hred_sub]; exact sub_eq_zero.2 hvw
    obtain ⟨b', hb'⟩ := h1 _ ((hred0 _).1 e)
    have e2 : red (lift v - lift w) = 0 := (hred0 _).2 ⟨b', hb'⟩
    rw [hred_sub, hredlift, hredlift] at e2
    exact sub_eq_zero.1 e2
  have fsurj := Finite.injective_iff_surjective.1 finj
  have h2 : ∀ a, ∃ a' b, T a' = a + N • b := by
    intro a
    obtain ⟨v, hv⟩ := fsurj (red a)
    have e : red (T (lift v) - a) = 0 := by
      rw [hred_sub]; exact sub_eq_zero.2 hv
    obtain ⟨b, hb⟩ := (hred0 _).1 e
    exact ⟨lift v, b, by rw [← hb]; abel⟩
  choose v b hvb using fun i : Fin h ⊕ Fin h => h2 (Pi.single i 1)
  let T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) :=
    ∑ i, (LinearMap.proj i : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)
  have hT' : ∀ x, T' x = ∑ i, x i • v i := by
    intro x; simp [T']
  have h3 : ∀ x, T (T' x) = x + N • ∑ i, x i • b i := by
    intro x
    rw [hT', map_sum]
    simp only [map_zsmul, hvb, smul_add, Finset.sum_add_distrib]
    congr 1
    · funext j
      simp [Finset.sum_apply, Pi.single_apply]
    · rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  refine ⟨h1, h2, T', fun x => ⟨_, h3 x⟩, ?_⟩
  intro m' hmm' x y
  have e1 := hT (T' x) (T' y)
  rw [h3, h3] at e1
  have e2 := omegaStd_add_nsmul_modEq N x y (∑ i, x i • b i) (∑ i, y i • b i)
  have e3 : (m : ℤ) * omegaStd (T' x) (T' y) ≡ omegaStd x y [ZMOD N] := e1.symm.trans e2
  have hmm'' : (m : ℤ) * m' ≡ 1 [ZMOD N] := by
    unfold Nat.ModEq at hmm'
    unfold Int.ModEq
    exact_mod_cast hmm'
  calc omegaStd (T' x) (T' y) = 1 * omegaStd (T' x) (T' y) := by ring
    _ ≡ ((m : ℤ) * m') * omegaStd (T' x) (T' y) [ZMOD N] := Int.ModEq.mul_right _ hmm''.symm
    _ = m' * ((m : ℤ) * omegaStd (T' x) (T' y)) := by ring
    _ ≡ m' * omegaStd x y [ZMOD N] := Int.ModEq.mul_left _ e3

end GlobalTheory.SympModN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorSquarePerfectProjection
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem tensorSquare_perfectProjection (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A : Type) [CommRing A] [Algebra k A] (π : A →ₐ[k] A) :
    ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : A ⊗[k] A, IsNilpotent (a - Algebra.TensorProduct.map π π a)) ∧ ∀ a : A ⊗[k] A, ∃ b : A ⊗[k] A, Algebra.TensorProduct.map π π a = Algebra.TensorProduct.map π π b ^ p) := by
  rintro ⟨h1, h2⟩
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpA : ((p : ℕ) : A ⊗[k] A) = 0 := by
    rw [← map_natCast (algebraMap k (A ⊗[k] A)) p, CharP.cast_eq_zero, map_zero]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← mem_nilradical]
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul]
      have e : a ⊗ₜ[k] b - π a ⊗ₜ[k] π b = (a - π a) ⊗ₜ[k] b + π a ⊗ₜ[k] (b - π b) := by
        rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have : (a - π a) ⊗ₜ[k] b = Algebra.TensorProduct.includeLeft (S := k) (B := A) (a - π a) * ((1 : A) ⊗ₜ[k] b) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_right _ _ (mem_nilradical.2 ((h1 a).map _))
      · have : π a ⊗ₜ[k] (b - π b) = ((π a) ⊗ₜ[k] (1 : A)) * Algebra.TensorProduct.includeRight (R := k) (A := A) (b - π b) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_left _ _ (mem_nilradical.2 ((h1 b).map _))
    | add x y hx hy =>
      rw [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ hx hy
  · induction a using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [hp0]⟩
    | tmul a b =>
      obtain ⟨a', ha⟩ := h2 a
      obtain ⟨b', hb⟩ := h2 b
      refine ⟨a' ⊗ₜ[k] b', ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, ha, hb]
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      rw [map_add, map_add, hu, hv, ← frobRing_apply hpA, ← frobRing_apply hpA, ← frobRing_apply hpA, map_add]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundMultiplierSqrtNegDStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bound_multiplier_sqrt_neg_d : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (σ p : ℂ), d.Prime → 4 < d → l ≠ d → Sz l lam 0 (12 * p) → Sz l lam 0 (-2 * (d : ℂ) * σ + ((d : ℂ) + 1) * p) → (l = 3 → d % 3 = 2) → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else 0) σ := by
  first | exact @GlobalTheory.SzMult.main | exact GlobalTheory.SzMult.main | (intros; apply GlobalTheory.SzMult.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundThreeInertStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_bound_three_inert : ∀ [Fact (Nat.Prime 3)] (lam : algebraicClosure ℚ ℂ →+* ℂ_[3]) (d : ℕ) (w σ p : ℂ), d % 3 = 1 → w ^ 2 = -(d : ℂ) → Sz 3 lam 0 (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz 3 lam 0 (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p) → Sz 3 lam 0 σ := by
  first | exact @GlobalTheory.ArithThreeInert.main | exact GlobalTheory.ArithThreeInert.main | (intros; apply GlobalTheory.ArithThreeInert.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VirtualCharacterCosetNormOneSingleStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.virtualCharacter_coset_normOne_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧ ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  first | (exact @GlobalTheory.Shin.virt_coset_norm_one_single) | (exact GlobalTheory.Shin.virt_coset_norm_one_single) | (intros; apply GlobalTheory.Shin.virt_coset_norm_one_single <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTorsionIsModularFamilyStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_torsion_isModularFamily : ∀ (N : ℕ) [NeZero N], IsFam (vact N) 2 (wp N) ∧ IsFam (vact N) 3 (wpd N) := by
  first | exact @GlobalTheory.WpFam.isFam_wp_wpd | exact GlobalTheory.WpFam.isFam_wp_wpd | (intros; apply GlobalTheory.WpFam.isFam_wp_wpd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassTorsionQExpansionIntegralStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassTorsion_qExpansion_integral : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 → QAll (Sz l lam 0) N (wB N x) ∧ QAll (Sz l lam 0) N (wpd N x) := by
  first | exact @GlobalTheory.WpFam.ExpansionIntegral.main | exact GlobalTheory.WpFam.ExpansionIntegral.main | (intros; apply GlobalTheory.WpFam.ExpansionIntegral.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCocycleUniqueness
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_cocycle_uniqueness : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (E : ℕ → Q → Q → kˣ → Prop), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → ∃ c, E n a b c) → (∀ n, 0 < n → ∀ (a b : Q) (c c' : kˣ), E n a b c → E n a b c' → c = c') → (∀ n m, 0 < n → 0 < m → ∀ (a b : Q) (c : kˣ), a ^ (n * m) = 1 → b ^ (n * m) = 1 → E (n * m) a b c → E n (a ^ m) (b ^ m) (c ^ m)) → ∀ (I : TateIsoO D k Q act E) (ζ : ℕ → kˣ) (ev : ℕ → D.La → Q), (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r, (∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) → (∀ r x, ev (r + 1) x ^ p = ev r x) → (∀ r x y, E (p ^ r) (ev r x) (ev r y) (ζ r ^ (2 * D.EF x y))) → ∃ J : GTateIso D.toG k Q act E, ∀ n, 0 < n → n.Coprime p → ∀ y : D.La, J.ev n y = I.ev n y := by
  first | (exact @GlobalTheory.TateGlue.exists_gTateIso) | (exact GlobalTheory.TateGlue.exists_gTateIso) | (intros; apply GlobalTheory.TateGlue.exists_gTateIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleFreeFiniteOfReduction
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem wittModule_free_finite_of_reduction : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (M V : Type) [AddCommGroup M] [Module (WittVector p k) M] [AddCommGroup V] [Module k V] [Module.Finite k V] (r : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V), IsHausdorff (Ideal.span {(p : WittVector p k)}) M → (∀ m : M, (p : WittVector p k) • m = 0 → m = 0) → Function.Surjective r → (∀ m, r m = 0 → ∃ n, m = p • n) → Module.Free (WittVector p k) M ∧ Module.Finite (WittVector p k) M := by
  intro p _ k _ _ _ M V _ _ _ _ _ r hH htf hr hker
  classical
  let I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  have hpow : ∀ (j : ℕ) (m : M), ((p : WittVector p k) ^ j) • m = 0 → m = 0 := by
    intro j
    induction j with
    | zero => intro m h; simpa using h
    | succ j ih =>
      intro m h
      rw [pow_succ, mul_smul] at h
      exact htf m (ih _ h)
  haveI : Module.IsTorsionFree (WittVector p k) M :=
    Module.IsTorsionFree.of_smul_eq_zero fun a m h => by
      by_cases ha : a = 0
      · exact Or.inl ha
      right
      obtain ⟨j, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
      rw [mul_smul] at h
      have h1 := hpow j _ h
      rw [← Units.smul_def] at h1
      exact (smul_eq_zero_iff_eq u).mp h1
  haveI : IsHausdorff I M := hH
  let b := Module.finBasis k V
  choose m hm using fun i => hr (b i)
  let F : (Fin (Module.finrank k V) → WittVector p k) →ₗ[WittVector p k] M :=
    Fintype.linearCombination (WittVector p k) m
  haveI : IsPrecomplete I (Fin (Module.finrank k V) → WittVector p k) :=
    GlobalTheory.isPrecomplete_pi I _
  have hs : Function.Surjective F := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨fun i => WittVector.teichmuller p (b.repr (r x) i), ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h0 : r (F (fun i => WittVector.teichmuller p (b.repr (r x) i)) - x) = 0 := by
      rw [map_sub, Fintype.linearCombination_apply, map_sum]
      simp only [map_smulₛₗ, hm, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      rw [sub_eq_zero]
      exact b.sum_repr (r x)
    obtain ⟨y, hy⟩ := hker _ h0
    rw [hy]
    have : ((p : WittVector p k)) • y ∈ (I • ⊤ : Submodule (WittVector p k) M) :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    simpa [Nat.cast_smul_eq_nsmul] using this
  haveI : Module.Finite (WittVector p k) M := Module.Finite.of_surjective F hs
  exact ⟨Module.free_of_finite_type_torsion_free', inferInstance⟩

end GlobalTheory
end


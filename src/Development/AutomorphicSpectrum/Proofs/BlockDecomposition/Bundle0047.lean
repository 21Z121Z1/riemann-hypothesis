import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0016
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0022

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointEqTranslate
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.CoverStep

variable {A : Type} [CommRing A] {a r t : ℕ}

private theorem yc_sub_mul_mul_mul_eq (e : A)
    (P : GlobalTheory.CompanionTheory.NullFr.Fx A a r → GlobalTheory.CompanionTheory.NullFr.Fx A r a)
    (z : GlobalTheory.CompanionTheory.NullFr.Fx A a r × GlobalTheory.CompanionTheory.NullFr.Fx A a t) (hP : P z.1 * z.1 = e • 1)
    (Y₀ : GlobalTheory.CompanionTheory.NullFr.Fx A r t) (hY₀ : e • Y₀ = Y₀) (S D : GlobalTheory.CompanionTheory.NullFr.Fx A t t) :
    GlobalTheory.CompanionTheory.NullFr.yc P (z.1, (z.2 - z.1 * Y₀) * S * D) =
      (GlobalTheory.CompanionTheory.NullFr.yc P z - Y₀) * S * D := by
  simp only [GlobalTheory.CompanionTheory.NullFr.yc]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc, hP,
    Matrix.smul_mul, Matrix.one_mul, hY₀]

private theorem vc_sub_mul_mul_mul_eq (e : A)
    (P : GlobalTheory.CompanionTheory.NullFr.Fx A a r → GlobalTheory.CompanionTheory.NullFr.Fx A r a)
    (z : GlobalTheory.CompanionTheory.NullFr.Fx A a r × GlobalTheory.CompanionTheory.NullFr.Fx A a t) (hP : P z.1 * z.1 = e • 1)
    (Y₀ : GlobalTheory.CompanionTheory.NullFr.Fx A r t) (hY₀ : e • Y₀ = Y₀) (S D : GlobalTheory.CompanionTheory.NullFr.Fx A t t) :
    GlobalTheory.CompanionTheory.NullFr.vc P (z.1, (z.2 - z.1 * Y₀) * S * D) = GlobalTheory.CompanionTheory.NullFr.vc P z * S * D := by
  simp only [GlobalTheory.CompanionTheory.NullFr.vc]
  rw [yc_sub_mul_mul_mul_eq e P z hP Y₀ hY₀ S D, ← Matrix.mul_assoc z.1,
    ← Matrix.mul_assoc z.1, ← Matrix.sub_mul, ← Matrix.sub_mul, Matrix.mul_sub z.1,
    sub_sub_sub_cancel_right]

theorem mul_gU_apply' {m : ℕ} (M : Fx A m t) (i : Fin t) (d : Fin t → A) (p : Fin m) (j : Fin t) :
    (M * gU i d) p j = M p j + if j = i then ∑ k, d k * M p k else 0 := by
  rw [GlobalTheory.CompanionTheory.NullFr.gU, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases h : j = i
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.of_apply, if_pos h, mul_comm]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.of_apply, if_neg h, mul_zero]

theorem mul_gD_apply' {m : ℕ} (M : Fx A m t) (i : Fin t) (u : A) (p : Fin m) (j : Fin t) :
    (M * gD i u) p j = if j = i then u * M p i else M p j := by
  rw [GlobalTheory.CompanionTheory.NullFr.gD, Matrix.mul_diagonal]
  by_cases h : j = i
  · subst h
    simp [mul_comm]
  · simp [h, Function.update_apply]

theorem mul_gU_gD_apply {m : ℕ} (M : Fx A m t) (i : Fin t) (c : Fin t → A) (u' : A) (p : Fin m)
    (j : Fin t) :
    (M * gU i (-c) * gD i u') p j =
      if j = i then u' * (M p i - ∑ k, c k * M p k) else M p j := by
  rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gD_apply', GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply', GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply']
  by_cases h : j = i
  · rw [if_pos h, if_pos h, if_pos rfl]
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp only [if_neg h, add_zero]

theorem gU_neg_mul (i : Fin t) (c : Fin t → A) (hc : c i = 0) : gU i (-c) * gU i c = 1 := by
  refine Matrix.ext fun p j => ?_
  rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply']
  by_cases h : j = i
  · subst h
    simp [GlobalTheory.CompanionTheory.NullFr.gU, Matrix.one_apply, mul_add, Finset.sum_add_distrib, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', hc]
  · simp [GlobalTheory.CompanionTheory.NullFr.gU, h]

theorem gD_mul (i : Fin t) (u' u : A) (h : u' * u = 1) : gD i u' * gD i u = 1 := by
  refine Matrix.ext fun p q => ?_
  rw [GlobalTheory.CompanionTheory.NullFr.gD, GlobalTheory.CompanionTheory.NullFr.gD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi
      simp [h]
    · simp [Function.update_apply, hpi]
  · simp [hpq]

end GlobalTheory.CompanionTheory.NullFr.CoverStep

namespace GlobalTheory.CompanionTheory.NullFr.CoverStep

theorem point_eq_translate : ∀ {A : Type} [CommRing A] {a r t : ℕ} (e f : A) (_ : e * e = e) (_ : f * e = f) (_ : f * f = f) (P : Fx A a r → Fx A r a)
    (i : Fin t) (C : Set A) (z : Fx A a r × Fx A a t) (_ : z ∈ admitted e P) (_ : ∀ p q, z.1 p q ∈ C)
    (_ : ∀ l k, f * yc P z l k ∈ C ∧ (1 - f) * yc P z l k ∈ C)
    (_ : ∀ p k, k ≠ i → vc P z p k ∈ C) (_ : ∀ p, (1 - f) * vc P z p i ∈ C)
    (c : Fin t → A) (_ : c i = 0) (_ : ∀ k, f * c k = c k) (_ : ∀ p, f * vc P z p i = ∑ k, c k * vc P z p k)
    (u : Aˣ) (_ : (1 - f) * (u : A) = 1 - f)
    (c₀ c₁ : Fin t → A) (_ : c₀ i = 0) (_ : ∀ k, f * c₀ k = c₀ k) (_ : c₁ i = 0)
    (_ : ∀ k, f * c₁ k = c₁ k ∧ c₁ k ∈ C) (_ : ∀ k, c k = c₀ k + u * c₁ k)
    (y₀ y₁ : Fin r → A) (_ : ∀ l, f * y₀ l = y₀ l) (_ : ∀ l, f * y₁ l = y₁ l ∧ y₁ l ∈ C)
    (_ : ∀ l, f * yc P z l i - ∑ k, c₀ k * yc P z l k = y₀ l + u * y₁ l),
    ∃ w ∈ Piece e f P i C, z = (w.1, w.2 * gD i (u : A) * gU i c₀ + w.1 * yU i y₀) := by
  intro A _ a r t e f he hfe hff P i C z hz hz1 hY hKo hKi c hci hfc hfK u hu c₀ c₁ hc₀i hfc₀
    hc₁i hc₁ hc y₀ y₁ hfy₀ hy₁ hy
  simp only [GlobalTheory.CompanionTheory.NullFr.admitted, Set.mem_setOf_eq] at hz
  obtain ⟨hez1, hez2, hP⟩ := hz
  have hey₀ : ∀ l, e * y₀ l = y₀ l := fun l => by
    rw [← hfy₀ l, ← mul_assoc, mul_comm e f, hfe]
  have hY₀ : e • GlobalTheory.CompanionTheory.NullFr.yU i y₀ = GlobalTheory.CompanionTheory.NullFr.yU i y₀ := by
    refine Matrix.ext fun l j => ?_
    simp only [GlobalTheory.CompanionTheory.NullFr.yU, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · exact hey₀ l
    · exact mul_zero e
  have hY₀i : ∀ l, GlobalTheory.CompanionTheory.NullFr.yU i y₀ l i = y₀ l := fun l => by
    simp [GlobalTheory.CompanionTheory.NullFr.yU]
  have hu' : (1 - f) * ((u⁻¹ : Aˣ) : A) = 1 - f := by
    conv_lhs => rw [← hu]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have h1fc₀ : ∀ k, (1 - f) * c₀ k = 0 := fun k => by
    rw [sub_mul, one_mul, hfc₀, sub_self]
  have h1fy₀ : ∀ l, (1 - f) * y₀ l = 0 := fun l => by
    rw [sub_mul, one_mul, hfy₀, sub_self]
  have hsum : ∀ l, ∑ k, c₀ k * (GlobalTheory.CompanionTheory.NullFr.yc P z - GlobalTheory.CompanionTheory.NullFr.yU i y₀) l k =
      ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k := by
    intro l
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = i
    · simp [hk, hc₀i]
    · simp [GlobalTheory.CompanionTheory.NullFr.yU, hk]
  have key : ∀ l, f * (GlobalTheory.CompanionTheory.NullFr.yc P z l i - y₀ l - ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k) =
      (u : A) * y₁ l := by
    intro l
    rw [mul_sub, mul_sub, hfy₀, Finset.mul_sum]
    simp_rw [← mul_assoc, hfc₀]
    rw [sub_right_comm, hy l, add_sub_cancel_left]
  have key2 : ∀ l, (1 - f) * (GlobalTheory.CompanionTheory.NullFr.yc P z l i - y₀ l -
      ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k) = (1 - f) * GlobalTheory.CompanionTheory.NullFr.yc P z l i := by
    intro l
    rw [mul_sub, mul_sub, h1fy₀, Finset.mul_sum]
    simp_rw [← mul_assoc, h1fc₀, zero_mul, Finset.sum_const_zero, sub_zero]
  have hD : GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A) * GlobalTheory.CompanionTheory.NullFr.gD i (u : A) = 1 :=
    GlobalTheory.CompanionTheory.NullFr.CoverStep.gD_mul i _ _ u.inv_mul
  have hS : GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) * GlobalTheory.CompanionTheory.NullFr.gU i c₀ = 1 :=
    GlobalTheory.CompanionTheory.NullFr.CoverStep.gU_neg_mul i c₀ hc₀i
  have hco := yc_sub_mul_mul_mul_eq e P z hP _ hY₀ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀))
    (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A))
  have hcm := vc_sub_mul_mul_mul_eq e P z hP _ hY₀ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀))
    (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A))
  refine ⟨(z.1, (z.2 - z.1 * GlobalTheory.CompanionTheory.NullFr.yU i y₀) * GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) *
    GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)), ?_, ?_⟩
  · simp only [GlobalTheory.CompanionTheory.NullFr.Piece, GlobalTheory.CompanionTheory.NullFr.admitted, Set.mem_setOf_eq]
    rw [hco, hcm]
    refine ⟨⟨hez1, ?_, hP⟩, hz1, ?_, ?_, ?_, c₁, hc₁i, hc₁, ?_⟩
    · rw [← Matrix.smul_mul, ← Matrix.smul_mul, smul_sub, ← Matrix.smul_mul, hez2, hez1]
    · intro l k
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply]
      by_cases hk : k = i
      · rw [if_pos hk, hsum l, Matrix.sub_apply, hY₀i l]
        refine ⟨?_, ?_⟩
        · rw [mul_left_comm, key l, ← mul_assoc, Units.inv_mul, one_mul]
          exact (hy₁ l).2
        · rw [← mul_assoc, hu', key2 l]
          exact (hY l i).2
      · have hE : (GlobalTheory.CompanionTheory.NullFr.yc P z - GlobalTheory.CompanionTheory.NullFr.yU i y₀) l k =
            GlobalTheory.CompanionTheory.NullFr.yc P z l k := by
          simp [GlobalTheory.CompanionTheory.NullFr.yU, hk]
        rw [if_neg hk, hE]
        exact hY l k
    · intro p k hk
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_neg hk]
      exact hKo p k hk
    · intro p
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_pos rfl, ← mul_assoc, hu', mul_sub,
        Finset.mul_sum]
      simp_rw [← mul_assoc, h1fc₀, zero_mul, Finset.sum_const_zero, sub_zero]
      exact hKi p
    · intro p
      have hR : ∑ k, c₁ k * (GlobalTheory.CompanionTheory.NullFr.vc P z * GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) *
          GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)) p k = ∑ k, c₁ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply]
        by_cases hk : k = i
        · simp [hk, hc₁i]
        · rw [if_neg hk]
      have hL : f * (GlobalTheory.CompanionTheory.NullFr.vc P z p i - ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k) =
          (u : A) * ∑ k, c₁ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k := by
        rw [mul_sub, hfK p, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, hfc₀, ← sub_mul, hc k, add_sub_cancel_left, mul_assoc]
      rw [hR, GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_pos rfl, mul_left_comm, hL,
        ← mul_assoc, Units.inv_mul, one_mul]
  · refine Prod.ext rfl ?_
    dsimp only
    rw [Matrix.mul_assoc _ (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)) (GlobalTheory.CompanionTheory.NullFr.gD i (u : A)),
      hD, Matrix.mul_one, Matrix.mul_assoc _ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀)) (GlobalTheory.CompanionTheory.NullFr.gU i c₀), hS,
      Matrix.mul_one, sub_add_cancel]

end GlobalTheory.CompanionTheory.NullFr.CoverStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialRootsOfClosedQuotient
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.RootsUpToUnits

theorem subsingleton_of_mul_eq_one {S : Type} [CommRing S] {ϖ c : S}
    (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (h : ϖ * c = 1) : Subsingleton S := by
  have hu := (Ideal.mem_jacobson_bot.mp hJ) (-c)
  rw [mul_neg, h, neg_add_cancel] at hu
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

theorem normal_form {S : Type} [CommRing S] (ϖ : S) (h : ∀ f : S, ϖ ∣ f ∨ f ∣ ϖ) (f : S) (M : ℕ) :
    ϖ ^ M ∣ f ∨ ∃ (j : ℕ) (f' : S), f = ϖ ^ j * f' ∧ f' ∣ ϖ := by
  induction M generalizing f with
  | zero => left; simp
  | succ M ih =>
    rcases h f with ⟨g, rfl⟩ | hf
    · rcases ih g with hg | ⟨j, f', rfl, hf'⟩
      · left; rw [pow_succ']; exact mul_dvd_mul_left ϖ hg
      · right; exact ⟨j + 1, f', by ring, hf'⟩
    · right; exact ⟨0, f, by simp, hf⟩

theorem root_of_dvd {S : Type} [CommRing S] {ϖ g : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hA : Aic (S ⧸ Ideal.span {ϖ ^ 2})) (hg : g ∣ ϖ) {i : ℕ} (hi : 0 < i) :
    ∃ (r : S) (u : Sˣ), g = u * r ^ i := by
  obtain ⟨h, hh⟩ := hg
  by_cases hn : Nontrivial (S ⧸ Ideal.span {ϖ ^ 2})
  · haveI := hn
    obtain ⟨x, hx⟩ := hA (Polynomial.X ^ i - Polynomial.C (Ideal.Quotient.mk _ g))
      (Polynomial.monic_X_pow_sub_C _ hi.ne') (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hi)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) r) ^ i - Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) g = 0 := by
      simpa using hx
    have hmem : r ^ i - g ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      exact hx'
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    have hu := (Ideal.mem_jacobson_bot.mp hJ) (t * h)
    have key : r ^ i = g * (ϖ * (t * h) + 1) := by
      have e1 : r ^ i = g + t * ϖ ^ 2 := by rw [ht]; ring
      rw [e1, hh]; ring
    refine ⟨r, hu.unit⁻¹, ?_⟩
    rw [key]
    calc g = ((↑hu.unit⁻¹ : S) * (ϖ * (t * h) + 1)) * g := by rw [hu.val_inv_mul, one_mul]
      _ = (↑hu.unit⁻¹ : S) * (g * (ϖ * (t * h) + 1)) := by ring
  · have hs : Subsingleton (S ⧸ Ideal.span {ϖ ^ 2}) := not_nontrivial_iff_subsingleton.mp hn
    have h1 : (1 : S) ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := ϖ * a) hJ (by rw [← ha]; ring)
    exact ⟨1, 1, Subsingleton.elim _ _⟩

theorem roots_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S ⧸ Ideal.span {ϖ ^ 2}) → Roots ϖ := by
  intro S _ ϖ hJ hϖ hD hA f N i hf hi
  have hdich : ∀ g : S, ϖ ∣ g ∨ g ∣ ϖ := fun g =>
    hD g ϖ ⟨1, by rw [pow_one]; exact Ideal.subset_span (by simp)⟩
  rcases normal_form ϖ hdich f (N + 1) with hM | ⟨j, f', rfl, hf'⟩
  · obtain ⟨k, hk⟩ := dvd_trans hM hf
    have e0 : (1 - ϖ * k) * ϖ ^ N = 0 := by linear_combination hk
    have e1 : 1 - ϖ * k = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hϖ N)).mp e0
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := k) hJ (by linear_combination -e1)
    exact ⟨1, 1, Subsingleton.elim _ _⟩
  · obtain ⟨r0, u0, h0⟩ := root_of_dvd hJ hA (dvd_refl ϖ) hi
    obtain ⟨r, u, hr⟩ := root_of_dvd hJ hA hf' hi
    refine ⟨r0 ^ j * r, u0 ^ j * u, ?_⟩
    rw [hr, h0]; push_cast; ring

end GlobalTheory.CompanionTheory.RootsUpToUnits
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdPairSumsEqSumPowersetScore
section
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem prod_pairs_add_eq_sum_score {n : ℕ} (z : Fin n → ℂ) :
    ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, ∏ a, z a ^ score T a := by
  have h1 : ∀ (S : Finset (Fin n × Fin n)) (f : Fin n × Fin n → Fin n),
      ∏ p ∈ S, z (f p) = ∏ a, z a ^ (S.filter fun p => f p = a).card := by
    intro S f
    rw [← Finset.prod_fiberwise_of_maps_to (g := f) (t := univ) (fun _ _ => mem_univ _)]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2]), prod_const]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [h1 T Prod.fst, h1 (prs n \ T) Prod.snd, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  have : score T a = (((T.filter fun p => p.1 = a).card + ((prs n \ T).filter fun p => p.2 = a).card : ℕ) : ℤ) := by
    simp [score]
  rw [this, zpow_natCast, pow_add]

end GlobalTheory.CompanionTheory.CoefId
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSubsetSumVanishesStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_subset_sum_vanishes : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (r : ℕ) (m : Multiset ℂ) (A B : R[X]), 0 < r → A.Monic → B.Monic → A.natDegree = r →
  A * B = (m.map fun x => X + C (algebraMap ℂ R x)).prod →
  ((m.powersetCard r).map fun S => A.coeff (r - 1) - algebraMap ℂ R S.sum).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | exact GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex | (intros; apply GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBoxVolumeBound
section
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox

theorem pi_smul_const_family {P : Type} [Fintype P] {X : P → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : P → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  haveI : ∀ i, SigmaFinite (c i • μ i) := fun i => inferInstance
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib, ENNReal.coe_finset_prod]

theorem map_pi_smul {P : Type} [Fintype P] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] (r : P → ℝ) (hr : ∀ w, 0 < r w) :
    (volume : Measure (P → E)).map (fun x w => r w • x w) =
      ENNReal.ofReal (∏ w, (r w ^ Module.finrank ℝ E)⁻¹) • (volume : Measure (P → E)) := by
  have hc : ∀ w, (volume : Measure E).map (fun y => r w • y) =
      Real.toNNReal ((r w ^ Module.finrank ℝ E)⁻¹) • (volume : Measure E) := fun w => by
    rw [Measure.map_addHaar_smul _ (hr w).ne', abs_of_pos (inv_pos.mpr (pow_pos (hr w) _))]
    ext s _
    rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]
  haveI : ∀ w, SigmaFinite ((volume : Measure E).map (fun y => r w • y)) := fun w => by
    rw [hc w]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : P => (volume : Measure E))
    (f := fun w (y : E) => r w • y)
    (fun w => (continuous_id.const_smul (r w)).measurable.aemeasurable)
  beta_reduce at hmap
  rw [volume_pi, hmap]
  simp only [hc]
  rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.pi_smul_const_family, ← Real.toNNReal_prod_of_nonneg
    (fun w _ => (inv_pos.mpr (pow_pos (hr w) (Module.finrank ℝ E))).le)]
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]

variable {P ι : Type}

theorem continuous_qR0 [Fintype ι] (A : P → Matrix ι ι ℝ) : Continuous (qR0 A) := by
  unfold GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0
  exact continuous_pi fun w => continuous_const.mul
    ((continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w)))

theorem continuous_gaussR [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) :
    Continuous (gaussR Pm) := by
  unfold gaussR
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ =>
    Continuous.dotProduct (continuous_apply w)
      (Continuous.matrix_mulVec continuous_const (continuous_apply w))))

theorem boxR_one_eq [Fintype P] [Fintype ι] :
    boxR (fun _ : P => (1 : ℝ)) = Metric.closedBall (0 : P → ι → ℝ) 1 := by
  ext x
  simp only [boxR, Set.mem_setOf_eq, mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).symm

theorem unit_box_bound [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ)
    (hDi : Continuous Di)
    (hD : ∀ U : Set (P → ℝ), MeasurableSet U →
      ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) :
    ∃ C : ℝ≥0, ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR (fun _ => (1 : ℝ))) ≤
        (C : ℝ≥0∞) * volume U := by
  have hBc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)) := by
    rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]; exact isCompact_closedBall _ _
  have hBm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)) :=
    hBc.isClosed.measurableSet
  have hBne : (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)).Nonempty := by
    rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq]; exact ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P := P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A
  have hKc : IsCompact (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A '' (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) :=
    hBc.image hQc
  obtain ⟨x₀, -, hx₀⟩ := hBc.exists_isMinOn hBne (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_gaussR Pm).continuousOn
  obtain ⟨D, hD'⟩ := hKc.exists_bound_of_continuousOn hDi.continuousOn
  have hm : 0 < GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀ := Real.exp_pos _
  refine ⟨Real.toNNReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D), fun U hU => ?_⟩
  change _ ≤ ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * _
  have hS : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := (hQc.measurable hU).inter hBm
  have hK : MeasurableSet (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := hU.inter hKc.isClosed.measurableSet
  have h1 : ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ))
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) ≤
      ENNReal.ofReal D * volume U := by
    calc ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) * (volume : Measure (P → ι → ℝ))
          (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))
        = ∫⁻ _ in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x) :=
          setLIntegral_mono' hS fun x hx => ENNReal.ofReal_le_ofReal (isMinOn_iff.mp hx₀ x hx.2)
      _ ≤ ∫⁻ x in GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))),
            ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x) :=
          lintegral_mono_set fun x hx => ⟨hx.1, x, hx.2, rfl⟩
      _ = ∫⁻ y in U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)), ENNReal.ofReal (Di y) := hD _ hK
      _ ≤ ∫⁻ _ in U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ)), ENNReal.ofReal D :=
          setLIntegral_mono' hK fun y hy =>
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hD' y hy.2))
      _ = ENNReal.ofReal D * volume (U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ''
            (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ : P => (1 : ℝ)) : Set (P → ι → ℝ))) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal D * volume U := mul_le_mul_right (measure_mono Set.inter_subset_left) _
  calc (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))
      = ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by
        rw [inv_mul_cancel₀ hm.ne', ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)))) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]
    _ ≤ ENNReal.ofReal (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * (ENNReal.ofReal D * volume U) :=
        mul_le_mul_right h1 _
    _ = ENNReal.ofReal ((GlobalTheory.CompanionTheory.WeilSiegel.Inf0.gaussR Pm x₀)⁻¹ * D) * volume U := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), mul_assoc]

theorem qR0_scale [Fintype ι] (A : P → Matrix ι ι ℝ) (t : P → ℝ) (x : P → ι → ℝ) :
    qR0 A (fun w => t w • x w) = fun w => (t w ^ 2) • qR0 A x w := by
  funext w
  simp only [qR0, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem image_box_bound : ∀ (P ι : Type) [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ), 2 ≤ Fintype.card ι → Continuous Di → (∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∃ C : ℝ≥0, ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by
  intro P ι _ _ A Pm Di hcard hDi hD
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.unit_box_bound A Pm Di hDi hD
  refine ⟨C, fun t ht U hU => ?_⟩
  have hQc : Continuous (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 (P := P) A) := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_qR0 A
  have hφm : Measurable (fun (x : P → ι → ℝ) (w : P) => t w • x w) :=
    (continuous_pi fun w => (continuous_apply w).const_smul (t w)).measurable
  have hψm : Measurable (fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) :=
    (continuous_pi fun w => (continuous_apply w).const_smul (t w ^ 2)).measurable
  have hBox : IsClosed (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ)) := by
    show IsClosed {x : P → ι → ℝ | ∀ w, ‖x w‖ ≤ t w}
    rw [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_le (continuous_apply w).norm continuous_const
  have hSm : MeasurableSet (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t : Set (P → ι → ℝ))) :=
    (hQc.measurable hU).inter hBox.measurableSet
  have hpre : (fun (x : P → ι → ℝ) (w : P) => t w • x w) ⁻¹'
      (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) =
      GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
        GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.qR0_scale]
    refine and_congr_right fun _ => ?_
    simp only [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR, Set.mem_setOf_eq]
    exact forall_congr' fun w => by
      rw [norm_smul, Real.norm_of_nonneg (ht w).le, mul_le_iff_le_one_right (ht w)]
  have hφ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) (ι → ℝ) t ht
  have hψ := GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul (P := P) ℝ (fun w => t w ^ 2) (fun w => pow_pos (ht w) 2)
  rw [Module.finrank_fintype_fun_eq_card] at hφ
  rw [Module.finrank_self] at hψ
  have e1 : ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) *
      (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t) =
      volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
        GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by
    rw [← hpre, ← Measure.map_apply hφm hSm, hφ, Measure.smul_apply, smul_eq_mul]
  have e2 : ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * (volume : Measure (P → ℝ)) U =
      volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) := by
    rw [← Measure.map_apply hψm hU, hψ, Measure.smul_apply, smul_eq_mul]
  have hprod : ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
      ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le),
      ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), ENNReal.ofReal_one]
  have hreal : (∏ w, t w ^ Fintype.card ι) * ∏ w, ((t w ^ 2) ^ 1)⁻¹ =
      ∏ w, t w ^ (Fintype.card ι - 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [pow_one, show t w ^ Fintype.card ι = t w ^ (Fintype.card ι - 2) * t w ^ 2 by
        rw [← pow_add, Nat.sub_add_cancel hcard],
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (ht w).ne'), mul_one]
  calc (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t)
      = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) * (ENNReal.ofReal (∏ w, (t w ^ Fintype.card ι)⁻¹) *
          (volume : Measure (P → ι → ℝ)) (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' U ∩ GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR t)) := by
        rw [← mul_assoc, hprod, one_mul]
    _ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          volume (GlobalTheory.CompanionTheory.WeilSiegel.Inf0.qR0 A ⁻¹' ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U) ∩
            GlobalTheory.CompanionTheory.WeilSiegel.Inf0.boxR (fun _ => (1 : ℝ))) := by rw [e1]
    _ ≤ ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ((C : ℝ≥0∞) * volume ((fun (z : P → ℝ) (w : P) => t w ^ 2 • z w) ⁻¹' U)) :=
        mul_le_mul_right (hC _ (hψm hU)) _
    _ = ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ((C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹) * volume U)) := by rw [e2]
    _ = (C : ℝ≥0∞) * (ENNReal.ofReal (∏ w, t w ^ Fintype.card ι) *
          ENNReal.ofReal (∏ w, ((t w ^ 2) ^ 1)⁻¹)) * volume U := by ring
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by
        rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (pow_pos (ht w) _).le), hreal]

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableGenericFibreLocalizationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_generic_fibre_localization : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → ∀ (F : Type) [Field F] [Algebra O F] [IsLocalization.Away ϖ F], (IsLocalization.Away.map F (Localization.Away (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ)) (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ})) ϖ).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Semistable.smooth_generic_fibre | exact GlobalTheory.CompanionTheory.Semistable.smooth_generic_fibre | (intros; apply GlobalTheory.CompanionTheory.Semistable.smooth_generic_fibre <;> assumption)
end


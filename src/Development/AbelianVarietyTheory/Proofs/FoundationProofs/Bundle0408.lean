import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0403
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwist
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0405

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormGaussSumModPrimePowerLeHalfPower
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem norm_gSum_le : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)),
    z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  intro l _ m z ψ hz
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨k, hk⟩ : ∃ k, k = m / 2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = m - k := ⟨_, rfl⟩
  rw [← hk]
  have hsm : s ≤ m := by omega
  have hmss : m ≤ s + s := by omega
  have hmsk : m = s + k := by omega
  haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let π : ZMod (l ^ m) →+* ZMod (l ^ s) := ZMod.castHom (pow_dvd_pow l hsm) (ZMod (l ^ s))
  have hsurj : Function.Surjective π := ZMod.castHom_surjective (pow_dvd_pow l hsm)
  let q : ZMod (l ^ m) := ((l ^ s : ℕ) : ZMod (l ^ m))
  have hqq : q * q = 0 := by
    simp only [q, ← Nat.cast_mul, ← pow_add, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow l hmss
  have hπq : π q = 0 := by
    simp only [q]
    rw [map_natCast, ZMod.natCast_self]
  have hfib : ∀ x x0 : ZMod (l ^ m), π x = π x0 → ∃ y, x = x0 + q * y := by
    intro x x0 h
    have h0 : π (x - x0) = 0 := by rw [map_sub, h, sub_self]
    have hd : ((x - x0).val : ZMod (l ^ m)) = x - x0 := ZMod.natCast_zmod_val _
    rw [← hd, map_natCast, ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨j, hj⟩ := h0
    refine ⟨(j : ZMod (l ^ m)), ?_⟩
    rw [← sub_eq_iff_eq_add', ← hd, hj, Nat.cast_mul]
  let e : ZMod (l ^ m) → Qbar l := fun x => z ^ x.val
  have he : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    simp only [e, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hz).symm
  let g : ZMod (l ^ m) → Qbar l := fun x => ψ x * e x
  have hzn : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    simp only [g, e, norm_mul, norm_pow, hzn, one_pow, mul_one]
    exact DirichletCharacter.norm_le_one ψ x
  have hsum : gSum m z ψ = ∑ x, g x := by
    unfold gSum
    symm
    rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun x _ hx => by
      by_contra h; exact hx (by simp [g, MulChar.map_nonunit ψ h]))]
    refine Finset.sum_bij' (fun x hx => (Finset.mem_filter.1 hx).2.unit) (fun b _ => (b : ZMod (l ^ m)))
      ?_ ?_ ?_ ?_ ?_ <;> simp [g, e]
  have hmove : ∀ x x0 y : ZMod (l ^ m), π x = π x0 → x * q * y = x0 * q * y := by
    intro x x0 y h
    obtain ⟨y', rfl⟩ := hfib x x0 h
    linear_combination (y' * y) * hqq
  have h1 : ∀ y : ZMod (l ^ m), (1 - q * y) * (1 + q * y) = 1 := fun y => by
    linear_combination (-(y * y)) * hqq
  have hinv : ∀ x0 y : ZMod (l ^ m), ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x =
      ψ (1 + q * y) * e (x0 * q * y) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x := by
    intro x0 y
    rw [Finset.mul_sum]
    calc ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x
        = ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g (x * (1 + q * y)) := by
          refine Finset.sum_nbij' (fun x => x * (1 - q * y)) (fun x => x * (1 + q * y)) ?_ ?_ ?_ ?_ ?_
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_sub, map_one, hπq,
              zero_mul, sub_zero, mul_one] at ha ⊢
            exact ha
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_add, map_one, hπq,
              zero_mul, add_zero, mul_one] at ha ⊢
            exact ha
          · intro a _
            simp only [mul_assoc, h1, mul_one]
          · intro a _
            simp only [mul_assoc, mul_comm (1 + q * y), h1, mul_one]
          · intro a _
            simp only [mul_assoc, h1, mul_one]
      _ = _ := Finset.sum_congr rfl fun x hx => by
          have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
          show ψ (x * (1 + q * y)) * e (x * (1 + q * y)) = ψ (1 + q * y) * e (x0 * q * y) * (ψ x * e x)
          rw [map_mul, show x * (1 + q * y) = x + x * q * y by ring, he, hmove x x0 y hx']
          ring
  have H : ∀ u w y' : ZMod (l ^ m), IsUnit u → w = u + q * y' →
      (∀ y, ψ (1 + q * y) * e (u * q * y) = 1) → g w = g u := by
    intro u w y' hu hw hχu
    obtain ⟨U, rfl⟩ := hu
    have hUU : (U : ZMod (l ^ m)) * ((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = 1 := Units.mul_inv U
    have hw' : w = (U : ZMod (l ^ m)) + U * q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y') := by
      rw [hw]; linear_combination (-(q * y')) * hUU
    have hw'' : w = (U : ZMod (l ^ m)) * (1 + q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')) := by
      rw [hw']; ring
    have := hχu (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')
    show ψ w * e w = ψ U * e U
    rw [hw'', map_mul, ← hw'', hw', he]
    linear_combination (ψ U * e U) * this
  have hcard0 : ∀ x0, (Finset.univ.filter (fun x => π x = π x0)).card =
      (Finset.univ.filter (fun x => π x = 0)).card := by
    intro x0
    refine Finset.card_nbij' (fun x => x - x0) (fun x => x + x0) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_sub, ha, sub_self]
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_add, ha, zero_add]
    · intro a _; simp
    · intro a _; simp
  have htot : l ^ m = l ^ s * (Finset.univ.filter (fun x => π x = 0)).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := π)
      (fun x _ => Finset.mem_univ _)
    rw [Finset.card_univ, ZMod.card] at this
    refine this.trans ?_
    rw [Finset.sum_congr rfl (g := fun _ => (Finset.univ.filter (fun x => π x = 0)).card) (fun c _ => by
      obtain ⟨x0, rfl⟩ := hsurj c
      exact hcard0 x0), Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  have hcardk : (Finset.univ.filter (fun x => π x = 0)).card = l ^ k := by
    have h2 : l ^ s * (Finset.univ.filter (fun x => π x = 0)).card = l ^ s * l ^ k := by
      rw [← htot, ← pow_add, ← hmsk]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos s) h2
  rw [hsum, ← Finset.sum_fiberwise Finset.univ π g]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => ?_
  obtain ⟨x0, rfl⟩ := hsurj c
  by_cases hχ : ∀ y, ψ (1 + q * y) * e (x0 * q * y) = 1
  · have hall : ∀ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = g x0 := by
      intro x hx
      have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
      obtain ⟨y', hy'⟩ := hfib x x0 hx'
      by_cases hu0 : IsUnit x0
      · exact H x0 x y' hu0 hy' hχ
      by_cases hu : IsUnit x
      · refine (H x x0 (-y') hu (by rw [hy']; ring) fun y => ?_).symm
        rw [hmove x x0 y hx']
        exact hχ y
      · show ψ x * e x = ψ x0 * e x0
        rw [MulChar.map_nonunit ψ hu, MulChar.map_nonunit ψ hu0, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, norm_mul, hcard0, hcardk]
    push_cast
    calc ‖(l : Qbar l) ^ k‖ * ‖g x0‖ ≤ ‖(l : Qbar l) ^ k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hg1 x0) (norm_nonneg _)
      _ = _ := mul_one _
  · push_neg at hχ
    obtain ⟨y, hy⟩ := hχ
    have hI := hinv x0 y
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
      have hm : (1 - ψ (1 + q * y) * e (x0 * q * y)) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
        rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 (Ne.symm hy))
    rw [h0, norm_zero]
    positivity

end GlobalTheory.KZ.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesEqZeroOfValsTendstoZero
section
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

namespace GlobalTheory

theorem KZ.norm_prime_lt_one_qbar (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem KZ.eq_zero_of_cg_all (l : ℕ) [Fact l.Prime] (x : Qbar l) (h : ∀ k : ℕ, Cg k x 0) :
    x = 0 := by
  have hlt := KZ.norm_prime_lt_one_qbar l
  have hn : 0 ≤ ‖((l : ℕ) : Qbar l)‖ := norm_nonneg _
  have ht : Filter.Tendsto (fun k : ℕ => ‖((l : ℕ) : Qbar l)‖ ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hn hlt
  have hle : ∀ k : ℕ, ‖x‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ k := by
    intro k
    have := h k
    unfold Cg at this
    simpa [norm_pow] using this
  have h0 : ‖x‖ ≤ 0 := ge_of_tendsto' ht hle
  exact norm_le_zero_iff.mp h0

theorem KZ.series_eq_zero_of_vals_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)), (∀ n, F.coeff n ∈ c.O) → (∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) → F = 0 := by
  intro l _ c F hO hv
  ext n
  rw [map_zero]
  apply KZ.eq_zero_of_cg_all l
  intro k
  obtain ⟨m₁, hm⟩ := hv k
  exact GlobalTheory.T.coefficient_congruence_of_twisted_values l c F k m₁ hO hm n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerDecompositionDirichletTwistedPower
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.TeichDec

variable {l : ℕ} [Fact l.Prime]

noncomputable def emb (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* Qbar l := (algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom

theorem norm_emb (x : ℤ_[l]) : ‖emb l x‖ = ‖x‖ := PadicAlgCl.norm_extends l (x : ℚ_[l])

theorem norm_emb_le_of_dvd {d x : ℤ_[l]} (h : d ∣ x) : ‖emb l x‖ ≤ ‖emb l d‖ := by
  obtain ⟨y, rfl⟩ := h
  rw [map_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by rw [norm_emb]; exact PadicInt.norm_le_one y)

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem norm_eq_one_of_pow {x : Qbar l} (hx : x ^ (l - 1) = 1) : ‖x‖ = 1 := by
  have h2 := (Fact.out : l.Prime).two_le
  have h1 := congrArg norm hx
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1

theorem eq_of_pow_eq_one {x y : Qbar l} (hx : x ^ (l - 1) = 1) (hy : y ^ (l - 1) = 1) (h : ‖x - y‖ < 1) : x = y := by
  have h2 := (Fact.out : l.Prime).two_le
  by_contra hne
  have hx1 := norm_eq_one_of_pow hx
  have hy1 := norm_eq_one_of_pow hy
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  set z := x / y with hz
  have hz1 : z ^ (l - 1) = 1 := by rw [hz, div_pow, hx, hy, div_one]
  have hzn : ‖z‖ = 1 := norm_eq_one_of_pow hz1
  have hzne : z - 1 ≠ 0 := by
    intro h0
    exact hne ((div_eq_one_iff_eq hy0).1 (sub_eq_zero.1 h0))
  have hzd : ‖z - 1‖ = ‖x - y‖ := by
    have : z - 1 = (x - y) / y := by rw [hz]; field_simp
    rw [this, norm_div, hy1, div_one]
  have hs : ∑ i ∈ Finset.range (l - 1), z ^ i = 0 := by
    have := geom_sum_mul z (l - 1)
    rw [hz1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hzne
  have hb : ‖∑ i ∈ Finset.range (l - 1), (z ^ i - 1)‖ ≤ ‖z - 1‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [← geom_sum_mul, norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_pow, hzn, one_pow]
  have hsum : (1 : Qbar l) = (l : Qbar l) + ∑ i ∈ Finset.range (l - 1), (z ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  have h3 := IsUltrametricDist.norm_add_le_max (l : Qbar l) (∑ i ∈ Finset.range (l - 1), (z ^ i - 1))
  rw [← hsum, norm_one] at h3
  exact absurd h3 (not_le.2 (max_lt norm_l_lt_one (hb.trans_lt (hzd ▸ h))))

theorem norm_natCast_eq_one {n : ℕ} (hn : ¬ l ∣ n) : ‖(n : ℤ_[l])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hn ?_)
  have h1 : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
  exact Int.natCast_dvd_natCast.1 ((PadicInt.norm_int_lt_one_iff_dvd _).1 h1)

theorem exists_root {c : ℕ} (hc : ¬ l ∣ c) : ∃ z : ℤ_[l], z ^ (l - 1) = 1 ∧ (l : ℤ_[l]) ∣ z - c := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  have hd : ‖Polynomial.aeval (c : ℤ_[l]) (Polynomial.derivative (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))‖ = 1 := by
    have : Polynomial.aeval (c : ℤ_[l]) (Polynomial.derivative (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))
        = (((l - 1) * c ^ (l - 1 - 1) : ℕ) : ℤ_[l]) := by
      simp [Polynomial.derivative_X_pow]
    rw [this]
    refine norm_natCast_eq_one fun h => ?_
    rcases (hp.dvd_mul).1 h with h | h
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · exact hc (hp.dvd_of_dvd_pow h)
  have hv : ‖Polynomial.aeval (c : ℤ_[l]) (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l])‖ < 1 := by
    have : Polynomial.aeval (c : ℤ_[l]) (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l])
        = (((c : ℤ) ^ (l - 1) - 1 : ℤ) : ℤ_[l]) := by
      simp
    rw [this, PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one (by rwa [Ne, ZMod.natCast_eq_zero_iff]), sub_self]
  obtain ⟨z, hz, hz1, -⟩ := hensels_lemma (F := (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l])) (a := (c : ℤ_[l]))
    (by rw [hd, one_pow]; exact hv)
  rw [hd] at hz1
  refine ⟨z, ?_, (PadicInt.norm_lt_one_iff_dvd _).1 hz1⟩
  simpa [sub_eq_zero] using hz

theorem exists_decomp (hl : l ≠ 2) (R : ℕ) {j : ℕ} (hj : ¬ l ∣ j) :
    ∃ c t : ℕ, ¬ l ∣ c ∧ j ≡ c ^ (l ^ R) * (1 + l) ^ t [MOD l ^ (R + 1)] := by
  classical
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ (R + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h := GlobalTheory.sum_units_primePow_teichmuller_reindex l hl R ℕ
    (fun x => if x = (j : ZMod (l ^ (R + 1))) then 1 else 0)
  have hcop : Nat.Coprime j (l ^ (R + 1)) := Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd).2 hj).symm
  have hne : ∑ b : (ZMod (l ^ (R + 1)))ˣ, (if (b : ZMod (l ^ (R + 1))) = (j : ZMod (l ^ (R + 1))) then 1 else 0 : ℕ) ≠ 0 := by
    intro h0
    have := Finset.sum_eq_zero_iff.1 h0 (ZMod.unitOfCoprime j hcop) (Finset.mem_univ _)
    simp at this
  rw [h] at hne
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  refine ⟨(c : ZMod l).val, t, fun hd => ?_, ?_⟩
  · have h0 : (((c : ZMod l).val : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [ZMod.natCast_zmod_val] at h0
    exact c.ne_zero h0
  · refine ((ZMod.natCast_eq_natCast_iff _ _ _).1 ?_).symm
    by_contra h1
    exact ht (if_neg h1)

theorem dvd_of_modEq {n a b : ℕ} (h : a ≡ b [MOD n]) : (n : ℤ_[l]) ∣ (b : ℤ_[l]) - a := by
  have h1 := map_dvd (Int.castRingHom ℤ_[l]) (Nat.modEq_iff_dvd.1 h)
  simpa using h1

theorem teich : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e R j : ℕ), l ≠ 2 →
    ∃ (ε : Qbar l) (t : ℕ), (ε = 0 ∨ ε ^ (l - 1) = 1) ∧
      Cg R (φ (j : ZMod l) * (j : Qbar l) ^ e) (ε * ((1 + (l : Qbar l)) ^ e) ^ t) ∧
      ∀ m, 1 ≤ m → m ≤ R → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), InComp φ e ψ →
        ψ⁻¹ (j : ZMod (l ^ m)) = ε * (ψ⁻¹ (1 + (l : ZMod (l ^ m)))) ^ t := by
  intro l _ φ e R j hl
  have hp : l.Prime := Fact.out
  by_cases hj : l ∣ j
  · refine ⟨0, 0, Or.inl rfl, ?_, fun m hm _ ψ _ => ?_⟩
    · rw [(ZMod.natCast_eq_zero_iff _ _).2 hj, MulChar.map_nonunit _ not_isUnit_zero]
      simp [Cg]
    · rw [zero_mul]
      refine MulChar.map_nonunit _ fun hu => ?_
      have h1 := (ZMod.isUnit_iff_coprime _ _).1 hu
      have h2 : l ∣ Nat.gcd j (l ^ m) := Nat.dvd_gcd hj (dvd_pow_self l (by omega))
      rw [h1] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  obtain ⟨c, t, hc, hjc⟩ := exists_decomp hl R hj
  obtain ⟨z, hz, hzc⟩ := exists_root hc
  set b : ℕ := c ^ (l ^ R) with hb
  set w : ℤ_[l] := z ^ (l ^ R) with hw
  have hw1 : w ^ (l - 1) = 1 := by rw [hw, ← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have hwb : (l : ℤ_[l]) ^ (R + 1) ∣ w - b := by
    have := dvd_sub_pow_of_dvd_sub hzc R
    rw [hb]; push_cast; exact this
  have hj0 : (j : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hφ : φ (j : ZMod l) ^ (l - 1) = 1 := by rw [← map_pow, ZMod.pow_card_sub_one_eq_one hj0, map_one]
  have hφn := norm_eq_one_of_pow hφ
  have hε : (emb l w ^ e * φ (j : ZMod l)) ^ (l - 1) = 1 := by
    rw [mul_pow, hφ, mul_one, ← pow_mul, mul_comm, pow_mul, ← map_pow, hw1, map_one, one_pow]
  refine ⟨emb l w ^ e * φ (j : ZMod l), t, Or.inr hε, ?_, fun m hm hmR ψ hψ => ?_⟩
  · have h1 : (l : ℤ_[l]) ^ (R + 1) ∣ (j : ℤ_[l]) - w * (1 + l) ^ t := by
      have h2 := dvd_of_modEq (l := l) hjc.symm
      push_cast at h2
      have h3 : (j : ℤ_[l]) - w * (1 + l) ^ t = (j - b * (1 + l) ^ t) - (w - b) * (1 + l) ^ t := by ring
      rw [h3]
      exact dvd_sub h2 (hwb.mul_right _)
    have h4 : (l : ℤ_[l]) ^ R ∣ (j : ℤ_[l]) ^ e - (w * (1 + l) ^ t) ^ e :=
      ((pow_dvd_pow _ (Nat.le_succ R)).trans h1).trans (sub_dvd_pow_sub_pow _ _ _)
    have h5 := norm_emb_le_of_dvd h4
    simp only [map_sub, map_pow, map_mul, map_add, map_one, map_natCast] at h5
    unfold Cg
    have h6 : φ (j : ZMod l) * (j : Qbar l) ^ e - emb l w ^ e * φ (j : ZMod l) * ((1 + (l : Qbar l)) ^ e) ^ t
        = φ (j : ZMod l) * ((j : Qbar l) ^ e - (emb l w * (1 + (l : Qbar l)) ^ t) ^ e) := by ring
    rw [h6, norm_mul, hφn, one_mul]
    exact h5
  · haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hmd : l ^ m ∣ l ^ (R + 1) := pow_dvd_pow _ (by omega)
    have hld : l ∣ l ^ m := dvd_pow_self l (by omega)
    have hcc : Nat.Coprime c l := ((hp.coprime_iff_not_dvd).2 hc).symm
    have hbcop : Nat.Coprime b (l ^ m) := Nat.Coprime.pow _ _ hcc
    have hb1 : b ^ (l - 1) ≡ 1 [MOD l ^ m] := by
      have h1 := Nat.ModEq.pow_totient (Nat.Coprime.pow_right (R + 1) hcc)
      rw [Nat.totient_prime_pow_succ hp, pow_mul] at h1
      exact h1.of_dvd hmd
    have hb2 : (b : ZMod (l ^ m)) ^ (l - 1) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hb1
      simpa using this
    have hu : ZMod.unitOfCoprime b hbcop ^ (l - 1) = 1 := Units.ext (by simpa using hb2)
    have h7 := hψ _ hu
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast] at h7
    have hvb : b % l ^ m ≡ b [MOD l] := (Nat.mod_modEq b (l ^ m)).of_dvd hld
    have hbj : (b : ZMod l) = (j : ZMod l) := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hjc.of_dvd (dvd_pow_self l (Nat.succ_ne_zero R)))
      rw [this]; push_cast; simp
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hvb, hbj] at h7
    have h8 : (l : ℤ_[l]) ∣ ((b % l ^ m : ℕ) : ℤ_[l]) ^ e - w ^ e := by
      refine Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ _)
      have h2 := dvd_of_modEq (l := l) hvb.symm
      have h3 : ((b % l ^ m : ℕ) : ℤ_[l]) - w = (((b % l ^ m : ℕ) : ℤ_[l]) - b) - (w - b) := by ring
      rw [h3]
      exact dvd_sub h2 ((dvd_pow_self _ (Nat.succ_ne_zero R)).trans hwb)
    have h9 := (norm_emb_le_of_dvd h8).trans_lt (by rw [map_natCast]; exact norm_l_lt_one)
    rw [map_sub, map_pow, map_pow, map_natCast] at h9
    have hψb : ψ⁻¹ (b : ZMod (l ^ m)) ^ (l - 1) = 1 := by rw [← map_pow, hb2, map_one]
    have h10 : ψ⁻¹ (b : ZMod (l ^ m)) = emb l w ^ e * φ (j : ZMod l) := by
      refine eq_of_pow_eq_one hψb hε ?_
      have h3 : ψ⁻¹ (b : ZMod (l ^ m)) - emb l w ^ e * φ (j : ZMod l) =
          (ψ⁻¹ (b : ZMod (l ^ m)) - ((b % l ^ m : ℕ) : Qbar l) ^ e * φ (j : ZMod l)) +
            (((b % l ^ m : ℕ) : Qbar l) ^ e - emb l w ^ e) * φ (j : ZMod l) := by ring
      rw [h3]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h7 ?_)
      rw [norm_mul, hφn, mul_one]
      exact h9
    rw [← h10, ← map_pow, ← map_mul, (ZMod.natCast_eq_natCast_iff _ _ _).2 (hjc.of_dvd hmd)]
    push_cast
    rfl

end GlobalTheory.TeichDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwistStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → 1 ≤ N → ∀ (n w d q : ℕ), Odd w → q.Prime → ¬ q ∣ N * l → ((q : Ω))⁻¹ ∈ A → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω, IsLat 1 φ → IsLat 1 φ' →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
  IsThB X A N l n (X.act l (sgD N l (d * q) : Matrix (Fin 2) (Fin 2) ℤ) b) φ' →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b)) (hq ε q φ + ((q : Ω) ^ (w + 1)) • vq q φ') := by
  first | exact @GlobalTheory.HeckeTh.isThB_heckeT | exact GlobalTheory.HeckeTh.isThB_heckeT | (intros; apply GlobalTheory.HeckeTh.isThB_heckeT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOneStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOperator_upperU_l_commute_scale_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → 1 ≤ N → Odd w → (l : Ω) ∈ A.nonunits → d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsLat 1 φ →
  IsThB X A N l (n + 1) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (uq l φ) := by
  first | exact @GlobalTheory.ThHeckeU.isThB_act_heckeU | exact GlobalTheory.ThHeckeU.isThB_act_heckeU | (intros; apply GlobalTheory.ThHeckeU.isThB_act_heckeU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TruncatedShiftedSeriesEqIntegralPolyCombination
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem tval_eq_sum_pow_of_integral : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (N : ℕ), (∀ n, F.coeff n ∈ c.O) → ∃ a : ℕ → Qbar l, (∀ j, a j ∈ c.O) ∧ ∀ z : Qbar l, tval F N z = ∑ j ∈ Finset.range N, a j * z ^ j := by
  intro l _ c F N hF
  let Q : Polynomial c.O := ∑ n ∈ Finset.range N, Polynomial.C (⟨F.coeff n, hF n⟩ : c.O) * (Polynomial.X - Polynomial.C 1) ^ n
  refine ⟨fun j => ((Q.coeff j : c.O) : Qbar l), fun j => (Q.coeff j).2, fun z => ?_⟩
  have hdeg : Q.natDegree < N ∨ N = 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact Or.inr h
    · left
      obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)
      have hn' : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_pow_le).trans ?_)
      calc n * (Polynomial.X - Polynomial.C (1 : c.O)).natDegree ≤ n * 1 :=
            Nat.mul_le_mul_left _ (Polynomial.natDegree_X_sub_C_le _)
        _ ≤ k := by omega
  rcases hdeg with hd | rfl
  · have h1 := Polynomial.aeval_eq_sum_range' (R := c.O) (x := z) hd
    have h2 : Polynomial.aeval z Q = tval F N z := by
      simp [Q, tval, map_sum]
    rw [← h2, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    rfl
  · simp [tval]

end GlobalTheory.KZ.Cmp
end


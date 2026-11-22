import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLogDivSubOneLeThreeMulLogAddOne
section
open Finset

namespace GlobalTheory

theorem sub_one_le_two_mul_sub_one_mul_factorization_factorial {p B : ℕ} (hp : p.Prime)
    (hpB : p ≤ B) :
    (B : ℝ) - 1 ≤ 2 * (((p : ℝ) - 1) * ((B.factorial.factorization p : ℕ) : ℝ)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (p - 1) * padicValNat p B.factorial = B - (Nat.digits p B).sum :=
    sub_one_mul_padicValNat_factorial B
  have hp2 : 2 ≤ p := hp.two_le
  have hB : 0 < B := by omega
  have h2 : (Nat.digits p B).sum ≤ B % p + B / p := by
    rw [Nat.digits_def' (by omega) hB, List.sum_cons]
    exact Nat.add_le_add_left (Nat.digit_sum_le _ _) _
  have h3 : B % p + p * (B / p) = B := Nat.mod_add_div B p
  have h4 : B % p < p := Nat.mod_lt _ (by omega)
  have h5 : 1 ≤ B / p := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have h6 : m ≤ m * (B / (m + 2)) := Nat.le_mul_of_pos_right _ h5
  have h7 : 2 * (Nat.digits (m + 2) B).sum ≤ B + 1 := by nlinarith
  rw [Nat.factorization_def _ hp]
  have h8 : B ≤ 2 * ((m + 1) * padicValNat (m + 2) B.factorial) + 1 := by
    have : m + 2 - 1 = m + 1 := by omega
    rw [this] at h1
    omega
  have h9 : (B : ℝ) ≤ 2 * (((m : ℝ) + 1) * (padicValNat (m + 2) B.factorial : ℝ)) + 1 := by
    exact_mod_cast h8
  push_cast
  linarith

theorem factorial_succ_le_pow (n : ℕ) : (n + 1).factorial ≤ (n + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, pow_succ']
    exact Nat.mul_le_mul_left _ (ih.trans (Nat.pow_le_pow_left (by omega) _))

theorem sum_log_div_sub_one_le_two_mul_log {B : ℕ} (hB : 2 ≤ B) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ B) :
    ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 2 * Real.log B := by
  have hB1 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have h1 : ∑ p ∈ S, ((B.factorial.factorization p : ℕ) : ℝ) * Real.log p
      ≤ Real.log (B.factorial : ℕ) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors]
      exact ⟨(hS p hp).1, ((hS p hp).1.dvd_factorial).2 (hS p hp).2, B.factorial_ne_zero⟩
    · intro p _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have h2 : Real.log (B.factorial : ℕ) ≤ ((B : ℝ) - 1) * Real.log B := by
    obtain ⟨n, rfl⟩ : ∃ n, B = n + 1 := ⟨B - 1, by omega⟩
    have h := factorial_succ_le_pow n
    have h' : (((n + 1).factorial : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ n := by exact_mod_cast h
    have := Real.log_le_log (by exact_mod_cast (n + 1).factorial_pos) h'
    rw [Real.log_pow] at this
    convert this using 2
    push_cast; ring
  have h3 : ((B : ℝ) - 1) * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1)
      ≤ 2 * ∑ p ∈ S, ((B.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
    have h := sub_one_le_two_mul_sub_one_mul_factorization_factorial (hS p hp).1 (hS p hp).2
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg _
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right h hl]
  refine le_of_mul_le_mul_left ?_ hB1
  nlinarith

theorem log_div_sub_one_le_of_lt {B p : ℕ} (hB : 1 ≤ B) (h : B < p) :
    Real.log p / ((p : ℝ) - 1) ≤ (Real.log B + 1) / B := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hp : (B : ℝ) + 1 ≤ p := by exact_mod_cast h
  have hl : 0 ≤ Real.log B := Real.log_natCast_nonneg _
  have h1 : Real.log (p / B) ≤ p / B - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  rw [Real.log_div (by linarith) (by linarith)] at h1
  have h2 : (Real.log p - Real.log B) * B ≤ p - B := by
    have := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ B)
    rwa [sub_mul ((p : ℝ) / B), div_mul_cancel₀ _ (by linarith), one_mul] at this
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg hl (by linarith : (0 : ℝ) ≤ p - 1 - B)]

theorem sum_log_div_sub_one_le_three_mul_log_add_one :
    ∀ (B : ℕ) (S : Finset ℕ), 3 ≤ B → (∀ p ∈ S, p.Prime) →
      (S.filter (fun p => B < p)).card ≤ B →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 := by
  intro B S hB hS hc
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => B < p)]
  have h1 := sum_log_div_sub_one_le_two_mul_log (B := B) (by omega)
    (S.filter (fun p => ¬ B < p)) (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨hS p hp.1, by omega⟩)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hl : 0 ≤ Real.log B := Real.log_natCast_nonneg _
  have h2 : ∑ p ∈ S.filter (fun p => B < p), Real.log p / ((p : ℝ) - 1)
      ≤ (S.filter (fun p => B < p)).card • ((Real.log B + 1) / B) :=
    Finset.sum_le_card_nsmul _ _ _ fun p hp =>
      log_div_sub_one_le_of_lt (by omega) (Finset.mem_filter.1 hp).2
  rw [nsmul_eq_mul] at h2
  have h3 : ((S.filter (fun p => B < p)).card : ℝ) * ((Real.log B + 1) / B)
      ≤ B * ((Real.log B + 1) / B) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  rw [mul_div_cancel₀ _ hB0.ne'] at h3
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormEntriesMulLe
section
namespace GlobalTheory.EntryNormProductBound

theorem sum_norm_entries_mul_le {n : ℕ} {α : Type} [NormedRing α]
    (a b : Matrix (Fin n) (Fin n) α) :
    ∑ i : Fin n, ∑ j : Fin n, ‖(a * b) i j‖ ≤
      (∑ i : Fin n, ∑ j : Fin n, ‖a i j‖) * ∑ i : Fin n, ∑ j : Fin n, ‖b i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j : Fin n, ‖(a * b) i j‖
      ≤ ∑ j : Fin n, ∑ k : Fin n, ‖a i k‖ * ‖b k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k : Fin n, ‖a i k‖ * ∑ j : Fin n, ‖b k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k : Fin n, ‖a i k‖ * ∑ l : Fin n, ∑ j : Fin n, ‖b l j‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun l => ∑ j : Fin n, ‖b l j‖)
          (fun l _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)
    _ = (∑ k : Fin n, ‖a i k‖) * ∑ l : Fin n, ∑ j : Fin n, ‖b l j‖ :=
        (Finset.sum_mul _ _ _).symm

end GlobalTheory.EntryNormProductBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTracePowMulSubMulPowTelescope
section
namespace GlobalTheory.ChernCalc

theorem sum_trace_pow_mul_sub_mul_pow (R : Type) [CommRing R] (r : Type) [Fintype r]
    [DecidableEq r] (P Q : Matrix r r R) (k : ℕ) :
    ∑ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ k).trace - (Q ^ k).trace := by
  have h : ∀ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ (i + 1) * Q ^ (k - (i + 1))).trace - (P ^ i * Q ^ (k - i)).trace := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have e1 : k - 1 - i = k - (i + 1) := by omega
    have e2 : k - i = (k - (i + 1)) + 1 := by omega
    rw [e1, e2, ← Matrix.trace_sub, mul_sub, sub_mul, ← pow_succ, pow_succ' Q, mul_assoc]
  rw [Finset.sum_congr rfl h,
    Finset.sum_range_sub (fun i => (P ^ i * Q ^ (k - i)).trace)]
  simp

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTranslatesEqDoubleCosetAverage
section
namespace GlobalTheory
namespace CosetAvg

open MulAction

theorem orbit_sum {H X M : Type*} [Group H] [Fintype H] [MulAction H X] [AddCommGroup M]
    [Module ℂ M] (y : X) [Fintype (orbit H y)] (F : X → M) :
    (Fintype.card (orbit H y) : ℂ) • ∑ h : H, F (h • y) =
      (Fintype.card H : ℂ) • ∑ z : orbit H y, F z := by
  have h1 : ∀ z : orbit H y, ∑ h : H, F (h • (z : X)) = ∑ h : H, F (h • y) := by
    rintro ⟨z, g, rfl⟩
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => by simp [mul_smul])
  have h2 : ∀ h : H, ∑ z : orbit H y, F (h • (z : X)) = ∑ z : orbit H y, F z := by
    intro h
    exact Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun z => rfl)
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.card_univ,
    ← Finset.sum_const, ← Finset.sum_const]
  calc ∑ _z : orbit H y, ∑ h : H, F (h • y) = ∑ z : orbit H y, ∑ h : H, F (h • (z : X)) :=
        Finset.sum_congr rfl (fun z _ => (h1 z).symm)
    _ = ∑ h : H, ∑ z : orbit H y, F (h • (z : X)) := Finset.sum_comm
    _ = ∑ _h : H, ∑ z : orbit H y, F z := Finset.sum_congr rfl (fun h _ => h2 h)

theorem avg_of_invariant {H X M ι : Type*} [Group H] [Fintype H] [MulAction H X]
    [AddCommGroup M] [Module ℂ M] (s : Finset ι) (y : ι → X) [∀ i, Fintype (orbit H (y i))]
    (F : ι → X → M) (hinv : ∀ h : H, ∑ i ∈ s, F i (h • y i) = ∑ i ∈ s, F i (y i)) :
    ∑ i ∈ s, F i (y i) =
      ∑ i ∈ s, ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hO : ∀ i, (Fintype.card (orbit H (y i)) : ℂ) ≠ 0 := fun i => by
    haveI : Nonempty (orbit H (y i)) := ⟨⟨y i, mem_orbit_self _⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  have key : ∀ i, ∑ h : H, F i (h • y i) = (Fintype.card H : ℂ) •
      ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
    intro i
    rw [smul_comm (Fintype.card H : ℂ), ← orbit_sum, smul_smul, inv_mul_cancel₀ (hO i), one_smul]
  apply smul_right_injective M hH
  simp only
  calc (Fintype.card H : ℂ) • ∑ i ∈ s, F i (y i) = ∑ _h : H, ∑ i ∈ s, F i (y i) := by
        rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = ∑ h : H, ∑ i ∈ s, F i (h • y i) := Finset.sum_congr rfl (fun h _ => (hinv h).symm)
    _ = ∑ i ∈ s, ∑ h : H, F i (h • y i) := Finset.sum_comm
    _ = _ := by rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _ => key i)

end CosetAvg
end GlobalTheory

namespace GlobalTheory
namespace CosetAvg

open MulAction

theorem sum_translates_eq_avg : ∀ {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : G →* Module.End ℂ M) (K : Subgroup G) {ι : Type} (s : Finset ι) (a : ι → G) (R : ι → Finset G) (w : ι → M), (∀ i ∈ s, (∀ γ ∈ R i, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a i * k₂) ∧ ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a i * k₂) → ∃! γ, γ ∈ R i ∧ γ⁻¹ * x ∈ K) → (∀ i ∈ s, ∀ k ∈ K, ρ k (w i) = w i) → (∀ k ∈ K, ρ k (∑ i ∈ s, ρ (a i) (w i)) = ∑ i ∈ s, ρ (a i) (w i)) → ∑ i ∈ s, ρ (a i) (w i) = ∑ i ∈ s, ((R i).card : ℂ)⁻¹ • ∑ γ ∈ R i, ρ γ (w i) := by
  intro G M _ _ _ ρ K ι s a R w hR hw hm
  classical
  have hsm : ∀ (k : K) (g : G), k • ((g : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) := fun k g => rfl
  let Y : SubMulAction K (G ⧸ K) :=
    { carrier := {q | ∃ i ∈ s, ∃ k : K, q = k • ((a i : G) : G ⧸ K)}
      smul_mem' := by
        rintro c q ⟨i, hi, k, rfl⟩
        exact ⟨i, hi, c * k, (mul_smul c k _).symm⟩ }
  have hYsub : (Y : Set (G ⧸ K)) ⊆
      ((s.biUnion fun i => (R i).image (QuotientGroup.mk : G → G ⧸ K) : Finset (G ⧸ K)) :
        Set (G ⧸ K)) := by
    rintro q ⟨i, hi, k, rfl⟩
    obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i hi).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨γ, hγ, ?_⟩⟩)
    rw [hsm, QuotientGroup.eq]
    exact hγk
  haveI : Finite Y := (Set.Finite.subset (Finset.finite_toSet _) hYsub).to_subtype
  letI : Fintype Y := Fintype.ofFinite Y
  let φ := MulAction.toPermHom K Y
  let H := φ.range
  letI : Fintype H := Fintype.ofFinite H
  have hy : ∀ i ∈ s, ((a i : G) : G ⧸ K) ∈ Y := fun i hi => ⟨i, hi, 1, by simp⟩
  let y : s → Y := fun i => ⟨((a i : G) : G ⧸ K), hy i i.2⟩
  letI : ∀ i, Fintype (orbit H (y i)) := fun i => Fintype.ofFinite _
  let F : s → Y → M := fun i q => ρ (q : G ⧸ K).out (w i)
  have hF : ∀ (i : s) (q : Y) (g : G), (q : G ⧸ K) = (g : G ⧸ K) → F i q = ρ g (w i) := by
    intro i q g hq
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [F, hq, hk, map_mul, Module.End.mul_apply, hw i i.2 k k.2]
  have hval : ∀ (k : K) (i : s),
      ((((⟨φ k, k, rfl⟩ : H) • y i : Y)) : G ⧸ K) = ((k * a i : G) : G ⧸ K) := fun k i => rfl
  have hinv : ∀ h : H, ∑ i ∈ Finset.univ, F i (h • y i) = ∑ i ∈ Finset.univ, F i (y i) := by
    rintro ⟨_, k, rfl⟩
    rw [Finset.sum_congr rfl (fun i _ => hF i _ _ (hval k i)),
      Finset.sum_congr rfl (fun i _ => hF i (y i) (a i) rfl)]
    simp only [map_mul, Module.End.mul_apply]
    rw [← map_sum, Finset.sum_coe_sort s (fun i => ρ (a i) (w i)), hm k k.2]
  have hmain := avg_of_invariant (H := H) Finset.univ y F hinv

  have horb : ∀ i : s, ∃ e : (R i) ≃ orbit H (y i),
      ∀ γ : R i, ((e γ : Y) : G ⧸ K) = ((γ : G) : G ⧸ K) := by
    intro i
    have hmemY : ∀ γ ∈ R i, ((γ : G) : G ⧸ K) ∈ Y := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (hR i i.2).1 γ hγ
      exact ⟨i, i.2, ⟨k₁, hk₁⟩, by rw [hsm, QuotientGroup.mk_mul_of_mem _ hk₂]⟩
    have hmemO : ∀ (γ : G) (hγ : γ ∈ R i), (⟨(γ : G ⧸ K), hmemY γ hγ⟩ : Y) ∈ orbit H (y i) := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, hγe⟩ := (hR i i.2).1 γ hγ
      refine ⟨⟨φ ⟨k₁, hk₁⟩, ⟨k₁, hk₁⟩, rfl⟩, Subtype.ext ?_⟩
      exact (hval _ _).trans ((QuotientGroup.mk_mul_of_mem _ hk₂).symm.trans (congrArg _ hγe.symm))
    let f : R i → orbit H (y i) := fun γ => ⟨⟨(γ : G ⧸ K), hmemY γ γ.2⟩, hmemO γ γ.2⟩
    have hbij : Function.Bijective f := by
      constructor
      · rintro ⟨γ, hγ⟩ ⟨γ', hγ'⟩ he
        have he' : ((γ : G) : G ⧸ K) = ((γ' : G) : G ⧸ K) :=
          congrArg (fun z : orbit H (y i) => ((z : Y) : G ⧸ K)) he
        rw [QuotientGroup.eq] at he'
        have hu := (hR i i.2).2 γ' ((hR i i.2).1 γ' hγ')
        exact Subtype.ext (hu.unique ⟨hγ, he'⟩ ⟨hγ', by simp⟩)
      · rintro ⟨z, ⟨⟨_, k, rfl⟩, hz⟩⟩
        obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i i.2).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
        refine ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
        exact (QuotientGroup.eq.mpr hγk).trans ((hval k i).symm.trans (congrArg Subtype.val hz))
    exact ⟨Equiv.ofBijective f hbij, fun γ => rfl⟩
  rw [← Finset.sum_coe_sort s, ← Finset.sum_coe_sort s, Finset.sum_congr rfl
    (fun i _ => (hF i (y i) (a i) rfl).symm), hmain]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨e, he⟩ := horb i
  rw [← Fintype.card_congr e, Fintype.card_coe]
  congr 1
  rw [← Finset.sum_coe_sort (R i)]
  exact (Fintype.sum_equiv e _ _ (fun γ => (hF i _ _ (he γ)).symm)).symm

end CosetAvg
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransversalLeftTranslateInvariant
section
namespace GlobalTheory

theorem sum_transversal_left_translate_invariant :
    ∀ {G X : Type} [Group G] [AddCommMonoid X] (H K : Subgroup G) (R : Finset G) (f : G → X),
      (∀ r ∈ R, r ∈ H) → (∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K) →
      (∀ r ∈ H, ∀ c ∈ K, f (r * c) = f r) → ∀ k ∈ H, ∑ r ∈ R, f (k * r) = ∑ r ∈ R, f r := by
  intro G X _ _ H K R f hR hU hf k hk
  have hkH : ∀ a ∈ R, k * a ∈ H := fun a ha => H.mul_mem hk (hR a ha)
  refine Finset.sum_bij (fun a ha => Classical.choose (hU (k * a) (hkH a ha)).exists)
    (fun a ha => (Classical.choose_spec (hU (k * a) (hkH a ha)).exists).1) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ heq
    have h1 := (Classical.choose_spec (hU (k * a₁) (hkH a₁ ha₁)).exists).2
    have h2 := (Classical.choose_spec (hU (k * a₂) (hkH a₂ ha₂)).exists).2
    rw [heq] at h1
    set r' := Classical.choose (hU (k * a₂) (hkH a₂ ha₂)).exists
    have hm : a₁⁻¹ * a₂ ∈ K := by
      have := K.mul_mem (K.inv_mem h1) h2
      simpa [mul_assoc] using this
    have hu := (hU a₂ (hR a₂ ha₂)).unique (y₁ := a₁) (y₂ := a₂) ⟨ha₁, hm⟩ ⟨ha₂, by simpa using K.one_mem⟩
    exact hu
  · intro b hb
    have hb' : k⁻¹ * b ∈ H := H.mul_mem (H.inv_mem hk) (hR b hb)
    obtain ⟨a, ⟨ha, haK⟩, -⟩ := hU (k⁻¹ * b) hb'
    refine ⟨a, ha, ?_⟩
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    have hbK : b⁻¹ * (k * a) ∈ K := by
      have := K.inv_mem haK
      simpa [mul_assoc] using this
    exact (hU (k * a) (hkH a ha)).unique hs ⟨hb, hbK⟩
  · intro a ha
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    set r' := Classical.choose (hU (k * a) (hkH a ha)).exists
    have := hf r' (hR r' hs.1) (r'⁻¹ * (k * a)) hs.2
    rw [mul_inv_cancel_left] at this
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricFunctionInverseInvariant
section
namespace GlobalTheory

theorem exists_perm_of_univ_map_eq {ι β : Type} [Fintype ι] (g g' : ι → β)
    (h : Finset.univ.val.map g = Finset.univ.val.map g') :
    ∃ π : Equiv.Perm ι, ∀ i, g (π i) = g' i := by
  classical
  have hc : ∀ c, Fintype.card {i // g' i = c} = Fintype.card {i // g i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this.symm
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

theorem eq_of_perm_inv_invariant_of_multiset_eq :
    ∀ (m : ℕ) (f : (Fin m → ℂ) → ℂ), (∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) → (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧ ∀ i, f (Function.update α i (α i)⁻¹) = f α) → ∀ α α' : Fin m → ℂ, (∀ i, α i ≠ 0) → Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) = Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) → f α = f α' := by
  classical
  intro m f hf α α' hα h
  have hα' : ∀ i, α' i ≠ 0 := by
    intro i hi
    have hmem : (0 : ℂ) ∈ Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, hi⟩))
    rw [← h] at hmem
    rcases Multiset.mem_add.1 hmem with h1 | h1
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j hj
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j (inv_eq_zero.1 hj)
  have h2 := congrArg (Multiset.map (fun x : ℂ => x + x⁻¹)) h
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => (γ i)⁻¹ + γ i) = fun i => γ i + (γ i)⁻¹ :=
    fun γ => funext fun i => add_comm _ _
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => α i + (α i)⁻¹)
      = Finset.univ.val.map (fun i => α' i + (α' i)⁻¹) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    have h4 := hπ i
    have ha := hα (π i)
    have hb := hα' i
    have h5 : (α' i - α (π i)) * (α' i * α (π i) - 1) = 0 := by
      field_simp at h4
      linear_combination -h4
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact Or.inl (sub_eq_zero.1 h6)
    · exact Or.inr (eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h6))
  have hβ : ∀ i, (α ∘ π) i ≠ 0 := fun i => hα _
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      have hne : ∀ i, (fun i => if i ∈ s then α' i else (α ∘ π) i) i ≠ 0 := by
        intro i
        by_cases hi : i ∈ s
        · simpa [hi] using hα' i
        · simpa [hi] using hα (π i)
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf _ hne).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α hα).1 π, ← this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleSumPowMul
section
namespace GlobalTheory.TwoCocycle

theorem interchange {Γ D : Type} [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (a b x y : Γ) :
    c (a * b) (x * y) + c x y + c a b = c a x + c b y + c (a * x) (b * y) := by
  have h1 := hc a b (x * y)
  have h2 := hc b y x
  have h3 := hc a x (b * y)
  rw [mul_comm y x, hs y x, hs (b * y) x] at h2
  rw [mul_left_comm x b y] at h3
  linear_combination (norm := abel) h2 + h3 - h1

theorem sum_pow_mul (Γ D : Type) [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (n : ℕ) (x y : Γ) :
    ∑ i ∈ Finset.range n, c ((x * y) ^ i) (x * y) + n • c x y =
      ∑ i ∈ Finset.range n, c (x ^ i) x + ∑ i ∈ Finset.range n, c (y ^ i) y
        + c (x ^ n) (y ^ n) - c 1 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := interchange c hs hc (x ^ n) (y ^ n) x y
    rw [← mul_pow] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, succ_nsmul,
      pow_succ x, pow_succ y]
    linear_combination (norm := abel) ih + h

end GlobalTheory.TwoCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorInvolutionAlgebraProperties
section
namespace GlobalTheory

open IsLocalization in
theorem localFlat_dvd_descends : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ Q _ f b h
  set P : Ideal B := Q.comap (algebraMap B D) with hP
  let φ : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (algebraMap B D) rfl
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) := φ.toAlgebra
  have hφ : ∀ x : B, φ (algebraMap B (Localization.AtPrime P) x) = algebraMap B (Localization.AtPrime Q) x := by
    intro x
    simp [φ, Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
  have hfl : φ.Flat := RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) Q P rfl
  haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime Q) := hfl
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) :=
    (inferInstance : IsLocalHom φ)
  haveI : Module.FaithfullyFlat (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have key : algebraMap B (Localization.AtPrime P) b ∈
      (Ideal.span {f}).map (algebraMap B (Localization.AtPrime P)) := by
    rw [Ideal.map_span, Set.image_singleton,
      ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Localization.AtPrime Q)
        (Ideal.span {algebraMap B (Localization.AtPrime P) f}), Ideal.mem_comap,
      Ideal.map_span, Set.image_singleton]
    change φ _ ∈ Ideal.span {φ _}
    rw [hφ, hφ]; exact h
  obtain ⟨s, hs, h2⟩ := (algebraMap_mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P) _ b).1 key
  exact ⟨s, hs, h2⟩

end GlobalTheory
end


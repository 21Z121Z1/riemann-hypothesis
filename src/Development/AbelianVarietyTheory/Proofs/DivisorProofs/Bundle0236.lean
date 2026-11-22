import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotModEqOfLt
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem Reg.not_modEq_of_lt {q N k u v : ℕ} (hq : 2 ≤ q) (h : Reg q N k) (huv : u < v) (hv : v < u + N) :
    ¬ k * q ^ v ≡ k * q ^ u [MOD q ^ N - 1] := by
  intro hmod
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
  have hd0 : 0 < d := by omega
  have hdN : d < N := by omega
  have hN : 0 < N := by omega
  have hcop : Nat.Coprime (q ^ N - 1) (q ^ u) := by
    obtain ⟨t, ht⟩ : ∃ t, q ^ N = t + 1 := ⟨q ^ N - 1, by have := Nat.one_le_pow N q (by omega); omega⟩
    have h2 : Nat.Coprime (q ^ N - 1) (q ^ N) := by
      rw [ht, Nat.add_sub_cancel]
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right t)
    exact (h2.coprime_dvd_right (dvd_pow_self q hN.ne')).pow_right u
  have key : k * q ^ d ≡ k [MOD q ^ N - 1] := by
    apply Nat.ModEq.cancel_right_of_coprime (c := q ^ u) hcop
    have e : k * q ^ d * q ^ u = k * q ^ (u + d) := by ring
    rw [e]
    exact hmod
  exact h d hd0 hdN key

theorem reg_step_of_dvd : ∀ q l m k : ℕ, 2 ≤ q → 0 < l → 0 < m → Reg q (l * m) k →
    (∀ i, Reg (q ^ l) m (k * q ^ i)) ∧ (2 ≤ l * m → ∀ i, ¬ k * q ^ i ≡ 0 [MOD q ^ (l * m) - 1]) ∧
    ∀ i j a, i < l → j < l → a < m →
      (k * q ^ i * (q ^ l) ^ a ≡ k * q ^ j [MOD (q ^ l) ^ m - 1] ↔ i = j ∧ a = 0) := by
  intro q l m k hq hl hm h
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj0 hjm hmod
    simp only [← pow_mul] at hmod
    rw [mul_assoc, ← pow_add] at hmod
    have hlj : 0 < l * j := Nat.mul_pos hl hj0
    have hljm : l * j < l * m := (Nat.mul_lt_mul_left hl).mpr hjm
    exact Reg.not_modEq_of_lt hq h (by omega : i < i + l * j) (by omega : i + l * j < i + l * m) hmod
  · intro hlm i hmod
    have h1 : k * q ^ (i + 1) ≡ k * q ^ i [MOD q ^ (l * m) - 1] := by
      have e : k * q ^ (i + 1) = k * q ^ i * q := by ring
      rw [e]
      have h0 := hmod.mul_right q
      rw [zero_mul] at h0
      exact h0.trans hmod.symm
    exact Reg.not_modEq_of_lt hq h (by omega : i < i + 1) (by omega : i + 1 < i + l * m) h1
  · intro i j a hi hj ha
    constructor
    · intro hmod
      simp only [← pow_mul] at hmod
      rw [mul_assoc, ← pow_add] at hmod
      have hla : l * a + l ≤ l * m := by
        calc l * a + l = l * (a + 1) := by ring
          _ ≤ l * m := Nat.mul_le_mul_left l ha
      rcases lt_trichotomy (i + l * a) j with hlt | heq | hgt
      · exact absurd hmod.symm (Reg.not_modEq_of_lt hq h hlt (by omega))
      · rcases Nat.eq_zero_or_pos a with ha0 | ha0
        · subst ha0
          simp at heq
          exact ⟨heq, rfl⟩
        · have := Nat.le_mul_of_pos_right l ha0
          omega
      · exact absurd hmod (Reg.not_modEq_of_lt hq h hgt (by omega))
    · rintro ⟨rfl, rfl⟩
      simp [Nat.ModEq]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiEigenSublatticeFreeEqDifferentScaledStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piEigenSublattice_free_eq_differentScaled : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ = GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.flatLattice (r := r) a τ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ) := by
  first | exact @GlobalTheory.EigenSubFree.main | exact GlobalTheory.EigenSubFree.main | (intros; apply GlobalTheory.EigenSubFree.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicIsOfFinOrderOfFiniteInt
section
set_option autoImplicit false
open NumberField

namespace GlobalTheory.PicDom

theorem exists_int_mem_span {B : Type} [CommRing B] [IsDomain B] [Algebra.IsIntegral ℤ B] {d : B} (hd : d ≠ 0) :
    ∃ a : ℤ, a ≠ 0 ∧ (a : B) ∈ Ideal.span {d} := by
  have h := Ideal.comap_ne_bot_of_integral_mem hd (Ideal.mem_span_singleton_self d)
    (Algebra.IsIntegral.isIntegral (R := ℤ) d)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨a, ha0, by simpa using ha⟩

theorem isOfFinOrder_of_not_charZero (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (hc : ¬ CharZero B) (M : CommRing.Pic B) : IsOfFinOrder M := by
  have hp : ringChar B ≠ 0 := by
    intro h
    apply hc
    have : CharP B 0 := h ▸ ringChar.charP B
    exact CharP.charP_to_charZero B
  have hfin : Finite B := Module.finite_of_fg_torsion B fun x =>
    ⟨⟨(ringChar B : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, by
      change ((ringChar B : ℤ)) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, ringChar.Nat.cast_ringChar, zero_mul]⟩
  exact isOfFinOrder_of_finite M

variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]

theorem finiteDimensional_of_isFractionRing (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [CharZero K] :
    FiniteDimensional ℚ K := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
  have key : ∀ y : B, algebraMap B K y ∈
      Submodule.span ℚ (algebraMap B K '' (s : Set B)) := fun y => by
    have hy : y ∈ Submodule.span ℤ (s : Set B) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_zsmul]; exact zsmul_mem hx a
  classical
  refine Module.finite_def.2 ⟨s.image (algebraMap B K), ?_⟩
  rw [Finset.coe_image, eq_top_iff]
  intro x _
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
  have hdK : algebraMap B K d ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha0
  have : algebraMap B K b / algebraMap B K d =
      ((a : ℚ)⁻¹) • algebraMap B K (c * b) := by
    rw [Rat.smul_def, map_mul, Rat.cast_inv, Rat.cast_intCast]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    have hcK : algebraMap B K c ≠ 0 := by
      intro h; apply haK; rw [h2, h, zero_mul]
    rw [h2]
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ (key _)

end GlobalTheory.PicDom

namespace GlobalTheory.PicDom

variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]

theorem isOfFinOrder_of_numberField (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [NumberField K]
    (M : CommRing.Pic B) : IsOfFinOrder M := by
  let φ : B →+* 𝓞 K :=
    { toFun := fun b => ⟨algebraMap B K b, (Algebra.IsIntegral.isIntegral (R := ℤ) b).algebraMap⟩
      map_zero' := by ext; simp only [RingOfIntegers.map_mk, map_zero]
      map_one' := by ext; simp only [RingOfIntegers.map_mk, map_one]
      map_add' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_add]; rfl
      map_mul' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_mul]; rfl }
  have hφ : ∀ b, ((φ b : 𝓞 K) : K) = algebraMap B K b := fun b => rfl
  have hinj : Function.Injective φ := fun x y h => IsFractionRing.injective B K (by
    rw [← hφ, ← hφ, h])

  have hmul : ∀ ω : 𝓞 K, ∃ a : ℤ, a ≠ 0 ∧ (a : 𝓞 K) * ω ∈ φ.range := fun ω => by
    obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := B) (ω : K)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have hdK : algebraMap B K d ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
    refine ⟨a, ha0, c * b, ?_⟩
    apply RingOfIntegers.ext
    rw [hφ, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, ← hbd]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    rw [h2, mul_assoc]
    congr 1
    exact (mul_div_cancel₀ _ hdK).symm
  classical
  choose a ha0 ha using hmul
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ) (M := 𝓞 K)
  set N : ℤ := ∏ ω ∈ t, a ω
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun ω _ => ha0 ω
  have hNmem : ∀ x : 𝓞 K, (N : 𝓞 K) * x ∈ φ.range := fun x => by
    have hx : x ∈ Submodule.span ℤ (t : Set (𝓞 K)) := ht ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem ω hω =>
      show ((∏ ω ∈ t, a ω : ℤ) : 𝓞 K) * ω ∈ φ.range
      rw [← Finset.mul_prod_erase t a (Finset.mem_coe.1 hω), Int.cast_mul, mul_comm (a ω : 𝓞 K), mul_assoc]
      exact mul_mem (intCast_mem _ _) (ha ω)
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact zsmul_mem hx k
  have hn0 : N.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hN0
  have hcond : ∀ x : 𝓞 K, ((N.natAbs : ℕ) : 𝓞 K) * x ∈ φ.range := fun x => by
    rcases Int.natAbs_eq N with h | h
    · have := hNmem x
      rwa [h, Int.cast_natCast] at this
    · have := neg_mem (hNmem x)
      rwa [h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this
  haveI : Finite (CommRing.Pic (𝓞 K)) := Finite.of_equiv _ (ClassGroup.equivPic (𝓞 K)).toEquiv
  exact GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B (𝓞 K) φ N.natAbs hinj hn0 hcond M (isOfFinOrder_of_finite _)

theorem isOfFinOrder_of_charZero (M : CommRing.Pic B) : IsOfFinOrder M := by
  haveI : CharZero (FractionRing B) := IsFractionRing.charZero_of_isFractionRing B
  haveI : FiniteDimensional ℚ (FractionRing B) := finiteDimensional_of_isFractionRing B (FractionRing B)
  haveI : NumberField (FractionRing B) := ⟨⟩
  exact isOfFinOrder_of_numberField B (FractionRing B) M

end GlobalTheory.PicDom

theorem GlobalTheory.pic_isOfFinOrder_of_finite_int : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (M : CommRing.Pic B), IsOfFinOrder M := by
  intro B _ _ _ M
  by_cases hc : CharZero B
  · exact GlobalTheory.PicDom.isOfFinOrder_of_charZero B M
  · exact GlobalTheory.PicDom.isOfFinOrder_of_not_charZero B hc M
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirectedStatement
section
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsDirected (EtNbhd R) (· ≤ ·) := by
  first | exact @GlobalTheory.Henselisation.etNbhd_isDirected | exact GlobalTheory.Henselisation.etNbhd_isDirected | (intros; apply GlobalTheory.Henselisation.etNbhd_isDirected <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolUnitNeZero
section
noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam

def polUnit (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [single]⟩

@[simp] theorem polUnit_coe (d : ℕ) :
    ((polUnit d : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) = single (Sum.inl 0) (Sum.inr 0) 1 :=
  rfl

end GlobalTheory.ZarhinFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialGrowthOfPeriodicIntegralSpans
section
open Filter Topology

namespace GlobalTheory.StripGrowth

theorem int_coord_const (g m : ℕ) (U : Set ℂ) (hU : IsPreconnected U) (μ ν : ℂ → Fin m → Fin g → ℂ)
    (hμ : ContinuousOn μ U) (hν : ContinuousOn ν U) (hli : ∀ s ∈ U, LinearIndependent ℝ (μ s))
    (hn : ∀ s ∈ U, ∀ j, ∃ n : Fin m → ℤ, ν s j = ∑ i, n i • μ s i) :
    ∃ P : Fin m → Fin m → ℤ, ∀ s ∈ U, ∀ j, ν s j = ∑ i, P j i • μ s i := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨0, by simp⟩
  choose! n hnE using hn
  have key : ∀ j, ∀ s ∈ U, n s j = n s₀ j := by
    intro j
    have hcont : ContinuousOn (fun s i => ((n s j i : ℤ) : ℝ)) U := by
      refine GlobalTheory.T.continuousOn_coords_of_linearIndependent' g m U μ (fun s => ν s j) (fun s i => (n s j i : ℝ)) hμ ?_ hli ?_
      · exact (continuous_apply j).comp_continuousOn hν
      · intro s hs
        rw [hnE s hs j]
        simp [Int.cast_smul_eq_zsmul]
    have hcz : ContinuousOn (fun s => n s j) U := by
      rw [continuousOn_pi] at hcont ⊢
      intro i
      exact (Int.isUniformEmbedding_coe_real.isEmbedding.continuousOn_iff).2 (hcont i)
    intro s hs
    exact hU.constant hcz hs hs₀
  exact ⟨n s₀, fun s hs j => by rw [hnE s hs j, key j s hs]⟩

theorem strip_growth : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ), ContinuousOn lam {s : ℂ | s.re < 0} → (∀ s : ℂ, s.re < 0 → LinearIndependent ℝ (lam s)) → (∀ s : ℂ, s.re < 0 → ∀ z : Fin g → ℂ, (∃ n : Fin m → ℤ, z = ∑ j, n j • lam (s + 2 * Real.pi * Complex.I) j) ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lam s j) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  intro g m lam C k hcont hli hspan hB
  have hU : IsPreconnected {s : ℂ | s.re < 0} := (convex_halfSpace_re_lt 0).isPreconnected
  have hre : ∀ s : ℂ, (s + 2 * Real.pi * Complex.I).re = s.re := by intro s; simp
  have hshift : ContinuousOn (fun s => lam (s + 2 * Real.pi * Complex.I)) {s : ℂ | s.re < 0} :=
    hcont.comp (continuousOn_id.add continuousOn_const) (fun s hs => by
      simpa [Set.mem_setOf_eq, hre] using hs)
  have hli' : ∀ s ∈ {s : ℂ | s.re < 0}, LinearIndependent ℝ (lam (s + 2 * Real.pi * Complex.I)) :=
    fun s hs => hli _ (by simpa [hre] using hs)
  have hsingle : ∀ (v : Fin m → Fin g → ℂ) (j : Fin m), v j = ∑ i, (Pi.single j 1 : Fin m → ℤ) i • v i := by
    intro v j
    classical
    simp [Pi.single_apply]
  obtain ⟨P, hP⟩ := int_coord_const g m _ hU lam (fun s => lam (s + 2 * Real.pi * Complex.I)) hcont hshift
    (fun s hs => hli s hs) (fun s hs j => (hspan s hs _).1 ⟨Pi.single j 1, hsingle _ j⟩)
  obtain ⟨Q, hQ⟩ := int_coord_const g m _ hU (fun s => lam (s + 2 * Real.pi * Complex.I)) lam hshift hcont
    hli' (fun s hs j => (hspan s hs _).2 ⟨Pi.single j 1, hsingle _ j⟩)
  exact GlobalTheory.T.polyGrowth_strip_of_integral_monodromy g m lam C k P Q (fun s hs j => hP s hs j) (fun s hs j => hQ s hs j) hB

end GlobalTheory.StripGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNormMulSeminormSliceRLe
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceWeight

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] : ‖(inrL (V := V) κ κ')‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simp [inrL]
  | inr j => simpa [inrL] using norm_le_pi_norm y j

theorem norm_le_norm_elim_left {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (y : κ' → V) :
    ‖x‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inl j)

theorem iteratedFDeriv_sliceR_norm_le {κ κ' : Type} [Fintype κ] [Fintype κ']
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (n : ℕ) (y : κ' → V) :
    ‖iteratedFDeriv ℝ n (sliceR f x) y‖ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
  have hfun : (sliceR f x : (κ' → V) → ℂ) = (fun z => f (Sum.elim x 0 + z)) ∘ (inrL (V := V) κ κ') := by
    funext y'
    simp only [sliceR_apply, Function.comp_apply]
    exact congrArg f (congrFun (elim_eq_add (V := V) (κ' := κ') x) y')
  have hg : ContDiff ℝ ∞ (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) :=
    (f.smooth ⊤).comp (contDiff_const.add contDiff_id)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast le_top)]
  have h2 : iteratedFDeriv ℝ n (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) (inrL κ κ' y)
      = iteratedFDeriv ℝ n f (Sum.elim x y) := by
    rw [iteratedFDeriv_comp_add_left]
    congr 1
    exact (congrFun (elim_eq_add (V := V) (κ' := κ') x) y).symm
  rw [h2]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖(inrL (V := V) κ κ')‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
  calc _ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem pow_norm_mul_seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (a k n : ℕ) (x : κ → V) :
    ‖x‖ ^ a * SchwartzMap.seminorm ℂ k n (sliceR f x) ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
  have hpt : ∀ y : κ' → V, ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
      ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
    intro y
    have h1 := iteratedFDeriv_sliceR_norm_le f x n y
    have hx := norm_le_norm_elim_left x y
    have hy := norm_le_norm_elim x y
    calc ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
        ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ a * (‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ k
            * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖) := by gcongr
      _ = ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ (a + k) * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
          rw [pow_add, mul_assoc]
      _ ≤ _ := SchwartzMap.le_seminorm ℂ (a + k) n f _
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x) a) with h0 | hpos
  · rw [← h0, zero_mul]; exact apply_nonneg _ _
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ k n _ (div_nonneg (apply_nonneg _ _) hpos.le) fun y => ?_
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt y

end GlobalTheory.SliceWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveReductionOfFlatLift
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FlatLift

theorem projective_of_nilpotent_of_reduced_quotient (D : Type) [CommRing D] [IsArtinianRing D] (x : D) (hx : IsNilpotent x)
    (hr : IsReduced (D ⧸ Ideal.span {x})) (N : Type 1) [AddCommGroup N] [Module D N]
    [Module.Finite D N]
    (h : ∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) :
    Module.Projective D N := by
  have hflat : Module.Flat D N := by
    apply Module.flat_of_localized_maximal
    intro P _
    have hloc := GlobalTheory.T.localization_maximalIdeal_eq_span_nilpotent_artinian D x hx hr P
    have hann := GlobalTheory.T.localizedModule_mem_annSpan_smul_of_mem D P.primeCompl x N h
    haveI := GlobalTheory.T.free_of_principal_maximalIdeal_of_ker_smul_le' (Localization.AtPrime P) (algebraMap D _ x) hloc
      (LocalizedModule P.primeCompl N) inferInstance hann
    exact Module.Flat.trans D (Localization.AtPrime P) _
  haveI : Module.FinitePresentation D N := Module.finitePresentation_of_finite D N
  exact Module.Flat.projective_of_finitePresentation

theorem projective_reduction_of_flat_lift : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), Function.Surjective π → RingHom.ker π = Ideal.span {(p : Λ)} → (p : Λ) ^ 2 = 0 → (∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] 𝓞 F) M] [IsScalarTower Λ (Λ ⊗[ℤ] 𝓞 F) M], Module.Finite Λ M → Module.Free Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] 𝓞 F) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ M)) → Module.Projective (k ⊗[ℤ] 𝓞 F) N := by
  intro p _ F _ _ Λ _ k _ π hπ hker hp2 hann M _ _ _ _ hfin hfree N _ _ f hf hkerf
  have hpk : (p : k) = 0 := by
    have : (p : Λ) ∈ RingHom.ker π := by rw [hker]; exact Ideal.subset_span rfl
    simpa using this
  have hkerp := GlobalTheory.T.mem_span_smul_of_smul_eq_zero_of_free Λ (p : Λ) hann M hfree
  have hkerf' : ∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M) := by
    intro m hm; rw [← hker]; exact hkerf m hm
  obtain ⟨ϖ, z, hϖz, ⟨n0, hn0⟩, hred⟩ := GlobalTheory.T.exists_global_uniformizer_above_prime p F
  haveI : IsArtinianRing (k ⊗[ℤ] 𝓞 F) := IsArtinianRing.of_finite k (k ⊗[ℤ] 𝓞 F)
  haveI : Module.Finite (k ⊗[ℤ] 𝓞 F) N := GlobalTheory.T.finite_of_surjective_semilinear_tensor Λ k π (𝓞 F) M hfin N f hf
  have hnil : IsNilpotent ((1 : k) ⊗ₜ[ℤ] ϖ) := by
    refine ⟨n0, ?_⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hn0
    rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hy, mul_comm, ← nsmul_eq_mul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, mul_one, hpk,
      TensorProduct.zero_tmul]
  have hfinQ : Finite (𝓞 F ⧸ Ideal.span {(p : 𝓞 F), ϖ}) := by
    have hne : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by
      simp [Ideal.span_singleton_eq_bot, (Fact.out : p.Prime).ne_zero]
    haveI : Finite (𝓞 F ⧸ Ideal.span {(p : 𝓞 F)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective
      (Ideal.span_mono (by simp : ({(p : 𝓞 F)} : Set (𝓞 F)) ⊆ {(p : 𝓞 F), ϖ})))
  have hredD := GlobalTheory.T.isReduced_quot_tensor_of_reduced_mod_p (𝓞 F) k p ϖ hpk (GlobalTheory.T.isReduced_field_tensor_int_finite_reduced _ k)
  have hannN := GlobalTheory.T.annihilator_lift_of_mul_eq_p_alt p (𝓞 F) Λ k π hpk hp2 M hkerp N f hf hkerf' ϖ z hϖz
  exact projective_of_nilpotent_of_reduced_quotient _ _ hnil hredD N hannN

end GlobalTheory.FlatLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareSectionsGlueOfBasisStatement
section
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_sections_glue_of_basis : ∀ {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (B : Set X.Opens), (∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W) → (∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)), (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a = (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b) → GlobalTheory.PinchLift.Glues p i i' p' := by
  first | exact @GlobalTheory.PinchLift.glues_of_basis | exact GlobalTheory.PinchLift.glues_of_basis | (intros; apply GlobalTheory.PinchLift.glues_of_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
section
open IsLocalRing

namespace GlobalTheory

def PurityFree (R : Type) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 →
    (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
    Module.Free R A

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem QAll.of_dvd {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {p : ℂ → Prop} {f : ℍ → ℂ}
    (h0 : p 0) (hf : QAll p N f) : QAll p N' f := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, hpa⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, fun n => ?_⟩
  unfold spread
  split_ifs
  · exact hpa _
  · exact h0

theorem QConj.of_dvd {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {g : ℂ ≃+* ℂ} {f f' : ℍ → ℂ}
    (hf : QConj g N f f') : QConj g N' f f' := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, ha'⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, ?_⟩
  have key : (fun n => g (spread M a n)) = spread M (fun n => g (a n)) := by
    funext n
    unfold spread
    split_ifs <;> simp
  rw [key]
  exact hasQ_mul_spread N M f' _ hN hM ha'

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosedStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N → (∀ c ∈ R, QAll (· ∈ R) N fun _ => c) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ + g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ - g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ * g τ) ∧ (∀ f (k : ℕ), QAll (· ∈ R) N f → QAll (· ∈ R) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ), (∀ k ∈ s, QAll (· ∈ R) N (f k)) → (QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧ QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  first | exact @GlobalTheory.QFam.QAllSubring.ring_closed | exact GlobalTheory.QFam.QAllSubring.ring_closed | (intros; apply GlobalTheory.QFam.QAllSubring.ring_closed <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanImageSpan
section
open NumberField

noncomputable section

namespace GlobalTheory.Mem.R3.LiftForms

variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

theorem relSet_eq {n : ℕ} (S : Set (Fin n → K)) :
    {x' : Fin n → K' | ∃ x ∈ S, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = (fun x k => φ (x k)) '' S := by
  ext x'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, h⟩; exact ⟨x, hx, funext fun k => (h k k rfl).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, fun k k' hk => by rw [Fin.ext hk]⟩

theorem span_image_span {n : ℕ} (S : Set (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun x k => φ (x k)) '' (Submodule.span (𝓞 K) S : Set (Fin n → K))) =
      Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      rw [SetLike.mem_coe]
      convert Submodule.zero_mem (Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S)) using 1
      funext k; simp
    | add y z _ _ hy hz =>
      rw [SetLike.mem_coe] at hy hz ⊢
      convert Submodule.add_mem _ hy hz using 1; funext k; simp
    | smul a y _ hy =>
      rw [SetLike.mem_coe] at hy ⊢
      convert Submodule.smul_mem _ (RingOfIntegers.mapRingHom φ a) hy using 1
      funext k
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
      rfl
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem span_image_inf {n : ℕ} (X : Submodule (𝓞 K) (Fin n → K)) (V : Submodule K (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' (X : Set (Fin n → K))) ⊓
      (Submodule.span K' ((fun (x : Fin n → K) k => φ (x k)) '' (V : Set (Fin n → K)))).restrictScalars (𝓞 K') =
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) ''
      ((X ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  classical
  set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ
  set ψ : 𝓞 K →+* 𝓞 K' := RingOfIntegers.mapRingHom φ with hψdef
  have hψ : ∀ a : 𝓞 K, ((ψ a : 𝓞 K') : K') = φ (a : K) := fun a => rfl
  apply le_antisymm
  · rintro y ⟨hyX, hyV⟩

    let bQ := Module.finBasis K ((Fin n → K) ⧸ V)
    let ℓ : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → (Fin n → K) →ₗ[K] K := fun r => (bQ.coord r).comp V.mkQ
    have hℓV : ∀ x, x ∈ V ↔ ∀ r, ℓ r x = 0 := by
      intro x
      constructor
      · intro hx r
        simp [ℓ, (Submodule.Quotient.mk_eq_zero V).2 hx]
      · intro h
        have : V.mkQ x = 0 := bQ.ext_elem fun r => by simpa [ℓ] using h r
        exact (Submodule.Quotient.mk_eq_zero V).1 this
    let q : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → Fin n → K := fun r k => ℓ r (Pi.single k 1)
    have hℓ : ∀ r x, ℓ r x = ∑ k, q r k * x k := by
      intro r x
      rw [LinearMap.pi_apply_eq_sum_univ (ℓ r) x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hyℓ : ∀ r, ∑ k, φ (q r k) * y k = 0 := by
      intro r
      have key : ∀ z ∈ Submodule.span K' (Φ '' V), ∑ k, φ (q r k) * z k = 0 := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨x, hx, rfl⟩ := hw
          have h0 := (hℓV x).1 hx r
          rw [hℓ] at h0
          have := congrArg φ h0
          rw [map_sum, map_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
        | zero => simp
        | add a b _ _ ha hb => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
        | smul a b _ hb =>
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [show ∑ k, φ (q r k) * (a * b k) = a * ∑ k, φ (q r k) * b k by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hb, mul_zero]
      exact key y hyV
    obtain ⟨m, r0, g, hg⟩ := Submodule.mem_span_set'.1 hyX
    choose x hxX hx using fun i => (g i).2
    have hy : ∀ k, y k = ∑ i, (r0 i : K') * φ (x i k) := by
      intro k
      rw [← hg, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, ← hx i]
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
      (fun z : Fin m × Fin (Module.finrank K ((Fin n → K) ⧸ V)) => ℓ z.2 (x z.1))
    choose b hb using hd
    have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
      have := nonZeroDivisors.coe_ne_zero d
      exact_mod_cast this
    have hb' : ∀ i r, ((b (i, r) : 𝓞 K) : K) = ((d : 𝓞 K) : K) * ℓ r (x i) := fun i r => by
      have := hb (i, r)
      rw [Algebra.smul_def] at this
      exact this
    letI : Algebra (𝓞 K) (𝓞 K') := ψ.toAlgebra
    have hinj : Function.Injective ψ := fun a a' h => by
      have := congrArg (fun z : 𝓞 K' => (z : K')) h
      simp only [hψ] at this
      exact RingOfIntegers.ext (φ.injective this)
    haveI : Module.Flat (𝓞 K) (𝓞 K') := by
      rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
      rintro z ⟨a, ha⟩
      have ha' : ψ a * z = 0 := ha
      rcases mul_eq_zero.1 ha' with h | h
      · exact absurd (hinj (h.trans (map_zero ψ).symm)) (nonZeroDivisors.coe_ne_zero a)
      · exact h
    obtain ⟨N, a, yv, hr, ha⟩ := GlobalTheory.Proof.IdempotentLatticeSequence.flat_system (fun i r => b (i, r)) r0 (fun r => by
      apply RingOfIntegers.ext
      have h1 : ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, φ (b (i, r) : K) * (r0 i : K') := by
        rw [show ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, ((b (i, r) • r0 i : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      rw [h1]
      simp only [hb', map_mul]
      have h2 := hyℓ r
      simp only [hy, Finset.mul_sum] at h2
      rw [Finset.sum_comm] at h2
      change _ = (0 : K')
      rw [← mul_zero (φ ((d : 𝓞 K) : K)), ← h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hℓ, map_sum]
      simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring)
    let u : Fin N → Fin n → K := fun l => ∑ i, a i l • x i
    have huX : ∀ l, u l ∈ X := fun l => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxX i)
    have huV : ∀ l, u l ∈ V := by
      intro l
      rw [hℓV]
      intro r
      have h1 := congrArg (fun z : 𝓞 K => (z : K)) (ha l r)
      simp only [map_sum, map_mul, hb', map_zero] at h1
      apply mul_left_cancel₀ hd0
      rw [mul_zero, ← h1, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul_of_tower, Algebra.smul_def]
      ring
    have hyu : y = ∑ l, yv l • Φ (u l) := by
      funext k
      rw [hy, Finset.sum_apply]
      simp only [Pi.smul_apply, hΦ, u, Finset.sum_apply, map_sum, Algebra.smul_def]
      have h2 : ∀ i, ((r0 i : 𝓞 K') : K') = ∑ l, φ (a i l : K) * (yv l : K') := by
        intro i
        rw [hr i]
        rw [show ((∑ l, a i l • yv l : 𝓞 K') : K') = ∑ l, ((a i l • yv l : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      simp only [h2, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      change _ = (algebraMap (𝓞 K') K' (yv l)) * φ (((a i l) : K) * x i k)
      rw [map_mul]
      change φ (a i l : K) * (yv l : K') * φ (x i k) = (yv l : K') * (φ (a i l : K) * φ (x i k))
      ring
    rw [hyu]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u l, ⟨huX l, huV l⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxX, hxV⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨x, hxX, rfl⟩, Submodule.subset_span ⟨x, hxV, rfl⟩⟩

end GlobalTheory.Mem.R3.LiftForms

namespace GlobalTheory.Mem.R3.LiftForms
variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

theorem span_rel_inf {n n' : ℕ} (hn : n = n') (S : Set (Fin n → K)) (V : Submodule K (Fin n → K))
    (S' : Set (Fin n' → K')) (V' : Submodule K' (Fin n' → K'))
    (hS : S' = {x' | ∃ x ∈ S, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)})
    (hV : V' = Submodule.span K' {x' | ∃ x ∈ V, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    Submodule.span (𝓞 K') S' ⊓ V'.restrictScalars (𝓞 K') =
      Submodule.span (𝓞 K') {x' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
        ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)} := by
  subst hn hS hV
  have e1 : {x' : Fin n → K' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' (V : Set (Fin n → K)) := relSet_eq φ (V : Set (Fin n → K))
  have e2 : {x' : Fin n → K' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
      ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' ((Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) :
        Set (Fin n → K)) := relSet_eq φ _
  rw [relSet_eq, e1, e2, ← span_image_span φ S]
  exact span_image_inf φ _ V

end GlobalTheory.Mem.R3.LiftForms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem zsumR_eq_sum_toFinset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ)
    (h : (zerosIn χ t T).Finite) :
    zsumR χ t T f = ∑ ρ ∈ h.toFinset, (zmult χ ρ : ℝ) * f ρ := by
  unfold zsumR
  exact finsum_mem_eq_finite_toFinset_sum _ h

open Classical in

theorem sum_indicator_le_zsumR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (S : Finset ℂ)
    (h : (zerosIn χ t T).Finite) :
    ∑ ρ ∈ S, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ t T then 1 else 0) ≤ zsumR χ t T (fun _ => 1) := by
  rw [zsumR_eq_sum_toFinset χ t T _ h]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact h.mem_toFinset.mpr hx.2
  · intro x _ _
    exact Nat.cast_nonneg _

open Classical in

theorem recip_le_sum_windows {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) (ρ : ℂ)
    (hρ : ρ ∈ zerosIn χ 0 T) :
    (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0 : ℝ) ≤
      ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) +
        (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ (j : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (j : ℝ) 1 then 1 else 0) +
      (if ρ ∈ zerosIn χ (-(j : ℝ)) 1 then 1 else 0)) := by
    intro j
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg j))
    apply add_nonneg <;> split_ifs <;> norm_num
  by_cases h1 : 1 < |ρ.im|
  · rw [if_pos h1]
    obtain ⟨hre0, hre1, hT, hL⟩ := hρ
    rw [sub_zero] at hT
    have hk1 : 1 ≤ ⌊|ρ.im|⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact h1.le)
    have hkT : ⌊|ρ.im|⌋₊ ≤ ⌊T⌋₊ := Nat.floor_mono hT
    have hkle : (⌊|ρ.im|⌋₊ : ℝ) ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
    have hklt : |ρ.im| < ⌊|ρ.im|⌋₊ + 1 := Nat.lt_floor_add_one _
    have hkpos : (0 : ℝ) < ⌊|ρ.im|⌋₊ := by exact_mod_cast hk1
    have hind : (1 : ℝ) ≤ (if ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 then 1 else 0) +
        (if ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 then 1 else 0) := by
      rcases le_or_gt 0 ρ.im with him | him
      · have hmem : ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 := by
          refine ⟨hre0, hre1, ?_, hL⟩
          have hab : |ρ.im| = ρ.im := abs_of_nonneg him
          rw [abs_le]
          constructor <;> linarith
        rw [if_pos hmem]
        split_ifs <;> norm_num
      · have hmem : ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 := by
          refine ⟨hre0, hre1, ?_, hL⟩
          have hab : |ρ.im| = -ρ.im := abs_of_neg him
          rw [abs_le]
          constructor <;> linarith
        rw [if_pos hmem]
        split_ifs <;> norm_num
    calc 1 / ‖ρ‖ ≤ ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)⁻¹ := by
          rw [one_div]
          exact inv_anti₀ hkpos (hkle.trans (Complex.abs_im_le_norm ρ))
      _ ≤ ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 then 1 else 0) +
          (if ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 then 1 else 0)) :=
          le_mul_of_one_le_right (inv_nonneg.mpr hkpos.le) hind
      _ ≤ _ := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_Icc.mpr ⟨hk1, hkT⟩)
  · rw [if_neg h1]
    exact Finset.sum_nonneg (fun j _ => hnn j)

theorem zsumR_recip_le : GlobalTheory.Mem.An.ZeroCount → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T → zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) ≤ C * Real.log (q * T) ^ 2 ∧ zsumR χ 0 1 (fun _ => 1) ≤ C * Real.log (3 * q) := by
  classical
  rintro ⟨C0, hC0⟩
  set D := max C0 0 with hD
  have hD0 : 0 ≤ D := le_max_right _ _
  have hZ : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
      zsumR χ t 1 (fun _ => 1) ≤ D * Real.log (q * (|t| + 2)) := by
    intro q _ χ hχ t
    refine (hC0 q χ hχ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg ?_))
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    nlinarith [abs_nonneg t]
  refine ⟨12 * D, ?_⟩
  intro q _ χ hχ T hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine ⟨?_, ?_⟩
  · obtain ⟨hfin, _⟩ := GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order q χ 0 T
    have hfin' : ∀ t : ℝ, (zerosIn χ t 1).Finite := fun t => (GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order q χ t 1).1
    have hN1 : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
    have hNT : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
    have hNpos : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast hN1
    rw [zsumR_eq_sum_toFinset χ 0 T _ hfin]
    have hsplit : ∀ k : ℕ, ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ((k : ℝ)⁻¹ *
        ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0))) =
        (k : ℝ)⁻¹ * (∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) +
          ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
      intro k
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      ring
    have hLA : 0 ≤ Real.log (q * (T + 2)) := Real.log_nonneg (by nlinarith)
    calc ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0)
        ≤ ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ *
            ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          exact mul_le_mul_of_nonneg_left (recip_le_sum_windows χ T ρ (hfin.mem_toFinset.mp hρ))
            (Nat.cast_nonneg _)
      _ = ∑ k ∈ Icc 1 ⌊T⌋₊, ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ((k : ℝ)⁻¹ *
            ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0))) := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ * (2 * D * Real.log (q * (T + 2))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          have hkT : (k : ℝ) ≤ T := (Nat.cast_le.mpr hk'.2).trans hNT
          rw [hsplit k]
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg k))
          have e1 := (sum_indicator_le_zsumR χ (k : ℝ) 1 hfin.toFinset (hfin' _)).trans (hZ q χ hχ k)
          have e2 := (sum_indicator_le_zsumR χ (-(k : ℝ)) 1 hfin.toFinset (hfin' _)).trans
            (hZ q χ hχ (-(k : ℝ)))
          rw [abs_neg] at e2
          have hlog : Real.log (q * (|(k : ℝ)| + 2)) ≤ Real.log (q * (T + 2)) := by
            apply Real.log_le_log (by nlinarith [abs_nonneg (k : ℝ)])
            rw [abs_of_nonneg (Nat.cast_nonneg k)]
            nlinarith
          have := mul_le_mul_of_nonneg_left hlog hD0
          linarith
      _ = 2 * D * Real.log (q * (T + 2)) * ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ ≤ 2 * D * Real.log (q * (T + 2)) * (1 + Real.log T) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hLA)
          have h := harmonic_le_one_add_log ⌊T⌋₊
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
          have := Real.log_le_log hNpos hNT
          linarith
      _ ≤ 12 * D * Real.log (q * T) ^ 2 := by
          have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
          have hu : Real.log 2 ≤ Real.log (q * T) := Real.log_le_log (by norm_num) hqT
          have hl2 := Real.log_two_gt_d9
          have hA : Real.log (q * (T + 2)) ≤ 2 * Real.log (q * T) := by
            have h := Real.log_le_log (by nlinarith : (0 : ℝ) < q * (T + 2))
              (by nlinarith : (q : ℝ) * (T + 2) ≤ 2 * (q * T))
            rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by nlinarith : (0 : ℝ) < q * T))] at h
            linarith
          have hB : 1 + Real.log T ≤ 3 * Real.log (q * T) := by
            have := Real.log_le_log (by linarith : (0 : ℝ) < T) (by nlinarith : T ≤ (q : ℝ) * T)
            linarith
          have hB0 : 0 ≤ 1 + Real.log T := by
            have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
            linarith
          have h := mul_le_mul hA hB hB0 (by linarith)
          have h' := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * D)
          calc 2 * D * Real.log (q * (T + 2)) * (1 + Real.log T)
              = 2 * D * (Real.log (q * (T + 2)) * (1 + Real.log T)) := by ring
            _ ≤ 2 * D * (2 * Real.log (q * T) * (3 * Real.log (q * T))) := h'
            _ = 12 * D * Real.log (q * T) ^ 2 := by ring
  · have h := hZ q χ hχ 0
    rw [abs_zero, zero_add] at h
    refine h.trans ?_
    have h1 : Real.log (q * 2) ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
    have h2 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 hD0, mul_nonneg hD0 h2]

end GlobalTheory.Mem.An
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.ChiLaws

theorem infDiag_mul_finPart {L : Type} [Field L] [NumberField L] (k : Lˣ) :
    infDiag k * finPartI L (diagUnits L k) = diagUnits L k := by
  have h : ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
      ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem phase_sq {a u : ℂ} (ha : a ≠ 0) (h : u * starRingEnd ℂ a = a) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = u := by
  have hc : starRingEnd ℂ a ≠ 0 := by simpa using ha
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', div_eq_iff (mul_ne_zero ha hc)]
  linear_combination (-a) * h

theorem chi_laws (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (hχ : IsChiPsi H χ) :
    (∀ x ∈ UOT H, tildeD H χ x = 1) ∧
    (letI := H.cmStar; ∀ z : unitary H.E,
      ((tildeD H χ (e1T H z) : ℂˣ) : ℂ) = ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹) := by
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (GlobalTheory.T.unitaryDeterminantKernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v => (hχ.unr v).levelLe 1) (fun v _ => hχ.unr v)
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_UOT H).1 hx
    rw [tildeD_mk H hK]
    refine GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v y hy => ?_
    refine hχ.unr v y ?_
    unfold IsUnitAt
    rw [hy]
    exact ha v
  · letI := H.cmStar
    intro z
    obtain ⟨h1, h2⟩ := GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap R H
    obtain ⟨k, hk⟩ := h2 z
    rw [← h1 k z hk, tildeD_mk H hK]
    have e := congrArg χ.1 (infDiag_mul_finPart k)
    rw [map_mul, χ.2.2 k, mul_comm, mul_eq_one_iff_eq_inv] at e
    have hi : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _ := hχ.inf k
    rw [e, Units.val_inv_eq_inv_val, hi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine phase_sq ((map_ne_zero _).2 k.ne_zero) ?_
    have hc : embPsi H τ (H.conj (k : H.E)) = starRingEnd ℂ (embPsi H τ (k : H.E)) :=
      H.conjE_apply _ _
    rw [← hc]
    exact (map_mul (embPsi H τ) _ _).symm.trans (congrArg _ hk)

end GlobalTheory.Mem.ChiLaws
end
end


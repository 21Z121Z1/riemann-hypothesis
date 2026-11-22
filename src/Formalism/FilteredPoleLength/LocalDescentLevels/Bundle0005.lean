import Formalism.FilteredPoleLength.ReducedBasisBounds.Bundle0002
import Formalism.GelfandTransference.HadamardGelfand.Hadamard
import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0004
import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
import Formalism.FilteredPoleLength.LocalDescentLevels.MemSpanBasisFun
import Formalism.IncomingBounds.FlowDegreeBounds.IndexLastReductionHolds
import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0003
import Formalism.FilteredPoleLength.LocalDescentLevels.LatticeIndexBis

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.InvFromBlocksApplyZero
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Matrix MeasureTheory

theorem complexHadamard : ComplexHadamard := by
  intro n M A hA
  have h1 := Formalism.HadamardInequality.P.hadamard_inequality_holds n M.transpose
  rw [Matrix.det_transpose] at h1
  simp only [Matrix.transpose_apply] at h1
  have hprod : (∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2)) ^ 2 = ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ =>
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  refine ⟨?_, ?_⟩
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _) two_ne_zero).1 ?_
    rw [hprod]
    exact h1
  · have h2 := Formalism.HadamardInequality.P.hadamard_maximum_holds n M A hA
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA ⟨0, hn⟩ ⟨0, hn⟩)
    have h3 : ((Real.sqrt n * A) ^ n) ^ 2 = ((n : ℝ) * A ^ 2) ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [h3]
    exact h2

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LengthResidueFieldBase
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem filteredPoleLength : FilteredPoleLength := by
  intro O' Rr A _ _ _ _ _ _ _ _ _ _ x mm n F r h0 hn hF hinj hlen

  have hpow : ∀ k, k < n → ∀ m : ℕ, ∀ a ∈ F k, x ^ m • a ∈ F (k + 1) → a ∈ F (k + 1) := by
    intro k hk m
    induction m with
    | zero => intro a _ h; simpa using h
    | succ m ih =>
      intro a ha h
      refine ih a ha (hinj k hk _ ((F k).smul_mem _ ha) ?_)
      rwa [smul_smul, ← pow_succ']

  have hstrict : ∀ k, k ≤ n → ∀ a : A, x ^ mm • a ∈ F k → a ∈ F k := by
    intro k
    induction k with
    | zero => intro _ a _; rw [h0]; trivial
    | succ k ih =>
      intro hk a h
      exact hpow k hk mm a (ih (by omega) a (hF k hk h)) h
  set N : Submodule Rr A := (⊤ : Submodule Rr A).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A))
    with hN
  have hcap : ∀ k, k ≤ n → N ⊓ F k = (F k).map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A)) := by
    intro k hk
    ext b
    constructor
    · rintro ⟨⟨a, -, rfl⟩, hb⟩
      exact ⟨a, hstrict k hk a hb, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, trivial, rfl⟩, (F k).smul_mem _ ha⟩

  have hfl := filteredLength Rr A n (fun k => F (min k n)) (by simpa using h0) (by simpa using hn)
    (by
      intro k
      rcases lt_or_ge k n with hk | hk
      · simpa [min_eq_left hk.le, min_eq_left (Nat.succ_le_of_lt hk)] using hF k hk
      · simp [min_eq_right hk, min_eq_right (hk.trans (Nat.le_succ k))]) N
  have hsum : Module.length Rr (A ⧸ N) = (((∑ k ∈ Finset.range n, r k) * mm : ℕ) : ℕ∞) := by
    rw [hfl, Finset.sum_mul, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.mp hk
    rw [min_eq_left hk'.le, min_eq_left (Nat.succ_le_of_lt hk'), hcap k hk'.le]
    exact hlen k hk'
  rw [IsLocalRing.length_restrictScalars O' Rr (A ⧸ N), hsum]

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LevelsChain
section
namespace Formalism.LatticeBaseChangeAlt

open Module

theorem localStep : LocalStep := by
  intro O K V W _ _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' X NK
    hMl hΘl hNΘ hthM hthΘ hker hcM ha ha' hdet hXN hN₁ hZ hZm hρ hkρ himg hN₁' hAA hf1 hf2 hf3 V'
  have hp0 : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  have hsm : ∀ v : V, (algebraMap O K ϖ) ^ e • v = ϖ ^ e • v := by
    intro v
    rw [← map_pow, algebraMap_smul]

  have hIdx := Formalism.IncomingBounds.index_last_reduction_holds O K V ϖ hϖ (e : ℤ) M Θ hMl hΘl V'
  have hbridge : M.map ((((algebraMap O K ϖ) ^ (e : ℤ)) • LinearMap.id : V →ₗ[K] V).restrictScalars O)
      = X := by
    ext x
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, zpow_natCast, X, LinearMap.smul_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (hsm y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, hsm y⟩
  rw [hbridge] at hIdx

  have hLA := localAssembly O K V W ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a'
    hNΘ hthM hthΘ hker hcM ha ha' hdet hXN hN₁ hZ hZm hρ hkρ himg hN₁' hAA

  have hthX : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X := by
    intro j
    rw [hsm]
    exact ⟨th j, hthM j, rfl⟩
  have hcX : ∀ x ∈ X, ∀ i, ∃ u : O,
      c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K u := by
    rintro _ ⟨y, hy, rfl⟩ i
    obtain ⟨u, hu⟩ := hcM y hy i
    refine ⟨u, ?_⟩
    show c (ϖ ^ e • y) i = _
    rw [← hsm, map_smul, Pi.smul_apply, hu, smul_eq_mul, ← mul_assoc, sub_eq_add_neg,
      zpow_add₀ hp0, zpow_natCast]
  obtain ⟨m, -, hmle⟩ := quotientLength O K V ϖ hϖ n c _ hker X e be th hcX hthX a a' ha ha' hdet
  set q : ℤ := ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
      ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ) with hqdef
  have hq : 0 ≤ q := le_trans (Int.natCast_nonneg m) hmle

  set L1 := Module.length O (↥AA' ⧸ AA.comap AA'.subtype)
  set L2 := Module.length O (↥AA ⧸ N₁'.comap AA.subtype)
  set L3 := Module.length O (↥Zm ⧸ Z.comap Zm.subtype)
  set L := Formalism.LatticeIndexTer.qlen O V (X ⊔ Θ) Θ with hL
  have hLA' : L ≤ L1 + L2 + L3 + ((q.toNat : ℕ) : ℕ∞) := hLA
  have hsum : L1 + L2 + L3 + ((q.toNat : ℕ) : ℕ∞) =
      ((L1.toNat + L2.toNat + L3.toNat + q.toNat : ℕ) : ℕ∞) := by
    rw [← ENat.natCast_toNat hf1, ← ENat.natCast_toNat hf2, ← ENat.natCast_toNat hf3]
    simp only [ENat.toNat_natCast]
    push_cast; rfl
  rw [hsum] at hLA'
  have hLt : L.toNat ≤ L1.toNat + L2.toNat + L3.toNat + q.toNat := by
    have hLne : L ≠ ⊤ := ne_top_of_le_ne_top (by simp) hLA'
    rw [← ENat.natCast_toNat hLne] at hLA'
    exact_mod_cast hLA'
  have hqt : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq
  have : ((L.toNat : ℕ) : ℤ) ≤ (L1.toNat : ℤ) + (L2.toNat : ℤ) + (L3.toNat : ℤ) + q := by
    rw [← hqt]; exact_mod_cast hLt
  linarith

theorem levelsChain : LevelsChain := by
  intro ι _ ep f ν v νs c' T e hep hT hc' hv hν hcase
  apply levelsSum ι ep f (fun z => max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉) v T c'
  intro z
  have hpos : (0 : ℝ) < ep z := by exact_mod_cast hep z
  have h : ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) / ep z ≤ T * c' * v z := by
    rcases hcase with ⟨h1, h2⟩ | h3
    · exact poleOrderGood (ep z) T (ν z) νs c' (v z) e (hep z) hc' (hv z) (hν z) (h2 z) h1
    · subst h3
      exact poleOrderBad (ep z) T (ν z) νs c' (v z) (hep z) hT hc' (hv z) (hν z)
  rw [div_le_iff₀ hpos] at h
  linarith

end Formalism.LatticeBaseChangeAlt
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepDescent
section
namespace Formalism.LatticeBaseChangeAlt

theorem localStepDescent : LocalStepDescent :=
  localStepDescent_of finrank_span_image_alt inter_baseChange_lattice index_baseChange_lattice

end Formalism.LatticeBaseChangeAlt
end


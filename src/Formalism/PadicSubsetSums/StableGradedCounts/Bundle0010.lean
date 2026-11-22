import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
import Formalism.GaloisIrreducibility.NoSolvableTransitive
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0007
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0009
import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit
import Mathlib
import Formalism.ResultantValuation.ResultantAdjugateProofs.Bundle0001
import Formalism.ResultantValuation.ResultantAdjugateProofs.Bundle0002
import Formalism.ResultantValuation.Bundle0001
import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
import Formalism.ResultantValuation.PrimePairDyadicDisjointAlt

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRBBCard
section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem bad_primes_cardinality : BBCard := by
  classical
  intro g N hg
  set T : ℕ → Finset ℕ := fun d => (Finset.range (g ^ N + 1)).filter (fun l =>
    l.Prime ∧ g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) with hT
  have hTd : ∀ d ∈ Finset.Icc 1 N, (T d).card ≤ 3 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    apply Formalism.GaloisIrreducibility.bbAtMostThree g d (T d) hg hd.1
    · intro l hl
      simp only [hT, Finset.mem_filter] at hl
      exact hl.2.1
    · intro l hl
      simp only [hT, Finset.mem_filter] at hl
      have h1 : g ^ d < (l ^ padicValNat l (g ^ d - 1)) ^ 4 := by
        rw [← pow_mul, mul_comm]; exact hl.2.2
      have h2 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 = (g : ℝ) ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        have : (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = (d : ℝ) := by push_cast; ring
        rw [this, Real.rpow_natCast]
      have h3 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 <
          (((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ^ 4 := by
        rw [h2]; exact_mod_cast h1
      exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h3
  have hsub : (Finset.range (g ^ N + 1)).filter (fun l =>
      l.Prime ∧ ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) ⊆
      (Finset.Icc 1 N).biUnion T := by
    intro l hl
    simp only [Finset.mem_filter] at hl
    obtain ⟨hr, hp, d, hd, hlt⟩ := hl
    rw [Finset.mem_biUnion]
    exact ⟨d, hd, by simp only [hT, Finset.mem_filter]; exact ⟨hr, hp, hlt⟩⟩
  have hcard : ((Finset.Icc 1 N).biUnion T).card ≤ 3 * N := by
    calc ((Finset.Icc 1 N).biUnion T).card ≤ ∑ d ∈ Finset.Icc 1 N, (T d).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ Finset.Icc 1 N, 3 := Finset.sum_le_sum hTd
      _ = 3 * N := by simp [mul_comm]
  unfold BB
  calc _ ≤ _ + 1 := Finset.card_insert_le _ _
    _ ≤ 3 * N + 1 := by
      have := (Finset.card_le_card hsub).trans hcard
      convert Nat.add_le_add_right this 1

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRSamePartCount
section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem lpow_order_iff {G : Type*} [Monoid G] {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) (z : G)
    (hz : z ^ n = 1) : (∃ a : ℕ, z ^ (l ^ a) = 1) ↔ z ^ (l ^ padicValNat l n) = 1 := by
  constructor
  · rintro ⟨a, ha⟩
    have hg : z ^ (l ^ a).gcd n = 1 := pow_gcd_eq_one.2 ⟨ha, hz⟩
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow hl).1 (Nat.gcd_dvd_left (l ^ a) n)
    have hkn : l ^ k ∣ n := by
      rw [← hk']
      exact Nat.gcd_dvd_right _ _
    haveI := Fact.mk hl
    have hkv : k ≤ padicValNat l n := (padicValNat_dvd_iff_le hn).1 hkn
    obtain ⟨c, hc⟩ := pow_dvd_pow l hkv
    rw [hc, pow_mul, ← hk', hg, one_pow]
  · intro h
    exact ⟨_, h⟩

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TWCutOperator
section
namespace Formalism.IrreducibleCountingLemmas.TW

theorem asAlgebraHom_apply_eq_sum {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (x : MonoidAlgebra K G) (v : V) :
    ρ.asAlgebraHom x v = ∑ g ∈ x.coeff.support, x.coeff g • ρ g v := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply]
  rfl

theorem truncation_operator_holds : CutOperator := by
  intro O K _ _ _ _ _ _ _ G _ _ V _ _ _ _ ρ Msup U ψU e hM he hc v hv hψ
  have hcomm : ∀ (g : G) (x : MonoidAlgebra K G) (w : V), (∀ y, x * y = y * x) →
      ρ g (ρ.asAlgebraHom x w) = ρ.asAlgebraHom x (ρ g w) := by
    intro g x w hx
    rw [← Representation.asAlgebraHom_single_one ρ g, ← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul, hx]
  have hcA : ∀ y : MonoidAlgebra K G,
      ((Fintype.card G : K) • e) * y = y * ((Fintype.card G : K) • e) := by
    intro y
    rw [smul_mul_assoc, mul_smul_comm, hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [asAlgebraHom_apply_eq_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    have hint : IsIntegral ℤ ((Fintype.card G : K) * e.coeff g) :=
      central_idempotent_integral_twist K G e he hc g
    have hintO : IsIntegral O ((Fintype.card G : K) * e.coeff g) := hint.tower_top
    obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintO
    have : ((Fintype.card G : K) • e).coeff g = algebraMap O K o := by
      rw [ho, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rw [this, algebraMap_smul]
    exact Msup.smul_mem o (hM g v hv)
  · intro u
    rw [hcomm _ _ _ hcA, hψ u, map_smul]
  · rw [← Module.End.mul_apply, ← map_mul, mul_smul_comm, he]
  · intro hev
    rw [map_smul, LinearMap.smul_apply, hev]
  · intro T hT
    rw [asAlgebraHom_apply_eq_sum, asAlgebraHom_apply_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, hT]

end Formalism.IrreducibleCountingLemmas.TW
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TWIndexDet
section
open Module

namespace Formalism.IrreducibleCountingLemmas.TW

namespace Idx

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

theorem valuation_unique {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a : ℤ) (m : ℕ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a
      = algebraMap O K v * algebraMap O K ϖ ^ (a + (m : ℤ))) : m = 0 := by
  have hπ : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  rw [zpow_add₀ hπ, zpow_natCast, mul_comm (_ ^ a), ← mul_assoc] at h
  have h2 := mul_right_cancel₀ (zpow_ne_zero a hπ) h
  rw [← map_pow, ← map_mul] at h2
  have h3 := IsFractionRing.injective O K h2
  by_contra hm
  have : IsUnit (ϖ ^ m) := isUnit_of_mul_isUnit_right (h3 ▸ u.isUnit)
  exact hϖ.not_isUnit ((isUnit_pow_iff hm).1 this)

theorem val_unique {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a b : ℤ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a = algebraMap O K v * algebraMap O K ϖ ^ b) :
    a = b := by
  rcases le_total a b with hab | hab
  · obtain ⟨m, rfl⟩ := Int.le.dest hab
    have := valuation_unique hϖ u v a m h
    simp [this]
  · obtain ⟨m, rfl⟩ := Int.le.dest hab
    have := valuation_unique hϖ v u b m h.symm
    simp [this]

end Idx

theorem index_of_determinant : IndexDet := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ d b w ϖ u n hϖ hdet
  have hinj := IsFractionRing.injective O K
  have hπ : algebraMap O K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hu : algebraMap O K (u : O) ≠ 0 := (map_ne_zero_iff _ hinj).2 u.ne_zero
  have hne : b.det w ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hu (zpow_ne_zero _ hπ)
  have hb := (b.is_basis_iff_det).2 (isUnit_iff_ne_zero.2 hne)
  obtain ⟨wb, rfl⟩ : ∃ wb : Basis (Fin d) K V, ⇑wb = w :=
    ⟨Basis.mk hb.1 hb.2.ge, Basis.coe_mk _ _⟩
  have hB := Idx.isLat_span_basis (O := O) b
  have hW := Idx.isLat_span_basis (O := O) wb
  have hQ := Idx.isLat_inf hB hW
  obtain ⟨n', γ, hγ⟩ := Idx.exists_basis hQ
  have hn : n' = d := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 := Module.finrank_eq_card_basis γ
    simpa using h2.symm.trans h1
  subst hn
  obtain ⟨D1, hD1, l1⟩ := Idx.relLen_span_of_le (O := O) b γ (hγ ▸ inf_le_left)
    (b.isUnit_det γ).ne_zero
  obtain ⟨D2, hD2, l2⟩ := Idx.relLen_span_of_le (O := O) wb γ (hγ ▸ inf_le_right)
    (wb.isUnit_det γ).ne_zero
  have hD1ne : D1 ≠ 0 := by
    rintro rfl; rw [map_zero] at hD1; exact (b.isUnit_det γ).ne_zero hD1.symm
  have hD2ne : D2 ≠ 0 := by
    rintro rfl; rw [map_zero] at hD2; exact (wb.isUnit_det γ).ne_zero hD2.symm
  rw [Idx.sIdx_eq_sub hB hW hQ inf_le_left inf_le_right, ← hγ, l1, l2]
  obtain ⟨k1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD1ne hϖ
  obtain ⟨k2, u2, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD2ne hϖ
  rw [Idx.ord_unit_mul_pow hϖ, Idx.ord_unit_mul_pow hϖ, ENat.toNat_natCast, ENat.toNat_natCast]
  have hmul := b.det_mul_det wb γ
  rw [← hD1, ← hD2, hdet] at hmul
  have key : (k1 : ℤ) = n + k2 := by
    apply Idx.val_unique (K := K) hϖ u1 (u * u2)
    rw [zpow_add₀ hπ, zpow_natCast, zpow_natCast, Units.val_mul, map_mul]
    rw [map_mul, map_mul, map_pow, map_pow] at hmul
    rw [← hmul]; ring
  omega

end Formalism.IrreducibleCountingLemmas.TW
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.ZReuse
section
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem twist_invertible_holds : TwistInvertible := by
  intro k V _ _ _ _ γ₀ c hc hne
  let L : Module.End k V := c⁻¹ • γ₀ - 1
  have hL : ∀ v, L v = c⁻¹ • γ₀ v - v := fun v => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hL, sub_eq_zero] at hv
    have h2 : γ₀ v = c • v := by
      calc γ₀ v = c • (c⁻¹ • γ₀ v) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        _ = c • v := by rw [hv]
    by_contra hv0
    exact hne (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr h2, hv0⟩)
  have hbij : Function.Bijective L := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  exact hbij

theorem phi15_is_unit_holds : PrimitiveRootFifteenSubOneUnit := by
  intro R _ _ ζ hζ
  have hnp : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ 15 := by
    intro p hp k h
    have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (show 3 ∣ p ^ k by rw [h]; norm_num)
    have h5 : 5 ∣ p := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow (show 5 ∣ p ^ k by rw [h]; norm_num)
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    have e5 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).mp h5
    omega
  have hev : (Polynomial.cyclotomic 15 R).eval 1 = 1 := Polynomial.eval_one_cyclotomic_not_prime_pow hnp
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  have hmem : ζ ∈ primitiveRoots 15 R := (mem_primitiveRoots (by norm_num)).mpr hζ
  have hdvd : (1 - ζ) ∣ 1 := (Finset.dvd_prod_of_mem (fun μ => (1 : R) - μ) hmem).trans hev.dvd
  have hu : IsUnit (1 - ζ) := isUnit_of_dvd_one hdvd
  rw [show ζ - 1 = -(1 - ζ) by ring]
  exact hu.neg

theorem g5b_multiplicity_holds : UnitEvalOfMultiplicity := by
  intro O _ _ t c s' hs hmult
  have hmap : (s' * (X - C c) ^ t).map (IsLocalRing.residue O) =
      s'.map (IsLocalRing.residue O) * (X - C (IsLocalRing.residue O c)) ^ t := by
    simp
  have hs0 : s'.map (IsLocalRing.residue O) ≠ 0 := (hs.map _).ne_zero
  rw [hmap, Polynomial.rootMultiplicity_mul
    (mul_ne_zero hs0 (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))),
    Polynomial.rootMultiplicity_X_sub_C_pow] at hmult
  have h0 : (s'.map (IsLocalRing.residue O)).rootMultiplicity (IsLocalRing.residue O c) = 0 := by
    omega
  rw [Polynomial.rootMultiplicity_eq_zero_iff] at h0
  have hne : (s'.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O c) ≠ 0 :=
    fun e => hs0 (h0 e)
  rw [Polynomial.eval_map, Polynomial.eval₂_hom] at hne
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne

theorem same_residue_holds : SameResidue := by
  intro O _ _ X _ T hT a ha x y
  let ev : X → (T →+* IsLocalRing.ResidueField O) := fun z =>
    (IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) z).comp T.val.toRingHom)
  have hev : ∀ z (b : T), ev z b = IsLocalRing.residue O ((b : X → O) z) := fun z b => rfl
  have hsurj : ∀ z, Function.Surjective (ev z) := by
    intro z k
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective k
    exact ⟨algebraMap O T r, by rw [hev]; simp⟩
  have hmax : ∀ z, RingHom.ker (ev z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hmem : ((⟨a, ha⟩ : T) - algebraMap O T (a x)) ∈ RingHom.ker (ev x) := by
    rw [RingHom.mem_ker, map_sub, hev, hev]
    simp
  rw [hmax x, ← hmax y, RingHom.mem_ker, map_sub, hev, hev, sub_eq_zero] at hmem
  simpa using hmem.symm

end Formalism.IrreducibleCountingLemmas.Z
end


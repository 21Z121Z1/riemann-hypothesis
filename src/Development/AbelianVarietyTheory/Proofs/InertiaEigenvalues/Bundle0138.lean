import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueGaussIntegralNormForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0126
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsRootResidueCofactorUnramifiedExt
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResMult

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem not_isRoot_cofactor : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O,
    (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y =
      f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z) →
    ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic →
      r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree →
      p.natDegree = d * r.natDegree →
      p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) →
      ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := by
  intro K K' d φ hU s hgen p r c hp hr hrbar hdeg heq
  classical
  set φO := intMap hU with hφO
  have hspec : (algebraMap K'.O K'.E).comp φO = φ.comp (algebraMap K.O K.E) :=
    RingHom.ext fun a => intMap_spec hU a
  have hmax : ∀ a ∈ IsLocalRing.maximalIdeal K.O, φO a ∈ IsLocalRing.maximalIdeal K'.O := by
    intro a ha
    rw [← map_maximalIdeal hU]
    exact Ideal.mem_map_of_mem _ ha
  haveI : IsLocalHom φO := ⟨fun a ha => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).1 (hmax a ((IsLocalRing.mem_maximalIdeal _).2 h)) ha⟩
  let k := IsLocalRing.ResidueField K.O
  let k' := IsLocalRing.ResidueField K'.O
  let ψ : k →+* k' := IsLocalRing.ResidueField.map φO
  have hψ : ∀ a : K.O, ψ (IsLocalRing.residue K.O a) = IsLocalRing.residue K'.O (φO a) :=
    fun a => IsLocalRing.ResidueField.map_residue φO a
  letI : Algebra k k' := ψ.toAlgebra
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype k' := Fintype.ofFinite k'
  set Q := Fintype.card k with hQdef
  have hQ : Q = K.q ^ 2 := by rw [hQdef, ← Nat.card_eq_fintype_card]; exact K.card_res
  have hQ' : Fintype.card k' = Q ^ d := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (IsLocalRing.ResidueField K'.O) = _
    rw [K'.card_res, hU.1, hQ, ← pow_mul, ← pow_mul, mul_comm]
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hd : d ≠ 0 := hU.ne_zero
  set F := FiniteField.frobeniusAlgHom k k' with hF
  have hFpow : ∀ (i : ℕ) (x : k'), (F ^ i) x = x ^ (Q ^ i) := by
    intro i x
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom]
      show (x ^ Q ^ i) ^ Q = x ^ Q ^ (i + 1)
      rw [← pow_mul, ← pow_succ]

  have hrc : r * c = p.map φO := by
    apply Polynomial.map_injective _ (IsFractionRing.injective K'.O K'.E)
    rw [← heq, Polynomial.map_map, hspec]
  set sb := IsLocalRing.residue K'.O s with hsb
  set P := (r * c).map (IsLocalRing.residue K'.O) with hP
  have hP2 : P = (p.map (IsLocalRing.residue K.O)).map ψ := by
    rw [hP, hrc, Polynomial.map_map, Polynomial.map_map]
    congr 1
  have hPmon : P.Monic := by rw [hP2]; exact (hp.map _).map _
  have hP0 : P ≠ 0 := hPmon.ne_zero
  have hPdeg : P.natDegree = d * r.natDegree := by
    rw [hP2, (hp.map _).natDegree_map, hp.natDegree_map, hdeg]
  have hPmul : P = r.map (IsLocalRing.residue K'.O) * c.map (IsLocalRing.residue K'.O) := by
    rw [hP, Polynomial.map_mul]
  have hmu : rootMultiplicity sb P = r.natDegree + rootMultiplicity sb (c.map (IsLocalRing.residue K'.O)) := by
    rw [hPmul, rootMultiplicity_mul (hPmul ▸ hP0), hrbar, rootMultiplicity_X_sub_C_pow]

  have hconj : ∀ i : ℕ, rootMultiplicity sb P ≤ rootMultiplicity (sb ^ (Q ^ i)) P := by
    intro i
    have h := le_rootMultiplicity_map (f := ((F ^ i : k' →ₐ[k] k') : k' →+* k')) (p := P) ?_ sb
    · have hPFi : P.map ((F ^ i : k' →ₐ[k] k') : k' →+* k') = P := by
        rw [hP2, Polynomial.map_map]
        congr 1
        exact RingHom.ext fun x => (F ^ i).commutes x
      rw [hPFi] at h
      simpa [hFpow] using h
    · rw [hP2, Polynomial.map_map]
      have : ((F ^ i : k' →ₐ[k] k') : k' →+* k').comp ψ = ψ := RingHom.ext fun x => (F ^ i).commutes x
      rw [this, ← hP2]; exact hP0

  have hinj : ∀ i j, i < j → j < d → sb ^ (Q ^ i) ≠ sb ^ (Q ^ j) := by
    intro i j hij hjd h
    obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
    have hm : 0 < m := by omega
    have hfix : sb ^ (Q ^ m) = sb := by
      apply RingHom.injective ((F ^ i : k' →ₐ[k] k') : k' →+* k')
      rw [AlgHom.coe_toRingHom, hFpow, hFpow, h, ← pow_mul, pow_add, mul_comm]
    have hall : ∀ y : k', y ^ (Q ^ m) = y := by
      intro y
      obtain ⟨y', rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨f, z, hz, hy⟩ := hgen y'
      have hy' : y' = f.eval₂ φO s + z := by
        apply IsFractionRing.injective K'.O K'.E
        rw [hy, map_add, Polynomial.hom_eval₂, hspec]
      have hres : IsLocalRing.residue K'.O y' = f.eval₂ (ψ.comp (IsLocalRing.residue K.O)) sb := by
        rw [hy', map_add, (IsLocalRing.residue_eq_zero_iff z).2 hz, add_zero, Polynomial.hom_eval₂]
        congr 1
      have hev := Polynomial.hom_eval₂ f (ψ.comp (IsLocalRing.residue K.O))
        ((F ^ m : k' →ₐ[k] k') : k' →+* k') sb
      have hc : ((F ^ m : k' →ₐ[k] k') : k' →+* k').comp (ψ.comp (IsLocalRing.residue K.O)) =
          ψ.comp (IsLocalRing.residue K.O) := RingHom.ext fun a => (F ^ m).commutes (IsLocalRing.residue K.O a)
      rw [hc, AlgHom.coe_toRingHom, hFpow m sb, hfix, hFpow] at hev
      rw [hres]; exact hev
    have hQm : 1 < Q ^ m := Nat.one_lt_pow hm.ne' hQ1
    have hcard : Fintype.card k' ≤ Q ^ m := by
      have h1 := card_le_degree_of_subset_roots (p := (X ^ (Q ^ m) - X : k'[X])) (Z := Finset.univ) (by
        intro y _
        rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero (K' := k') hQm)]
        simp [IsRoot, hall y])
      rwa [FiniteField.X_pow_card_sub_X_natDegree_eq (K' := k') hQm, Finset.card_univ] at h1
    rw [hQ'] at hcard
    exact absurd hcard (not_le.2 (Nat.pow_lt_pow_right hQ1 (by omega)))

  let t : ℕ → k' := fun i => sb ^ (Q ^ i)
  have htinj : Set.InjOn t (Finset.range d) := by
    intro i hi j hj h
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (hinj i j h' (by simpa using hj))
    · exact h'
    · exact absurd h.symm (hinj j i h' (by simpa using hi))
  set S := (Finset.range d).image t with hSdef
  have hS : S.card = d := by rw [Finset.card_image_of_injOn htinj, Finset.card_range]
  have hsum1 : d * rootMultiplicity sb P ≤ ∑ x ∈ S, P.roots.count x := by
    calc d * rootMultiplicity sb P = ∑ _x ∈ S, rootMultiplicity sb P := by
          rw [Finset.sum_const, hS, smul_eq_mul]
      _ ≤ ∑ x ∈ S, P.roots.count x := Finset.sum_le_sum fun x hx => by
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
          rw [count_roots]; exact hconj i
  have hsum2 : ∑ x ∈ S, P.roots.count x ≤ Multiset.card P.roots := by
    calc ∑ x ∈ S, P.roots.count x ≤ ∑ x ∈ S ∪ P.roots.toFinset, P.roots.count x :=
          Finset.sum_le_sum_of_subset Finset.subset_union_left
      _ = ∑ x ∈ P.roots.toFinset, P.roots.count x :=
          (Finset.sum_subset Finset.subset_union_right fun x _ hx =>
            Multiset.count_eq_zero.2 (by simpa using hx)).symm
      _ = Multiset.card P.roots := Multiset.toFinset_sum_count_eq _
  have hle : d * rootMultiplicity sb P ≤ d * r.natDegree :=
    hsum1.trans (hsum2.trans ((card_roots' P).trans hPdeg.le))
  have hle' := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hd)
  have hc0 : c.map (IsLocalRing.residue K'.O) ≠ 0 := right_ne_zero_of_mul (hPmul ▸ hP0)
  intro hroot
  have := (rootMultiplicity_pos hc0).2 hroot
  omega

end GlobalTheory.UnitLemma.Unr.ResMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LiftExp

variable {l : ℕ} [hl : Fact l.Prime]

theorem one_add_pow_expand (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∃ r : ℚ_[l], ‖r‖ ≤ 1 ∧
      (1 + x) ^ n - 1 = n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r) := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr, h⟩ := ih
    refine ⟨(n.choose 2 : ℕ) + (r + x * r), ?_, ?_⟩
    · refine (Padic.nonarchimedean _ _).trans (max_le ?_ ((Padic.nonarchimedean _ _).trans
        (max_le hr ?_)))
      · exact IsUltrametricDist.norm_natCast_le_one _ _
      · rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hr
    · have h2 : (1 + x) ^ n = 1 + (n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r)) := by
        rw [← h]; ring
      rw [pow_succ, h2, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
      push_cast
      ring

theorem norm_add_of_lt {a b : ℚ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [Padic.add_eq_max_of_ne h.ne', max_eq_left h.le]

theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt

theorem zpow_lt {a b : ℤ} (h : a < b) : (l : ℝ) ^ a < (l : ℝ) ^ b :=
  zpow_lt_zpow_right₀ one_lt_l h

theorem norm_pow_sub_one_of (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (e c : ℤ) (hn : ‖(n : ℚ_[l])‖ = (l : ℝ) ^ (-e))
    (hc : ‖((n.choose 2 : ℕ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-c)) (h1 : e < c + j) (h2 : e < 2 * j) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
  have hl0 : (l : ℝ) ≠ 0 := (zero_lt_one.trans one_lt_l).ne'
  have hx : ‖u - 1‖ ≤ 1 := by
    rw [hu]; exact zpow_le_one_of_nonpos₀ one_lt_l.le (by omega)
  obtain ⟨r, hr, h⟩ := one_add_pow_expand (u - 1) hx n
  rw [add_sub_cancel] at h
  have hm : ‖(n : ℚ_[l]) * (u - 1)‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
    rw [norm_mul, hn, hu, ← zpow_add₀ hl0]; congr 1; ring
  rw [h, norm_add_of_lt, hm]
  rw [hm]
  refine (Padic.nonarchimedean _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ (l : ℝ) ^ (-c) * ((l : ℝ) ^ (-(j : ℤ))) ^ 2 := by gcongr
      _ = (l : ℝ) ^ (-c + (-(j : ℤ)) * 2) := by
        rw [zpow_add₀ hl0, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ ((l : ℝ) ^ (-(j : ℤ))) ^ 3 * 1 := by gcongr
      _ = (l : ℝ) ^ ((-(j : ℤ)) * 3) := by
        rw [mul_one, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)

theorem norm_pow_coprime (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (hn : ¬ l ∣ n) : ‖u ^ n - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by
  have := norm_pow_sub_one_of j hj u hu n 0 0
    (by
      rw [neg_zero, zpow_zero, Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
    (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
    (by omega) (by omega)
  simpa using this

theorem norm_pow_prime (j : ℕ) (hj : Lev l j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ l - 1‖ = (l : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) := by
  have hn : ‖(l : ℚ_[l])‖ = (l : ℝ) ^ (-(1 : ℤ)) := by simp
  have hj1 := hj.1
  push_cast
  by_cases h2 : l = 2
  · have := hj.2 h2
    exact norm_pow_sub_one_of j hj.1 u hu l 1 0 hn
      (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
      (by omega) (by omega)
  · have h3 : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h2)
    obtain ⟨m, hm⟩ := hl.out.dvd_choose_self (k := 2) two_ne_zero h3
    refine norm_pow_sub_one_of j hj.1 u hu l 1 1 hn ?_ (by omega) (by omega)
    rw [hm, Nat.cast_mul, norm_mul, hn]
    exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)

theorem norm_pow_prime_pow (a : ℕ) (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ (l ^ a) - 1‖ = (l : ℝ) ^ (-((j + a : ℕ) : ℤ)) := by
  induction a with
  | zero => simpa using hu
  | succ a ih =>
    have h : Lev l (j + a) := ⟨by have := hj.1; omega, fun h => by have := hj.2 h; omega⟩
    rw [pow_succ, pow_mul]
    exact norm_pow_prime (j + a) h _ ih

theorem norm_pow_nat (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (n : ℕ) (hn : n ≠ 0) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValNat l n : ℤ))) := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [padicValNat.mul (pow_ne_zero _ hl.out.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, pow_mul,
    norm_pow_coprime (j + a) (by have := hj.1; omega) _ (norm_pow_prime_pow a j hj u hu) m hm]
  push_cast
  simp

theorem norm_zpow_sub_one : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l],
    ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 →
      ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  intro l _ j hj u hu k hk
  have hu1 : ‖u‖ = 1 := by
    have h : ‖u - 1‖ < ‖(1 : ℚ_[l])‖ := by
      rw [hu, norm_one]
      exact zpow_lt_one_of_neg₀ one_lt_l (by have := hj.1; omega)
    have := norm_add_of_lt h
    simpa using this
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have key := norm_pow_nat j hj u hu k.natAbs (Int.natAbs_ne_zero.2 hk)
  unfold padicValInt
  rw [← key]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp
  · rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have : (u ^ n)⁻¹ - 1 = -((u ^ n - 1) * (u ^ n)⁻¹) := by field_simp; ring
    rw [this, norm_neg, norm_mul, norm_inv, norm_pow, hu1]; simp

end GlobalTheory.Cyc.LiftExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurent
section
open GlobalTheory.NL

namespace GlobalTheory.NL.Twist

variable {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M]

theorem conv_mem_of_forall (w : PowerSeries L) (g : ℤ → M) (S : Submodule L M) (j : ℤ)
    (h : ∀ i : ℕ, g (j - i) ∈ S) : conv w g j ∈ S := by
  unfold conv
  exact finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem)
    (fun i => S.smul_mem _ (h i))

theorem conv_eq_sum (w : PowerSeries L) (g : ℤ → M) (m : ℤ) (hg : ∀ j < m, g j = 0) (k : ℤ) :
    conv w g k = ∑ i ∈ Finset.range ((k - m).toNat + 1), PowerSeries.coeff i w • g (k - i) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push_neg at hc
  apply hi
  have : g (k - i) = 0 := hg _ (by omega)
  simp [this]

theorem tri (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M) (hSub : Monotone Sub) (y : ℕ)
    (f : ℤ → M) (hf : ∃ m : ℤ, ∀ j < m, f j = 0) (hfS : ∀ j, f j ∈ Sub j) (k : ℤ)
    (hk : ∀ j < k, f j ∈ Sub (j - y)) :
    (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧
    (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧
    (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧
    conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  obtain ⟨m, hm⟩ := hf
  have hg : ∀ j < m, (fun m => u ^ m • f m) j = 0 := fun j hj => by simp [hm j hj]
  refine ⟨⟨m, fun j hj => ?_⟩, fun j => ?_, fun j hj => ?_, ?_⟩
  · refine (Submodule.mem_bot L).1 (conv_mem_of_forall w _ ⊥ j (fun i => ?_))
    rw [hm _ (by omega), smul_zero]
    exact Submodule.zero_mem _
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) ≤ j) (hfS _)))
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) - y ≤ j - y) (hk _ (by omega))))
  · rw [conv_eq_sum w _ m hg k, Finset.sum_range_succ']
    have h0 : PowerSeries.coeff 0 w • (u ^ (k - ((0 : ℕ) : ℤ)) • f (k - ((0 : ℕ) : ℤ))) -
        (PowerSeries.constantCoeff w * u ^ k) • f k = 0 := by
      simp [mul_smul]
    rw [add_sub_assoc, h0, add_zero]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))
    exact hSub (by omega : k - ((i + 1 : ℕ) : ℤ) - y ≤ k - y) (hk _ (by omega))

end GlobalTheory.NL.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilUnipotentTorusPreserveTestStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticWeil_unipotent_torus_preserve_test : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → (∀ z, IsTest (nOp A ψ x z φ)) ∧ ∀ s, IsTest (mOp A ω s φ) := by
  first | exact @GlobalTheory.JR.WeilQuad.isTest_nOp_mOp | exact GlobalTheory.JR.WeilQuad.isTest_nOp_mOp | (intros; apply GlobalTheory.JR.WeilQuad.isTest_nOp_mOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationIndexEqOneOfAdjoinRangeEqTop
section
open ValuativeRel

namespace GlobalTheory

open GroundTheory.LocalField IntermediateField

theorem ramificationIndex_eq_one_of_adjoin_range_eq_top (F E K L : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L]
    [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension K L]
    [FiniteDimensional F E] [FiniteDimensional K L] :
    GroundTheory.LocalField.ramificationIndex F E = 1 →
      Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
        GroundTheory.LocalField.ramificationIndex K L = 1 := by
  intro he hadj
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he
  set m := Nat.card 𝓀[E] - 1 with hm_def
  have hmE : (m : 𝓀[E]) ≠ 0 := natCast_card_residueField_sub_one_ne_zero E
  have hmF : (m : 𝓀[F]) ≠ 0 := fun h0 ↦ hmE (by rw [← map_natCast (algebraMap 𝓀[F] 𝓀[E]), h0, map_zero])
  have hmK : (m : 𝓀[K]) ≠ 0 := fun h0 ↦ hmF ((algebraMap 𝓀[F] 𝓀[K]).injective (by rw [map_natCast, h0, map_zero]))
  have hζ' : IsPrimitiveRoot (algebraMap E L ζ) m := hζ.map_of_injective (algebraMap E L).injective
  have hE : Set.range (algebraMap E L) ⊆ Algebra.adjoin K {algebraMap E L ζ} := by
    rintro _ ⟨e, rfl⟩
    have he' : e ∈ Algebra.adjoin F {ζ} := by
      rw [algebra_adjoin_eq_top_of_adjoin_eq_top htop]; trivial
    have h1 : algebraMap E L e ∈ (Algebra.adjoin F {ζ}).map (IsScalarTower.toAlgHom F E L) :=
      ⟨e, he', rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h1
    have h2 : Algebra.adjoin F {(IsScalarTower.toAlgHom F E L) ζ} ≤
        (Algebra.adjoin K {algebraMap E L ζ}).restrictScalars F :=
      Algebra.adjoin_le (by simpa using Algebra.subset_adjoin (R := K) (s := {algebraMap E L ζ}))
    exact h2 h1
  have hadjK : Algebra.adjoin K {algebraMap E L ζ} = ⊤ := by
    rw [eq_top_iff, ← hadj]
    exact Algebra.adjoin_le hE
  have htopK : K⟮algebraMap E L ζ⟯ = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff (F := K) (E := L)).mpr hadjK
  exact ramificationIndex_eq_one_of_adjoin_eq_top hζ' hmK htopK

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalizedStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : Fin s → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    Nonempty ((relJacD e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) := by
  first | exact @GlobalTheory.JacStages.relJacD_piTensor_equiv | exact GlobalTheory.JacStages.relJacD_piTensor_equiv | (intros; apply GlobalTheory.JacStages.relJacD_piTensor_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueGaussIntegralNormFormStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_gauss_integral_norm_form : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → IsField A.K → IsField A.L → ∀ (O : Subring A.L) (ϖ : A.Kˣ), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) → μ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} = ENNReal.ofReal (A.absK (ϖ : A.K) ^ 2) * μ (O : Set A.L) → ∀ a : A.K, (∀ s : A.K, algebraMap A.K A.L s ∈ O → A.psiK ψ (a * ϖ * s) = 1) → (∃ s : A.K, algebraMap A.K A.L s ∈ O ∧ A.psiK ψ (a * s) ≠ 1) → ∫ y in (O : Set A.L), A.psiK ψ (a * A.NL y) ∂μ = -((A.absK (ϖ : A.K) : ℝ) : ℂ) * (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.JR.ResidueGauss.residue_gauss_integral | exact GlobalTheory.JR.ResidueGauss.residue_gauss_integral | (intros; apply GlobalTheory.JR.ResidueGauss.residue_gauss_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversionStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → (∃! μ : Measure V, SelfDual μ (fun x y => ψ (β x y))) ∧ ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ f, IsTest f → IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  first | exact @GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest | exact GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest | (intros; apply GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearMatrixComm
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

theorem semilinear_matrix_comm {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] {r : ℕ}
    (σ τ : A →+* A) (f g : D →+ D) (hf : ∀ a x, f (a • x) = σ a • f x)
    (hg : ∀ a x, g (a • x) = τ a • g x) (hc : ∀ x, f (g x) = g (f x))
    (b : Fin r → D) (hb : LinearIndependent A b) (e : A) (P Q : Fin r → Fin r → A)
    (hQ : ∀ k, g (b k) = ∑ m, Q m k • b m) (hP : ∀ k, e • f (b k) = ∑ m, P m k • b m)
    (p k : Fin r) :
    e * ∑ m, Q p m * τ (P m k) = τ e * ∑ m, P p m * σ (Q m k) := by
  have h1 : τ e • g (f (b k)) = ∑ p, (∑ m, Q p m * τ (P m k)) • b p := by
    rw [← hg, hP, map_sum]
    simp only [hg, hQ, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h2 : e • f (g (b k)) = ∑ p, (∑ m, P p m * σ (Q m k)) • b p := by
    rw [hQ, map_sum, Finset.smul_sum]
    simp only [hf, smul_comm e, hP, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h3 : ∑ p, (e * ∑ m, Q p m * τ (P m k)) • b p
      = ∑ p, (τ e * ∑ m, P p m * σ (Q m k)) • b p := by
    simp only [mul_smul, ← Finset.smul_sum]
    rw [← h1, ← h2, hc, smul_comm]
  exact (Fintype.linearIndependent_iffₛ.1 hb) _ _ h3 p

theorem matrices_comm : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∀ (M : ℕ) (Φ Gm : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧), (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (Gm i m k) : LetA O n) • (b m : W.DD T)) → (∀ k, (fun _ => j R.E : LetA O n) ^ M • W.φD T (b k : W.DD T) = ∑ m, (fun i => j (Φ i m k) : LetA O n) • (b m : W.DD T)) → ∀ i, R.E ^ M • (Gm i * (Φ i).map R.γ) = R.γ R.E ^ M • (Φ i * (Gm (i - 1)).map R.φ) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF _ _ M Φ Gm hG hΦ i
  obtain ⟨hj, -, hφ, hγ, -⟩ := hF
  have hb : LinearIndependent (LetA O n) (fun k => (b k : W.DD T)) :=
    b.linearIndependent.map' (W.N T).subtype (Submodule.ker_subtype _)
  have key := semilinear_matrix_comm (A := LetA O n) (letφ (n := n) W.φ₀).toRingHom
    (letγ (n := n) (W.γ₀ W.gam)).toRingHom (W.φD T).toAddMonoidHom (W.γD T W.gam).toAddMonoidHom
    (fun a x => by
      change W.φD T (a • x) = letφ W.φ₀ a • W.φD T x
      rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul])
    (fun a x => by
      change W.γD T W.gam (a • x) = letγ (W.γ₀ W.gam) a • W.γD T W.gam x
      rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul])
    (fun x => W.φγ_comm T W.gam x) _ hb ((fun _ => j R.E : LetA O n) ^ M)
    (fun m k i => j (Φ i m k)) (fun m k i => j (Gm i m k)) hG hΦ
  ext1 p k
  apply hj
  have h := congrFun (key p k) i
  simp only [Pi.mul_apply, Finset.sum_apply, Pi.pow_apply, map_pow] at h
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow,
    map_sum, hφ, hγ]
  exact h

end GlobalTheory.WachTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityLatticeCountRelationStatement
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senMultiplicity_lattice_count_relation : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ s : ℕ, P ≤ sh (-s) Q → ∀ x : k, sen g P x + qmult g P Q (x + 1) = sen g Q x + qmult g P Q x ∧ (qmult g P Q x ≠ 0 → ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ sen g Q (x - j) ≠ 0) := by
  first | exact @GlobalTheory.PhiGam.Count.sen_count | exact GlobalTheory.PhiGam.Count.sen_count | (intros; apply GlobalTheory.PhiGam.Count.sen_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralMulNormStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  first | exact @GlobalTheory.JR.WeilQuad.GaussTrans.main | exact GlobalTheory.JR.WeilQuad.GaussTrans.main | (intros; apply GlobalTheory.JR.WeilQuad.GaussTrans.main <;> assumption)
end


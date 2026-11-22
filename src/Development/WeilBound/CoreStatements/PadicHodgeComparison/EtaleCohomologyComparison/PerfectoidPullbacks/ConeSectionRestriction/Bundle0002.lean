import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsAwayIsDomainOfSmooth
section
set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem exists_away_isDomain_of_smooth {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime] :
    ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  obtain ⟨ι, σ, _, _, ⟨Pr⟩⟩ := hstd.out
  haveI : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension K (Localization.Away g) :=
    ⟨⟨ι, σ, ‹_›, ‹_›, Pr, rfl⟩⟩
  obtain ⟨φ, hφ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    (n := Pr.dimension) (R := K) (S := Localization.Away g)
  letI : Algebra (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := φ.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := hφ
  haveI hq : (p.map (algebraMap A (Localization.Away g))).IsPrime := by
    apply IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ _ ‹_›
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  obtain ⟨g', hg', hdom⟩ := exists_away_isDomain_of_etale
    (P := MvPolynomial (Fin Pr.dimension) K) (A := Localization.Away g)
    (p.map (algebraMap A (Localization.Away g)))
  refine ⟨g * (IsLocalization.Away.sec g g').1, ?_, ?_⟩
  · refine Ideal.IsPrime.mul_notMem ‹_› hg fun hmem => hg' ?_
    rw [Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g g').symm]
    exact Ideal.mem_map_of_mem (algebraMap A (Localization.Away g)) hmem
  · intro S _ _ _
    haveI : IsLocalization.Away (g * (IsLocalization.Away.sec g g').1) (Localization.Away g') :=
      .mul_of_associated _ _ g' <| IsLocalization.Away.associated_sec_fst g g'
    let e : S ≃ₐ[A] Localization.Away g' :=
      IsLocalization.algEquiv (Submonoid.powers (g * (IsLocalization.Away.sec g g').1)) S
        (Localization.Away g')
    exact e.toRingEquiv.toMulEquiv.isDomain

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RaTpowSinglePow
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] {n : ℕ}

def fldF (K : Type) [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ) :
    IntermediateField K (FractionRing R) :=
  IntermediateField.adjoin K (Set.range fun k => algebraMap R (FractionRing R) (t k : R))

theorem ra_tpow_add {d : ℕ} (t : Fin d → Rˣ) (m m' : Fin d → ℤ) : tpow t (m + m') = tpow t m * tpow t m' := by
  simp only [tpow, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]

theorem ra_tpow_zero {d : ℕ} (t : Fin d → Rˣ) : tpow t 0 = 1 := by
  simp [tpow]

theorem ra_tpow_single {d : ℕ} (t : Fin d → Rˣ) (k : Fin d) (z : ℤ) : tpow t (Pi.single k z) = ((t k ^ z : Rˣ) : R) := by
  unfold tpow
  rw [Finset.prod_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp

theorem ra_unit_pow_eq {d : ℕ} (t : Fin d → Rˣ) (k : Fin d) (N : ℕ) :
    (t k : R) ^ N = tpow t (Pi.single k (N : ℤ)) := by
  rw [ra_tpow_single, zpow_natCast, Units.val_pow_eq_pow_val]

theorem ra_expS_add {d : ℕ} (S : Finset (Fin (d + 1))) (m m' : Fin d → ℤ) (hm : m ∈ expS S) (hm' : m' ∈ expS S) :
    m + m' ∈ expS S := by
  refine ⟨fun k hk => ?_, fun h0 => ?_⟩
  · simpa using add_nonneg (hm.1 k hk) (hm'.1 k hk)
  · simp only [Pi.add_apply, Finset.sum_add_distrib]
    linarith [hm.2 h0, hm'.2 h0]

theorem ra_zero_mem_expS {d : ℕ} (S : Finset (Fin (d + 1))) : (0 : Fin d → ℤ) ∈ expS S :=
  ⟨fun _ _ => le_rfl, fun _ => by simp⟩

theorem ra_tpow_single_pow {d : ℕ} (t : Fin d → Rˣ) (k : Fin d) (z : ℤ) (N : ℕ) :
    tpow t (Pi.single k z) ^ N = tpow t (Pi.single k (z * N)) := by
  rw [ra_tpow_single, ra_tpow_single, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]

theorem ra_prod_pow {d : ℕ} (t : Fin d → Rˣ) (e : Fin d → ℕ) :
    ∏ j, (t j : R) ^ (e j) = tpow t (fun j => (e j : ℤ)) := by
  unfold tpow
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_natCast, Units.val_pow_eq_pow_val]

theorem ra_torusS_le_span (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) :
    ∀ x ∈ torusS K t S, x ∈ Submodule.span K (tpow t '' expS S) := by
  intro x hx
  have hx' : x ∈ Subalgebra.toSubmodule (torusS K t S) := hx
  rw [torusS, Algebra.adjoin_eq_span] at hx'
  refine Submodule.span_mono (fun y hy => ?_) hx'
  induction hy using Submonoid.closure_induction with
  | mem y hy => exact hy
  | one => exact ⟨0, ra_zero_mem_expS S, ra_tpow_zero t⟩
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm, rfl⟩ := hy
    obtain ⟨m', hm', rfl⟩ := hz
    exact ⟨m + m', ra_expS_add S m m' hm hm', ra_tpow_add t m m'⟩

theorem tpow_mem_torusS (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) (m : Fin (n + 1) → ℤ) (hm : m ∈ expS S) :
    tpow t m ∈ torusS K t S :=
  Algebra.subset_adjoin ⟨m, hm, rfl⟩

theorem t_mem_torusS (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) (hS : (0 : Fin (n + 2)) ∈ S) (k : Fin (n + 1)) :
    (t k : R) ∈ torusS K t S := by
  have h := tpow_mem_torusS (K := K) t S (Pi.single k 1) ⟨fun j _ => by
    rw [Pi.single_apply]; split_ifs <;> norm_num, fun h => absurd hS h⟩
  rwa [ra_tpow_single, zpow_one] at h

theorem torusS_loc (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) (S : Finset (Fin (n + 2)))
    (hS : (0 : Fin (n + 2)) ∈ S) :
    Function.Injective (MvPolynomial.aeval (fun k => (⟨t k, t_mem_torusS t S hS k⟩ : torusS K t S)) :
      MvPolynomial (Fin (n + 1)) K →ₐ[K] torusS K t S) ∧
    ∀ a : torusS K t S, ∃ f g : MvPolynomial (Fin (n + 1)) K,
      IsUnit (MvPolynomial.aeval (fun k => (⟨t k, t_mem_torusS t S hS k⟩ : torusS K t S)) g) ∧
      a * MvPolynomial.aeval (fun k => (⟨t k, t_mem_torusS t S hS k⟩ : torusS K t S)) g =
        MvPolynomial.aeval (fun k => (⟨t k, t_mem_torusS t S hS k⟩ : torusS K t S)) f := by
  classical
  set u : Fin (n + 1) → torusS K t S := fun k => ⟨t k, t_mem_torusS t S hS k⟩ with hu
  have hval : ∀ p : MvPolynomial (Fin (n + 1)) K,
      ((MvPolynomial.aeval u p : torusS K t S) : R) = MvPolynomial.aeval (fun k => (t k : R)) p := fun p => by
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, Subalgebra.coe_add, hp, hq]
    | mul_X p k hp => simp only [map_mul, Subalgebra.coe_mul, hp, MvPolynomial.aeval_X]; rfl
  have hinj := algebraicIndependent_iff_injective_aeval.mp ht
  refine ⟨fun p q h => hinj (by rw [← hval, ← hval, h]), fun a => ?_⟩
  have key : ∀ x (hx : x ∈ torusS K t S), ∃ f g : MvPolynomial (Fin (n + 1)) K,
      IsUnit (MvPolynomial.aeval u g) ∧
        x * MvPolynomial.aeval (fun k => (t k : R)) g = MvPolynomial.aeval (fun k => (t k : R)) f := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      refine ⟨∏ j, MvPolynomial.X j ^ (m j).toNat, ∏ j, MvPolynomial.X j ^ (-m j).toNat, ?_, ?_⟩
      · have hmem : (fun j => -((-m j).toNat : ℤ)) ∈ expS S := by
          refine ⟨fun i hi => ?_, fun h0 => ?_⟩
          · have := hm.1 i hi
            simp only [neg_nonneg, Nat.cast_nonpos]
            omega
          · exact Finset.sum_nonpos fun i _ => by simp
        refine IsUnit.of_mul_eq_one ⟨_, tpow_mem_torusS t S _ hmem⟩ (Subtype.ext ?_)
        rw [Subalgebra.coe_mul, hval]
        simp only [map_prod, map_pow, MvPolynomial.aeval_X, Subalgebra.coe_one]
        rw [ra_prod_pow, ← ra_tpow_add]
        convert ra_tpow_zero t using 2
        ext j
        simp
      · simp only [map_prod, map_pow, MvPolynomial.aeval_X]
        rw [ra_prod_pow, ra_prod_pow, ← ra_tpow_add]
        congr 1
        ext j
        simp only [Pi.add_apply]
        omega
    | algebraMap c =>
      exact ⟨MvPolynomial.C c, 1, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨f1, g1, hg1, h1⟩ := hx
      obtain ⟨f2, g2, hg2, h2⟩ := hy
      refine ⟨f1 * g2 + f2 * g1, g1 * g2, by rw [map_mul]; exact hg1.mul hg2, ?_⟩
      simp only [map_add, map_mul]
      linear_combination (MvPolynomial.aeval (fun k => (t k : R)) g2) * h1 +
        (MvPolynomial.aeval (fun k => (t k : R)) g1) * h2
    | mul x y _ _ hx hy =>
      obtain ⟨f1, g1, hg1, h1⟩ := hx
      obtain ⟨f2, g2, hg2, h2⟩ := hy
      refine ⟨f1 * f2, g1 * g2, by rw [map_mul]; exact hg1.mul hg2, ?_⟩
      simp only [map_mul]
      linear_combination (y * MvPolynomial.aeval (fun k => (t k : R)) g2) * h1 +
        (MvPolynomial.aeval (fun k => (t k : R)) f1) * h2
  obtain ⟨f, g, hg, hfg⟩ := key a a.2
  exact ⟨f, g, hg, Subtype.ext (by rw [Subalgebra.coe_mul, hval, hval]; exact hfg)⟩

theorem torusS_frac [IsDomain R] (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) (hS : S.Nonempty) (k : Fin (n + 1)) :
    ∃ a' ∈ torusS K t S, a' ≠ 0 ∧ (t k : R) * a' ∈ torusS K t S := by
  classical
  by_cases h0 : (0 : Fin (n + 2)) ∈ S
  · exact ⟨1, one_mem _, one_ne_zero, by rw [mul_one]; exact t_mem_torusS t S h0 k⟩
  · obtain ⟨s, hs⟩ := hS
    obtain ⟨j, rfl⟩ : ∃ j : Fin (n + 1), j.succ = s := Fin.exists_succ_eq.mpr fun h => h0 (h ▸ hs)
    refine ⟨tpow t (Pi.single j (-1)), tpow_mem_torusS t S _ ⟨fun i hi => ?_, fun _ => ?_⟩,
      by unfold tpow; exact Units.ne_zero _, ?_⟩
    · rw [Pi.single_apply]
      split_ifs with h
      · subst h; exact absurd hs hi
      · exact le_rfl
    · simp
    · have : (t k : R) * tpow t (Pi.single j (-1)) = tpow t (Pi.single k 1 + Pi.single j (-1)) := by
        rw [ra_tpow_add, ra_tpow_single t k 1, zpow_one]
      rw [this]
      refine tpow_mem_torusS t S _ ⟨fun i hi => ?_, fun _ => ?_⟩
      · have hij : i ≠ j := fun h => hi (h ▸ hs)
        simp only [Pi.add_apply, Pi.single_apply, hij, if_false, add_zero]
        split_ifs <;> norm_num
      · simp [Finset.sum_add_distrib]

theorem torusS_succ_span (t : Fin (n + 1) → Rˣ) (k : Fin (n + 1)) :
    ∀ x ∈ torusS K t (Finset.univ.erase k.succ), x ∈ Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}) := by
  intro x hx
  refine Submodule.span_mono (Set.image_mono fun m hm h => ?_) (ra_torusS_le_span t _ x hx)
  have := hm.1 k (by simp)
  rw [h] at this
  norm_num at this

theorem torus_scale [IsDomain R] (t : Fin (n + 1) → Rˣ) (i : Fin (n + 2)) :
    ∃ w ∈ torusS K t (Finset.univ.erase i), w ≠ 0 ∧
      ∀ x ∈ torusS K t Finset.univ, ∃ N : ℕ, w ^ N * x ∈ torusS K t (Finset.univ.erase i) := by
  classical
  have hscale : ∀ (A : Subalgebra K R) (w : R), w ∈ A → (∀ m, ∃ N : ℕ, w ^ N * tpow t m ∈ A) →
      ∀ x ∈ torusS K t Finset.univ, ∃ N : ℕ, w ^ N * x ∈ A := by
    intro A w hw hgen x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, _, rfl⟩ := hx
      exact hgen m
    | algebraMap c => exact ⟨0, by simpa using A.algebraMap_mem c⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1⟩ := hx
      obtain ⟨N2, h2⟩ := hy
      refine ⟨N1 + N2, ?_⟩
      have : w ^ (N1 + N2) * (x + y) = w ^ N2 * (w ^ N1 * x) + w ^ N1 * (w ^ N2 * y) := by ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hw _) h1) (mul_mem (pow_mem hw _) h2)
    | mul x y _ _ hx hy =>
      obtain ⟨N1, h1⟩ := hx
      obtain ⟨N2, h2⟩ := hy
      refine ⟨N1 + N2, ?_⟩
      have : w ^ (N1 + N2) * (x * y) = (w ^ N1 * x) * (w ^ N2 * y) := by ring
      rw [this]
      exact mul_mem h1 h2
  have hne : ∀ z : ℤ, ∀ k, tpow t (Pi.single k z) ≠ 0 := fun z k => by unfold tpow; exact Units.ne_zero _
  induction i using Fin.cases with
  | zero =>
    have hS : ∀ i : Fin (n + 1), i.succ ∈ Finset.univ.erase (0 : Fin (n + 2)) := fun i =>
      Finset.mem_erase.mpr ⟨Fin.succ_ne_zero i, Finset.mem_univ _⟩
    refine ⟨tpow t (Pi.single 0 (-1)), tpow_mem_torusS t _ _ ⟨fun i hi => absurd (hS i) hi, fun _ => by simp⟩,
      hne _ _, hscale _ _ (tpow_mem_torusS t _ _ ⟨fun i hi => absurd (hS i) hi, fun _ => by simp⟩) fun m => ?_⟩
    refine ⟨(∑ k, m k).toNat, ?_⟩
    rw [ra_tpow_single_pow, ← ra_tpow_add]
    refine tpow_mem_torusS t _ _ ⟨fun i hi => absurd (hS i) hi, fun _ => ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true]
    omega
  | succ k =>
    have h0 : (0 : Fin (n + 2)) ∈ Finset.univ.erase k.succ :=
      Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero k).symm, Finset.mem_univ _⟩
    have hk : ∀ i : Fin (n + 1), i.succ ∉ Finset.univ.erase k.succ → i = k := fun i hi => by
      by_contra h
      exact hi (Finset.mem_erase.mpr ⟨fun h' => h (Fin.succ_inj.mp h'), Finset.mem_univ _⟩)
    have hw : tpow t (Pi.single k 1) ∈ torusS K t (Finset.univ.erase k.succ) := by
      rw [ra_tpow_single, zpow_one]
      exact t_mem_torusS t _ h0 k
    refine ⟨tpow t (Pi.single k 1), hw, hne _ _, hscale _ _ hw fun m => ⟨(-m k).toNat, ?_⟩⟩
    rw [ra_tpow_single_pow, ← ra_tpow_add]
    refine tpow_mem_torusS t _ _ ⟨fun i hi => ?_, fun h => absurd h0 h⟩
    obtain rfl := hk i hi
    simp only [Pi.add_apply, Pi.single_eq_same]
    omega

theorem prod_inv_mem (t : Fin (n + 1) → Rˣ) :
    (((∏ k, t k)⁻¹ : Rˣ) : R) ∈ torusS K t Finset.univ := by
  have h := tpow_mem_torusS (K := K) t Finset.univ (fun _ => -1) ⟨fun k hk => absurd (Finset.mem_univ _) hk,
    fun h => absurd (Finset.mem_univ _) h⟩
  rwa [tpow, Finset.prod_congr rfl (fun k _ => zpow_neg_one (t k)), Finset.prod_inv_distrib] at h

theorem torusS_le_univ (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) :
    torusS K t S ≤ torusS K t Finset.univ :=
  Algebra.adjoin_mono (Set.image_mono fun m _ => ⟨fun k hk => absurd (Finset.mem_univ _) hk,
    fun h => absurd (Finset.mem_univ _) h⟩)

theorem inv_mem_univ (t : Fin (n + 1) → Rˣ) (k : Fin (n + 1)) :
    (((t k)⁻¹ : Rˣ) : R) ∈ torusS K t Finset.univ := by
  have h := tpow_mem_torusS (K := K) t Finset.univ (Pi.single k (-1)) ⟨fun k hk => absurd (Finset.mem_univ _) hk,
    fun h => absurd (Finset.mem_univ _) h⟩
  rwa [ra_tpow_single, zpow_neg_one] at h

theorem jacS_mono {d m : ℕ} (B B' : Subalgebra K R) (hB : B ≤ B') (D : Fin d → Derivation K R R) (κ : Fin m → Fin d) :
    jacS B D κ ≤ jacS B' D κ :=
  AddSubgroup.closure_mono fun _ ⟨b, bs, hy⟩ =>
    ⟨Subalgebra.inclusion hB b, fun l => Subalgebra.inclusion hB (bs l), hy⟩

end CrystallineSemistableComparison.Pb
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidChartPf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

open Polynomial

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R]

theorem chart_ext_scale (A T : Subalgebra K R) (w : R) (hwA : w ∈ A)
    (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) (g : R) (hg : IsIntegral T g) :
    ∃ N : ℕ, IsIntegral A (w ^ N * g) := by
  obtain ⟨p, hpm, hp⟩ := hg
  have hmono : ∀ (x : R) (n m : ℕ), n ≤ m → w ^ n * x ∈ A → w ^ m * x ∈ A := by
    intro x n m hnm hx
    have : w ^ m * x = w ^ (m - n) * (w ^ n * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]
    rw [this]
    exact A.mul_mem (A.pow_mem hwA _) hx
  have hc : ∀ i : ℕ, ∃ n : ℕ, w ^ n * ((p.coeff i : T) : R) ∈ A := fun i =>
    hscale _ (p.coeff i).2
  choose n hn using hc
  set N : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hN
  have hcN : ∀ i ≤ p.natDegree, w ^ N * ((p.coeff i : T) : R) ∈ A := by
    intro i hi
    refine hmono _ (n i) N ?_ (hn i)
    exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set P : R[X] := p.map (algebraMap T R) with hP
  have hPm : P.Monic := hpm.map _
  have hPdeg : P.natDegree = p.natDegree := hpm.natDegree_map _
  have hPcoeff : ∀ i, P.coeff i = ((p.coeff i : T) : R) := fun i => by
    rw [hP, coeff_map]; rfl
  set Q : R[X] := P.scaleRoots (w ^ N) with hQ
  have hQm : Q.Monic := (monic_scaleRoots_iff _).2 hPm
  have hQlift : Q ∈ lifts (algebraMap A R) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    have hmem : Q.coeff i ∈ A := by
      rw [hQ, coeff_scaleRoots, hPdeg, hPcoeff]
      rcases lt_trichotomy i p.natDegree with hlt | heq | hgt
      · have h1 : (w ^ N) ^ (p.natDegree - i) = (w ^ N) ^ (p.natDegree - i - 1) * w ^ N := by
          rw [← pow_succ]; congr 1; omega
        rw [h1, mul_comm, mul_assoc]
        exact A.mul_mem (A.pow_mem (A.pow_mem hwA _) _) (hcN i hlt.le)
      · subst heq
        have : p.coeff p.natDegree = 1 := hpm.coeff_natDegree
        rw [this, Nat.sub_self, pow_zero, mul_one]
        exact A.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp only [ZeroMemClass.coe_zero, zero_mul]
        exact A.zero_mem
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q, hqQ, -, hqm⟩ := lifts_and_degree_eq_and_monic hQlift hQm
  refine ⟨N, q, hqm, ?_⟩
  rw [← eval_map, hqQ, hQ, scaleRoots_eval_mul, hP, eval_map, hp, mul_zero]

theorem chart_ext_pf (A T B0 Bu : Subalgebra K R) (hAT : A ≤ T) (hAB0 : A ≤ B0) (hB0 : B0 ≤ Bu) (hTBu : T ≤ Bu)
    (hB0FG : B0.FG) (hB0Int : ∀ b ∈ B0, IsIntegral A b) (hBuFG : Bu.FG) (hBuInt : ∀ b ∈ Bu, IsIntegral T b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b)
    (w : R) (hwA : w ∈ A) (hw0 : w ≠ 0) (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) :
    ∃ B' : Subalgebra K R, B0 ≤ B' ∧ B'.FG ∧ (∀ b ∈ B', IsIntegral A b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b := by
  classical
  obtain ⟨t, ht⟩ := hB0FG
  obtain ⟨s, hs⟩ := hBuFG
  have hkey : ∀ g : R, ∃ N : ℕ, g ∈ Bu → IsIntegral A (w ^ N * g) := by
    intro g
    by_cases hg : g ∈ Bu
    · obtain ⟨N, hN⟩ := chart_ext_scale A T w hwA hscale g (hBuInt g hg)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose N hN using hkey
  set u : Finset R := t ∪ s.image (fun g => w ^ N g * g) with hu
  set B' : Subalgebra K R := Algebra.adjoin K (u : Set R) with hB'
  have htB' : B0 ≤ B' := by
    rw [← ht, hB']
    exact Algebra.adjoin_mono (by rw [hu, Finset.coe_union]; exact Set.subset_union_left)
  have hwB' : w ∈ B' := htB' (hAB0 hwA)
  have hgen : ∀ g ∈ s, w ^ N g * g ∈ B' := by
    intro g hg
    apply Algebra.subset_adjoin
    rw [hu, Finset.coe_union]
    exact Or.inr (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hg))
  have hsBu : ∀ g ∈ s, g ∈ Bu := fun g hg => by
    rw [← hs]; exact Algebra.subset_adjoin (Finset.mem_coe.2 hg)

  have hpow : ∀ b ∈ Bu, ∃ L : ℕ, w ^ L * b ∈ B' := by
    intro b hb
    rw [← hs] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact ⟨N x, hgen x (Finset.mem_coe.1 hx)⟩
    | algebraMap k => exact ⟨0, by rw [pow_zero, one_mul]; exact B'.algebraMap_mem k⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x + y) = w ^ L2 * (w ^ L1 * x) + w ^ L1 * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.add_mem (B'.mul_mem (B'.pow_mem hwB' _) h1) (B'.mul_mem (B'.pow_mem hwB' _) h2)
    | mul x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x * y) = (w ^ L1 * x) * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.mul_mem h1 h2
  refine ⟨B', htB', ⟨u, hB'.symm⟩, ?_, ?_⟩
  · intro b hb
    rw [hB'] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      rw [hu, Finset.coe_union] at hx
      rcases hx with hx | hx
      · apply hB0Int
        rw [← ht]
        exact Algebra.subset_adjoin hx
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact hN g (hsBu g hg)
    | algebraMap k =>
      have hk : algebraMap K R k ∈ A := A.algebraMap_mem k
      have : algebraMap K R k = algebraMap A R ⟨_, hk⟩ := rfl
      rw [this]
      exact isIntegral_algebraMap
    | add x y _ _ ihx ihy => exact ihx.add ihy
    | mul x y _ _ ihx ihy => exact ihx.mul ihy
  · intro r
    obtain ⟨b, hb, b', hb', hb'0, hrb⟩ := hFrac r
    obtain ⟨L1, h1⟩ := hpow b hb
    obtain ⟨L2, h2⟩ := hpow b' hb'
    refine ⟨w ^ (L1 + L2) * b, ?_, w ^ (L1 + L2) * b', ?_, ?_, ?_⟩
    · have : w ^ (L1 + L2) * b = w ^ L2 * (w ^ L1 * b) := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h1
    · have : w ^ (L1 + L2) * b' = w ^ L1 * (w ^ L2 * b') := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h2
    · exact mul_ne_zero (pow_ne_zero _ hw0) hb'0
    · rw [← hrb]; ring

end CrystallineSemistableComparison.Pb
end
end


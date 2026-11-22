import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulLeFinrankOfEmbedding
section
open Pointwise

namespace GlobalTheory

theorem length_quotient_smul_range_le_finrank_mul : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] (W M : Type) [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W] [FiniteDimensional K W] [AddCommGroup M] [Module O M] (f : M →ₗ[O] W), Function.Injective f → ∀ a : O, Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) ≤ (Module.finrank K W : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  intro O K _ _ _ _ _ _ W M _ _ _ _ _ _ _ f hf a
  set R := LinearMap.range (a • (LinearMap.id : M →ₗ[O] M)) with hR
  refine GlobalTheory.T.length_le_of_forall_fg_submodule_length_le O (M ⧸ R) _ ?_
  intro N hN
  obtain ⟨s, hs⟩ := hN
  set g := Function.surjInv (Submodule.mkQ_surjective R) with hg
  have hgs : ∀ q, R.mkQ (g q) = q := Function.surjInv_eq (Submodule.mkQ_surjective R)
  let N' : Submodule O M := Submodule.span O (g '' (s : Set (M ⧸ R)))
  have hmap : N'.map R.mkQ = N := by
    rw [Submodule.map_span, ← hs, ← Set.image_comp]
    congr 1
    ext q
    simp [hgs]
  haveI : Module.Finite O N' := Module.Finite.iff_fg.mpr (Submodule.fg_span (s.finite_toSet.image g))
  let e : N' →ₗ[O] W := f ∘ₗ N'.subtype
  have he : Function.Injective e := hf.comp N'.injective_subtype
  haveI : Module.IsTorsionFree K W := inferInstance
  haveI : Module.IsTorsionFree O W :=
    Module.IsTorsionFree.comap (S := K) (algebraMap O K)
      (fun r hr => IsRegular.of_ne_zero (by
        intro h0
        have hinj := IsFractionRing.injective O K
        have : r = 0 := hinj (by simpa using h0)
        subst this
        exact (not_isRegular_zero (R := O)) hr))
      (fun r m => algebraMap_smul K r m)
  haveI : Module.IsTorsionFree O N' := Function.Injective.moduleIsTorsionFree e he e.map_smul
  haveI : Module.Free O N' := Module.free_of_finite_type_torsion_free'
  have hrank : Module.finrank O N' ≤ Module.finrank K W := by
    let b := Module.finBasis O N'
    have h1 : LinearIndependent O (e ∘ b) := b.linearIndependent.map' e (LinearMap.ker_eq_bot.mpr he)
    have h2 : LinearIndependent K (e ∘ b) := (LinearIndependent.iff_fractionRing O K).mp h1
    simpa using h2.fintype_card_le_finrank
  let p : N' →ₗ[O] N := (R.mkQ ∘ₗ N'.subtype).codRestrict N (by
    intro x
    rw [← hmap]
    exact ⟨x, x.2, rfl⟩)
  have hp : Function.Surjective p := by
    rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let R' := LinearMap.range (a • (LinearMap.id : N' →ₗ[O] N'))
  have hker : R' ≤ LinearMap.ker p := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    have : R.mkQ (a • (x : M)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, by simp⟩
    simpa [p] using this
  let q : (N' ⧸ R') →ₗ[O] N := R'.liftQ p hker
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨R'.mkQ x, by simp [q]⟩
  calc Module.length O N ≤ Module.length O (N' ⧸ R') := Module.length_le_of_surjective q hq
    _ = (Module.finrank O N' : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := GlobalTheory.T.length_quotient_scalar_mul O N' a
    _ ≤ _ := by
      gcongr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruencePrimePowTorsionFree
section
open GlobalTheory.Cong

namespace GlobalTheory.CongTorsion

open Finset

variable {R : Type} [CommRing R] {a : ℕ}

lemma one_add_smul_pow (t : R) (z : Matrix (Fin a) (Fin a) R) (n : ℕ) :
    (1 + t • z) ^ n = 1 + t • ∑ m ∈ range n, t ^ m • ((n.choose (m + 1)) • z ^ (m + 1)) := by
  rw [add_comm, (Commute.one_right (t • z)).add_pow, sum_range_succ', add_comm]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
  congr 1
  rw [smul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [← nsmul_eq_mul', smul_pow, smul_smul, ← pow_succ', smul_comm]

lemma dvd_entries_of_pow_eq_one [IsDomain R] [IsLocalRing R] [CharZero R] {l p : ℕ} (hl : l.Prime)
    (hlu : ¬ IsUnit (l : R)) (hp : p.Prime) {t : R} (ht : (l : R) ^ 2 ∣ t) (ht0 : t ≠ 0)
    {z : Matrix (Fin a) (Fin a) R} (hz : (1 + t • z) ^ p = 1) (i j : Fin a) : (l : R) ∣ z i j := by
  have h := one_add_smul_pow t z p
  rw [hz] at h
  have hS : t • ∑ m ∈ range p, t ^ m • ((p.choose (m + 1)) • z ^ (m + 1)) = 0 := by
    have := congrArg (fun A => A - 1) h
    simpa using this.symm
  rw [smul_eq_zero] at hS
  have hS := hS.resolve_left ht0
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rw [sum_range_succ'] at hS
  have he := congrFun (congrFun hS i) j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    pow_zero, one_smul, zero_add, Nat.choose_one_right, pow_one, Matrix.zero_apply] at he
  simp only [nsmul_eq_mul] at he
  have hdiv : (l : R) ^ 2 ∣ ((q + 1 : ℕ) : R) * z i j := by
    have : ((q + 1 : ℕ) : R) * z i j = -(∑ m ∈ range q, t ^ (m + 1) *
        (((q + 1).choose (m + 1 + 1) : R) * (z ^ (m + 1 + 1)) i j)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact he
    rw [this, dvd_neg]
    exact dvd_sum fun m _ => dvd_mul_of_dvd_left (ht.trans (dvd_pow_self t (Nat.succ_ne_zero m))) _
  have hl0 : (l : R) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  by_cases hpl : q + 1 = l
  · rw [hpl, pow_two] at hdiv
    exact (mul_dvd_mul_iff_left hl0).mp hdiv
  · have hcop : Nat.Coprime (q + 1) l := (Nat.coprime_primes hp hl).mpr hpl
    have hc : IsCoprime ((q + 1 : ℕ) : R) (l : R) := by
      have := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom R)
      simpa using this
    obtain ⟨u, v, huv⟩ := hc
    have hpu : IsUnit ((q + 1 : ℕ) : R) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one huv with h1 | h1
      · exact isUnit_of_mul_isUnit_right h1
      · exact absurd (isUnit_of_mul_isUnit_right h1) hlu
    exact (dvd_pow_self (l : R) two_ne_zero).trans ((hpu.dvd_mul_left).mp hdiv)

lemma pow_dvd_entries_of_pow_eq_one [IsDomain R] [IsLocalRing R] [CharZero R] {l p : ℕ}
    (hl : l.Prime) (hlu : ¬ IsUnit (l : R)) (hp : p.Prime) (N : ℕ) :
    ∀ (t : R) (z : Matrix (Fin a) (Fin a) R), (l : R) ^ 2 ∣ t → t ≠ 0 → (1 + t • z) ^ p = 1 →
      ∀ i j, (l : R) ^ N ∣ z i j := by
  have hl0 : (l : R) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  induction N with
  | zero => intro t z _ _ _ i j; simp
  | succ N ih =>
    intro t z ht ht0 hz i j
    have hd := dvd_entries_of_pow_eq_one hl hlu hp ht ht0 hz
    choose w hw using hd
    have hzz : z = (l : R) • Matrix.of w := by ext i j; simp [hw i j]
    have htz : t • z = (t * l) • Matrix.of w := by rw [hzz, smul_smul]
    have h' := ih (t * l) (Matrix.of w) (dvd_mul_of_dvd_left ht _) (mul_ne_zero ht0 hl0)
      (by rw [← htz]; exact hz) i j
    rw [hw i j, pow_succ']
    exact mul_dvd_mul_left _ (by simpa using h')

lemma eq_zero_of_forall_pow_dvd [IsDomain R] [IsDiscreteValuationRing R] {c b : R}
    (hc : ¬ IsUnit c) (h : ∀ N, c ^ N ∣ b) : b = 0 := by
  by_contra hb
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hc hb
  exact hn (h _)

end GlobalTheory.CongTorsion

namespace GlobalTheory

open GlobalTheory.CongTorsion in

theorem principalCongruence_torsionFree :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (l m a : ℕ),
      l.Prime → ¬ IsUnit (l : R) → 2 ≤ m → ∀ (x : Matrix (Fin a) (Fin a) R) (n : ℕ), 0 < n →
        (1 + ((l : R) ^ m) • x) ^ n = 1 → x = 0 := by
  intro R _ _ _ _ l m a hl hlu hm x n hn hx
  have hl0 : (l : R) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hc0 : (l : R) ^ m ≠ 0 := pow_ne_zero _ hl0
  have hc2 : (l : R) ^ 2 ∣ (l : R) ^ m := pow_dvd_pow _ hm
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1
      rw [pow_one, add_eq_left, smul_eq_zero] at hx
      exact hx.resolve_left hc0
    · set p := n.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk; omega
        · exact h
      have hklt : k < n := by
        rw [hk]; exact lt_mul_left hkpos hp.one_lt
      have he := one_add_smul_pow ((l : R) ^ m) x p
      rw [hk, pow_mul, he] at hx
      have hx' := ih k hklt _ hkpos hx
      rw [hx', smul_zero, add_zero] at he
      ext i j
      exact eq_zero_of_forall_pow_dvd hlu
        (fun N => pow_dvd_entries_of_pow_eq_one hl hlu hp N _ x hc2 hc0 he i j)

end GlobalTheory
end


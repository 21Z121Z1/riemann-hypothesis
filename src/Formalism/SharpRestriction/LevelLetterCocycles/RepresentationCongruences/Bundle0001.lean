import Mathlib
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CoeffRelation
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open PowerSeries

theorem coeff_relation {O : Type*} [CommRing O] [IsDomain O] {d₁ d : ℕ} (p : O) (hp : p ≠ 0)
    (F : Fin d₁ → O⟦X⟧) (μ : Fin d₁ → Fin d → O) (k₀ : Fin d) (K s S h k : ℕ) (Q : O⟦X⟧)
    (hk : k < h) (hkS : S ≤ k)
    (heq : ∀ j : Fin d, ∃ R : O⟦X⟧,
      C p ^ K * (∑ m, F m * C (μ m j) - (if j = k₀ then C p ^ s * X ^ S * Q else 0)) = X ^ h * R) :
    ∀ j, ∑ m, coeff k (F m) * μ m j = if j = k₀ then p ^ s * coeff (k - S) Q else 0 := by
  intro j
  obtain ⟨R, hR⟩ := heq j
  have h1 : coeff k (C p ^ K * (∑ m, F m * C (μ m j) -
      (if j = k₀ then C p ^ s * X ^ S * Q else 0))) = 0 := by
    rw [hR, coeff_X_pow_mul', if_neg (by omega)]
  simp only [← map_pow, coeff_C_mul, map_sub, map_sum, coeff_mul_C] at h1
  have h2 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hp))
  rw [h2]
  split_ifs with hj
  · simp [← map_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul', hkS]
  · exact map_zero _

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.EqZeroOfForallMemCoeffFiltration
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS

open PowerSeries

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

def T (O : Type*) [CommRing O] [IsLocalRing O] (N : ℕ) : Ideal O⟦X⟧ where
  carrier := {x | ∀ m, coeff m x ∈ (IsLocalRing.maximalIdeal O) ^ (N - m)}
  add_mem' {a b} ha hb m := by
    simpa only [map_add] using Ideal.add_mem _ (ha m) (hb m)
  zero_mem' m := by simp
  smul_mem' c x hx m := by
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ ?_
    have h2 : p.2 ≤ m := by have := Finset.mem_antidiagonal.mp hp; omega
    exact Ideal.pow_le_pow_right (by omega) (hx p.2)

theorem mem_T {N : ℕ} {x : O⟦X⟧} :
    x ∈ T O N ↔ ∀ m, coeff m x ∈ (IsLocalRing.maximalIdeal O) ^ (N - m) := Iff.rfl

theorem T_anti {N N' : ℕ} (h : N ≤ N') : T O N' ≤ T O N := by
  intro x hx
  rw [mem_T] at hx ⊢
  exact fun m => Ideal.pow_le_pow_right (by omega) (hx m)

theorem T_mul {a b : ℕ} {x y : O⟦X⟧} (hx : x ∈ T O a) (hy : y ∈ T O b) : x * y ∈ T O (a + b) := by
  rw [mem_T] at hx hy ⊢
  intro m
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have h := Finset.mem_antidiagonal.mp hp
  have h2 := Ideal.mul_mem_mul (hx p.1) (hy p.2)
  rw [← pow_add] at h2
  exact Ideal.pow_le_pow_right (by omega) h2

private theorem maximalIdeal_pow_smul_whole_ring_eq_self (n : ℕ) :
    ((IsLocalRing.maximalIdeal O) ^ n • ⊤ : Submodule O O) = (IsLocalRing.maximalIdeal O) ^ n := by
  first
    | rw [Ideal.smul_eq_mul, Ideal.mul_top]
    | simp [Ideal.smul_eq_mul]
    | simp

theorem eq_zero_of_forall_mem_coeffFiltration {x : O⟦X⟧} (hx : ∀ N, x ∈ T O N) : x = 0 := by
  have H : IsHausdorff (IsLocalRing.maximalIdeal O) O := inferInstance
  ext m
  rw [map_zero]
  refine H.haus _ fun n => ?_
  rw [SModEq.zero, maximalIdeal_pow_smul_whole_ring_eq_self]
  have h := (mem_T.mp (hx (n + m))) m
  rwa [Nat.add_sub_cancel] at h

variable {g : O⟦X⟧}

theorem mem_T_one (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : g ∈ T O 1 := by
  rw [mem_T]
  intro m
  rcases m with _ | m
  · rw [Nat.sub_zero, pow_one, coeff_zero_eq_constantCoeff_apply]
    exact hg
  · rw [show 1 - (m + 1) = 0 by omega, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem pow_mem_coeffFiltration (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (N : ℕ) : g ^ N ∈ T O N := by
  induction N with
  | zero =>
    rw [pow_zero, mem_T]
    intro m
    rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    rw [pow_succ]
    exact T_mul ih (mem_T_one hg)

theorem aeval_mem_coeffFiltration (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) {N : ℕ} {p : Polynomial O}
    (hp : ∀ d < N, p.coeff d = 0) : Polynomial.aeval g p ∈ T O N := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d < N
  · rw [hp d hd, zero_smul]
    exact Submodule.zero_mem _
  · rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _
      (T_anti (not_lt.mp hd) (pow_mem_coeffFiltration hg d))

noncomputable def S (g : O⟦X⟧) (N : ℕ) (f : O⟦X⟧) : O⟦X⟧ := Polynomial.aeval g (trunc N f)

theorem S_sub_mem (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) {N N' : ℕ}
    (h : N ≤ N') : S g N' f - S g N f ∈ T O N := by
  unfold S
  rw [← map_sub (Polynomial.aeval (R := O) g)]
  refine aeval_mem_coeffFiltration hg fun d hd => ?_
  have hd' : d < N' := lt_of_lt_of_le hd h
  simp [coeff_trunc, hd, hd']

theorem exists_lim (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) (m : ℕ) :
    ∃ L : O, ∀ N, coeff m (S g N f) - L ∈ (IsLocalRing.maximalIdeal O) ^ (N - m) := by
  have hC : IsPrecomplete (IsLocalRing.maximalIdeal O) O := inferInstance
  obtain ⟨L, hL⟩ := hC.prec (f := fun k => coeff m (S g (k + m) f)) (fun {a b} hab => by
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_whole_ring_eq_self]
    have h1 := S_sub_mem hg f (show a + m ≤ b + m by omega) m
    rw [map_sub, Nat.add_sub_cancel] at h1
    have h2 := neg_mem h1
    rw [neg_sub] at h2
    exact h2)
  refine ⟨L, fun N => ?_⟩
  rcases le_or_gt m N with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    have h3 := hL k
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_whole_ring_eq_self] at h3
    rw [Nat.add_sub_cancel]
    exact h3
  · rw [Nat.sub_eq_zero_of_le h.le, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

noncomputable def subst (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) : O⟦X⟧ :=
  PowerSeries.mk fun m => Classical.choose (exists_lim hg f m)

theorem subst_sub_mem (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) (N : ℕ) :
    subst hg f - S g N f ∈ T O N := by
  rw [mem_T]
  intro m
  rw [map_sub]
  simp only [subst, coeff_mk]
  have h1 := Classical.choose_spec (exists_lim hg f m) N
  have h2 := neg_mem h1
  rwa [neg_sub] at h2

theorem subst_eq (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f y : O⟦X⟧) (N0 : ℕ)
    (hy : ∀ N, N0 ≤ N → y - S g N f ∈ T O N) : y = subst hg f := by
  have key : ∀ N, y - subst hg f ∈ T O N := fun N => by
    have h1 := hy (N + N0) (by omega)
    have h2 := subst_sub_mem hg f (N + N0)
    have h3 := sub_mem h1 h2
    rw [sub_sub_sub_cancel_right] at h3
    exact T_anti (by omega) h3
  exact sub_eq_zero.mp (eq_zero_of_forall_mem_coeffFiltration key)

private theorem truncEval_add (N : ℕ) (f f' : O⟦X⟧) :
    S g N (f + f') = S g N f + S g N f' := by
  have h : trunc N (f + f') = trunc N f + trunc N f' := map_add (trunc N) f f'
  simp only [S, h, map_add]

theorem subst_add (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f f' : O⟦X⟧) :
    subst hg (f + f') = subst hg f + subst hg f' := by
  refine (subst_eq hg (f + f') _ 0 fun N _ => ?_).symm
  rw [truncEval_add, add_sub_add_comm]
  exact add_mem (subst_sub_mem hg f N) (subst_sub_mem hg f' N)

private theorem truncEval_smul (N : ℕ) (r : O) (f : O⟦X⟧) :
    S g N (r • f) = r • S g N f := by
  have h : trunc N (r • f) = r • trunc N f := by
    first
      | exact map_smul (trunc N) r f
      | (ext d; simp only [coeff_trunc, Polynomial.coeff_smul, coeff_smul]; split_ifs <;> simp)
  simp only [S, h, map_smul]

theorem subst_smul (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (r : O) (f : O⟦X⟧) :
    subst hg (r • f) = r • subst hg f := by
  refine (subst_eq hg (r • f) _ 0 fun N _ => ?_).symm
  rw [truncEval_smul, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ r (subst_sub_mem hg f N)

private theorem coeff_trunc_mul_trunc_of_lt {N d : ℕ} (hd : d < N) (f f' : O⟦X⟧) :
    (trunc N f * trunc N f').coeff d = coeff d (f * f') := by
  rw [Polynomial.coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.mem_antidiagonal.mp hx
  have h1 : x.1 < N := by omega
  have h2 : x.2 < N := by omega
  simp [coeff_trunc, h1, h2]

theorem subst_mul (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f f' : O⟦X⟧) :
    subst hg (f * f') = subst hg f * subst hg f' := by
  refine (subst_eq hg (f * f') _ 0 fun N _ => ?_).symm
  have hA := subst_sub_mem hg f N
  have hB := subst_sub_mem hg f' N
  have hT : S g N f * S g N f' - S g N (f * f') ∈ T O N := by
    unfold S
    rw [← map_mul (Polynomial.aeval (R := O) g), ← map_sub (Polynomial.aeval (R := O) g)]
    refine aeval_mem_coeffFiltration hg fun d hd => ?_
    rw [Polynomial.coeff_sub, coeff_trunc_mul_trunc_of_lt hd]
    simp [coeff_trunc, hd]
  have key : subst hg f * subst hg f' - S g N (f * f') =
      (subst hg f - S g N f) * subst hg f' +
        S g N f * (subst hg f' - S g N f') +
        (S g N f * S g N f' - S g N (f * f')) := by ring
  rw [key]
  exact add_mem (add_mem (Ideal.mul_mem_right _ _ hA) (Ideal.mul_mem_left _ _ hB)) hT

theorem subst_one (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : subst hg (1 : O⟦X⟧) = 1 := by
  refine (subst_eq hg 1 1 1 fun N hN => ?_).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [S, trunc_one, map_one, sub_self]
  exact Submodule.zero_mem _

theorem subst_X (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : subst hg (X : O⟦X⟧) = g := by
  refine (subst_eq hg X g 2 fun N hN => ?_).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [S, trunc_X, Polynomial.aeval_X, sub_self]
  exact Submodule.zero_mem _

noncomputable def substAlgHom (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : O⟦X⟧ →ₐ[O] O⟦X⟧ :=
  AlgHom.ofLinearMap
    { toFun := subst hg
      map_add' := subst_add hg
      map_smul' := subst_smul hg }
    (subst_one hg) (subst_mul hg)

theorem exists_algHom_X_eq (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) :
    ∃ h : O⟦X⟧ →ₐ[O] O⟦X⟧, h X = g := ⟨substAlgHom hg, subst_X hg⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGLLatBasisOfIsSplitEquiv
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.LTA

open PowerSeries

variable {O : Type*} [CommRing O]

theorem alg_C (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O) : h (C a) = C a := by
  have e : (C a : O⟦X⟧) = algebraMap O O⟦X⟧ a := by
    first
    | rfl
    | simp
    | (rw [PowerSeries.algebraMap_apply']; rfl)
  rw [e, AlgHom.commutes]

theorem constantCoeff_alg (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : constantCoeff (h X) = 0) (k : O⟦X⟧) :
    constantCoeff (h k) = constantCoeff k := by
  obtain ⟨m, hm⟩ : ∃ m : O⟦X⟧, k = m * X + C (constantCoeff k) := by
    first
    | exact ⟨_, PowerSeries.eq_shift_mul_X_add_const k⟩
    | exact ⟨PowerSeries.mk fun p => coeff (p + 1) k, by
        ext n; rcases n with _ | n <;> simp [PowerSeries.coeff_succ_mul_X]⟩
  rw [hm]
  simp [hX, alg_C]

private theorem exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one (l : ℕ) (x y : O⟦X⟧)
    (hx : constantCoeff x = 1) (hy : constantCoeff y = 1) :
    ∃ S : O⟦X⟧, constantCoeff S = l ∧ x ^ l - y ^ l = S * (x - y) := by
  refine ⟨∑ i ∈ Finset.range l, x ^ i * y ^ (l - 1 - i), ?_, ?_⟩
  · simp [map_sum, hx, hy]
  · first
    | exact (geom_sum₂_mul x y l).symm
    | exact ((Commute.all x y).geom_sum₂_mul l).symm

theorem exists_GL_latBasis_of_isSplitEquiv (l : ℕ) :
    ∃ Q0 : O⟦X⟧, constantCoeff Q0 = l ∧ (1 + X : O⟦X⟧) ^ l - 1 = X * Q0 := by
  obtain ⟨S, hS, e⟩ := exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one l (1 + X : O⟦X⟧) 1 (by simp) (by simp)
  exact ⟨S, hS, by linear_combination e⟩

theorem exists_S (l : ℕ) (a b : O⟦X⟧) (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    ∃ S : O⟦X⟧, constantCoeff S = l ∧ ((1 + a) ^ l - 1) - ((1 + b) ^ l - 1) = S * (a - b) := by
  obtain ⟨S, hS, e⟩ := exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one l (1 + a) (1 + b) (by simp [ha]) (by simp [hb])
  exact ⟨S, hS, by linear_combination e⟩

variable [IsDomain O] [CharZero O]

private theorem coeff_X_pow_mul_eq_constantCoeff (n : ℕ) (f : O⟦X⟧) :
    coeff n (X ^ n * f) = constantCoeff f := by
  rw [mul_comm]
  simpa using PowerSeries.coeff_mul_X_pow f n 0

theorem lt_unique (l : ℕ) [hp : Fact l.Prime]
    (φ₀ γ γ' : O⟦X⟧ →ₐ[O] O⟦X⟧) (hφ₀ : φ₀ X = (1 + X) ^ l - 1)
    (hc : ∀ f, φ₀ (γ f) = γ (φ₀ f)) (hc' : ∀ f, φ₀ (γ' f) = γ' (φ₀ f))
    (h0 : constantCoeff (γ X) = 0) (h0' : constantCoeff (γ' X) = 0)
    (h1 : coeff 1 (γ X) = coeff 1 (γ' X)) :
    γ X = γ' X := by
  classical
  have key : ∀ γ₁ : O⟦X⟧ →ₐ[O] O⟦X⟧, (∀ f, φ₀ (γ₁ f) = γ₁ (φ₀ f)) →
      φ₀ (γ₁ X) = (1 + γ₁ X) ^ l - 1 := by
    intro γ₁ hγ
    rw [hγ, hφ₀]
    simp only [map_sub, map_pow, map_add, map_one]
  by_contra hne
  have hd : γ X - γ' X ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨S, hS, hSe⟩ := exists_S l (γ X) (γ' X) h0 h0'
  have hφd : φ₀ (γ X - γ' X) = S * (γ X - γ' X) := by
    rw [map_sub, key γ hc, key γ' hc']
    exact hSe
  have hex : ∃ m, coeff m (γ X - γ' X) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hd (PowerSeries.ext fun m => by rw [hall m, map_zero])
  obtain ⟨n, hn, hmin⟩ : ∃ n, coeff n (γ X - γ' X) ≠ 0 ∧ ∀ m < n, coeff m (γ X - γ' X) = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by
      by_contra hcm
      exact Nat.find_min hex hm hcm⟩
  have hc0 : coeff 0 (γ X - γ' X) = 0 := by
    rw [map_sub]
    simp [h0, h0']
  have hc1 : coeff 1 (γ X - γ' X) = 0 := by
    rw [map_sub, h1, sub_self]
  have hn2 : 2 ≤ n := by
    by_contra hlt2
    push_neg at hlt2
    interval_cases n
    · exact hn hc0
    · exact hn hc1
  obtain ⟨u, hu⟩ := PowerSeries.X_pow_dvd_iff.mpr hmin
  have hu0 : constantCoeff u = coeff n (γ X - γ' X) := by
    rw [hu, coeff_X_pow_mul_eq_constantCoeff]
  obtain ⟨Q0, hQ0, hQe⟩ := exists_GL_latBasis_of_isSplitEquiv (O := O) l
  have hφX : φ₀ X = X * Q0 := by rw [hφ₀, hQe]
  have hcX : constantCoeff (φ₀ X) = 0 := by
    rw [hφX]
    simp
  have lhs : coeff n (φ₀ (γ X - γ' X)) = (l : O) ^ n * constantCoeff u := by
    rw [hu, map_mul, map_pow, hφX, mul_pow, mul_assoc, coeff_X_pow_mul_eq_constantCoeff, map_mul, map_pow,
      hQ0, constantCoeff_alg φ₀ hcX]
  have rhs : coeff n (S * (γ X - γ' X)) = (l : O) * constantCoeff u := by
    rw [hu, mul_left_comm, coeff_X_pow_mul_eq_constantCoeff, map_mul, hS]
  have heq : (l : O) ^ n * constantCoeff u = (l : O) * constantCoeff u := by
    rw [← lhs, ← rhs, hφd]
  have hcu : constantCoeff u ≠ 0 := by
    rw [hu0]
    exact hn
  have hpow : (l : O) ^ n = l := mul_right_cancel₀ hcu heq
  have hnat : l ^ n = l := by exact_mod_cast hpow
  have hl2 : 2 ≤ l := hp.out.two_le
  have hle : l ^ 2 ≤ l ^ n := Nat.pow_le_pow_right (by omega) hn2
  rw [hnat] at hle
  nlinarith

end Formalism.MainNotions.N.FrobeniusPowerSeries.LTA
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Imports
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb

open Finset

theorem split {R : Type*} [CommRing R] (π q l : R) (hq : q = π + l) (e B r : ℕ) :
    π ^ (r + 1) * q ^ (e * (r + 1)) =
      (∑ k ∈ (range (r + 1)).filter (fun k => k + e * (r + 1) < B),
        (-1 : R) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * π * q ^ (k + e * (r + 1))) +
      π * q ^ B * ∑ k ∈ (range (r + 1)).filter (fun k => ¬ k + e * (r + 1) < B),
        (-1 : R) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * q ^ (k + e * (r + 1) - B) := by
  have hπ : π = q + (-l) := by rw [hq]; ring
  have h1 : π ^ (r + 1) * q ^ (e * (r + 1)) = π * q ^ (e * (r + 1)) * (q + (-l)) ^ r := by
    rw [← hπ]; ring
  rw [h1, add_pow, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not (range (r + 1))
    (fun k => k + e * (r + 1) < B), Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow]
    ring
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : B ≤ k + e * (r + 1) := by
      simp only [Finset.mem_filter] at hk
      omega
    have hq' : q ^ (k + e * (r + 1)) = q ^ B * q ^ (k + e * (r + 1) - B) := by
      rw [← pow_add]; congr 1; omega
    rw [neg_pow]
    calc π * q ^ (e * (r + 1)) * (q ^ k * ((-1) ^ (r - k) * l ^ (r - k)) * (r.choose k : R))
        = (-1) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * π * q ^ (k + e * (r + 1)) := by ring
      _ = π * q ^ B * ((-1) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * q ^ (k + e * (r + 1) - B)) := by
        rw [hq']; ring

theorem count (e B r k : ℕ) (he : 1 ≤ e) (hk : k ≤ r) (hB : k + e * (r + 1) < B) (σ : ℝ)
    (hσ : (B : ℝ) / e ≤ σ) : ((r + 1 : ℕ) : ℝ) * (e + 1) / e ≤ σ + (r - k : ℕ) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : ((r - k : ℕ) : ℝ) = (r : ℝ) - k := by rw [Nat.cast_sub hk]
  have hB' : (k : ℝ) + e * (r + 1) + 1 ≤ B := by exact_mod_cast hB
  rw [h1, div_le_iff₀ he0]
  have h2 : (B : ℝ) ≤ σ * e := by rwa [div_le_iff₀ he0] at hσ
  push_cast
  have hkr : (k : ℝ) ≤ r := by exact_mod_cast hk
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  nlinarith [mul_nonneg (sub_nonneg.2 hkr) (sub_nonneg.2 he1)]

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb
end


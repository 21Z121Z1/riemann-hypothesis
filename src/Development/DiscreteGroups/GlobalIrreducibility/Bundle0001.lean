import Mathlib

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzCliff
section
open Module Polynomial

set_option linter.all false

namespace DiscreteGroups.sglob.DzCliff

variable {W V : Type*} [Group W] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem eig_unique {f : End ℂ V} {u : V} (hu : u ≠ 0) {a b : ℂ} (ha : f u = a • u) (hb : f u = b • u) : a = b :=
  smul_left_injective ℂ hu (ha.symm.trans hb)

theorem pow_apply_of_eig {f : End ℂ V} {v : V} {c : ℂ} (hv : f v = c • v) (m : ℕ) : (f ^ m) v = c ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem rho_inv_apply (ρ : Representation ℂ W V) (a : W) (v : V) : ρ a⁻¹ (ρ a v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rho_apply_inv (ρ : Representation ℂ W V) (a : W) (v : V) : ρ a (ρ a⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_ne_zero (ρ : Representation ℂ W V) (a : W) {v : V} (hv : v ≠ 0) : ρ a v ≠ 0 := by
  intro h
  apply hv
  rw [← rho_inv_apply ρ a v, h, map_zero]

theorem exists_common_eigenvector (S : Set (End ℂ V)) (hS : ∀ f ∈ S, ∀ g ∈ S, f * g = g * f)
    (U : Submodule ℂ V) (hU : U ≠ ⊥) (hUS : ∀ f ∈ S, ∀ v ∈ U, f v ∈ U) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ f ∈ S, ∃ c : ℂ, f u = c • u := by
  classical
  let P : Submodule ℂ V → Prop := fun X => X ≤ U ∧ X ≠ ⊥ ∧ ∀ f ∈ S, ∀ v ∈ X, f v ∈ X
  have hex : ∃ k, ∃ X, P X ∧ finrank ℂ X = k := ⟨_, U, ⟨le_rfl, hU, hUS⟩, rfl⟩
  obtain ⟨X, hX, hXk⟩ := Nat.find_spec hex
  have hmin : ∀ Y, P Y → finrank ℂ X ≤ finrank ℂ Y := fun Y hY => hXk ▸ Nat.find_min' hex ⟨Y, hY, rfl⟩
  obtain ⟨u, huX, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX.2.1
  refine ⟨u, hX.1 huX, hu0, fun f hf => ?_⟩
  haveI : Nontrivial X := Submodule.nontrivial_iff_ne_bot.mpr hX.2.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrict (fun v hv => hX.2.2 f hf v hv))
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx' : f (x : V) = c • (x : V) := by
    have := Module.End.mem_eigenspace_iff.mp hx.1
    simpa [LinearMap.restrict_apply] using congrArg Subtype.val this
  let Y : Submodule ℂ V := X ⊓ f.eigenspace c
  have hY : P Y := by
    refine ⟨le_trans inf_le_left hX.1, ?_, fun g hg v hv => ⟨hX.2.2 g hg v hv.1, Module.End.mem_eigenspace_iff.mpr
      (by rw [← Module.End.mul_apply, hS f hf g hg, Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp hv.2,
        map_smul])⟩⟩
    intro hbot
    have hxY : (x : V) ∈ Y := ⟨x.2, Module.End.mem_eigenspace_iff.mpr hx'⟩
    rw [hbot, Submodule.mem_bot] at hxY
    exact hx.2 (Subtype.ext hxY)
  have hYX : Y = X := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin Y hY)
  have huY : u ∈ Y := hYX ▸ huX
  exact ⟨c, Module.End.mem_eigenspace_iff.mp huY.2⟩

theorem eq_top_of_stable (ρ : Representation ℂ W V) (hρ : ρ.IsIrreducible) (S : Submodule ℂ V) (hS : S ≠ ⊥)
    (hst : ∀ σ : W, ∀ v ∈ S, ρ σ v ∈ S) : S = ⊤ := by
  let X : Subrepresentation ρ := ⟨S, fun σ v hv => hst σ v hv⟩
  rcases hρ.eq_bot_or_eq_top X with h | h
  · exact absurd (congrArg Subrepresentation.toSubmodule h) hS
  · exact congrArg Subrepresentation.toSubmodule h

end DiscreteGroups.sglob.DzCliff
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzDigCover
section
namespace DiscreteGroups.sglob.DzDig

open Finset

theorem cover_bound (N e D : ℕ) :
    #((range N).filter (fun u => 0 < u * D % N ∧ u * D % N < e)) ≤ e - 1 := by
  rcases Nat.eq_zero_or_pos D with hD | hD0
  · subst hD; simp
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp
  have hgpos : 0 < N.gcd D := Nat.gcd_pos_of_pos_right N hD0
  have hgN : N.gcd D ∣ N := Nat.gcd_dvd_left N D
  have hgD : N.gcd D ∣ D := Nat.gcd_dvd_right N D
  have hE : N / N.gcd D * N.gcd D = N := Nat.div_mul_cancel hgN
  have hEpos : 0 < N / N.gcd D := Nat.div_pos (Nat.le_of_dvd hNpos hgN) hgpos
  calc #((range N).filter (fun u => 0 < u * D % N ∧ u * D % N < e))
      ≤ #(((Ioc 0 (e - 1)).filter (fun a => N.gcd D ∣ a)) ×ˢ range (N.gcd D)) := by
        apply card_le_card_of_injOn (fun u => (u * D % N, u / (N / N.gcd D)))
        · intro u hu
          have hu' := mem_coe.mp hu
          rw [mem_filter, mem_range] at hu'
          simp only [mem_coe, mem_product, mem_filter, mem_Ioc, mem_range]
          refine ⟨⟨⟨hu'.2.1, by omega⟩, (Nat.dvd_mod_iff hgN).mpr (dvd_mul_of_dvd_right hgD u)⟩, ?_⟩
          rw [Nat.div_lt_iff_lt_mul hEpos, mul_comm, hE]
          exact hu'.1
        · intro u _ v _ huv
          simp only [Prod.mk.injEq] at huv
          have h1 : u * D ≡ v * D [MOD N] := huv.1
          have h2 : u % (N / N.gcd D) = v % (N / N.gcd D) := Nat.ModEq.cancel_right_div_gcd hNpos h1
          calc u = N / N.gcd D * (u / (N / N.gcd D)) + u % (N / N.gcd D) := (Nat.div_add_mod u _).symm
            _ = N / N.gcd D * (v / (N / N.gcd D)) + v % (N / N.gcd D) := by rw [huv.2, h2]
            _ = v := Nat.div_add_mod v _
    _ = (e - 1) / N.gcd D * N.gcd D := by
        rw [card_product, Nat.Ioc_filter_dvd_card_eq_div, card_range]
    _ ≤ e - 1 := Nat.div_mul_le_self _ _

theorem diff_mod {N a b u : ℕ} (hN : 0 < N) (hle : u * b % N ≤ u * a % N) :
    u * (a % N + (N - b % N)) % N = u * a % N - u * b % N := by
  have hb := Nat.mod_lt b hN
  have h1 : u * (a % N + (N - b % N)) + u * (b % N) = u * (a % N) + N * u := by
    have h0 : a % N + (N - b % N) + b % N = a % N + N := by omega
    calc u * (a % N + (N - b % N)) + u * (b % N) = u * (a % N + (N - b % N) + b % N) := by ring
      _ = u * (a % N + N) := by rw [h0]
      _ = u * (a % N) + N * u := by ring
  have h3 : (u * (a % N + (N - b % N)) + u * (b % N)) % N = u * a % N := by
    rw [h1, Nat.add_mul_mod_self_left, Nat.mul_mod_mod]
  rw [Nat.add_mod, Nat.mul_mod_mod] at h3
  have hr := Nat.mod_lt (u * (a % N + (N - b % N))) hN
  have hx := Nat.mod_lt (u * a) hN
  rcases Nat.lt_or_ge (u * (a % N + (N - b % N)) % N + u * b % N) N with h | h
  · rw [Nat.mod_eq_of_lt h] at h3; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at h3; omega

theorem totient_le {N e n k k' p : ℕ} (hN : 0 < N) (he : 0 < e)
    (hno : ∀ j < n, ¬ k' ≡ k * p ^ j [MOD N])
    (hm : ∀ u < N, N.Coprime u → ∃ j < n, p ^ j * (u * k % N) % N / e = u * k' % N / e) :
    N.totient ≤ n * (2 * (e - 1)) := by
  have hsub : (range N).filter (fun a => N.Coprime a) ⊆ (range n).biUnion (fun j =>
      (range N).filter (fun u => 0 < u * (k' % N + (N - k * p ^ j % N)) % N
          ∧ u * (k' % N + (N - k * p ^ j % N)) % N < e)
      ∪ (range N).filter (fun u => 0 < u * (k * p ^ j % N + (N - k' % N)) % N
          ∧ u * (k * p ^ j % N + (N - k' % N)) % N < e)) := by
    intro u hu
    rw [mem_filter, mem_range] at hu
    obtain ⟨j, hj, hje⟩ := hm u hu.1 hu.2
    rw [mem_biUnion]
    refine ⟨j, mem_range.mpr hj, ?_⟩
    have hy : p ^ j * (u * k % N) % N = u * (k * p ^ j) % N := by
      rw [Nat.mul_mod_mod, show p ^ j * (u * k) = u * (k * p ^ j) by ring]
    rw [hy] at hje
    have hb1 := Nat.div_add_mod (u * k' % N) e
    have hb2 := Nat.div_add_mod (u * (k * p ^ j) % N) e
    have hm1 := Nat.mod_lt (u * k' % N) he
    have hm2 := Nat.mod_lt (u * (k * p ^ j) % N) he
    rw [hje] at hb2
    rw [mem_union, mem_filter, mem_filter, mem_range]
    rcases lt_trichotomy (u * (k * p ^ j) % N) (u * k' % N) with h | h | h
    · left
      rw [diff_mod hN h.le]
      exact ⟨hu.1, by omega, by omega⟩
    · exfalso
      apply hno j hj
      have h' : u * k' ≡ u * (k * p ^ j) [MOD N] := h.symm
      exact Nat.ModEq.cancel_left_of_coprime hu.2 h'
    · right
      rw [diff_mod hN h.le]
      exact ⟨hu.1, by omega, by omega⟩
  calc N.totient = #((range N).filter (fun a => N.Coprime a)) := Nat.totient_eq_card_coprime N
    _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ j ∈ range n, 2 * (e - 1) := by
        apply sum_le_sum
        intro j _
        calc _ ≤ _ := card_union_le _ _
          _ ≤ (e - 1) + (e - 1) := add_le_add (cover_bound _ _ _) (cover_bound _ _ _)
          _ = 2 * (e - 1) := by ring
    _ = n * (2 * (e - 1)) := by rw [sum_const, card_range, smul_eq_mul]

end DiscreteGroups.sglob.DzDig
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzDigDef
section
namespace DiscreteGroups.sglob.DzType

def Dig : Prop :=
  ∀ (p n : ℕ), p.Prime → 2 ≤ n → 16 * n ^ 2 < p → ∀ k k' : ℕ,
    (∀ i j, i < n → j < n → k * p ^ i ≡ k * p ^ j [MOD p ^ n - 1] → i = j) →
    (∀ i j, i < n → j < n → k' * p ^ i ≡ k' * p ^ j [MOD p ^ n - 1] → i = j) →
    (∀ u b : ℕ, u.Coprime (p ^ n - 1) →
      (Nat.digits p ((u * k + b * ((p ^ n - 1) / (p - 1))) % (p ^ n - 1))).sum +
          (Nat.digits p (u * k' % (p ^ n - 1))).sum =
        (Nat.digits p ((u * k' + b * ((p ^ n - 1) / (p - 1))) % (p ^ n - 1))).sum +
          (Nat.digits p (u * k % (p ^ n - 1))).sum) →
    ∃ i : ℕ, k' ≡ k * p ^ i [MOD p ^ n - 1]

end DiscreteGroups.sglob.DzType
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzDigTot
section
namespace DiscreteGroups.sglob.DzDig

open Finset

theorem card_primes_le {s : Finset ℕ} {a : ℕ} (hs : ∀ q ∈ s, q.Prime) (ha : ∀ q ∈ s, q ≤ a)
    (h2 : 2 ≤ a) : 2 * #s ≤ a + 1 := by
  have h : #s ≤ #(range ((a - 1) / 2 + 1)) := by
    apply card_le_card_of_injOn (fun x => (x - 1) / 2)
    · intro x hx
      have := ha x (mem_coe.mp hx)
      simp only [mem_coe, mem_range]
      omega
    · intro x hx y hy hxy
      have hx2 := (hs x (mem_coe.mp hx)).two_le
      have hy2 := (hs y (mem_coe.mp hy)).two_le
      have ox := (hs x (mem_coe.mp hx)).eq_two_or_odd
      have oy := (hs y (mem_coe.mp hy)).eq_two_or_odd
      simp only at hxy
      omega
  rw [card_range] at h
  omega

theorem prod_sq_le : ∀ s : Finset ℕ, (∀ q ∈ s, q.Prime) → s.Nonempty →
    (∏ q ∈ s, q) ^ 2 ≤ 4 * (2 * #s - 1) * (∏ q ∈ s, (q - 1)) ^ 2 := by
  intro s
  induction s using Finset.induction_on_max
  · intro _ hne
    exact absurd hne (by simp)
  next a s hlt ih =>
    intro hs _
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha2 := (hs a (mem_insert_self a s)).two_le
    have hle : ∀ q ∈ insert a s, q ≤ a := by
      intro q hq
      rcases mem_insert.mp hq with h | h
      · omega
      · exact (hlt q h).le
    have hcard := card_primes_le hs hle ha2
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha]
    rw [card_insert_of_notMem ha] at hcard
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [show b + 1 - 1 = b by omega]
    rcases s.eq_empty_or_nonempty with hs0 | hsne
    · subst hs0
      rw [prod_empty, prod_empty, card_empty]
      norm_num <;> nlinarith [ha2]
    · have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
      have ih' := ih hs' hsne
      have hs1 : 1 ≤ #s := card_pos.mpr hsne
      obtain ⟨m, hm⟩ : ∃ m, #s = m + 1 := ⟨#s - 1, by omega⟩
      rw [hm] at ih' hcard
      rw [hm]
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at ih'
      rw [show 2 * (m + 1 + 1) - 1 = 2 * m + 3 by omega]
      have hb : 2 * m + 2 ≤ b := by omega
      have h2 : (b + 1) ^ 2 * (2 * m + 1) ≤ (2 * m + 3) * b ^ 2 := by
        have := Nat.mul_le_mul_right b hb
        nlinarith
      calc ((b + 1) * ∏ q ∈ s, q) ^ 2 = (b + 1) ^ 2 * (∏ q ∈ s, q) ^ 2 := by ring
        _ ≤ (b + 1) ^ 2 * (4 * (2 * m + 1) * (∏ q ∈ s, (q - 1)) ^ 2) := Nat.mul_le_mul_left _ ih'
        _ = 4 * ((b + 1) ^ 2 * (2 * m + 1)) * (∏ q ∈ s, (q - 1)) ^ 2 := by ring
        _ ≤ 4 * ((2 * m + 3) * b ^ 2) * (∏ q ∈ s, (q - 1)) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
        _ = 4 * (2 * m + 3) * (b * ∏ q ∈ s, (q - 1)) ^ 2 := by ring

theorem pow_bound : ∀ t, 4 ≤ t → (t + 1) * t ≤ 4 * 2 ^ t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

theorem pow_le_two_pow {p n : ℕ} (hn : 1 ≤ n) (h16 : 16 * n ^ 2 < p) : p ^ (2 * n) ≤ 2 ^ p := by
  have hs : 0 < 2 * n := by omega
  have ht : 4 * (2 * n) ≤ p / (2 * n) := by
    rw [Nat.le_div_iff_mul_le hs]
    nlinarith
  have hp1 : p < (p / (2 * n) + 1) * (2 * n) := by
    nlinarith [Nat.div_add_mod p (2 * n), Nat.mod_lt p hs]
  have ht4 : 4 ≤ p / (2 * n) := by omega
  have hpt : p ≤ 2 ^ (p / (2 * n)) := by
    nlinarith [Nat.mul_le_mul_left (p / (2 * n) + 1) ht, pow_bound (p / (2 * n)) ht4]
  calc p ^ (2 * n) ≤ (2 ^ (p / (2 * n))) ^ (2 * n) := Nat.pow_le_pow_left hpt _
    _ = 2 ^ (p / (2 * n) * (2 * n)) := (pow_mul 2 _ _).symm
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self p (2 * n))

theorem sq_le_totient {N : ℕ} (hN : 2 ≤ N) :
    N ^ 2 ≤ 4 * (2 * #N.primeFactors - 1) * N.totient ^ 2 := by
  have hNpos : 0 < N := by omega
  have hSp : ∀ q ∈ N.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hSne : N.primeFactors.Nonempty := by
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show N ≠ 1 by omega)
    exact ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩⟩
  have key := prod_sq_le N.primeFactors hSp hSne
  have htot := Nat.totient_mul_prod_primeFactors N
  have hQ : 0 < ∏ q ∈ N.primeFactors, (q - 1) :=
    prod_pos (fun q hq => by have := (hSp q hq).two_le; omega)
  have h1 : (N * ∏ q ∈ N.primeFactors, (q - 1)) ^ 2
      ≤ (4 * (2 * #N.primeFactors - 1) * N.totient ^ 2) * (∏ q ∈ N.primeFactors, (q - 1)) ^ 2 := by
    rw [← htot]
    calc (N.totient * ∏ q ∈ N.primeFactors, q) ^ 2
        = N.totient ^ 2 * (∏ q ∈ N.primeFactors, q) ^ 2 := by ring
      _ ≤ N.totient ^ 2 * (4 * (2 * #N.primeFactors - 1) * (∏ q ∈ N.primeFactors, (q - 1)) ^ 2) :=
          Nat.mul_le_mul_left _ key
      _ = _ := by ring
  rw [mul_pow] at h1
  exact Nat.le_of_mul_le_mul_right h1 (pow_pos hQ 2)

theorem card_primeFactors_pos {N : ℕ} (hN : 2 ≤ N) : 1 ≤ #N.primeFactors := by
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show N ≠ 1 by omega)
  exact card_pos.mpr ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩⟩

theorem two_pow_card_le {N : ℕ} (hN : 0 < N) : 2 ^ #N.primeFactors ≤ N :=
  (pow_card_le_prod N.primeFactors (fun q => q) 2
      (fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le)).trans
    (Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N))

theorem two_n_N_lt {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (h16 : 16 * n ^ 2 < p) :
    2 * n * (p ^ n - 1) < (p - 1) * (p ^ n - 1).totient := by
  have hp2 := hp.two_le
  have hpn : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
  have hp4 : 4 ≤ p ^ 2 := by nlinarith
  have hN2 : 2 ≤ p ^ n - 1 := by omega
  have hsq := sq_le_totient hN2
  have hw1 := card_primeFactors_pos hN2
  have hω := two_pow_card_le (show 0 < p ^ n - 1 by omega)
  have hφ : 0 < (p ^ n - 1).totient := Nat.totient_pos.mpr (by omega)
  have hwp : 2 * #(p ^ n - 1).primeFactors < p := by
    by_contra hc
    push_neg at hc
    have : 2 ^ p < 2 ^ p :=
      calc 2 ^ p ≤ 2 ^ (2 * #(p ^ n - 1).primeFactors) := Nat.pow_le_pow_right (by norm_num) hc
        _ = (2 ^ #(p ^ n - 1).primeFactors) ^ 2 := by ring
        _ ≤ (p ^ n - 1) ^ 2 := Nat.pow_le_pow_left hω 2
        _ < (p ^ n) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
        _ = p ^ (2 * n) := by ring
        _ ≤ 2 ^ p := pow_le_two_pow (by omega) h16
    exact lt_irrefl _ this
  have h16' : 16 * n ^ 2 ≤ p - 1 := by omega
  have hw2 : 2 * #(p ^ n - 1).primeFactors - 1 < p - 1 := by omega
  have hlt : 16 * n ^ 2 * (2 * #(p ^ n - 1).primeFactors - 1) < (p - 1) * (p - 1) :=
    calc 16 * n ^ 2 * (2 * #(p ^ n - 1).primeFactors - 1)
        ≤ (p - 1) * (2 * #(p ^ n - 1).primeFactors - 1) := Nat.mul_le_mul_right _ h16'
      _ < (p - 1) * (p - 1) := Nat.mul_lt_mul_of_pos_left hw2 (by omega)
  have hsq2 : (2 * n * (p ^ n - 1)) ^ 2 < ((p - 1) * (p ^ n - 1).totient) ^ 2 :=
    calc (2 * n * (p ^ n - 1)) ^ 2 = 4 * n ^ 2 * (p ^ n - 1) ^ 2 := by ring
      _ ≤ 4 * n ^ 2 * (4 * (2 * #(p ^ n - 1).primeFactors - 1) * (p ^ n - 1).totient ^ 2) :=
          Nat.mul_le_mul_left _ hsq
      _ = (16 * n ^ 2 * (2 * #(p ^ n - 1).primeFactors - 1)) * (p ^ n - 1).totient ^ 2 := by ring
      _ < ((p - 1) * (p - 1)) * (p ^ n - 1).totient ^ 2 :=
          Nat.mul_lt_mul_of_pos_right hlt (pow_pos hφ 2)
      _ = ((p - 1) * (p ^ n - 1).totient) ^ 2 := by ring
  by_contra hc
  push_neg at hc
  exact absurd hsq2 (not_lt.mpr (Nat.pow_le_pow_left hc 2))

end DiscreteGroups.sglob.DzDig
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFeOrth
section
noncomputable section

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime]

def psiC (ψ₀ : AddChar (ZMod g) Circle) : AddChar (ZMod g) ℂ where
  toFun x := (ψ₀ x : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem psiC_apply (ψ₀ : AddChar (ZMod g) Circle) (x : ZMod g) : psiC ψ₀ x = (ψ₀ x : ℂ) := rfl

theorem sum_psi_mul (ψ₀ : AddChar (ZMod g) Circle) (hψ : ψ₀ ≠ 1) (c : ZMod g) :
    ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) = if c = 0 then (g : ℂ) else 0 := by
  split_ifs with hc
  · subst hc; simp [ZMod.card]
  · obtain ⟨s, hs⟩ : ∃ s, ψ₀ s ≠ 1 := by
      by_contra h
      push Not at h
      exact hψ (by ext s; rw [h s, AddChar.one_apply])
    have key : (ψ₀ s : ℂ) * ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) = ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (s * c⁻¹)) _ _ (fun t => ?_)
      rw [Equiv.coe_addRight, add_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one, AddChar.map_add_eq_mul,
        Circle.coe_mul, mul_comm]
    have hs' : (ψ₀ s : ℂ) ≠ 1 := fun h => hs (Circle.ext (by simpa using h))
    have : ((ψ₀ s : ℂ) - 1) * ∑ t : ZMod g, (ψ₀ (t * c) : ℂ) = 0 := by rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hs')

theorem sum_pi_psi (ψ₀ : AddChar (ZMod g) Circle) (hψ : ψ₀ ≠ 1) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → ZMod g) :
    ∑ f : ι → ZMod g, (ψ₀ (∑ i, f i * c i) : ℂ) = if c = 0 then (g : ℂ) ^ Fintype.card ι else 0 := by
  have h1 : ∀ f : ι → ZMod g, (ψ₀ (∑ i, f i * c i) : ℂ) = ∏ i, (ψ₀ (f i * c i) : ℂ) := fun f => by
    have hs : ∀ s : Finset ι, psiC ψ₀ (∑ i ∈ s, f i * c i) = ∏ i ∈ s, psiC ψ₀ (f i * c i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [AddChar.map_zero_eq_one]
      | insert a s ha ih => rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha]
    exact hs Finset.univ
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i t => (ψ₀ (t * c i) : ℂ))]
  simp_rw [sum_psi_mul ψ₀ hψ]
  split_ifs with hc
  · subst hc
    simp
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end DiscreteGroups.sglob.DzFe
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalFin
section
namespace DiscreteGroups.sglob.DzType

theorem addChar_eq_trace {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Finite K] [Algebra (ZMod g) K]
    (ψ₀ : AddChar (ZMod g) Circle) (h₀ : ψ₀ ≠ 1) (ψb : AddChar K Circle) :
    ∃ β : K, ∀ x : K, ψb x = ψ₀ (Algebra.trace (ZMod g) K (β * x)) := by
  classical
  have := Fintype.ofFinite K
  let F : K → AddChar K Circle := fun β =>
    (ψ₀.compAddMonoidHom (Algebra.trace (ZMod g) K).toAddMonoidHom).mulShift β
  have hF : ∀ β x, F β x = ψ₀ (Algebra.trace (ZMod g) K (β * x)) := fun β x => rfl
  have hinj : Function.Injective F := by
    intro a b hab
    by_contra hne
    have hd : a - b ≠ 0 := sub_ne_zero.2 hne
    apply h₀
    ext c
    obtain ⟨y, rfl⟩ := Algebra.trace_surjective (ZMod g) K c
    have h1 := DFunLike.congr_fun hab ((a - b)⁻¹ * y)
    rw [hF, hF] at h1
    have h2 : y = a * ((a - b)⁻¹ * y) - b * ((a - b)⁻¹ * y) := by
      rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    rw [h2, map_sub, AddChar.map_sub_eq_div, h1, div_self', AddChar.one_apply]
  have hfin : Finite (AddChar K Circle) := Finite.of_equiv _ (AddChar.circleEquivComplex (α := K)).toEquiv.symm
  have hc : Nat.card K = Nat.card (AddChar K Circle) := by
    rw [Nat.card_congr (AddChar.circleEquivComplex (α := K)).toEquiv, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, AddChar.card_eq]
  obtain ⟨β, hβ⟩ := ((Nat.bijective_iff_injective_and_card F).2 ⟨hinj, hc⟩).2 ψb
  exact ⟨β, fun x => by rw [← hβ, hF]⟩

theorem algebraMap_norm_eq_pow {g n : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Nat.card K = g ^ n) (x : K) :
    algebraMap (ZMod g) K (Algebra.norm (ZMod g) x) = x ^ ((g ^ n - 1) / (g - 1)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : g.Prime).ne_zero)
  rw [FiniteField.algebraMap_norm_eq_pow, hK, Nat.card_zmod]

theorem char_orbit {G : Type*} [Group G] (α β : G →* ℂˣ) (N : ℕ) (hN : 0 < N) (hα : ∀ t, α t ^ N = 1) (q : ℕ)
    (h1 : ∀ t, ∃ j : ℕ, β t = α t ^ q ^ j) : ∃ j : ℕ, ∀ t, β t = α t ^ q ^ j := by
  have : NeZero N := ⟨hN.ne'⟩
  have hle : α.range ≤ rootsOfUnity N ℂ := by
    rintro _ ⟨t, rfl⟩
    exact (mem_rootsOfUnity _ _).2 (hα t)
  have : Finite α.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨⟨_, t₀, rfl⟩, h0⟩ := IsCyclic.exists_generator (α := α.range)
  obtain ⟨j, hj⟩ := h1 t₀
  refine ⟨j, fun t => ?_⟩
  obtain ⟨k, hk⟩ := h0 ⟨α t, t, rfl⟩
  have hk' : α t₀ ^ k = α t := congrArg Subtype.val hk
  obtain ⟨i, hi⟩ := h1 (t * (t₀ ^ k)⁻¹)
  rw [map_mul α, map_inv α, map_zpow α, hk', mul_inv_cancel, one_pow, map_mul, map_inv, map_zpow,
    mul_inv_eq_one] at hi
  rw [hi, hj, ← hk', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

end DiscreteGroups.sglob.DzType
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzStickDefs
section
noncomputable section

namespace DiscreteGroups.sglob.Stick

open NumberField IsDedekindDomain nonZeroDivisors

universe u

def dsum (p a : ℕ) : ℕ := (Nat.digits p a).sum

def psi (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Algebra (ZMod p) k] {A : Type*} [CommRing A]
    (ζ : A) (hζ : ζ ^ p = 1) : AddChar k A :=
  (AddChar.zmodChar p hζ).compAddMonoidHom (Algebra.trace (ZMod p) k).toAddMonoidHom

structure GSDatum (p f : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (A : Type*) [CommRing A] [IsDedekindDomain A] (Q : HeightOneSpectrum A) where
  card_eq : Fintype.card k = p ^ f
  ι : k →+* A ⧸ Q.asIdeal
  ω : MulChar k A
  mk_ω : ∀ x, Ideal.Quotient.mk Q.asIdeal (ω x) = ι x
  ζ : A
  prim : IsPrimitiveRoot ζ p

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}

def ψ (D : GSDatum p f k A Q) : AddChar k A := psi p k D.ζ D.prim.pow_eq_one

def g (D : GSDatum p f k A Q) (a : ℕ) : A := gaussSum (D.ω ^ a)⁻¹ D.ψ

end GSDatum
end DiscreteGroups.sglob.Stick
end
end


import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateLimitKernelZero
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem theta_period_eq_zero_of_theta_eq_zero :
    ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q, θ Q = 0 → ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → θ t = 0 := by
  intro B _ S F ϖ C _ _ ϖ' hϖ θ hker hS hlt q hq Q hQ t ht
  have hy : ∀ n, θ (ltIter ϖ q n Q) = 0 := by
    intro n
    induction n with
    | zero => simpa [ltIter] using hQ
    | succ n ih =>
      have hs : ltIter ϖ q (n + 1) Q = ϖ * ltIter ϖ q n Q + (ltIter ϖ q n Q) ^ q := by
        simp only [ltIter, Function.iterate_succ_apply']
      rw [hs, map_add, map_mul, map_pow, ih]
      simp [show q ≠ 0 by omega]
  have hne : θ ϖ ≠ 0 := by
    intro h0
    have h1 : θ ϖ * θ ϖ' = 1 := by rw [← map_mul, hϖ, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hapos : 0 < ‖θ ϖ‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := ht 1
  have hbound : ∀ m : ℕ, ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ ‖θ ϖ‖ ^ m := by
    intro m
    obtain ⟨N, hN⟩ := hc m
    obtain ⟨s, hsS, hs⟩ := hN N le_rfl
    have h0 := (hker _).mpr hs
    simp only [map_sub, map_mul, map_pow, hy, mul_zero, zero_sub] at h0
    have h1 : θ ϖ ^ c * θ t = -(θ ϖ ^ m * θ s) := by linear_combination -h0
    have h2 : ‖θ ϖ‖ ^ c * ‖θ t‖ = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
      have := congrArg norm h1
      simpa [norm_mul, norm_pow, norm_neg] using this
    rw [h2]
    exact mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hsS)
  have hlim : Filter.Tendsto (fun m : ℕ => ‖θ ϖ‖ ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hapos.le hlt
  have hle : ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ 0 := ge_of_tendsto' hlim hbound
  have hz : ‖θ t‖ ≤ 0 := by
    by_contra hcon
    have : 0 < ‖θ ϖ‖ ^ c * ‖θ t‖ := mul_pos (pow_pos hapos c) (not_le.mp hcon)
    linarith
  exact norm_le_zero_iff.mp hz

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateScaledIterateTends
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.LogConv

variable {B : Type} [CommRing B] {S : Subring B} {ϖ : B} {J : Ideal B}

theorem near_add {m : ℕ} {x y : B} (hx : Near S ϖ J m x) (hy : Near S ϖ J m y) :
    Near S ϖ J m (x + y) := by
  obtain ⟨s, hs, h⟩ := hx
  obtain ⟨s', hs', h'⟩ := hy
  refine ⟨s + s', S.add_mem hs hs', ?_⟩
  have := J.add_mem h h'
  convert this using 1; ring

theorem near_sub {m : ℕ} {x y : B} (hx : Near S ϖ J m x) (hy : Near S ϖ J m y) :
    Near S ϖ J m (x - y) := by
  obtain ⟨s, hs, h⟩ := hx
  obtain ⟨s', hs', h'⟩ := hy
  refine ⟨s - s', S.sub_mem hs hs', ?_⟩
  have := J.sub_mem h h'
  convert this using 1; ring

theorem near_mul {a b : ℕ} {x y : B} (hx : Near S ϖ J a x) (hy : Near S ϖ J b y) :
    Near S ϖ J (a + b) (x * y) := by
  obtain ⟨s, hs, h⟩ := hx
  obtain ⟨s', hs', h'⟩ := hy
  refine ⟨s * s', S.mul_mem hs hs', ?_⟩
  have := J.add_mem (J.mul_mem_right y h) (J.mul_mem_left (ϖ ^ a * s) h')
  convert this using 1; ring

theorem near_mono (hϖ : ϖ ∈ S) {a b : ℕ} (hab : a ≤ b) {x : B} (h : Near S ϖ J b x) :
    Near S ϖ J a x := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨ϖ ^ (b - a) * s, S.mul_mem (S.pow_mem hϖ _) hs, ?_⟩
  have e : ϖ ^ a * (ϖ ^ (b - a) * s) = ϖ ^ b * s := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab]
  rwa [e]

theorem near_of_mem {s : B} (hs : s ∈ S) : Near S ϖ J 0 s := ⟨s, hs, by simp⟩

theorem near_pow {a : ℕ} {x : B} (h : Near S ϖ J a x) (e : ℕ) : Near S ϖ J (a * e) (x ^ e) := by
  induction e with
  | zero => exact ⟨1, S.one_mem, by simp⟩
  | succ e ih =>
    rw [pow_succ, Nat.mul_succ]
    exact near_mul ih h

theorem near_anti {J' : Ideal B} (hJ : J ≤ J') {m : ℕ} {x : B} (h : Near S ϖ J m x) :
    Near S ϖ J' m x := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, hJ h⟩

variable {F : ℕ → Ideal B}

theorem near_all (E : PerEnv S F ϖ) (k : ℕ) {x : B} (h : ∀ m, Near S ϖ (F k) m x) : x ∈ F k := by
  obtain ⟨s, hs, h0⟩ := h 0
  have hs' : s ∈ F k := E.closed k s hs (fun m => by
    obtain ⟨s', hs', h'⟩ := h m
    refine ⟨s', hs', ?_⟩
    have := (F k).sub_mem h' h0
    convert this using 1; ring)
  have := (F k).add_mem h0 hs'
  convert this using 1; ring

theorem near_Qpow (E : PerEnv S F ϖ) {Q : B} (hQ : Q ∈ S) {M : ℕ}
    (h : Near S ϖ (F 1) 1 (Q ^ M)) (k : ℕ) : Near S ϖ (F k) 1 (Q ^ (M * k)) := by
  induction k with
  | zero => exact ⟨0, S.zero_mem, by rw [E.top]; trivial⟩
  | succ k ih =>
    obtain ⟨s, hs, h1⟩ := ih
    obtain ⟨s', hs', h2⟩ := h
    refine ⟨Q ^ (M * k) * s' + s * (Q ^ M - ϖ ^ 1 * s'),
      S.add_mem (S.mul_mem (S.pow_mem hQ _) hs')
        (S.mul_mem hs (S.sub_mem (S.pow_mem hQ _) (S.mul_mem (S.pow_mem E.mem _) hs'))), ?_⟩
    have := E.mul_le k 1 (Ideal.mul_mem_mul h1 h2)
    convert this using 1; ring

theorem iter_succ (ϖ : B) (q n : ℕ) (x : B) :
    ltIter ϖ q (n + 1) x = ϖ * ltIter ϖ q n x + ltIter ϖ q n x ^ q := by
  unfold ltIter
  rw [Function.iterate_succ_apply']

theorem iter_mem (hϖ : ϖ ∈ S) {Q : B} (hQ : Q ∈ S) (q n : ℕ) : ltIter ϖ q n Q ∈ S := by
  induction n with
  | zero => simpa [ltIter] using hQ
  | succ n ih =>
    rw [iter_succ]
    exact S.add_mem (S.mul_mem hϖ ih) (S.pow_mem ih _)

theorem pow_congr' {y z : B} (hy : y ∈ S) (hz : z ∈ S) (h : ∃ s ∈ S, y - z = ϖ * s) (e : ℕ) :
    ∃ s ∈ S, y ^ e - z ^ e = ϖ * s := by
  induction e with
  | zero => exact ⟨0, S.zero_mem, by simp⟩
  | succ e ih =>
    obtain ⟨s, hs, hh⟩ := h
    obtain ⟨u, hu, ih⟩ := ih
    refine ⟨y ^ e * s + u * z, S.add_mem (S.mul_mem (S.pow_mem hy _) hs) (S.mul_mem hu hz), ?_⟩
    linear_combination (y ^ e) * hh + z * ih

theorem iter_congr (hϖ : ϖ ∈ S) {Q : B} (hQ : Q ∈ S) (q n : ℕ) :
    ∃ s ∈ S, ltIter ϖ q n Q - Q ^ (q ^ n) = ϖ * s := by
  induction n with
  | zero => exact ⟨0, S.zero_mem, by simp [ltIter]⟩
  | succ n ih =>
    have hy := iter_mem hϖ hQ q n
    obtain ⟨u, hu, h2⟩ := pow_congr' hy (S.pow_mem hQ (q ^ n)) ih q
    refine ⟨ltIter ϖ q n Q + u, S.add_mem hy hu, ?_⟩
    rw [iter_succ, pow_succ q n, pow_mul]
    linear_combination h2

theorem near_iter (E : PerEnv S F ϖ) {q : ℕ} (hq : 2 ≤ q) {Q : B} (hQ : Q ∈ S) {M : ℕ}
    (h : Near S ϖ (F 1) 1 (Q ^ M)) (k : ℕ) : Near S ϖ (F k) 1 (ltIter ϖ q (M * k) Q) := by
  have hL : M * k ≤ q ^ (M * k) := (Nat.lt_pow_self hq).le
  obtain ⟨s, hs, hy⟩ := iter_congr E.mem hQ q (M * k)
  have e : Q ^ (q ^ (M * k)) = Q ^ (M * k) * Q ^ (q ^ (M * k) - M * k) := by
    rw [← pow_add, Nat.add_sub_cancel' hL]
  have h1 : Near S ϖ (F k) 1 (Q ^ (q ^ (M * k))) := by
    rw [e]
    exact near_mul (near_Qpow E hQ h k) (near_of_mem (S.pow_mem hQ _))
  obtain ⟨s1, hs1, h1'⟩ := h1
  refine ⟨s1 + s, S.add_mem hs1 hs, ?_⟩
  convert h1' using 1
  linear_combination hy

theorem near_step (hϖ : ϖ ∈ S) {q : ℕ} (hq : 2 ≤ q) {b : ℕ} (hb : 1 ≤ b) {y : B}
    (h : Near S ϖ J b y) : Near S ϖ J (b + 1) (ϖ * y + y ^ q) := by
  have h0 : Near S ϖ J 1 ϖ := ⟨1, S.one_mem, by simp⟩
  have h1 : Near S ϖ J (b + 1) (ϖ * y) := by
    rw [add_comm]; exact near_mul h0 h
  have h2 : Near S ϖ J (b + 1) (y ^ q) :=
    near_mono hϖ (by nlinarith) (near_pow h q)
  exact near_add h1 h2

theorem near_iter_add (E : PerEnv S F ϖ) {q : ℕ} (hq : 2 ≤ q) {Q : B} {k n0 : ℕ}
    (h : Near S ϖ (F k) 1 (ltIter ϖ q n0 Q)) (j : ℕ) :
    Near S ϖ (F k) (1 + j) (ltIter ϖ q (n0 + j) Q) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [show n0 + (j + 1) = n0 + j + 1 from rfl, iter_succ]
    exact near_step (b := 1 + j) E.mem hq (by omega) ih

theorem iter_diff {ϖ' : B} (hu : ϖ * ϖ' = 1) (q n : ℕ) (Q : B) :
    ϖ' ^ (n + 1) * ltIter ϖ q (n + 1) Q - ϖ' ^ n * ltIter ϖ q n Q =
      ϖ' ^ (n + 1) * ltIter ϖ q n Q ^ q := by
  rw [iter_succ]
  linear_combination (ϖ' ^ n * ltIter ϖ q n Q) * hu

theorem near_diff (E : PerEnv S F ϖ) {ϖ' : B} (hu : ϖ * ϖ' = 1) {q : ℕ} (hq : 2 ≤ q) {Q : B}
    {k n0 : ℕ} (h : Near S ϖ (F k) 1 (ltIter ϖ q n0 Q)) (j : ℕ) :
    Near S ϖ (F k) (1 + j) (ϖ ^ n0 * (ϖ' ^ (n0 + j + 1) * ltIter ϖ q (n0 + j + 1) Q -
      ϖ' ^ (n0 + j) * ltIter ϖ q (n0 + j) Q)) := by
  have h1 : Near S ϖ (F k) (2 * j + 2) (ltIter ϖ q (n0 + j) Q ^ q) :=
    near_mono E.mem (by nlinarith) (near_pow (near_iter_add E hq h j) q)
  obtain ⟨s, hs, hf⟩ := h1
  refine ⟨s, hs, ?_⟩
  have hU : ϖ ^ (n0 + j + 1) * ϖ' ^ (n0 + j + 1) = 1 := by rw [← mul_pow, hu, one_pow]
  have e : ϖ ^ n0 * (ϖ' ^ (n0 + j + 1) * ltIter ϖ q (n0 + j + 1) Q -
      ϖ' ^ (n0 + j) * ltIter ϖ q (n0 + j) Q) - ϖ ^ (1 + j) * s =
      (ϖ ^ n0 * ϖ' ^ (n0 + j + 1)) * (ltIter ϖ q (n0 + j) Q ^ q - ϖ ^ (2 * j + 2) * s) := by
    rw [iter_diff hu]
    linear_combination (ϖ ^ (1 + j) * s) * hU
  rw [e]
  exact (F k).mul_mem_left _ hf

theorem level_limit (E : PerEnv S F ϖ) {ϖ' : B} (hu : ϖ * ϖ' = 1) (x : ℕ → B) {k : ℕ} (c n0 : ℕ)
    (h : ∀ j, Near S ϖ (F k) (1 + j) (ϖ ^ c * (x (n0 + j + 1) - x (n0 + j)))) :
    ∃ t, ∀ m, ∃ N, ∀ n ≥ N, Near S ϖ (F k) m (ϖ ^ c * (x n - t)) := by
  choose s hs hf using h
  obtain ⟨r, hr, hsum⟩ := E.sumS s hs
  have tel : ∀ J, ϖ ^ c * (x (n0 + J) - x n0) -
      ∑ i ∈ Finset.range J, ϖ ^ (1 + i) * s i ∈ F k := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      have := (F k).add_mem ih (hf J)
      rw [Finset.sum_range_succ, show n0 + (J + 1) = n0 + J + 1 from rfl]
      convert this using 1; ring
  have hc : ϖ ^ c * ϖ' ^ c = 1 := by rw [← mul_pow, hu, one_pow]
  refine ⟨x n0 + ϖ' ^ c * (ϖ * r), fun m => ⟨n0 + m, fun n hn => ?_⟩⟩
  obtain ⟨J, rfl⟩ : ∃ J, n = n0 + J := ⟨n - n0, by omega⟩
  have hJ : m ≤ J + 1 := by omega
  obtain ⟨a, ha, hae⟩ := hsum J
  refine near_mono E.mem hJ ⟨-a, S.neg_mem ha, ?_⟩
  have hmul : ∑ i ∈ Finset.range J, ϖ ^ (1 + i) * s i =
      ϖ * ∑ i ∈ Finset.range J, ϖ ^ i * s i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e : ϖ ^ c * (x (n0 + J) - (x n0 + ϖ' ^ c * (ϖ * r))) - ϖ ^ (J + 1) * (-a) =
      ϖ ^ c * (x (n0 + J) - x n0) - ∑ i ∈ Finset.range J, ϖ ^ (1 + i) * s i := by
    rw [hmul]
    linear_combination (-(ϖ * r)) * hc - ϖ * hae
  rw [e]
  exact tel J

theorem glue (E : PerEnv S F ϖ) {ϖ' : B} (hu : ϖ * ϖ' = 1) (x : ℕ → B)
    (h : ∀ k, ∃ (c : ℕ) (t : B), ∀ m, ∃ N, ∀ n ≥ N, Near S ϖ (F k) m (ϖ ^ c * (x n - t))) :
    ∃ t, Tends S F ϖ x t := by
  choose c t h using h
  have key : ∀ k, t (k + 1) - t k ∈ F k := fun k => by
    have hall : ∀ m, Near S ϖ (F k) m (ϖ ^ (c k + c (k + 1)) * (t (k + 1) - t k)) := fun m => by
      obtain ⟨N1, h1⟩ := h k m
      obtain ⟨N2, h2⟩ := h (k + 1) m
      have a1 := h1 (max N1 N2) (le_max_left _ _)
      have a2 := near_anti (E.anti k) (h2 (max N1 N2) (le_max_right _ _))
      have b1 := near_mul (near_of_mem (S.pow_mem E.mem (c (k + 1)))) a1
      have b2 := near_mul (near_of_mem (S.pow_mem E.mem (c k))) a2
      have b := near_sub b1 b2
      rw [zero_add] at b
      convert b using 1; ring
    have := (F k).mul_mem_left (ϖ' ^ (c k + c (k + 1))) (near_all E k hall)
    convert this using 1
    rw [← mul_assoc, ← mul_pow, mul_comm ϖ', hu, one_pow, one_mul]
  obtain ⟨T, hT⟩ := E.complete t key
  refine ⟨T, fun k => ⟨c k, fun m => ?_⟩⟩
  obtain ⟨N, hN⟩ := h k m
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s, hs, hf⟩ := hN n hn
  refine ⟨s, hs, ?_⟩
  have := (F k).sub_mem hf ((F k).mul_mem_left (ϖ ^ c k) (hT k))
  convert this using 1; ring

theorem log_converges : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}, PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      ∃ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t := by
  rintro B _ S F ϖ E ϖ' hu q hq Q hQ ⟨M, -, hN⟩
  refine glue E hu _ fun k => ?_
  obtain ⟨t, ht⟩ := level_limit E hu (fun n => ϖ' ^ n * ltIter ϖ q n Q) (M * k) (M * k)
    (near_diff E hu hq (near_iter E hq hQ hN k))
  exact ⟨M * k, t, ht⟩

end GlobalTheory.CompanionTheory.LTPer.LogConv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTorsionApproximation
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

section ThQ

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem thq_add_le {x y : C} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem thq_pow_sub (b d : C) (hb : ‖b‖ ≤ 1) (hbd : ‖b + d‖ ≤ 1) (m : ℕ) :
    ∃ e : C, ‖e‖ ≤ ‖d‖ ∧ (b + d) ^ (m + 1) - b ^ (m + 1) = d * (((m + 1 : ℕ) : C) * b ^ m + e) := by
  induction m with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨e, he, h⟩ := ih
    refine ⟨d * ((m + 1 : ℕ) : C) * b ^ m + (b + d) * e, ?_, ?_⟩
    · apply thq_add_le
      · rw [norm_mul, norm_mul, norm_pow]
        have h1 : ‖((m + 1 : ℕ) : C)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one C (m + 1)
        have h2 : ‖b‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
        calc ‖d‖ * ‖((m + 1 : ℕ) : C)‖ * ‖b‖ ^ m ≤ ‖d‖ * 1 * 1 := by gcongr
          _ = ‖d‖ := by ring
      · rw [norm_mul]
        calc ‖b + d‖ * ‖e‖ ≤ 1 * ‖d‖ := by gcongr
          _ = ‖d‖ := one_mul _
    · have h3 : (b + d) ^ (m + 1 + 1) - b ^ (m + 1 + 1)
          = (b + d) * ((b + d) ^ (m + 1) - b ^ (m + 1)) + d * b ^ (m + 1) := by ring
      rw [h3, h]
      push_cast
      ring

theorem thq_step {P : C} {q : ℕ} (hq : 2 ≤ q) (hqP : ‖(q : C)‖ ≤ ‖P‖) {a b : C}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {r : ℝ} (hab : ‖a - b‖ ≤ r) (hr : r ≤ ‖P‖) :
    ‖(P * a + a ^ q) - (P * b + b ^ q)‖ ≤ ‖P‖ * r := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hab
  obtain ⟨e, he, h⟩ := thq_pow_sub b (a - b) hb (by simpa using ha) m
  rw [add_sub_cancel] at h
  have h1 : (P * a + a ^ (m + 1)) - (P * b + b ^ (m + 1))
      = P * (a - b) + (a - b) * (((m + 1 : ℕ) : C) * b ^ m + e) := by
    rw [← h]; ring
  rw [h1]
  apply thq_add_le
  · rw [norm_mul]; gcongr
  · have h2 : ‖((m + 1 : ℕ) : C) * b ^ m + e‖ ≤ ‖P‖ := by
      apply thq_add_le
      · rw [norm_mul, norm_pow]
        have h3 : ‖b‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
        calc ‖((m + 1 : ℕ) : C)‖ * ‖b‖ ^ m ≤ ‖P‖ * 1 := by gcongr
          _ = ‖P‖ := mul_one _
      · exact he.trans (hab.trans hr)
    rw [norm_mul, mul_comm]
    gcongr

theorem thq_ball {P : C} {q : ℕ} (hP : ‖P‖ ≤ 1) {a : C} (ha : ‖a‖ ≤ 1) : ‖P * a + a ^ q‖ ≤ 1 := by
  apply thq_add_le
  · rw [norm_mul]
    calc ‖P‖ * ‖a‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul _
  · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

theorem thq_iter {P : C} {q : ℕ} (hq : 2 ≤ q) (hqP : ‖(q : C)‖ ≤ ‖P‖) (hP : ‖P‖ ≤ 1) (n : ℕ) :
    ∀ (a b : C) (r : ℝ), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a - b‖ ≤ r → r ≤ ‖P‖ →
      ‖ltIter P q n a - ltIter P q n b‖ ≤ ‖P‖ ^ n * r := by
  induction n with
  | zero => intro a b r _ _ hab _; simpa [ltIter] using hab
  | succ n ih =>
    intro a b r ha hb hab hr
    have hr0 : 0 ≤ r := (norm_nonneg _).trans hab
    have h1 := thq_step hq hqP ha hb hab hr
    have h2 : ‖P‖ * r ≤ ‖P‖ := by
      calc ‖P‖ * r ≤ 1 * r := by gcongr
        _ = r := one_mul _
        _ ≤ ‖P‖ := hr
    have h3 := ih _ _ _ (thq_ball hP ha) (thq_ball hP hb) h1 h2
    have e1 : ∀ x : C, ltIter P q (n + 1) x = ltIter P q n (P * x + x ^ q) := fun x => by
      simp only [ltIter, Function.iterate_succ_apply]
    rw [e1, e1]
    calc _ ≤ ‖P‖ ^ n * (‖P‖ * r) := h3
      _ = ‖P‖ ^ (n + 1) * r := by ring

theorem thq_map {B : Type} [CommRing B] (θ : B →+* C) (ϖ : B) (q n : ℕ) (x : B) :
    θ (ltIter ϖ q n x) = ltIter (θ ϖ) q n (θ x) := by
  induction n generalizing x with
  | zero => simp [ltIter]
  | succ n ih =>
    have e1 : ltIter ϖ q (n + 1) x = ltIter ϖ q n (ϖ * x + x ^ q) := by
      simp only [ltIter, Function.iterate_succ_apply]
    have e2 : ltIter (θ ϖ) q (n + 1) (θ x) = ltIter (θ ϖ) q n (θ ϖ * θ x + θ x ^ q) := by
      simp only [ltIter, Function.iterate_succ_apply]
    rw [e1, e2, ih]
    simp

theorem thq_tower {P : C} {q : ℕ} {w : ℕ → C} (h0 : w 0 = 0)
    (hw : ∀ n, w (n + 1) ^ q + P * w (n + 1) = w n) (n : ℕ) : ltIter P q n (w n) = 0 := by
  induction n with
  | zero => simpa [ltIter] using h0
  | succ n ih =>
    have e1 : ltIter P q (n + 1) (w (n + 1)) = ltIter P q n (P * w (n + 1) + w (n + 1) ^ q) := by
      simp only [ltIter, Function.iterate_succ_apply]
    rw [e1, add_comm, hw, ih]

end ThQ

theorem theta_eq_zero_of_congr_torsion : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ →
    ∀ (θ : B →+* C), (∀ s ∈ S, ‖θ s‖ ≤ 1) → θ ϖ ≠ 0 → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q → ‖(q : C)‖ ≤ ‖θ ϖ‖ →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → ∀ (w : ℕ → C), w 0 = 0 → (∀ n, w (n + 1) ^ q + θ ϖ * w (n + 1) = w n) →
      (∀ n, ‖θ (v n) - w n‖ ≤ ‖θ ϖ‖) →
    ∀ Q ∈ S, (∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a) → θ Q = 0 := by
  intro B _ S F ϖ C _ _ _ θ hS _ hlt q hq hqP v hv w h0 hw hvw Q hQ hQn
  have hP : ‖θ ϖ‖ ≤ 1 := hlt.le
  have hwb : ∀ n, ‖w n‖ ≤ 1 := fun n => by
    have h1 : w n = θ (v n) + -(θ (v n) - w n) := by ring
    rw [h1]
    exact thq_add_le (hS _ (hv n)) (by rw [norm_neg]; exact (hvw n).trans hP)
  have hb : ∀ n, ‖θ Q‖ ≤ ‖θ ϖ‖ ^ (n + 1) := fun n => by
    obtain ⟨a, ha, hQa⟩ := hQn n
    have h1 : θ Q = ltIter (θ ϖ) q n (θ (v n)) + θ ϖ ^ (n + 1) * θ a := by
      have h2 : θ (Q - ltIter ϖ q n (v n)) = θ (ϖ ^ (n + 1) * a) := congrArg θ hQa
      rw [map_sub, thq_map, map_mul, map_pow] at h2
      rw [← h2]; ring
    have h3 := thq_iter hq hqP hP n (θ (v n)) (w n) _ (hS _ (hv n)) (hwb n) (hvw n) le_rfl
    rw [thq_tower h0 hw n, sub_zero] at h3
    rw [h1]
    apply thq_add_le
    · calc _ ≤ ‖θ ϖ‖ ^ n * ‖θ ϖ‖ := h3
        _ = ‖θ ϖ‖ ^ (n + 1) := by ring
    · rw [norm_mul, norm_pow]
      calc ‖θ ϖ‖ ^ (n + 1) * ‖θ a‖ ≤ ‖θ ϖ‖ ^ (n + 1) * 1 := by
            gcongr
            exact hS _ ha
        _ = ‖θ ϖ‖ ^ (n + 1) := mul_one _
  have hlim : Filter.Tendsto (fun n : ℕ => ‖θ ϖ‖ ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt).comp (Filter.tendsto_add_atTop_nat 1)
  have h0' : ‖θ Q‖ ≤ 0 := ge_of_tendsto' hlim hb
  exact norm_le_zero_iff.mp h0'

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct

namespace GlobalTheory.CompanionTheory.GE

variable {X Z : Scheme.{0}}

def secsSub {E : X.Modules} (S : Subobject E) (V : X.Opens) : Submodule Γ(X, V) Γ(E, V) where
  carrier := secs S V
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨a, rfl⟩
    exact ⟨r • a, Scheme.Modules.Hom.app_smul _ _ _⟩

def pullSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [Z.Over (Spec (.of A))]
    (φ : Z ⟶ X) (E : X.Modules) (S : ℕ → Subobject E) (e : ℕ) :
    Subobject ((Scheme.Modules.pullback φ).obj E) :=
  imageSubobject ((Scheme.Modules.pullback φ).map (S e).arrow) ⊔ powSub I _ (e + 1)

def adjMap (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    E ⟶ (Scheme.Modules.pushforward φ).obj (cokernel B.arrow) :=
  (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E (cokernel B.arrow) (cokernel.π B.arrow)

def adjKer (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    Subobject E :=
  kernelSubobject (adjMap φ B)

def ChartIn (φ : Z ⟶ X) (V : X.Opens) {N : Type} [AddCommGroup N] [Module Γ(X, V) N]
    (T : Submodule Γ(X, V) N) (x : N) : Prop :=
  ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
    letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
    x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U)) ∈ LinearMap.range (T.subtype.rTensor Γ(Z, U))

def powIdeal (J₀ : X.IdealSheafData) (m : ℕ) : X.IdealSheafData where
  ideal U := J₀.ideal U ^ m
  map_ideal_basicOpen U f := by
    rw [Ideal.map_pow, J₀.map_ideal_basicOpen]
    rfl

end GlobalTheory.CompanionTheory.GE
end
end


import Mathlib

-- bundled from GroundTheory.PAdicHodge.OrthoBasis
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]

omit [IsUltrametricDist k] [IsUltrametricDist E] in

theorem exists_sub_far_of_isClosed {U : Submodule k E} (hU : IsClosed (U : Set E)) {x : E}
    (hx : x ∉ U) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ u ∈ U, ∀ u' ∈ U, s * ‖x - u‖ ≤ ‖x - u - u'‖ := by
  have hne : (U : Set E).Nonempty := ⟨0, U.zero_mem⟩
  have hd : 0 < Metric.infDist x U := (hU.notMem_iff_infDist_pos hne).1 hx
  have hlt : Metric.infDist x U < Metric.infDist x U / s := by
    rw [lt_div_iff₀ hs0]; nlinarith
  obtain ⟨u, huU, hu⟩ := (Metric.infDist_lt_iff hne).1 hlt
  refine ⟨u, huU, fun u' hu' => ?_⟩
  have h1 : Metric.infDist x U ≤ dist x (u + u') :=
    Metric.infDist_le_dist_of_mem (U.add_mem huU hu')
  rw [dist_eq_norm, ← sub_sub] at h1
  rw [dist_eq_norm] at hu
  have h2 := (lt_div_iff₀ hs0).1 hu
  nlinarith

omit [IsUltrametricDist k] in

theorem le_norm_smul_add_of_far {U : Submodule k E} {w : E} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hw : ∀ u' ∈ U, s * ‖w‖ ≤ ‖w - u'‖) (a : k) {u : E} (hu : u ∈ U) :
    s * ‖a • w‖ ≤ ‖a • w + u‖ ∧ s * ‖u‖ ≤ ‖a • w + u‖ := by
  have h1 : s * ‖a • w‖ ≤ ‖a • w + u‖ := by
    by_cases ha : a = 0
    · simp [ha]
    · have he : a • w + u = a • (w - (-a⁻¹ • u)) := by
        rw [smul_sub, smul_smul, mul_neg, mul_inv_cancel₀ ha, neg_one_smul, sub_neg_eq_add]
      rw [he, norm_smul, norm_smul]
      have := hw (-a⁻¹ • u) (U.smul_mem _ hu)
      nlinarith [norm_nonneg a]
  refine ⟨h1, ?_⟩
  have h2 : ‖u‖ ≤ max ‖a • w + u‖ ‖a • w‖ := by
    have := IsUltrametricDist.norm_add_le_max (a • w + u) (-(a • w))
    have e : a • w + u + -(a • w) = u := by abel
    rwa [e, norm_neg] at this
  rcases le_max_iff.1 h2 with h | h
  · nlinarith [norm_nonneg u]
  · nlinarith [norm_nonneg u]

variable [CompleteSpace k]

theorem exists_orthogonal_fin (n : ℕ) : ∀ (v : Fin n → E), LinearIndependent k v →
    ∀ {τ : ℝ}, 0 < τ → τ < 1 →
    ∃ w : Fin n → E, (∀ i, w i ≠ 0) ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : Fin n → k) (i : Fin n), τ * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by
  induction n with
  | zero =>
    intro v _ τ _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ i => i.elim0⟩
  | succ n ih =>
    intro v hv τ hτ0 hτ1
    set s := Real.sqrt τ with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hτ0
    have hs1 : s < 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt hτ0.le hτ1
    have hss : s * s = τ := Real.mul_self_sqrt hτ0.le
    obtain ⟨w', hw'0, hw'mem, hw'⟩ :=
      ih (fun i => v i.castSucc) (hv.comp _ (Fin.castSucc_injective n)) hs0 hs1
    set U := Submodule.span k (Set.range w') with hUdef
    have : FiniteDimensional k U := FiniteDimensional.span_of_finite k (Set.finite_range w')
    have hUc : IsClosed (U : Set E) := U.closed_of_finiteDimensional
    have hrange : (Set.range fun i : Fin n => v i.castSucc) = v '' Set.range Fin.castSucc :=
      Set.range_comp v Fin.castSucc
    have hUv : U ≤ Submodule.span k (Set.range fun i : Fin n => v i.castSucc) :=
      Submodule.span_le.2 (Set.range_subset_iff.2 hw'mem)
    have hvv : Submodule.span k (Set.range fun i : Fin n => v i.castSucc) ≤
        Submodule.span k (Set.range v) :=
      Submodule.span_mono (Set.range_comp_subset_range _ _)
    have hx : v (Fin.last n) ∉ U := by
      intro h
      have h' := hUv h
      rw [hrange] at h'
      exact hv.notMem_span_image (s := Set.range Fin.castSucc) (x := Fin.last n)
        (by rintro ⟨j, hj⟩; exact (Fin.castSucc_lt_last j).ne hj) h'
    obtain ⟨u, huU, hu⟩ := exists_sub_far_of_isClosed hUc hx hs0 hs1
    set x := v (Fin.last n) - u with hxdef
    have hx0 : x ≠ 0 := by
      intro h
      apply hx
      rw [sub_eq_zero] at h
      rw [h]; exact huU
    have hfar : ∀ u' ∈ U, s * ‖x‖ ≤ ‖x - u'‖ := hu
    refine ⟨(Fin.snoc w' x : Fin (n + 1) → E), ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hx0
      | cast i => simpa using hw'0 i
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨Fin.last n, rfl⟩) (hvv (hUv huU))
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact hvv (hw'mem i)
    · intro c i
      have hsum : ∑ j, c j • (Fin.snoc w' x : Fin (n + 1) → E) j =
          c (Fin.last n) • x + ∑ j : Fin n, c j.castSucc • w' j := by
        rw [Fin.sum_univ_castSucc, add_comm]
        simp
      have hu'U : ∑ j : Fin n, c j.castSucc • w' j ∈ U :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨h1, h2⟩ := le_norm_smul_add_of_far hs0 hs1.le hfar (c (Fin.last n)) hu'U
      rw [hsum]
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        have : τ * ‖c (Fin.last n) • x‖ ≤ s * ‖c (Fin.last n) • x‖ := by
          rw [← hss]
          exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
        linarith
      | cast i =>
        simp only [Fin.snoc_castSucc]
        have h3 := hw' (fun j => c j.castSucc) i
        rw [← hss, mul_assoc]
        nlinarith

theorem exists_orthogonal_of_linearIndependent {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : LinearIndependent k v) {t : ℝ} (ht : t < 1) :
    ∃ w : ι → E, LinearIndependent k w ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : ι → k) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by
  set τ := max t (1 / 2) with hτ
  have hτ0 : 0 < τ := lt_max_of_lt_right (by norm_num)
  have hτ1 : τ < 1 := max_lt ht (by norm_num)
  let e := Fintype.equivFin ι
  obtain ⟨w, hw0, hwmem, hw⟩ := exists_orthogonal_fin (Fintype.card ι) (v ∘ e.symm)
    (hv.comp _ e.symm.injective) hτ0 hτ1
  have hsum : ∀ c : ι → k, ∑ j, c j • w (e j) = ∑ j, (c ∘ e.symm) j • w j := by
    intro c
    have := e.sum_comp (fun j => (c ∘ e.symm) j • w j)
    simpa using this
  have horth : ∀ (c : ι → k) (i : ι), τ * ‖c i • w (e i)‖ ≤ ‖∑ j, c j • w (e j)‖ := by
    intro c i
    rw [hsum]
    simpa using hw (c ∘ e.symm) (e i)
  refine ⟨fun i => w (e i), ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := horth g i
    rw [hg, norm_zero] at h
    have h0 : ‖g i • w (e i)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (g i • w (e i))]) (norm_nonneg _)
    rw [norm_eq_zero, smul_eq_zero] at h0
    exact h0.resolve_right (hw0 (e i))
  · intro i
    have := hwmem (e i)
    rwa [e.symm.surjective.range_comp v] at this
  · intro c i
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans (horth c i)

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.SemilinearResidue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Polynomial Module Finset

namespace SemilinearResidue

section Poly

variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]

include hp in

theorem coeff_pow_prime_pow (f : k[X]) (e n : ℕ) :
    (f ^ p ^ e).coeff n = if p ^ e ∣ n then f.coeff (n / p ^ e) ^ p ^ e else 0 := by
  have : ExpChar k p := ExpChar.prime hp.out
  rw [← map_iterateFrobenius_expand p f e, coeff_map, coeff_expand (pow_pos hp.out.pos e)]
  split_ifs <;> simp [iterateFrobenius_def, hp.out.ne_zero]

noncomputable def recPoly (q : ℕ) (c : ℕ → k) (ε : k) : ℕ → k[X]
  | 0 => C (c 0) * X ^ q - C ε
  | i + 1 => recPoly q c ε i ^ q + C (c (i + 1)) * X ^ q

omit [CharP k p] in
include hp in
theorem two_le_pow {e : ℕ} (he : 0 < e) : 2 ≤ p ^ e :=
  calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos he

variable {e : ℕ}

theorem recPoly_coeff_one (he : 0 < e) (c : ℕ → k) (ε : k) :
    ∀ i, (recPoly (p ^ e) c ε i).coeff 1 = 0 := by
  have h2 := two_le_pow (p := p) he
  have hq1 : (1 : ℕ) ≠ p ^ e := by omega
  have hnd : ¬ p ^ e ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  intro i
  cases i with
  | zero => simp [recPoly, coeff_C_mul, coeff_X_pow, hq1]
  | succ i => simp [recPoly, coeff_C_mul, coeff_pow_prime_pow, hnd]

theorem recPoly_coeff_zero (c : ℕ → k) : ∀ i, (recPoly (p ^ e) c 0 i).coeff 0 = 0 := by
  have hq0 : (0 : ℕ) ≠ p ^ e := (pow_pos hp.out.pos e).ne
  intro i
  induction i with
  | zero => simp [recPoly, coeff_X_pow, hq0]
  | succ i ih =>
    simp [recPoly, coeff_pow_prime_pow, ih, hp.out.ne_zero]

theorem recPoly_coeff_q (he : 0 < e) (c : ℕ → k) (ε : k) :
    ∀ j, (recPoly (p ^ e) c ε j).coeff (p ^ e) = c j := by
  have h2 := two_le_pow (p := p) he
  have hq0 : p ^ e ≠ 0 := by omega
  intro j
  cases j with
  | zero => simp [recPoly, coeff_C_mul, coeff_X_pow, coeff_C, hp.out.ne_zero]
  | succ j =>
    simp [recPoly, coeff_C_mul, coeff_pow_prime_pow, Nat.div_self (by omega : 0 < p ^ e),
      recPoly_coeff_one he, hp.out.ne_zero]

theorem recPoly_coeff_lead (he : 0 < e) (c : ℕ → k) (ε : k) (j : ℕ) :
    ∀ t, (recPoly (p ^ e) c ε (j + t)).coeff ((p ^ e) ^ (t + 1)) = c j ^ (p ^ e) ^ t := by
  have h2 := two_le_pow (p := p) he
  intro t
  induction t with
  | zero => simpa using recPoly_coeff_q he c ε j
  | succ t ih =>
    have hne : (p ^ e) ^ (t + 1 + 1) ≠ p ^ e := by
      intro h
      have : (p ^ e) ^ (t + 1 + 1) = p ^ e * (p ^ e) ^ (t + 1) := by ring
      have h3 : 2 ≤ (p ^ e) ^ (t + 1) := le_trans h2 (Nat.le_self_pow (by omega) _)
      nlinarith
    have hdvd : p ^ e ∣ (p ^ e) ^ (t + 1 + 1) := dvd_pow_self _ (by omega)
    have hdiv : (p ^ e) ^ (t + 1 + 1) / p ^ e = (p ^ e) ^ (t + 1) := by
      rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
    rw [show j + (t + 1) = (j + t) + 1 by ring, recPoly, coeff_add, coeff_pow_prime_pow,
      if_pos hdvd, hdiv, ih, coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero, add_zero, ← pow_mul,
      pow_succ]

end Poly

section Vec

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem linearIndependent_of_notMem_span (v : ℕ → V) : ∀ m : ℕ,
    (∀ j < m, v j ∉ Submodule.span k (Set.range (fun i : Fin j => v i))) →
      LinearIndependent k (fun i : Fin m => v i)
  | 0, _ => linearIndependent_empty_type
  | m + 1, h => by
    have ih := linearIndependent_of_notMem_span v m (fun j hj => h j (by omega))
    have : (fun i : Fin (m + 1) => v i) = Fin.snoc (fun i : Fin m => v i) (v m) := by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
    rw [this]
    exact linearIndependent_finSnoc.mpr ⟨ih, h m (by omega)⟩

variable (k) in

theorem exists_rel [FiniteDimensional k V] (v : ℕ → V) :
    ∃ m, (∃ c : ℕ → k, v m = ∑ i ∈ range m, c i • v i) ∧
      LinearIndependent k (fun i : Fin m => v i) := by
  classical
  let P : ℕ → Prop := fun j => v j ∈ Submodule.span k (Set.range (fun i : Fin j => v i))
  have hex : ∃ j, P j := by
    by_contra hcon
    push Not at hcon
    have li := linearIndependent_of_notMem_span v (finrank k V + 1) (fun j _ => hcon j)
    have := li.fintype_card_le_finrank
    simp at this
  refine ⟨Nat.find hex, ?_, linearIndependent_of_notMem_span v _ (fun j hj => Nat.find_min hex hj)⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (Nat.find_spec hex)
  refine ⟨fun i => if h : i < Nat.find hex then c ⟨i, h⟩ else 0, ?_⟩
  rw [← hc, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [i.2]

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}

omit hp [CharP k p] in
theorem solve_of_root (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V) (n : ℕ)
    (c : ℕ → k) (hrel : (⇑φ)^[n + 1] z = ∑ i ∈ range (n + 1), c i • (⇑φ)^[i] z) (ε y : k)
    (hy : (recPoly (p ^ e) c ε n).eval y = y) :
    φ (∑ i ∈ range (n + 1), (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) =
      (∑ i ∈ range (n + 1), (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) + ε • z := by
  have hit : ∀ i, φ ((⇑φ)^[i] z) = (⇑φ)^[i + 1] z := fun i =>
    (Function.iterate_succ_apply' _ _ _).symm
  rw [map_sum]
  simp_rw [hφ, hit]
  rw [Finset.sum_range_succ, hy, hrel, Finset.smul_sum, Finset.sum_range_succ' _ n,
    Finset.sum_range_succ' (fun i => (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) n]
  simp only [recPoly, eval_add, eval_pow, eval_mul, eval_C, eval_X, eval_sub,
    Function.iterate_zero, id, smul_smul, add_smul, sub_smul, Finset.sum_add_distrib]
  simp only [mul_comm (y ^ p ^ e)]
  abel

theorem exists_sub_eq [IsAlgClosed k] [FiniteDimensional k V] (he : 0 < e)
    (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V) : ∃ x, φ x - x = z := by
  obtain ⟨m, ⟨c, hrel⟩, -⟩ := exists_rel k (fun i => (⇑φ)^[i] z)
  cases m with
  | zero => exact ⟨0, by simpa using hrel.symm⟩
  | succ n =>
    set P : k[X] := recPoly (p ^ e) c 1 n - X with hP
    have hc1 : P.coeff 1 = -1 := by simp [hP, recPoly_coeff_one he]
    have hdeg : P.degree ≠ 0 := by
      intro h
      rw [Polynomial.eq_C_of_degree_eq_zero h] at hc1
      simp at hc1
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root P hdeg
    have hy' : (recPoly (p ^ e) c 1 n).eval y = y := by
      have := hy.eq_zero
      simp [hP] at this
      exact sub_eq_zero.mp this
    refine ⟨∑ i ∈ range (n + 1), (recPoly (p ^ e) c 1 i).eval y • (⇑φ)^[i] z, ?_⟩
    rw [solve_of_root hφ z n c hrel 1 y hy', one_smul, add_sub_cancel_left]

theorem exists_fixed_ne_zero [IsAlgClosed k] [FiniteDimensional k V] (he : 0 < e)
    (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V)
    (hz : ∀ N, (⇑φ)^[N] z ≠ 0) : ∃ x, x ≠ 0 ∧ φ x = x := by
  obtain ⟨m, ⟨c, hrel⟩, hli⟩ := exists_rel k (fun i => (⇑φ)^[i] z)
  cases m with
  | zero => exact absurd (by simpa using hrel) (hz 0)
  | succ n =>
    have h2 := two_le_pow (p := p) he
    obtain ⟨j, hj, hcj⟩ : ∃ j ∈ range (n + 1), c j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hz (n + 1)
      rw [hrel]
      exact Finset.sum_eq_zero (fun i hi => by rw [hcon i hi, zero_smul])
    obtain ⟨t, rfl⟩ : ∃ t, n = j + t := ⟨n - j, by simp at hj; omega⟩
    set N := (p ^ e) ^ (t + 1) with hN
    have hN2 : 2 ≤ N := le_trans h2 (Nat.le_self_pow (by omega) _)
    set P : k[X] := recPoly (p ^ e) c 0 (j + t) - X with hP
    have hP0 : P.coeff 0 = 0 := by simp [hP, recPoly_coeff_zero]
    have hP1 : P.coeff 1 = -1 := by simp [hP, recPoly_coeff_one he]
    have hPN : P.coeff N ≠ 0 := by
      have hN1 : N ≠ 1 := by omega
      simp only [hP, coeff_sub, coeff_X, hN, recPoly_coeff_lead he c 0 j t]
      rw [if_neg (by omega), sub_zero]
      exact pow_ne_zero _ hcj
    obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr hP0
    have hQ0 : Q.coeff 0 = -1 := by
      rw [← hP1, hQ, show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul]
    have hQN : Q.coeff (N - 1) ≠ 0 := by
      rw [← coeff_X_mul, show N - 1 + 1 = N by omega, ← hQ]
      exact hPN
    have hdeg : Q.degree ≠ 0 := by
      intro h
      rw [Polynomial.eq_C_of_degree_eq_zero h, coeff_C, if_neg (by omega)] at hQN
      exact hQN rfl
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root Q hdeg
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [IsRoot, ← coeff_zero_eq_eval_zero, hQ0] at hy
      exact one_ne_zero (neg_eq_zero.mp hy)
    have hy' : (recPoly (p ^ e) c 0 (j + t)).eval y = y := by
      have : P.eval y = 0 := by rw [hQ, eval_mul, hy.eq_zero, mul_zero]
      simp only [hP, eval_sub, eval_X] at this
      exact sub_eq_zero.mp this
    refine ⟨_, ?_, by rw [solve_of_root hφ z (j + t) c hrel 0 y hy', zero_smul, add_zero]⟩
    intro hx
    rw [Finset.sum_range] at hx
    have := Fintype.linearIndependent_iff.mp hli
      (fun i : Fin (j + t + 1) => (recPoly (p ^ e) c 0 i).eval y) hx ⟨j + t, by omega⟩
    exact hy0 (by simpa [hy'] using this)

end Vec

end SemilinearResidue

end GroundTheory.PAdicHodge
end

-- bundled from GroundTheory.PAdicHodge.SenTateCharQp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]

theorem norm_eq_one_of_compactSpace (η : G →* ℚ_[p]ˣ) (hη : Continuous η) (σ : G) :
    ‖((η σ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
  set f : G → ℝ := fun τ => ‖((η τ : ℚ_[p]ˣ) : ℚ_[p])‖ with hf
  have hcont : Continuous f := (Units.continuous_val.comp hη).norm
  obtain ⟨τ₀, -, hτ₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hbound : ∀ τ, f τ ≤ f τ₀ := fun τ => hτ₀ (Set.mem_univ τ)
  have hpow : ∀ τ : G, ∀ n : ℕ, f (τ ^ n) = f τ ^ n := by
    intro τ n
    simp only [hf, map_pow, Units.val_pow_eq_pow_val, norm_pow]
  have hle : ∀ τ, f τ ≤ 1 := by
    intro τ
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop (f τ₀) |>.exists
    have := hbound (τ ^ n)
    rw [hpow] at this
    linarith
  have hmul : f σ * f σ⁻¹ = 1 := by
    simp only [hf, map_inv, ← norm_mul, Units.val_inv_eq_inv_val]
    rw [mul_inv_cancel₀ (Units.ne_zero _), norm_one]
  have h0 : 0 ≤ f σ⁻¹ := norm_nonneg _
  apply le_antisymm (hle σ)
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt (hle σ⁻¹)
  linarith

theorem exists_continuous_units_padicInt_lift (η : G →* ℚ_[p]ˣ) (hη : Continuous η) :
    ∃ η' : G →* ℤ_[p]ˣ, Continuous η' ∧ ∀ σ, (((η' σ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = η σ := by
  have h1 := norm_eq_one_of_compactSpace η hη
  let η' : G →* ℤ_[p]ˣ :=
    { toFun := fun σ => PadicInt.mkUnits (h1 σ)
      map_one' := by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, map_one]
        rfl
      map_mul' := fun σ τ => by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq,
          PadicInt.mkUnits_eq, map_mul, Units.val_mul] }
  refine ⟨η', ?_, fun σ => PadicInt.mkUnits_eq (h1 σ)⟩
  have hval : Continuous fun σ => ((η σ : ℚ_[p]ˣ) : ℚ_[p]) := Units.continuous_val.comp hη
  have hinv : Continuous fun σ => (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) :=
    Units.continuous_val.comp (continuous_inv.comp hη)
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun σ => (⟨((η σ : ℚ_[p]ˣ) : ℚ_[p]), (h1 σ).le⟩ : ℤ_[p])
    exact hval.subtype_mk _
  · have hn : ∀ σ, ‖(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := fun σ => by
      rw [← map_inv]; exact (h1 σ⁻¹).le
    have e : (fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) =
        fun σ => (⟨(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), hn σ⟩ : ℤ_[p]) := by
      funext σ
      apply PadicInt.ext
      rw [← map_inv η' σ]
      show ((PadicInt.mkUnits (h1 σ⁻¹) : ℤ_[p]) : ℚ_[p]) = (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])
      rw [PadicInt.mkUnits_eq, map_inv]
    change Continuous fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    rw [e]
    exact hinv.subtype_mk _

end SenTateChar

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.WAFracAlg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

namespace WAFrac

theorem galois_mem_den {R : Type*} [CommRing R] [IsDomain R] (g : R →+* R) {a b β γ T : R}
    (hgb : g b ≠ 0) (hrel : g a * b - a * g b = T * g b * b) (h : β * a = γ * b) :
    g β * a = (g γ - T * g β) * b := by
  have hg := congrArg g h
  rw [map_mul, map_mul] at hg
  refine mul_right_cancel₀ hgb ?_
  linear_combination b * hg - g β * hrel

theorem galois_sub_of_mul_eq {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S)
    (gR : R →+* R) (gS : S →+* S) (hfg : ∀ x, gS (f x) = f (gR x)) {a b T : R} {u : S}
    (hb : f b ≠ 0) (hgb : gS (f b) ≠ 0) (hrel : gR a * b - a * gR b = T * gR b * b) (hu : u * f b = f a) :
    gS u - u = f T := by
  have h1 : gS u * gS (f b) = f (gR a) := by rw [← map_mul, hu, hfg]
  have h2 := congrArg f hrel
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, ← hfg, ← hfg] at h2
  refine mul_right_cancel₀ hb (mul_right_cancel₀ hgb ?_)
  linear_combination f b * h1 - gS (f b) * hu + h2 - f b * hfg a

end WAFrac

end GroundTheory.PAdicHodge
end


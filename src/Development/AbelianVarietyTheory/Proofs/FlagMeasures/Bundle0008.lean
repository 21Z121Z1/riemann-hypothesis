import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials
section
open Filter Topology

namespace GlobalTheory

open Filter Topology in
private theorem norm_update_sub_update_sub_smul_le {k : ℕ} (F : (Fin k → ℝ) → ℂ)
    (d : Fin k → (Fin k → ℝ) → ℂ)
    (hF : ∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i))
    (i : Fin k) (t y : Fin k → ℝ) {ε δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ z, dist z t < δ → ‖d i z - d i t‖ ≤ ε) (hy : dist y t < δ) {a b : ℝ}
    (ha : dist a (t i) < δ) (hb : dist b (t i) < δ) :
    ‖F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t‖ ≤ ε * |b - a| := by
  set g : ℝ → ℂ := fun s => F (Function.update y i s) - s • d i t with hg
  have hmem : ∀ s ∈ Metric.ball (t i) δ, dist (Function.update y i s) t < δ := by
    intro s hs
    rw [dist_pi_lt_iff hδ]
    intro m
    by_cases hm : m = i
    · subst hm
      simpa using hs
    · rw [Function.update_of_ne hm]
      exact lt_of_le_of_lt (dist_le_pi_dist y t m) hy
  have hderiv : ∀ s ∈ Metric.ball (t i) δ,
      HasDerivWithinAt g (d i (Function.update y i s) - d i t) (Metric.ball (t i) δ) s := by
    intro s _
    have h1 := hF i (Function.update y i s)
    simp only [Function.update_idem, Function.update_self] at h1
    have h2 : HasDerivAt (fun u : ℝ => u • d i t) ((1 : ℝ) • d i t) s :=
      (hasDerivAt_id s).smul_const (d i t)
    rw [one_smul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ s ∈ Metric.ball (t i) δ, ‖d i (Function.update y i s) - d i t‖ ≤ ε :=
    fun s hs => hgood _ (hmem s hs)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_ball (t i) δ) (Metric.mem_ball.2 ha) (Metric.mem_ball.2 hb)
  have hdiff : g b - g a = F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t := by
    simp only [hg, sub_smul]
    abel
  rw [hdiff, Real.norm_eq_abs] at key
  exact key

open Filter Topology in

theorem _root_.GlobalTheory.hasFDerivAt_of_continuous_partials :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ),
      (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) →
      (∀ i, Continuous (d i)) →
      ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  intro k F d hF hd t
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := c / (k + 1) with hε
  have hεpos : 0 < ε := div_pos hc (by positivity)
  have hev : ∀ᶠ z in 𝓝 t, ∀ i, dist (d i z) (d i t) < ε :=
    eventually_all.2 fun i => (hd i).continuousAt.eventually (Metric.ball_mem_nhds (d i t) hεpos)
  obtain ⟨δ, hδ, hδgood⟩ := Metric.eventually_nhds_iff.1 hev
  have hgood : ∀ i z, dist z t < δ → ‖d i z - d i t‖ ≤ ε := fun i z hz =>
    (dist_eq_norm (d i z) (d i t) ▸ (hδgood hz i)).le
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [dist_zero_right] at hh
  set p : ℕ → (Fin k → ℝ) := fun j m => if (m : ℕ) < j then t m + h m else t m with hp
  set a : ℕ → ℂ := fun j => if hj : j < k then h ⟨j, hj⟩ • d ⟨j, hj⟩ t else 0 with ha
  have hp0 : p 0 = t := by
    funext m
    simp [hp]
  have hpk : p k = t + h := by
    funext m
    simp [hp, m.isLt]
  have hsumL : (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h =
      ∑ j ∈ Finset.range k, a j := by
    rw [Finset.sum_range]
    simp [ha, ContinuousLinearMap.sum_apply]
  have htel : F (t + h) - F t = ∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j)) := by
    rw [Finset.sum_range_sub (fun j => F (p j)) k, hpk, hp0]
  have hpdist : ∀ j, dist (p j) t < δ := by
    intro j
    rw [dist_pi_lt_iff hδ]
    intro m
    simp only [hp]
    split_ifs
    · rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h m) hh
    · simpa using hδ
  have hstep : ∀ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ ≤ ε * ‖h‖ := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    set i : Fin k := ⟨j, hjk⟩ with hi
    have haj : a j = ((t i + h i) - t i) • d i t := by
      simp [ha, hjk, hi]
    have hnext : p (j + 1) = Function.update (p j) i (t i + h i) := by
      funext m
      by_cases hm : m = i
      · subst hm
        simp [hp, hi]
      · have hm' : (m : ℕ) ≠ j := fun e => hm (Fin.ext e)
        rw [Function.update_of_ne hm]
        simp only [hp]
        have : (m : ℕ) < j + 1 ↔ (m : ℕ) < j := by omega
        simp only [this]
    have hcur : p j = Function.update (p j) i (t i) := by
      symm
      rw [Function.update_eq_self_iff]
      simp [hp, hi]
    have hx : dist (t i + h i) (t i) < δ := by
      rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h i) hh
    have hmain := norm_update_sub_update_sub_smul_le F d hF i t (p j) hδ (hgood i) (hpdist j)
      (a := t i) (b := t i + h i) (by rw [dist_self]; exact hδ) hx
    rw [haj, hnext]
    conv_lhs => rw [hcur]
    rw [Function.update_idem]
    refine hmain.trans ?_
    gcongr
    rw [add_sub_cancel_left]
    simpa using norm_le_pi_norm h i
  calc ‖F (t + h) - F t - (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h‖
      = ‖∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j) - a j)‖ := by
        rw [hsumL, htel, ← Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k, ε * ‖h‖ := Finset.sum_le_sum hstep
    _ = k * (ε * ‖h‖) := by simp
    _ ≤ c * ‖h‖ := by
        rw [← mul_assoc]
        gcongr
        rw [hε, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisBis
section
universe u_1 u_2

namespace GlobalTheory.NonzeroSmulMemSpanLattice

theorem exists_ne_zero_smul_mem {E : Type u_1} {V : Type u_2} [Field E] [NumberField E]
    [AddCommGroup V] [Module E V] [Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (Λ : Submodule (NumberField.RingOfIntegers E) V) (hΛ : Submodule.IsLattice E Λ) (v : V) :
    ∃ o : NumberField.RingOfIntegers E, o ≠ 0 ∧ o • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set V) := by
    rw [hΛ.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem b hax
    · rw [mul_smul]; exact Λ.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨n, d, hd, hc⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (NumberField.RingOfIntegers E) E d ≠ 0 := by
      intro h
      exact hd0 ((IsFractionRing.injective (NumberField.RingOfIntegers E) E) (by simpa using h))
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have key : (d * a) • c • x = n • a • x := by
      rw [← algebraMap_smul E (d * a), ← algebraMap_smul E n, ← algebraMap_smul E a,
        smul_smul, smul_smul, ← hc, map_mul]
      congr 1
      field_simp
    rw [key]
    exact Λ.smul_mem n hax

end GlobalTheory.NonzeroSmulMemSpanLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisExtra
section
namespace GlobalTheory.SublatticeFacts

open Matrix

theorem finiteRing_sq_sub_mul_sq_eq_of_card {A : Type} [CommRing A] {S : Subring A} {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)) (hfg : Submodule.FG Λ)
    (hden : ∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) (X : Matrix n n A) :
    ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ := by
  classical
  obtain ⟨t, rfl⟩ := hfg
  choose f hf1 hf using fun v : n → A => hden (X *ᵥ v)
  refine ⟨∏ v ∈ t, f v, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ => by have := hf1 v; omega)
  · intro y hy
    rw [Nat.cast_smul_eq_nsmul A]
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase t f hx, mul_nsmul, ← Nat.cast_smul_eq_nsmul A (f x)]
      exact Submodule.smul_of_tower_mem _ (∏ v ∈ t.erase x, f v) (hf x)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Matrix.mulVec_add, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : X *ᵥ (a • x) = a • (X *ᵥ x) := by
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
      rw [this, smul_comm]
      exact Submodule.smul_mem _ a hx

theorem main : ∀ {A : Type} [inst : CommRing A] {S : Subring A} {n : Type} [inst_1 : Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)), Submodule.FG Λ →
    (∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) →
    ∀ (X : Matrix n n A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ :=
  fun Λ hfg hden X => finiteRing_sq_sub_mul_sq_eq_of_card Λ hfg hden X

end GlobalTheory.SublatticeFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisSide
section
namespace GlobalTheory.IntSmulMemSubmodule

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact L.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hdc⟩ := hc.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    let r : NumberField.RingOfIntegers E := ⟨d • c, hdc⟩
    have h : (d * a) • (c • x) = r • (a • x) := by
      have h1 : r • (a • x) = (d • c) • (a • x) := rfl
      rw [h1, smul_assoc, mul_smul, smul_comm a c x]
    rw [h]
    exact L.smul_mem r hax

end GlobalTheory.IntSmulMemSubmodule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisTer
section
open NumberField

namespace GlobalTheory.IntMulIntegral

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (z : K) :
    ∃ M : ℤ, M ≠ 0 ∧ IsIntegral ℤ ((M : K) * z) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint

theorem main : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V]
    [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V}, Submodule.span K (↑A : Set V) = ⊤ →
    ∀ (x : V), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • x ∈ A := by
  intro K V _ _ _ _ _ _ A hA x
  have hx : x ∈ Submodule.span K (↑A : Set V) := by rw [hA]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨N₁, h₁, m₁⟩ := hy
    obtain ⟨N₂, h₂, m₂⟩ := hw
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.smul_of_tower_mem N₂ m₁
    · rw [mul_smul]; exact A.smul_of_tower_mem N₁ m₂
  | smul c y _ hy =>
    obtain ⟨N, hN, m⟩ := hy
    obtain ⟨M, hM, hint⟩ := exists_int_mul_integral c
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    let o : NumberField.RingOfIntegers K := ⟨(M : K) * c, hint⟩
    have key : (M * N) • (c • y) = o • (N • y) := by
      rw [← algebraMap_smul K o (N • y)]
      have : algebraMap (NumberField.RingOfIntegers K) K o = (M : K) * c := rfl
      rw [this, mul_smul, mul_smul, ← Int.cast_smul_eq_zsmul K M, ← Int.cast_smul_eq_zsmul K N,
        ← Int.cast_smul_eq_zsmul K N, smul_comm c ((N : K)) y]
    rw [key]
    exact A.smul_mem o m

end GlobalTheory.IntMulIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsExtra
section
namespace GlobalTheory.ClearingDenominatorsInOrder

theorem main {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (NumberField.RingOfIntegers E) W]
    [IsScalarTower (NumberField.RingOfIntegers E) E W]
    (L : Submodule (NumberField.RingOfIntegers E) W) :
    ∀ v ∈ Submodule.span E (↑L : Set W),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • v ∈ L := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, hc1, h1⟩ := hx
    obtain ⟨c2, hc2, h2⟩ := hy
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add]
    apply L.add_mem
    · rw [mul_comm, mul_smul]; exact L.smul_mem c2 h1
    · rw [mul_smul]; exact L.smul_mem c1 h2
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a
    simp only at hnd
    have hd : (d : NumberField.RingOfIntegers E) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have key : (d : NumberField.RingOfIntegers E) • (a • x) = n • x := by
      rw [← algebraMap_smul E (d : NumberField.RingOfIntegers E), smul_smul, mul_comm, hnd,
        algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact L.smul_mem n h

end GlobalTheory.ClearingDenominatorsInOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsFurther
section
namespace GlobalTheory.ExistsSmulMemLattice

open NumberField

theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    {M : Submodule (RingOfIntegers K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) a
    have hs0 : (s : RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    refine ⟨(s : RingOfIntegers K) * d, mul_ne_zero hs0 hd, ?_⟩
    have key : ((s : RingOfIntegers K) * d) • (a • x) = n • (d • x) := by
      rw [← algebraMap_smul K ((s : RingOfIntegers K) * d), ← algebraMap_smul K n (d • x),
        ← algebraMap_smul K d x, smul_smul, smul_smul, map_mul]
      congr 1
      simp only at hs
      rw [← hs]; ring
    rw [key]; exact M.smul_mem _ h

end GlobalTheory.ExistsSmulMemLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsLast
section
open NumberField

namespace GlobalTheory.SmallIntegerVanishing

theorem eq_zero_of_small (E : Type) [Field E] [NumberField E] (x : RingOfIntegers E)
    (h : ∀ w : InfinitePlace E, w (x : E) < 1) : x = 0 := by
  classical
  by_contra hx
  have hnn : ∀ (w : InfinitePlace E) (y : E), 0 ≤ w y := fun w y => w.1.nonneg y
  have hne : Algebra.norm ℤ x ≠ 0 := by
    rwa [Ne, Algebra.norm_eq_zero_iff]
  have h1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : E)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]
    have : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs hne
    exact_mod_cast this
  rw [← NumberField.InfinitePlace.prod_eq_abs_norm] at h1
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)] at h1
  have hle : ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ 1 :=
    Finset.prod_le_one (fun w _ => pow_nonneg (hnn w _) _) fun w _ => pow_le_one₀ (hnn w _) (h w).le
  have hlt : w0 (x : E) ^ w0.mult < 1 :=
    pow_lt_one₀ (hnn w0 _) (h w0) NumberField.InfinitePlace.mult_ne_zero
  have h3 : w0 (x : E) ^ w0.mult * ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ w0 (x : E) ^ w0.mult :=
    mul_le_of_le_one_right (pow_nonneg (hnn w0 _) _) hle
  linarith

theorem exists_denominator (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ d : RingOfIntegers E, d ≠ 0 ∧ ∀ y ∈ Λ, ∀ a, ∃ x : RingOfIntegers E,
      (x : E) = (d : E) * y a := by
  classical
  obtain ⟨S, hS⟩ := hΛ
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun g => Finset.univ.image fun a => g a)
  refine ⟨(y : RingOfIntegers E), by exact_mod_cast hy0, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem g hg =>
    intro a
    have hint := hy (g a) (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩)
    refine ⟨⟨y • g a, hint⟩, ?_⟩
    simp [zsmul_eq_mul]
  | zero =>
    intro a
    exact ⟨0, by simp⟩
  | add u w _ _ hu hw =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    obtain ⟨x2, h2⟩ := hw a
    refine ⟨x1 + x2, ?_⟩
    calc ((x1 + x2 : RingOfIntegers E) : E) = (x1 : E) + (x2 : E) := rfl
      _ = _ := by rw [h1, h2, Pi.add_apply, mul_add]
  | smul r u _ hu =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    refine ⟨r * x1, ?_⟩
    calc ((r * x1 : RingOfIntegers E) : E) = (r : E) * (x1 : E) := rfl
      _ = (r : E) * (((y : RingOfIntegers E) : E) * u a) := by rw [h1]
      _ = ((y : RingOfIntegers E) : E) * (r • u) a := by
        rw [Pi.smul_apply, Algebra.smul_def]
        show _ = _ * ((r : E) * u a)
        ring

theorem main (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Λ,
      (∀ (w : InfinitePlace E) (a : Fin j), w (y a) < δ) → y = 0 := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_denominator E j Λ hΛ
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hnn : ∀ (w : InfinitePlace E) (z : E), 0 ≤ w z := fun w z => w.1.nonneg z
  set M : ℝ := ∑ w : InfinitePlace E, w (d : E) with hM
  have hwM : ∀ w : InfinitePlace E, w (d : E) ≤ M := fun w =>
    Finset.single_le_sum (f := fun w : InfinitePlace E => w (d : E)) (fun w _ => hnn w _) (Finset.mem_univ w)
  have hMpos : 0 < M := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    exact lt_of_lt_of_le (NumberField.InfinitePlace.pos_iff.mpr hdE) (hwM w0)
  refine ⟨1 / M, by positivity, fun y hy hsmall => ?_⟩
  funext a
  obtain ⟨x, hx⟩ := hd y hy a
  have hx0 : x = 0 := eq_zero_of_small E x fun w => by
    rw [hx, map_mul]
    calc w (d : E) * w (y a) ≤ M * w (y a) := mul_le_mul_of_nonneg_right (hwM w) (hnn w _)
      _ < M * (1 / M) := mul_lt_mul_of_pos_left (hsmall w a) hMpos
      _ = 1 := by field_simp
  have hza : (d : E) * y a = 0 := by rw [← hx, hx0]; rfl
  simpa [hdE] using hza

end GlobalTheory.SmallIntegerVanishing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsMore
section
namespace GlobalTheory.IntegralBoundFlagMeasures

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) :
    ∀ y ∈ Submodule.span E (↑Λ : Set (Fin n → E)),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ Λ := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem _ hax) (Λ.smul_mem _ hbz)
  | smul e x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) e
    simp only at hab
    have hb : (b : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero b.2
    refine ⟨(b : 𝓞 E) * c, mul_ne_zero hb hc, ?_⟩
    have key : (b : 𝓞 E) • (e • x) = a • x := by
      rw [← algebraMap_smul E (b : 𝓞 E) (e • x), smul_smul, mul_comm, hab, algebraMap_smul]
    have : ((b : 𝓞 E) * c) • (e • x) = a • (c • x) := by
      rw [mul_comm, mul_smul, key, smul_comm]
    rw [this]
    exact Λ.smul_mem _ hcx

end GlobalTheory.IntegralBoundFlagMeasures
end


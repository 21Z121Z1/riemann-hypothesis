import Mathlib
import Formalism.IncomingBounds.Bundle0002
import Formalism.IncomingBounds.Bundle0001

-- bundled from Formalism.IncomingBounds.FlowDegreeBounds.AltChooseSumEqZero
section
noncomputable section
open scoped BigOperators
open Finset fwdDiff

namespace Formalism.IncomingBounds

theorem altChoose_sum_eq_zero (D s y : ℕ) (hs : s ≤ D) :
    ∑ k ∈ range (D + 1 + 1), ((-1 : ℤ) ^ (D + 1 - k) * ((D + 1).choose k : ℤ)) *
      (((y + k).choose s : ℕ) : ℤ) = 0 := by
  have h := fwdDiff_iter_eq_sum_shift (1 : ℕ) (fun x ↦ (x.choose s : ℤ)) (D + 1) y
  have hz : (fwdDiff (1 : ℕ))^[D + 1] (fun x ↦ (x.choose s : ℤ) : ℕ → ℤ) y = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, D + 1 = (k + 1) + s := ⟨D - s, by omega⟩
    rw [hk, Function.iterate_add_apply]
    have h0 := fwdDiff_iter_choose 0 s
    simp only [add_zero] at h0
    rw [h0]
    simp only [Nat.choose_zero_right, Nat.cast_one, Function.iterate_succ_apply, fwdDiff_const]
    rw [fwdDiff_iter_eq_sum_shift]
    simp
  rw [hz] at h
  simpa [smul_eq_mul] using h.symm

theorem top_radius_holds : TopRadius := by
  intro l hl A cap J hA hcap hJ
  set T := (Finset.range J).filter Odd with hT
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hlpos : (0 : ℝ) < l := by linarith
  have hpow : ∀ n : ℕ, (0 : ℝ) < (l : ℝ) ^ n := fun n => pow_pos hlpos n
  have hle1 : ∀ j k : ℕ, max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 ≤ 1 := by
    intro j k
    apply max_le _ zero_le_one
    have : 0 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹ := by positivity
    linarith
  let S := T.filter (fun j => A / (l : ℝ) ^ j ≤ cap j)
  by_cases hS : S.Nonempty
  · obtain ⟨k, hkS, hkmin⟩ : ∃ k ∈ S, ∀ j ∈ S, k ≤ j :=
      ⟨S.min' hS, S.min'_mem hS, fun j hj => S.min'_le j hj⟩
    have hkT : k ∈ T := (Finset.mem_filter.mp hkS).1
    have hkJ : k < J := Finset.mem_range.mp (Finset.mem_filter.mp hkT).1
    have hkcap : A / (l : ℝ) ^ k ≤ cap k := (Finset.mem_filter.mp hkS).2
    refine ⟨((l : ℝ) ^ k)⁻¹, ?_, ?_⟩
    · exact inv_anti₀ (hpow k) (pow_le_pow_right₀ hl1 hkJ.le)
    · have hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 +
          (if j = k then A * ((l : ℝ) ^ k)⁻¹ else 0) ≤ min (cap j) (A / (l : ℝ) ^ j) := by
        intro j hj
        rcases lt_trichotomy j k with hjk | hjk | hjk
        · have hjS : j ∉ S := fun h => absurd (hkmin j h) (by omega)
          have hlt : cap j < A / (l : ℝ) ^ j := by
            by_contra hc
            push Not at hc
            exact hjS (Finset.mem_filter.mpr ⟨hj, hc⟩)
          rw [if_neg (by omega), add_zero, min_eq_left hlt.le]
          calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 ≤ cap j * 1 :=
                mul_le_mul_of_nonneg_left (hle1 j k) (hcap j)
            _ = cap j := mul_one _
        · subst hjk
          rw [if_pos rfl, mul_inv_cancel₀ (hpow j).ne', sub_self, max_self, mul_zero, zero_add,
            min_eq_right hkcap, div_eq_mul_inv]
        · have h1 : 1 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (hpow k), one_mul]
            exact pow_le_pow_right₀ hl1 hjk.le
          rw [if_neg (by omega), add_zero, max_eq_right (by linarith), mul_zero]
          exact le_min (hcap j) (div_nonneg hA (hpow j).le)
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hkT] at hsum
      have : 0 ≤ A / (l : ℝ) ^ J := div_nonneg hA (hpow J).le
      linarith
  · have hS' : ∀ j ∈ T, cap j < A / (l : ℝ) ^ j := by
      intro j hj
      by_contra hc
      push Not at hc
      exact hS ⟨j, Finset.mem_filter.mpr ⟨hj, hc⟩⟩
    refine ⟨((l : ℝ) ^ J)⁻¹, le_rfl, ?_⟩
    have hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ J)⁻¹) 0 ≤
        min (cap j) (A / (l : ℝ) ^ j) := by
      intro j hj
      rw [min_eq_left (hS' j hj).le]
      calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ J)⁻¹) 0 ≤ cap j * 1 :=
            mul_le_mul_of_nonneg_left (hle1 j J) (hcap j)
        _ = cap j := mul_one _
    have hsum := Finset.sum_le_sum hterm
    rw [div_eq_mul_inv A]
    linarith

theorem newton_window_holds : NewtonWindow := by
  intro R _ I D a y0 hwin
  let f : ℕ → R := fun y => ∑ s ∈ range (D + 1), a s * ((Nat.choose y s : ℕ) : R)
  let c : ℕ → ℤ := fun k => (-1 : ℤ) ^ (D + 1 - k) * (((D + 1).choose k : ℕ) : ℤ)
  have hsm : ∀ (z : ℤ) (x : R), x ∈ I → (z : R) * x ∈ I := by
    intro z x hx
    rw [← zsmul_eq_mul]
    exact I.zsmul_mem hx z
  have hZ : ∀ y s, s ≤ D →
      ∑ k ∈ range (D + 1 + 1), (c k : R) * (((y + k).choose s : ℕ) : R) = 0 := by
    intro y s hs
    have := congrArg (Int.cast : ℤ → R) (altChoose_sum_eq_zero D s y hs)
    push_cast at this
    simpa [c] using this
  have hE : ∀ y, ∑ k ∈ range (D + 1 + 1), (c k : R) * f (y + k) = 0 := by
    intro y
    have hk : ∀ k, (c k : R) * f (y + k) =
        ∑ s ∈ range (D + 1), a s * ((c k : R) * (((y + k).choose s : ℕ) : R)) := by
      intro k
      simp only [f, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    simp_rw [hk]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s hs
    rw [← Finset.mul_sum, hZ y s (by simp at hs; omega), mul_zero]
  have hup : ∀ t, f (y0 + t) ∈ I := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t ≤ D
      · exact hwin t ht
      · obtain ⟨u, rfl⟩ : ∃ u, t = u + (D + 1) := ⟨t - (D + 1), by omega⟩
        have h := hE (y0 + u)
        rw [Finset.sum_range_succ] at h
        have hc : (c (D + 1) : R) = 1 := by simp [c]
        rw [hc, one_mul] at h
        have hmem : ∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k) ∈ I := by
          apply AddSubgroup.sum_mem
          intro k hk
          apply hsm
          have := ih (u + k) (by simp at hk; omega)
          rwa [← add_assoc] at this
        have : f (y0 + (u + (D + 1))) = -(∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k)) := by
          rw [← add_assoc]
          linear_combination h
        rw [this]
        exact I.neg_mem hmem
  have hc0i : c 0 * c 0 = 1 := by
    simp only [c, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, ← mul_pow]
    simp
  have hc0 : (c 0 : R) * (c 0 : R) = 1 := by
    rw [← Int.cast_mul, hc0i, Int.cast_one]
  have hdown : ∀ m y, y0 ≤ y + m → f y ∈ I := by
    intro m
    induction m with
    | zero =>
      intro y hy
      obtain ⟨t, rfl⟩ : ∃ t, y = y0 + t := ⟨y - y0, by omega⟩
      exact hup t
    | succ m ih =>
      intro y hy
      have h := hE y
      rw [Finset.sum_range_succ'] at h
      simp only [add_zero] at h
      have hmem : ∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1)) ∈ I := by
        apply AddSubgroup.sum_mem
        intro k _
        apply hsm
        apply ih
        omega
      have : f y = (c 0 : R) * (-(∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1)))) := by
        linear_combination (c 0 : R) * h - (f y) * hc0
      rw [this]
      exact hsm _ _ (I.neg_mem hmem)
  intro y
  exact hdown y0 y (by omega)

end Formalism.IncomingBounds
end
end

-- bundled from Formalism.IncomingBounds.FlowDegreeBounds.BaseTermLeTopTerm
section
noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

lemma cor_gam_nonneg {l : ℕ} (hl : 3 ≤ l) : 0 ≤ gam l := by
  unfold gam
  have : (3:ℝ) ≤ l := by exact_mod_cast hl
  apply div_nonneg <;> nlinarith

lemma cor_gam_le {l : ℕ} (hl : 3 ≤ l) : gam l ≤ 9 / (8 * l) := by
  unfold gam
  have h3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

lemma cor_tsum_cmp {f g b : ℕ → ℝ} (hg0 : ∀ e, 0 ≤ g e) (hgf : ∀ e, g e ≤ f e)
    (hfb : ∀ e, f e ≤ b e) (hb : Summable b) : ∑' e, g e ≤ ∑' e, f e := by
  have hf : Summable f := Summable.of_nonneg_of_le (fun e => (hg0 e).trans (hgf e)) hfb hb
  have hg : Summable g := Summable.of_nonneg_of_le hg0 hgf hf
  exact hg.tsum_le_tsum hgf hf

lemma baseTerm_le_topTerm (l d : ℕ) [NeZero d] (hl : 3 ≤ l) (TT : Finset (ZMod d))
    (nu1 nu2 : ZMod d → ℕ) (s : ZMod d) :
    baseTerm l d TT nu1 nu2 s ≤ topTerm l d TT nu1 nu2 s := by
  classical
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb : Summable (fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) := by
    have : Summable (fun e : ℕ => ((l:ℝ)⁻¹) ^ e) :=
      summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
    simpa [div_eq_mul_inv, inv_pow] using this.mul_left (nu1 s : ℝ)
  unfold topTerm baseTerm
  refine cor_tsum_cmp (b := fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) ?_ ?_ ?_ hb
  · intro e
    try dsimp only
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hn2 : (0:ℝ) ≤ (nu2 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hsub : ((nu1 s : ℝ) - nu2 s) / (l:ℝ) ^ e =
        (nu1 s : ℝ) / (l:ℝ) ^ e - (nu2 s : ℝ) / (l:ℝ) ^ e := sub_div _ _ _
    by_cases ho : Odd e
    swap
    · simp [ho]
    rcases lt_trichotomy (e : ℕ∞) (dTop d TT s) with hlt | heq | hgt
    · rw [if_pos (show Odd e ∧ (e : ℕ∞) < dTop d TT s from ⟨ho, hlt⟩)]
      split_ifs
      · apply max_le_max _ le_rfl
        rw [hsub]; linarith
      · exact le_max_right _ _
    · have hP : ∃ e0 : ℕ, dTop d TT s = (e0 : ℕ∞) ∧ s + (e : ZMod d) = s + (e0 : ZMod d) :=
        ⟨e, heq.symm, rfl⟩
      rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (lt_irrefl _ (heq ▸ h.2))),
        if_neg (show ¬ (Odd e ∧ dTop d TT s < (e : ℕ∞)) from fun h => (lt_irrefl _ (heq ▸ h.2)))]
      split_ifs with h
      · exact absurd hP h.2
      · exact le_rfl
    · rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (not_lt.mpr hgt.le h.2)),
        if_pos (show Odd e ∧ dTop d TT s < (e : ℕ∞) from ⟨ho, hgt⟩)]
      split_ifs
      · exact max_le (by rw [hsub]; linarith) hA'
      · exact hA'
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    split_ifs
    · exact max_le (by linarith) hA'
    · exact le_rfl
    · exact hA'

theorem corFromThmA_of (hF : FlowAttained) (hA : LemmaFa) (hc : LemmaFc) (hI : IncomingBound) :
    CorFromThmA := by
  refine ⟨15, ?_⟩
  intro l d inst hl hd hev TT nu1 nu2 size N0 N1 a k c CA vK w E h21 h12 hk hw hE hoff hon hcap hThm
  classical
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hg := cor_gam_nonneg hl
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ s : ZMod d, w s := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun s _ => (hw s).le)
  obtain ⟨Ws, hWs⟩ : ∃ f : ZMod d → ℝ, f = fun s => ((k:ℝ) - 1) * w s := ⟨_, rfl⟩
  obtain ⟨Dr, hDr⟩ : ∃ f : ZMod d → ℝ, f = fun s => (Dl d TT nu1 size s : ℝ) := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ f : ZMod d → ℝ, f = fun s => if s ∈ TT then 2 * w s else 0 := ⟨_, rfl⟩
  have hWsapp : ∀ s, Ws s = ((k:ℝ) - 1) * w s := fun s => by rw [hWs]
  have hDr0 : 0 ≤ Dr := fun s => by show (0:ℝ) ≤ Dr s; rw [hDr]; exact Nat.cast_nonneg _
  have hE'0 : 0 ≤ E' := fun s => by
    show (0:ℝ) ≤ E' s
    rw [hE']
    try dsimp only
    split_ifs
    · linarith [hw s]
    · exact le_rfl
  have hDE : Dr + E' = Ws + E := by
    funext s
    simp only [Pi.add_apply, hDr, hE', hWs]
    by_cases hs : s ∈ TT
    · rw [if_pos hs, hon s hs]; ring
    · rw [if_neg hs, hoff s hs]; ring

  obtain ⟨⟨sD, hsD, -, hFsD⟩, -⟩ := hA l d hl hd hev Dr hDr0
  have h2 := (hc l d hl hd hev Dr E' sD hDr0 hE'0 ⟨hsD, hFsD⟩).2
  rw [hDE] at h2
  have hE'sum : ∑ s, E' s ≤ 2 * S := by
    rw [hS, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [hE']
    dsimp only
    split_ifs <;> linarith [hw s]

  have hWs0 : 0 ≤ Ws := fun s => by
    show (0:ℝ) ≤ Ws s
    rw [hWsapp]
    have := hw s
    have : (0:ℝ) ≤ (k:ℝ) - 1 := by linarith
    positivity
  obtain ⟨⟨sW, hsW, -, hFsW⟩, -⟩ := hA l d hl hd hev Ws hWs0
  have hoptW : IsOptDual l d Ws sW := ⟨hsW, hFsW⟩
  have h3 := (hc l d hl hd hev Ws E sW hWs0 (fun s => (hE s).1) hoptW).1
  have hinc := hI l d hl hd hev Ws sW hWs0 hoptW
  have hfilt : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s ≤ S / l := by
    have e1 : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), Ws s =
        ((k:ℝ) - 1) * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    have e2 : ∑ s, Ws s = ((k:ℝ) - 1) * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    rw [e1, e2, mul_div_assoc] at hinc
    have hk1 : 0 < (k:ℝ) - 1 := by linarith
    exact le_of_mul_le_mul_left hinc hk1
  have hpt : ∀ s, E s * max (sW s - gam l) 0 ≤
      8 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0) := by
    intro s
    obtain ⟨hE0, hE4⟩ := hE s
    have hs0 := (hsW.1 s).1
    have hs1 := (hsW.1 s).2
    have hws := hw s
    have hm0 : 0 ≤ max (sW s - gam l) 0 := le_max_right _ _
    have hq : 0 ≤ 8 * w s / l := by positivity
    split_ifs with hcase
    · have hm : max (sW s - gam l) 0 ≤ 1 := max_le (by linarith) zero_le_one
      calc E s * max (sW s - gam l) 0 ≤ E s * 1 := mul_le_mul_of_nonneg_left hm hE0
        _ ≤ 4 * w s := by linarith
        _ ≤ _ := by linarith
    · push Not at hcase
      have hm : max (sW s - gam l) 0 ≤ 2 / l := max_le (by linarith) (by positivity)
      calc E s * max (sW s - gam l) 0 ≤ (4 * w s) * (2 / l) :=
            mul_le_mul hE4 hm hm0 (by linarith)
        _ = 8 * w s / l + 4 * 0 := by ring
  have hsum3 : ∑ s, E s * max (sW s - gam l) 0 ≤ 12 * S / l := by
    calc ∑ s, E s * max (sW s - gam l) 0
        ≤ ∑ s, (8 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0)) :=
          Finset.sum_le_sum (fun s _ => hpt s)
      _ = 8 * S / l + 4 * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div,
            ← Finset.mul_sum, ← hS]
      _ ≤ 8 * S / l + 4 * (S / l) := by linarith
      _ = 12 * S / l := by ring

  have hgE : gam l * ∑ s, E' s ≤ 9 / 4 * S / l := by
    have hl' : (l:ℝ) ≠ 0 := ne_of_gt hl0
    calc gam l * ∑ s, E' s ≤ gam l * (2 * S) := mul_le_mul_of_nonneg_left hE'sum hg
      _ ≤ 9 / (8 * l) * (2 * S) := mul_le_mul_of_nonneg_right (cor_gam_le hl) (by linarith)
      _ = 9 / 4 * S / l := by field_simp; ring

  have h1 : ∑ s ∈ TT, baseTerm l d TT nu1 nu2 s ≤ ∑ s ∈ TT, topTerm l d TT nu1 nu2 s :=
    Finset.sum_le_sum (fun s _ => baseTerm_le_topTerm l d hl TT nu1 nu2 s)

  unfold ThmABound at hThm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hDr] at hThm
  rw [← hS, ← hWs]
  have hfin : 12 * S / l + 9 / 4 * S / l ≤ 15 * S / l := by
    rw [← add_div, div_le_div_iff_of_pos_right hl0]
    linarith
  linarith

theorem contentShift_of (hF : FlowAttained) (hA : LemmaFa) (hc : LemmaFc) (hI : IncomingBound) :
    ContentShift := by
  intro l d inst hl hd hev th D' E hth hD' hE hED
  classical
  obtain ⟨⟨sig, hsig, -, hFsig⟩, -⟩ := hA l d hl hd hev D' hD'
  have hopt : IsOptDual l d D' sig := ⟨hsig, hFsig⟩
  have h1 := (hc l d hl hd hev D' E sig hD' hE hopt).1
  have hinc := hI l d hl hd hev D' sig hD' hopt
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hg := cor_gam_nonneg hl
  have hpt : ∀ a, E a * max (sig a - gam l) 0 ≤
      4 * th * D' a / l + 2 * th * (if 2 / (l:ℝ) ≤ sig a then D' a else 0) := by
    intro a
    have hs0 := (hsig.1 a).1
    have hs1 := (hsig.1 a).2
    have hEa := hE a
    have hDa := hD' a
    have hEDa := hED a
    have hm : max (sig a - gam l) 0 ≤ sig a := max_le (by linarith) hs0
    have hm0 : 0 ≤ max (sig a - gam l) 0 := le_max_right _ _
    have hq : 0 ≤ 4 * th * D' a / l := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hth) hDa) hl0.le
    split_ifs with hcase
    · calc E a * max (sig a - gam l) 0 ≤ E a * 1 := mul_le_mul_of_nonneg_left (hm.trans hs1) hEa
        _ ≤ 2 * th * D' a := by linarith
        _ ≤ _ := by linarith
    · push Not at hcase
      calc E a * max (sig a - gam l) 0 ≤ (2 * th * D' a) * (2 / l) :=
            mul_le_mul hEDa (hm.trans hcase.le) hm0 (mul_nonneg (mul_nonneg (by norm_num) hth) hDa)
        _ = 4 * th * D' a / l + 2 * th * 0 := by ring
  have hsum : ∑ a, E a * max (sig a - gam l) 0 ≤ 6 * th * (∑ a, D' a) / l := by
    calc ∑ a, E a * max (sig a - gam l) 0
        ≤ ∑ a, (4 * th * D' a / l + 2 * th * (if 2 / (l:ℝ) ≤ sig a then D' a else 0)) :=
          Finset.sum_le_sum (fun a _ => hpt a)
      _ = 4 * th * (∑ a, D' a) / l +
            2 * th * ∑ a ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D' a := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div,
            ← Finset.mul_sum]
      _ ≤ 4 * th * (∑ a, D' a) / l + 2 * th * ((∑ a, D' a) / l) := by
          have : 0 ≤ 2 * th := by linarith
          nlinarith
      _ = 6 * th * (∑ a, D' a) / l := by ring
  linarith

end Formalism.IncomingBounds
end
end


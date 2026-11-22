import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open GroundTheory.Heights₂.Heights.NumbersDVR

section Growth

variable {K : Type} [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in

theorem mixedDiff_of_fin_zero (bs : Fin 0 → K → ℤ) (f : (K → ℤ) → ℤ) : mixedDiff bs f = f := by
  simp [mixedDiff]

omit [Fintype K] [DecidableEq K] in

theorem mixedDiff_snoc_eq_diffStep {n : ℕ} (bs : Fin n → K → ℤ) (b : K → ℤ) (f : (K → ℤ) → ℤ) :
    mixedDiff (Fin.snoc bs b : Fin (n + 1) → K → ℤ) f = mixedDiff bs (diffStep b f) := by
  unfold mixedDiff
  rw [List.ofFn_succ']
  simp [List.concat_eq_append, List.foldr_append]

omit [Fintype K] [DecidableEq K] in

theorem degLT_diffStep_of_degLT_succ {n : ℕ} {f : (K → ℤ) → ℤ} (hf : DegLT f (n + 1)) (b : K → ℤ) :
    DegLT (diffStep b f) n := by
  intro bs
  have h := hf (Fin.snoc bs b : Fin (n + 1) → K → ℤ)
  rwa [mixedDiff_snoc_eq_diffStep] at h

omit [Fintype K] in

theorem diffStep_single_natCast (g : (K → ℤ) → ℤ) (m : K → ℕ) (k : K) :
    diffStep (Pi.single k 1) g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) =
      g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) - g (fun j => (m j : ℤ)) := by
  unfold diffStep
  congr 2
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem sum_add_pi_single_one (m : K → ℕ) (k : K) :
    ∑ j, (m + Pi.single k 1 : K → ℕ) j = ∑ j, m j + 1 := by
  simp [Finset.sum_add_distrib]

theorem abs_sub_le_of_unit_steps (G : (K → ℕ) → ℤ) (A : ℕ) (D : ℝ) (hD : 0 ≤ D) (s : ℕ) :
    ∀ a : K → ℕ, ∑ k, a k = s → (∀ k, A ≤ a k) →
      (∀ (m : K → ℕ) (k : K), (∀ j, A ≤ m j) → ∑ j, m j + 1 ≤ s →
        |((G (m + Pi.single k 1) : ℝ) - G m)| ≤ D) →
      |((G a : ℝ) - G (fun _ => A))| ≤ D * s := by
  induction s with
  | zero =>
    intro a hs ha _
    have : a = fun _ => A := by
      funext k
      have h0 := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
      have := ha k
      omega
    subst this
    simp
  | succ s ih =>
    intro a hs ha hstep
    by_cases hall : ∀ k, a k = A
    · have : a = fun _ => A := funext hall
      subst this
      simp only [sub_self, abs_zero]
      positivity
    · push Not at hall
      obtain ⟨k, hk⟩ := hall
      have hk' : A < a k := lt_of_le_of_ne (ha k) (Ne.symm hk)
      set m : K → ℕ := a - Pi.single k 1 with hm_def
      have hma : m + Pi.single k 1 = a := by
        funext j
        by_cases h : j = k
        · subst h; simp [m]; omega
        · simp [m, h]
      have hmA : ∀ j, A ≤ m j := by
        intro j
        by_cases h : j = k
        · subst h; simp [m]; omega
        · simp [m, h]; exact ha j
      have hms : ∑ j, m j = s := by
        have := sum_add_pi_single_one m k
        rw [hma, hs] at this
        omega
      have h1 := ih m hms hmA (fun m' k' hm' hs' => hstep m' k' hm' (by omega))
      have h2 := hstep m k hmA (by omega)
      rw [hma] at h2
      calc |((G a : ℝ) - G (fun _ => A))|
          = |((G a : ℝ) - G m) + ((G m : ℝ) - G (fun _ => A))| := by ring_nf
        _ ≤ |((G a : ℝ) - G m)| + |((G m : ℝ) - G (fun _ => A))| := abs_add_le _ _
        _ ≤ D + D * s := add_le_add h2 h1
        _ = D * ((s + 1 : ℕ) : ℝ) := by push_cast; ring

theorem degLT_succ_growth_natPow (n : ℕ) : ∀ g : (K → ℤ) → ℤ, DegLT g (n + 1) →
    ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, A ≤ a k) →
      |(g (fun k => (a k : ℤ)) : ℝ)| ≤ C * (((∑ k, a k : ℕ) : ℝ) + 1) ^ n := by
  induction n with
  | zero =>
    intro g hg
    have hev : ∀ᶠ m in Filter.atTop, ∀ k, diffStep (Pi.single k 1) g m = 0 := by
      refine Filter.eventually_all.2 fun k => ?_
      have := degLT_diffStep_of_degLT_succ hg (Pi.single k 1) Fin.elim0
      simpa [mixedDiff_of_fin_zero] using this
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
    set A : ℕ := ∑ k, (m₀ k).toNat
    have hA : ∀ k, m₀ k ≤ (A : ℤ) := by
      intro k
      calc m₀ k ≤ ((m₀ k).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ (A : ℤ) := by
          exact_mod_cast Finset.single_le_sum (f := fun k => (m₀ k).toNat)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    refine ⟨A, |(g (fun _ => (A : ℤ)) : ℝ)|, abs_nonneg _, fun a ha => ?_⟩
    have hw := abs_sub_le_of_unit_steps (fun a : K → ℕ => g (fun k => (a k : ℤ))) A 0 le_rfl (∑ k, a k) a rfl ha
      (fun m k hm _ => by
        have hge : m₀ ≤ fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ) := by
          intro j
          have := hA j
          have := hm j
          simp only [Pi.add_apply]
          push_cast
          have : (0 : ℤ) ≤ ((Pi.single k 1 : K → ℕ) j : ℤ) := Nat.cast_nonneg _
          omega
        have := hm₀ _ hge k
        rw [diffStep_single_natCast] at this
        rw [sub_eq_zero.mp this]
        simp)
    simp only [zero_mul] at hw
    simp only [pow_zero, mul_one]
    have := abs_sub_abs_le_abs_sub (g (fun k => (a k : ℤ)) : ℝ) (g (fun _ => (A : ℤ)) : ℝ)
    linarith
  | succ n ih =>
    intro g hg
    have hd : ∀ k, ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ j, A ≤ a j) →
        |(diffStep (Pi.single k 1) g (fun j => (a j : ℤ)) : ℝ)| ≤
          C * (((∑ j, a j : ℕ) : ℝ) + 1) ^ n :=
      fun k => ih _ (degLT_diffStep_of_degLT_succ hg _)
    choose Ak Ck hCk hbk using hd
    set A : ℕ := ∑ k, Ak k
    set C : ℝ := ∑ k, Ck k
    have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => hCk k
    have hAk : ∀ k, Ak k ≤ A := fun k =>
      Finset.single_le_sum (f := Ak) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hCk' : ∀ k, Ck k ≤ C := fun k =>
      Finset.single_le_sum (f := Ck) (fun k _ => hCk k) (Finset.mem_univ k)
    set G0 : ℝ := |(g (fun _ => (A : ℤ)) : ℝ)|
    refine ⟨A, G0 + C, by positivity, fun a ha => ?_⟩
    set X : ℝ := ((∑ k, a k : ℕ) : ℝ) + 1 with hX
    have hS0 : (0 : ℝ) ≤ ((∑ k, a k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hX1 : 1 ≤ X := by simp only [X]; linarith
    have hw := abs_sub_le_of_unit_steps (fun a : K → ℕ => g (fun k => (a k : ℤ))) A (C * X ^ n) (by positivity)
      (∑ k, a k) a rfl ha (fun m k hm hs => by
        have h1 := hbk k (m + Pi.single k 1) (fun j => le_trans (hAk k)
          (le_trans (hm j) (by simp)))
        rw [diffStep_single_natCast] at h1
        push_cast at h1 ⊢
        refine le_trans h1 ?_
        have hs' : ((∑ j, (m + Pi.single k 1 : K → ℕ) j : ℕ) : ℝ) + 1 ≤ X := by
          rw [sum_add_pi_single_one]; simp only [X]; exact_mod_cast Nat.add_le_add_right hs 1
        have h0 : (0 : ℝ) ≤ ((∑ j, (m + Pi.single k 1 : K → ℕ) j : ℕ) : ℝ) + 1 := by positivity
        push_cast at hs' h0
        exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hs' n) (hCk k))
          (mul_le_mul_of_nonneg_right (hCk' k) (by positivity)))
    simp only at hw
    have htri := abs_sub_abs_le_abs_sub (g (fun k => (a k : ℤ)) : ℝ) (g (fun _ => (A : ℤ)) : ℝ)
    have hSX : ((∑ k, a k : ℕ) : ℝ) ≤ X := by simp only [X]; linarith
    have hXn : X ^ n * ((∑ k, a k : ℕ) : ℝ) ≤ X ^ (n + 1) := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left hSX (by positivity)
    have hX1n : 1 ≤ X ^ (n + 1) := one_le_pow₀ hX1
    have hG0 : 0 ≤ G0 := abs_nonneg _
    push_cast at hw htri
    calc |(g (fun k => (a k : ℤ)) : ℝ)|
        ≤ G0 + C * X ^ n * ((∑ k, a k : ℕ) : ℝ) := by push_cast; simp only [G0]; linarith
      _ ≤ G0 * X ^ (n + 1) + C * X ^ (n + 1) := by
          have := mul_le_mul_of_nonneg_left hXn hC
          have := mul_le_mul_of_nonneg_left hX1n hG0
          nlinarith
      _ = (G0 + C) * X ^ (n + 1) := by ring

end Growth

theorem DegLTGrowth.proof : DegLTGrowth.Statement := by
  intro K _ _ n g hg
  cases n with
  | zero =>
    have hev : ∀ᶠ m in Filter.atTop, g m = 0 := by
      simpa [mixedDiff_of_fin_zero] using hg Fin.elim0
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
    refine ⟨∑ k, (m₀ k).toNat, 0, fun a ha => ?_⟩
    have hge : m₀ ≤ fun k => (a k : ℤ) := by
      intro k
      calc m₀ k ≤ ((m₀ k).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ ((∑ k, (m₀ k).toNat : ℕ) : ℤ) := by
          exact_mod_cast Finset.single_le_sum (f := fun k => (m₀ k).toNat)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        _ ≤ (a k : ℤ) := by exact_mod_cast ha k
    rw [hm₀ _ hge]
    simp
  | succ n =>
    obtain ⟨A, C, _, hb⟩ := degLT_succ_growth_natPow n g hg
    refine ⟨A, C, fun a ha => ?_⟩
    have h := hb a ha
    have he : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
    push_cast at h
    exact h

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff

noncomputable section

namespace EventualPolynomial

variable {K : Type} [DecidableEq K]

def listDiff (L : List K) (g : (K → ℕ) → ℚ) : (K → ℕ) → ℚ :=
  L.foldr (fun k h => Δ_[(Pi.single k 1 : K → ℕ)] h) g

theorem listDiff_cons (k : K) (L : List K) (g : (K → ℕ) → ℚ) (t : K → ℕ) :
    listDiff (k :: L) g t = listDiff L g (t + Pi.single k 1) - listDiff L g t := rfl

theorem listDiff_append (L₁ L₂ : List K) (g : (K → ℕ) → ℚ) :
    listDiff (L₁ ++ L₂) g = listDiff L₁ (listDiff L₂ g) := by
  simp [listDiff, List.foldr_append]

theorem listDiff_replicate (j : ℕ) (k : K) (g : (K → ℕ) → ℚ) :
    listDiff (List.replicate j k) g = (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]; rfl

theorem listDiff_zero (L : List K) : listDiff L (0 : (K → ℕ) → ℚ) = 0 := by
  induction L with
  | nil => rfl
  | cons k L ih =>
    funext t
    rw [listDiff_cons, ih]
    simp

theorem listDiff_long {n : ℕ} {g : (K → ℕ) → ℚ}
    (hg : ∀ L : List K, L.length = n + 1 → listDiff L g = 0) (L : List K) (hL : n + 1 ≤ L.length) :
    listDiff L g = 0 := by
  rw [← List.take_append_drop (L.length - (n + 1)) L, listDiff_append,
    hg _ (by simp; omega), listDiff_zero]

def binomPoly (c : ℕ) (k : K) (j : ℕ) : MvPolynomial K ℚ :=
  C ((j.factorial : ℚ)⁻¹) * ∏ i ∈ range j, (X k - C ((c + i : ℕ) : ℚ))

omit [DecidableEq K] in
theorem binomPoly_totalDegree (c : ℕ) (k : K) (j : ℕ) : (binomPoly c k j).totalDegree ≤ j := by
  unfold binomPoly
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ range j, (X k - C ((c + i : ℕ) : ℚ) : MvPolynomial K ℚ).totalDegree
        ≤ ∑ _i ∈ range j, 1 :=
          sum_le_sum fun i _ => (totalDegree_sub_C_le _ _).trans (by rw [totalDegree_X])
    _ = j := by simp

omit [DecidableEq K] in
theorem eval_binomPoly (c : ℕ) (k : K) (j : ℕ) (x : K → ℚ) (m : ℕ) (hx : x k = (m : ℚ) + c) :
    eval x (binomPoly c k j) = (m.choose j : ℚ) := by
  unfold binomPoly
  simp only [map_mul, eval_C, map_prod, map_sub, eval_X, hx]
  have : ∏ i ∈ range j, ((m : ℚ) + c - ((c + i : ℕ) : ℚ)) = ∏ i ∈ range j, ((m : ℚ) - i) :=
    prod_congr rfl fun i _ => by push_cast; ring
  rw [this, ← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

theorem newton (c : ℕ) (s : Finset K) : ∀ (n : ℕ) (g : (K → ℕ) → ℚ),
    (∀ L : List K, L.length = n + 1 → listDiff L g = 0) →
    ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ n ∧
      (∀ x y : K → ℚ, (∀ i ∈ s, x i = y i) → eval x P = eval y P) ∧
      ∀ t : K → ℕ, (∀ i ∉ s, t i = 0) → g t = eval (fun i => (t i : ℚ) + c) P := by
  induction s using Finset.induction_on with
  | empty =>
    intro n g _
    refine ⟨C (g 0), by rw [totalDegree_C]; exact Nat.zero_le _, fun x y _ => by simp,
      fun t ht => ?_⟩
    have : t = 0 := funext fun i => ht i (Finset.notMem_empty i)
    simp [this]
  | insert k s hk ih =>
    intro n g hg
    have hg' := listDiff_long hg
    have hsub : ∀ j, ∀ L : List K, L.length = n - j + 1 →
        listDiff L ((Δ_[(Pi.single k 1 : K → ℕ)])^[j] g) = 0 := by
      intro j L hL
      rw [← listDiff_replicate, ← listDiff_append]
      exact hg' _ (by simp; omega)
    choose P hPdeg hPloc hPval using fun j => ih (n - j) _ (hsub j)
    have hzero : ∀ j, n + 1 ≤ j → (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g = 0 := fun j hj => by
      rw [← listDiff_replicate]; exact hg' _ (by simp; omega)
    refine ⟨∑ j ∈ range (n + 1), binomPoly c k j * P j, ?_, ?_, ?_⟩
    · refine totalDegree_finsetSum_le fun j hj => ?_
      have := mem_range.mp hj
      refine (totalDegree_mul _ _).trans ?_
      have h1 := binomPoly_totalDegree c k j
      have h2 := hPdeg j
      omega
    · intro x y hxy
      simp only [map_sum, map_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [hPloc j x y fun i hi => hxy i (mem_insert_of_mem hi)]
      congr 1
      unfold binomPoly
      simp [hxy k (mem_insert_self k s)]
    · intro t ht
      set y : K → ℕ := Function.update t k 0 with hy
      have hyt : t = y + t k • (Pi.single k 1 : K → ℕ) := by
        funext i
        by_cases h : i = k
        · subst h; simp [hy]
        · simp [hy, h]
      have hys : ∀ i ∉ s, y i = 0 := by
        intro i hi
        by_cases h : i = k
        · subst h; simp [hy]
        · simp only [hy, Function.update_of_ne h]; exact ht i (by simp [h, hi])
      have hty : ∀ i ∈ s, (t i : ℚ) + c = (y i : ℚ) + c := by
        intro i hi
        have : i ≠ k := fun h => hk (h ▸ hi)
        simp [hy, Function.update_of_ne this]
      have e1 : ∑ j ∈ range (t k + 1), (t k).choose j • (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y
          = ∑ j ∈ range (n + t k + 1), ((t k).choose j : ℚ) * (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y := by
        simp only [nsmul_eq_mul]
        refine sum_subset (s₁ := range (t k + 1)) (fun j hj => by rw [mem_range] at hj ⊢; omega) fun j _ hj => ?_
        rw [mem_range, not_lt] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      have e2 : eval (fun i => (t i : ℚ) + c) (∑ j ∈ range (n + 1), binomPoly c k j * P j)
          = ∑ j ∈ range (n + t k + 1), ((t k).choose j : ℚ) * (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y := by
        rw [map_sum]
        refine Eq.trans ?_ (sum_subset (s₁ := range (n + 1)) (fun j hj => by rw [mem_range] at hj ⊢; omega) fun j _ hj => ?_)
        · refine sum_congr rfl fun j _ => ?_
          rw [map_mul, eval_binomPoly c k j _ (t k) rfl, hPval j y hys,
            hPloc j _ (fun i => (y i : ℚ) + c) hty]
        · rw [mem_range, not_lt] at hj
          rw [hzero j hj]
          simp
      calc g t = g (y + t k • (Pi.single k 1 : K → ℕ)) := congrArg g hyt
        _ = ∑ j ∈ range (t k + 1), (t k).choose j • (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y :=
          shift_eq_sum_fwdDiff_iter _ g (t k) y
        _ = _ := by rw [e1, e2]

theorem listDiff_eq_mixedDiff (f : (K → ℤ) → ℤ) (c : ℕ) (L : List K) (t : K → ℕ) :
    listDiff L (fun t => (f (fun k => (c : ℤ) + t k) : ℚ)) t =
      (((L.map fun k => (Pi.single k 1 : K → ℤ)).foldr diffStep f)
        (fun k => (c : ℤ) + t k + L.count k) : ℚ) := by
  induction L generalizing t with
  | nil => simp [listDiff]
  | cons k L ih =>
    rw [listDiff_cons, ih, ih, List.map_cons, List.foldr_cons, diffStep, Int.cast_sub]
    have a1 : (fun i => (c : ℤ) + (((t + Pi.single k 1 : K → ℕ) i : ℕ) : ℤ) + (L.count i : ℤ)) =
        fun i => (c : ℤ) + t i + ((k :: L).count i : ℤ) := by
      funext i
      by_cases h : i = k
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    have a2 : (fun i => (c : ℤ) + t i + (L.count i : ℤ)) =
        (fun i => (c : ℤ) + t i + ((k :: L).count i : ℤ)) - Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    rw [a1, a2]

end EventualPolynomial

open EventualPolynomial in

theorem EventualPolynomial.proof : EventualPolynomial.Statement := by
  intro K _ _ n f hf
  have hall : ∀ᶠ m in Filter.atTop, ∀ v : Fin (n + 1) → K,
      mixedDiff (fun i => (Pi.single (v i) 1 : K → ℤ)) f m = 0 :=
    Filter.eventually_all.mpr fun v => hf _
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.mp hall
  set c : ℕ := ∑ k, (m₁ k).toNat with hcdef
  have hc : ∀ k, m₁ k ≤ (c : ℤ) := fun k => by
    have h1 : (m₁ k).toNat ≤ c := single_le_sum (f := fun k => (m₁ k).toNat) (fun _ _ => Nat.zero_le _) (mem_univ k)
    have h2 := Int.self_le_toNat (m₁ k)
    omega
  have hL : ∀ L : List K, L.length = n + 1 →
      listDiff L (fun t => (f (fun k => (c : ℤ) + t k) : ℚ)) = 0 := by
    intro L hlen
    funext t
    rw [listDiff_eq_mixedDiff]
    obtain ⟨v, rfl⟩ : ∃ v : Fin (n + 1) → K, List.ofFn v = L :=
      ⟨fun i => L[i.val]'(by have := i.isLt; omega),
        List.ext_getElem (by simp [hlen]) fun j _ _ => by rw [List.getElem_ofFn]⟩
    have hv := hm₁ (fun k => (c : ℤ) + t k + (List.ofFn v).count k)
      (fun k => by have := hc k; dsimp; omega) v
    have hmap : (List.ofFn v).map (fun k => (Pi.single k 1 : K → ℤ)) =
        List.ofFn (fun i => (Pi.single (v i) 1 : K → ℤ)) := by rw [List.map_ofFn]; rfl
    rw [hmap]
    change ((mixedDiff (fun i => (Pi.single (v i) 1 : K → ℤ)) f _ : ℤ) : ℚ) = 0
    rw [hv]
    simp
  obtain ⟨P, hdeg, -, hval⟩ := newton c univ n _ hL
  refine ⟨P, c, hdeg, fun a ha => ?_⟩
  have h1 : ((f fun k => (c : ℤ) + ((a k - c : ℕ) : ℤ) : ℤ) : ℚ) =
      eval (fun i => ((a i - c : ℕ) : ℚ) + c) P :=
    hval (fun k => a k - c) fun i hi => absurd (mem_univ i) hi
  have e1 : (fun k => (c : ℤ) + ((a k - c : ℕ) : ℤ)) = fun k => (a k : ℤ) :=
    funext fun k => by have := ha k; omega
  have e2 : (fun i => ((a i - c : ℕ) : ℚ) + c) = fun k => (a k : ℚ) :=
    funext fun k => by rw [Nat.cast_sub (ha k)]; ring
  rw [e1, e2] at h1
  exact h1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeZariskiDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem PrimeZariskiDense.eval_eq_zero_of_mem_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {F : MvPolynomial (Σ k, ι k) ℂ}
    (hF : F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))) : eval z F = 0 := by
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hz.2 f hf
  exact RingHom.mem_ker.mp (hle hF)

theorem PrimeZariskiDense.proof (h1 : ComplexFormsOnPoints.Statement) (h2 : PrimeComplexRadical.Statement)
    (h3 : ComplexMinimalPrimesContract.Statement) : PrimeZariskiDense.Statement := by
  intro K _ ι _ P j hP hj g hg z hz
  by_cases hrel : IsRelevant P
  · set Pc := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPc
    have hgj : g * map (Int.castRingHom ℂ) j ∈ Pc := by
      refine h1 K ι P hP hrel _ fun w hw => ?_
      rw [map_mul]
      by_cases hjw : eval w (map (Int.castRingHom ℂ) j) = 0
      · rw [hjw, mul_zero]
      · rw [hg w hw hjw, zero_mul]
    have hrad : Pc.radical = Pc := (h2 (Σ k, ι k) P hP).radical
    have hgPc : g ∈ Pc := by
      rw [← hrad, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro Q hQ
      change Q ∈ Pc.minimalPrimes at hQ
      have hQp : Q.IsPrime := hQ.1.1
      have hjQ : map (Int.castRingHom ℂ) j ∉ Q := by
        intro h
        apply hj
        rw [← h3 (Σ k, ι k) P hP Q hQ, Ideal.mem_comap]
        exact h
      exact (hQp.mem_or_mem (hQ.1.2 hgj)).resolve_right hjQ
    exact PrimeZariskiDense.eval_eq_zero_of_mem_map P hz hgPc
  · exfalso
    simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
    obtain ⟨k, hk⟩ := hrel
    obtain ⟨i, hi⟩ := hz.1 k
    apply hi
    simpa using hz.2 _ (hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end


import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0005
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ColumnSpanNumericalFacts

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SegStartSpec
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem posAdd_cdist {n' : ℕ} (x y : Fin n') : posAdd x (cdist x y) = y := by
  apply Fin.ext
  show (x.val + (y.val + n' - x.val) % n') % n' = y.val
  rw [Nat.add_mod_mod]
  have h : x.val + (y.val + n' - x.val) = y.val + n' := by
    have := x.isLt
    omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

theorem mem_segDists {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (d : ℕ) :
    d ∈ segDists TT j ↔ ∃ s ∈ TT, ¬ Even s.val ∧ 0 < cdist (segStart TT j) s ∧
      cdist (segStart TT j) s < segG TT j ∧ cdist (segStart TT j) s = d := by
  unfold segDists
  rw [Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Finset.mem_filter] at hs
    exact ⟨s, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, rfl⟩
  · rintro ⟨s, hs, h1, h2, h3, rfl⟩
    exact ⟨s, Finset.mem_filter.2 ⟨hs, h1, h2, h3⟩, rfl⟩

theorem segPos_spec {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ TT ∧ ¬ Even (segPos TT j i).val ∧
      cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i ∧ 0 < (segDists TT j).get i ∧
      (segDists TT j).get i < segG TT j := by
  obtain ⟨s, hs, h1, h2, h3, h4⟩ := (mem_segDists TT j _).1 (List.get_mem (segDists TT j) i)
  have e : segPos TT j i = s := by
    unfold segPos
    rw [← h4]
    exact posAdd_cdist _ _
  rw [e]
  exact ⟨hs, h1, h4, h4 ▸ h2, h4 ▸ h3⟩

theorem mem_evenTops {n' : ℕ} (TT : Finset (Fin n')) (x : Fin n') : x ∈ evenTops TT ↔ x ∈ TT ∧ Even x.val := by
  unfold evenTops
  rw [Finset.mem_sort, Finset.mem_filter]

theorem segStart_spec {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segStart TT j ∈ TT ∧ Even (segStart TT j).val :=
  (mem_evenTops TT _).1 (List.get_mem _ _)

theorem ex_cast {n' : ℕ} {TT : Finset (Fin n')} (z : Fin n' → ℤ) (c : ℕ) (s : Fin n') (hs : s ∈ TT) (h0 : 0 ≤ z s) :
    ((ex (TT := TT) (fun s => (z s + c).toNat) s : ℕ) : ℝ) = (z s : ℝ) + c := by
  unfold ex
  rw [dif_pos hs]
  have h : ((z s + c).toNat : ℤ) = z s + c := Int.toNat_of_nonneg (by positivity)
  have h' : (((z s + c).toNat : ℤ) : ℝ) = ((z s + c : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  exact h'

theorem min_shift (b a c P : ℝ) (hc : 0 ≤ c) (hP : 1 ≤ P) : min (b + c) ((a + c) / P) ≤ min b (a / P) + c := by
  have hP0 : 0 < P := by linarith
  have h1 : c / P ≤ c := div_le_self hc hP
  have h2 : (a + c) / P = a / P + c / P := add_div _ _ _
  rw [← min_add_add_right]
  exact min_le_min le_rfl (by rw [h2]; linarith)

open Classical in
theorem tle_of (hO : RestOddTops) {K : Cst} (hK : K.Pos) {CH : ℝ} {C : ℝ} (hC : 4 * K.Ct + 4 ≤ C)
    {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) (aw bw : Fin X.n' → ℤ)
    (hw : ∀ s ∈ X.TT, aw s ∈ IaZ X.m X.Y X.ar ∧ bw s ∈ IbZ X.bl X.bu) :
    (X.tStar K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) : ℝ) + 2 * X.n' * X.ccl ≤
      tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw := by
  have hseg2 : 2 ≤ numSeg X.TT := h.2.2.2.1
  have hbl : 0 ≤ X.bl := by
    have := lowb_of h
    linarith [B.hb8]
  have hp1 : (1 : ℝ) ≤ X.p := by linarith [B.hp25]
  have har200 : (200 : ℝ) ≤ X.ar := by
    have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
    linarith [B.hpa]
  have ha0 : ∀ s ∈ X.TT, 0 ≤ aw s := fun s hs =>
    le_trans (Int.ceil_nonneg (by linarith)) (Finset.mem_Icc.1 (hw s hs).1).1
  have hb0 : ∀ s ∈ X.TT, 0 ≤ bw s := fun s hs =>
    le_trans (Int.ceil_nonneg hbl) (Finset.mem_Icc.1 (hw s hs).2).1
  set S : ℝ := ∑ y ∈ X.TT.filter (fun y => ¬ IsTypeV y),
      min (bw y : ℝ) ((aw (yPrev X.TT y) : ℝ) / (X.p : ℝ) ^ dPrev X.TT y) with hS
  set S' : ℝ := ∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        min ((ex (TT := X.TT) (fun s => (bw s + X.ccl).toNat) (segPos X.TT j i) : ℕ) : ℝ)
          (((ex (TT := X.TT) (fun s => (aw s + X.ccl).toNat) (segStart X.TT j) : ℕ) : ℝ) /
            (X.p : ℝ) ^ ((segDists X.TT j).get i)) with hS'
  have hcount : (∑ j : Fin (numSeg X.TT), ∑ _i : Fin (segS X.TT j), (X.ccl : ℝ)) ≤ X.N * X.ccl := by
    have := hO X.n' X.TT hseg2 (fun _ _ _ => (X.ccl : ℝ))
    rw [this, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold Dat.N
    exact_mod_cast Finset.card_filter_le _ _
  have hSS : S' ≤ S + X.N * X.ccl := by
    have e := hO X.n' X.TT hseg2 (fun y x d => min (bw y : ℝ) ((aw x : ℝ) / (X.p : ℝ) ^ d))
    have h1 : S' ≤ ∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        (min (bw (segPos X.TT j i) : ℝ) ((aw (segStart X.TT j) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i)) +
          (X.ccl : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      rw [ex_cast bw X.ccl _ (segPos_spec X.TT j i).1 (hb0 _ (segPos_spec X.TT j i).1),
        ex_cast aw X.ccl _ (segStart_spec X.TT j).1 (ha0 _ (segStart_spec X.TT j).1)]
      exact min_shift _ _ _ _ (by positivity) (one_le_pow₀ hp1)
    simp only [Finset.sum_add_distrib] at h1
    rw [e] at h1
    linarith
  have hS'0 : 0 ≤ S' := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    exact le_min (by positivity) (by positivity)

  have ha1 : (1 : ℝ) ≤ X.a := by linarith [B.haa]
  have hlog0 : 0 ≤ Real.log X.a := Real.log_nonneg ha1
  have hlog2 : Real.log X.a ≤ 2 * Real.log X.ar := by
    have h10 : (X.a : ℝ) ≤ X.ar ^ 2 := by
      have : 2 * X.ar ≤ X.ar * X.ar := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have e : X.ar ^ 2 = X.ar * X.ar := by ring
      rw [e]
      linarith [B.haa1]
    have := Real.log_le_log (by linarith) h10
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hC0 : 0 < K.C₀ := hK.1
  have hcn : 0 ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 := by positivity
  have hLa'0 : 0 ≤ LaI K.C₀ X.N₁ X.a := by unfold LaI; exact mul_nonneg hcn hlog0
  have hLa'2 : LaI K.C₀ X.N₁ X.a ≤ 2 * LaI K.C₀ X.N₁ X.ar := by
    unfold LaI
    have := mul_le_mul_of_nonneg_left hlog2 hcn
    linarith
  have hk1 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
  have hb : 0 < X.b' := by linarith [B.hb8]
  have hp0 : (0 : ℝ) < X.p := by linarith
  have hJ : X.J0 K = LaI K.C₀ X.N₁ X.a * X.b' / X.k := rfl
  have key := tle_abs K.Ct C X.N X.N₁ X.p X.k ((X.p : ℝ) ^ X.G') (Real.logb X.p X.ar) X.ar X.a X.b'
    (LaI K.C₀ X.N₁ X.ar) (LaI K.C₀ X.N₁ X.a) X.ccl X.cStar X.n' S S' hK.2.2.2.2.2.2.2.1 hC (by linarith [B.hN2])
    B.hN1 hp0 hk1 B.hQ (by linarith [B.hL1]) (by linarith) (by linarith) (by linarith [B.haa1]) hb
    (by linarith [B.hLa1]) hLa'0 hLa'2 (by positivity) (by positivity) (by positivity) hSS
  have hx0 : 0 ≤ X.t0 K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) + X.N * X.J0 K := by
    rw [initial_level_formula, hJ]
    have hCt : 0 < K.Ct := hK.2.2.2.2.2.2.2.1
    have hk0 : 0 < X.k := by linarith
    have hQ0 : (0 : ℝ) < (X.p : ℝ) ^ X.G' := by positivity
    have := hS'0
    positivity
  have hceil : (X.tStar K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) : ℝ) ≤
      (S' + K.Ct * X.N * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.a * X.a / (X.p * X.k) +
        LaI K.C₀ X.N₁ X.a * X.b' / X.k + X.k * (X.p : ℝ) ^ X.G' +
        (X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + 2 * X.N * X.ccl + 2 * X.n' * X.ccl))) +
        X.N * (LaI K.C₀ X.N₁ X.a * X.b' / X.k) + 1 := by
    have h1 := (Nat.ceil_lt_add_one hx0).le
    have h2 := initial_level_formula K X (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat)
    unfold Dat.tStar
    calc _ ≤ _ := h1
      _ = _ := by rw [h2, hJ]
  have htI : tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw =
      S + C * X.N * X.N₁ * (X.ar / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.ar * X.ar / (X.p * X.k) +
          LaI K.C₀ X.N₁ X.ar * X.b' / X.k) +
        C * X.N * ((X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + C * X.N * X.k * Real.logb X.p X.ar + 4 * X.N * X.ccl +
          2 * X.n' * X.ccl) + X.k * (X.p : ℝ) ^ X.G' + X.k * Real.logb X.p X.ar + X.ccl) + 2 * X.n' * X.ccl := rfl
  rw [htI]
  linarith

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdFinalFacts
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

structure WinFacts (K : Cst) (X : Dat) : Prop where
  arnn : 0 ≤ X.ar
  uann : 0 ≤ X.ar + X.ar / (X.k * X.Y)
  blge : X.b' / 2 ≤ X.bl
  bule : X.bu ≤ 3 * X.b' / 2
  bunn : 0 ≤ X.bu
  wa_ge : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' - 1 ≤ ((X.Wa 0).card : ℝ)
  wb_ge : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' / X.k - 1 ≤ ((X.Wb 0).card : ℝ)

theorem card_first_window (X : Dat) : (X.Wa 0).card = X.ua + 1 - X.a := by
  simp only [Dat.Wa, Nat.add_zero, Nat.card_Icc]

theorem card_second_window (X : Dat) : (X.Wb 0).card = X.ub + 1 - X.lb := by
  simp only [Dat.Wb, Nat.add_zero, Nat.card_Icc]

private theorem natCast_sub_le_natCast_natSub (x y : ℕ) : (x : ℝ) - y ≤ ((x - y : ℕ) : ℝ) := by
  rcases le_total y x with hxy | hxy
  · rw [Nat.cast_sub hxy]
  · rw [Nat.sub_eq_zero_of_le hxy, Nat.cast_zero, sub_nonpos]
    exact_mod_cast hxy

theorem winFacts_of (K : Cst) (hK : K.Pos) (CH : ℝ) (hCH : K.TLP ≤ CH) (X : Dat) (h : X.Hyp K.C₀ CH) :
    WinFacts K X := by
  have B := base_of K hK CH hCH X h
  have hH := h
  unfold Dat.Hyp HypI at hH
  obtain ⟨_, _, _, _, _, _, _, _, h9, h10, h11, h12, h13, h14, _, h16, _, _, _, _, _, _, h23, h24⟩ := hH
  have hN : (X.TT.card : ℝ) = X.N := rfl
  have hk : (X.m : ℝ) + 1 = X.k := rfl
  rw [hN, hk] at h12 h16
  have har : 0 < X.ar := by
    have : 0 ≤ (X.p : ℝ) * X.b' := by positivity
    linarith [B.hpa]
  have hk0 : 0 < X.k := by linarith [B.hk5]
  have hY := B.hY
  have hY0 : 0 < X.Y := by linarith
  have h108 : (108 : ℝ) ≤ CH := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hCH
  have hYb : 0 ≤ X.Yb := by linarith
  have hLa := B.hLa1
  have hN0 : (0 : ℝ) ≤ X.N := by positivity
  refine ⟨har.le, by positivity, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [card_first_window]
    have e1 := Nat.lt_floor_add_one (X.ar + X.ar / (X.k * X.Y))
    have e2 := B.haa1
    have e3 := natCast_sub_le_natCast_natSub (X.ua + 1) X.a
    push_cast at e3
    have hkey : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' ≤ X.ar / (X.k * X.Y) := by
      rw [le_div_iff₀ (by positivity)]
      have f1 : X.k * X.Y ^ 2 * X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * Real.log X.ar * X.b' ≤ X.ar := by
        rwa [le_div_iff₀ h9] at h16
      have hYl : 1 ≤ X.Y * Real.log X.ar := one_le_mul_of_one_le_of_one_le hY B.hlog1
      have hpos : 0 ≤ X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' * (X.k * X.Y) := by positivity
      have f2 := mul_le_mul_of_nonneg_left hYl hpos
      nlinarith
    have e4 : (X.ua : ℝ) = ⌊X.ar + X.ar / (X.k * X.Y)⌋₊ := rfl
    linarith
  · rw [card_second_window]
    have e1 := Nat.lt_floor_add_one X.bu
    have e2 := Nat.ceil_lt_add_one (show 0 ≤ X.bl by linarith)
    have e3 := natCast_sub_le_natCast_natSub (X.ub + 1) X.lb
    push_cast at e3
    have e4 : (X.ub : ℝ) = ⌊X.bu⌋₊ := rfl
    have e5 : (X.lb : ℝ) = ⌈X.bl⌉₊ := rfl
    linarith

theorem below_abs (N wa wb c : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (ha : 2 * Y * N * c ≤ wa) (hb : 2 * Y * N * c ≤ wb)
    (hwa : 0 < wa) (hwb : 0 < wb) :
    (wa : ℝ) ^ N * (wb : ℝ) ^ N - ((wa - c : ℕ) : ℝ) ^ N * ((wb - c : ℕ) : ℝ) ^ N ≤
      1 / Y * ((wa : ℝ) ^ N * (wb : ℝ) ^ N) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [pow_zero, mul_one, sub_self]
    positivity
  have hY0 : 0 < Y := by linarith
  have hA : (0 : ℝ) < wa := by exact_mod_cast hwa
  have hB : (0 : ℝ) < wb := by exact_mod_cast hwb
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have h2YN : 1 ≤ 2 * Y * N := by nlinarith
  have hcc := mul_le_mul_of_nonneg_right h2YN hc0
  have hca : (c : ℝ) ≤ wa := by linarith
  have hcb : (c : ℝ) ≤ wb := by linarith
  have hca' : c ≤ wa := by exact_mod_cast hca
  have hcb' : c ≤ wb := by exact_mod_cast hcb
  rw [Nat.cast_sub hca', Nat.cast_sub hcb']

  have bern : ∀ A : ℝ, 0 < A → (c : ℝ) ≤ A → A ^ N * (1 - N * c / A) ≤ (A - c) ^ N := by
    intro A hA hcA
    have hq : -2 ≤ -((c : ℝ) / A) := by
      have : (c : ℝ) / A ≤ 1 := (div_le_one hA).2 hcA
      linarith
    have hb := one_add_mul_le_pow hq N
    have e : (A - c) ^ N = A ^ N * (1 + -((c : ℝ) / A)) ^ N := by
      rw [← mul_pow]
      congr 1
      field_simp
      ring
    rw [e]
    have e2 : 1 - (N : ℝ) * c / A = 1 + (N : ℝ) * -((c : ℝ) / A) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hpa : (N : ℝ) * c / wa ≤ 1 / (2 * Y) := by
    rw [div_le_div_iff₀ hA (by positivity)]
    nlinarith
  have hpb : (N : ℝ) * c / wb ≤ 1 / (2 * Y) := by
    rw [div_le_div_iff₀ hB (by positivity)]
    nlinarith
  have hp0 : 0 ≤ (N : ℝ) * c / wa := by positivity
  have hq0 : 0 ≤ (N : ℝ) * c / wb := by positivity
  have hhalf : 1 / (2 * Y) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h1 := bern wa hA hca
  have h2 := bern wb hB hcb
  set p := (N : ℝ) * c / wa
  set q := (N : ℝ) * c / wb
  have hX : 0 ≤ (wa : ℝ) ^ N * (wb : ℝ) ^ N := by positivity
  have hprod : (wa : ℝ) ^ N * (1 - p) * ((wb : ℝ) ^ N * (1 - q)) ≤ ((wa : ℝ) - c) ^ N * ((wb : ℝ) - c) ^ N :=
    mul_le_mul h1 h2 (by nlinarith [pow_pos hB N]) (by nlinarith [pow_pos hA N])
  have hpq : 1 - 1 / Y ≤ (1 - p) * (1 - q) := by
    have e : 1 / Y = 1 / (2 * Y) + 1 / (2 * Y) := by field_simp; ring
    nlinarith [mul_nonneg hp0 hq0]
  have h3 : (wa : ℝ) ^ N * (wb : ℝ) ^ N * (1 - 1 / Y) ≤ (wa : ℝ) ^ N * (wb : ℝ) ^ N * ((1 - p) * (1 - q)) :=
    mul_le_mul_of_nonneg_left hpq hX
  nlinarith

theorem threshold_final_facts (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => ColumnSpanNumericalFacts K) := by
  have h108T : (108 : ℝ) ≤ K.TLP := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨K.TLP, 1, by linarith, one_pos, ?_⟩
  intro CH hCH C _ X h
  have W := winFacts_of K hK CH hCH X h
  have B := base_of K hK CH hCH X h
  have hH := h
  unfold Dat.Hyp HypI at hH
  obtain ⟨_, _, _, _, _, _, _, _, h9, h10, h11, h12, h13, h14, _, h16, _, _, _, _, _, _, h23, h24⟩ := hH
  have hN : (X.TT.card : ℝ) = X.N := rfl
  have hk : (X.m : ℝ) + 1 = X.k := rfl
  rw [hN, hk] at h24
  have h108 : (108 : ℝ) ≤ CH := le_trans h108T hCH
  have hY := B.hY
  have hk5 := B.hk5
  have hN2 := B.hN2
  have hLa := B.hLa1
  have hk0 : 0 < X.k := by linarith
  have hYb : (108 : ℝ) ≤ X.Yb := by linarith
  have hq : (1 : ℝ) ≤ ((X.p : ℝ) ^ X.G') ^ 4 := one_le_pow₀ B.hQ
  have hc8 : (8 : ℝ) ≤ X.cStar := by
    have : 8 ≤ X.cStar := le_trans (by omega) h23
    exact_mod_cast this
  have hS : (8 : ℝ) ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl := by
    have : (0 : ℝ) ≤ X.N * X.ccl + X.n' * X.ccl := by positivity
    linarith
  have hSN : (X.N : ℝ) * X.ccl ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl := by
    have : (0 : ℝ) ≤ X.cStar + X.n' * X.ccl := by positivity
    linarith
  set S := (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl with hSdef
  set q := ((X.p : ℝ) ^ X.G') ^ 4 with hqdef
  have hN1 : (1 : ℝ) ≤ X.N := by linarith
  have hcc : (X.ccl : ℝ) ≤ q * S := by
    have hc0 : (0 : ℝ) ≤ X.ccl := by positivity
    have e1 : (X.ccl : ℝ) ≤ X.N * X.ccl := le_mul_of_one_le_left hc0 hN1
    have e2 : S ≤ q * S := le_mul_of_one_le_left (by linarith) hq
    linarith
  have hR : 0 ≤ CH * X.k ^ 3 * X.N * X.Y := by
    have : 0 ≤ CH := by linarith
    positivity
  have hC : CH * X.k ^ 3 * (X.N * X.ccl * X.Y) ≤ X.b' := by
    calc CH * X.k ^ 3 * (X.N * X.ccl * X.Y) = CH * X.k ^ 3 * X.N * X.Y * X.ccl := by ring
      _ ≤ CH * X.k ^ 3 * X.N * X.Y * (q * S) := mul_le_mul_of_nonneg_left hcc hR
      _ = CH * X.k ^ 3 * X.N * q * S * X.Y := by ring
      _ ≤ X.b' := h24
  have hk2 : (25 : ℝ) ≤ X.k ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hk5 2
    norm_num at this
    linarith
  have hCk2 : (2700 : ℝ) ≤ CH * X.k ^ 2 := by
    have := mul_le_mul h108 hk2 (by norm_num) (by linarith)
    linarith
  have hbk : X.k ≤ X.b' := by
    have f1 : (1 : ℝ) ≤ CH * X.k ^ 2 := by linarith
    have f2 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N := one_le_mul_of_one_le_of_one_le f1 hN1
    have f3 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N * q := one_le_mul_of_one_le_of_one_le f2 hq
    have f4 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N * q * S := one_le_mul_of_one_le_of_one_le f3 (by linarith)
    have f5 : (1 : ℝ) ≤ CH * X.k ^ 2 * X.N * q * S * X.Y := one_le_mul_of_one_le_of_one_le f4 hY
    have f6 := mul_le_mul_of_nonneg_left f5 hk0.le
    linarith
  have hu : (0 : ℝ) ≤ X.N * X.ccl * X.Y := by positivity
  have h2k : 2 * X.k ≤ CH * X.k ^ 3 := by
    have := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ CH * X.k ^ 2 by linarith) hk0.le
    linarith
  have h2uk := mul_le_mul_of_nonneg_right h2k hu
  have hQ1 : (108 : ℝ) * 2 ≤ X.Yb * X.N := mul_le_mul hYb hN2 (by norm_num) (by linarith)
  have hQ2 : (216 : ℝ) ≤ X.Yb * X.N * LaI K.C₀ X.N₁ X.ar := by
    have := mul_le_mul hQ1 hLa (by norm_num) (by linarith)
    linarith
  have hb8 := B.hb8
  have hQb : (216 : ℝ) * X.b' ≤ X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' :=
    mul_le_mul_of_nonneg_right hQ2 (by linarith)
  have h2u : 2 * (X.N * X.ccl * X.Y) ≤ CH * X.k ^ 3 * (X.N * X.ccl * X.Y) :=
    mul_le_mul_of_nonneg_right (by linarith) hu
  have hwa := W.wa_ge
  have hwb := W.wb_ge
  have hwbD : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' / X.k - 1 ≥ 2 * X.Y * X.N * X.ccl := by
    rw [ge_iff_le, le_sub_iff_add_le, le_div_iff₀ hk0]
    linarith
  have haN : 2 * X.Y * X.N * X.ccl ≤ ((X.Wa 0).card : ℝ) := by linarith
  have hbN : 2 * X.Y * X.N * X.ccl ≤ ((X.Wb 0).card : ℝ) := by linarith
  have hwa0 : 0 < (X.Wa 0).card := by
    have : (0 : ℝ) < (X.Wa 0).card := by linarith
    exact_mod_cast this
  have hwb0 : 0 < (X.Wb 0).card := by
    have : (0 : ℝ) < (X.Wb 0).card := by
      have : (1 : ℝ) ≤ X.b' / X.k := (one_le_div hk0).2 hbk
      have e : X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * X.b' / X.k = X.Yb * X.N * LaI K.C₀ X.N₁ X.ar * (X.b' / X.k) := by
        ring
      have := mul_le_mul hQ2 this (by norm_num) (by linarith)
      linarith
    exact_mod_cast this
  have ea : (Finset.Icc (X.a + X.ccl) X.ua).card = (X.Wa 0).card - X.ccl := by
    rw [Nat.card_Icc, card_first_window, Nat.sub_sub]
  have eb : (Finset.Icc (X.lb + X.ccl) X.ub).card = (X.Wb 0).card - X.ccl := by
    rw [Nat.card_Icc, card_second_window, Nat.sub_sub]
  refine ⟨W.arnn, W.uann, by linarith [W.blge], W.bunn, hY, by exact_mod_cast B.hN1,
    by exact_mod_cast (show (1 : ℝ) ≤ X.N by linarith), ⟨hwa0, hwb0⟩, ?_, ?_⟩
  · rw [ea, eb]
    exact below_abs X.N _ _ X.ccl X.Y hY haN hbN hwa0 hwb0
  · have hb0 : 0 < X.b' := by linarith
    have hY0 : 0 < X.Y := by linarith
    rw [div_le_div_iff₀ hb0 hY0]
    have h12k : 12 * X.k ≤ CH * X.k ^ 3 := by
      have := mul_le_mul_of_nonneg_right (show (12 : ℝ) ≤ CH * X.k ^ 2 by linarith) hk0.le
      linarith
    have := mul_le_mul_of_nonneg_right h12k hu
    linarith

end Formalism.MainNotions.flipOneThree.Pf

end
end


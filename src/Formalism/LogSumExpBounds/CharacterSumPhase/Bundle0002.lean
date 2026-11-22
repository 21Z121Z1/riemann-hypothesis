import Formalism.LogSumExpBounds.NuclearBound

-- bundled from Formalism.LogSumExpBounds.CharacterSumPhase.DecayAsm
section
namespace Formalism.NuclearRankWeightBounds.P

open Finset Formalism.NuclearRankWeightBounds.D

theorem decay_of_facts : Formalism.NuclearRankWeightBounds.D.CBWeights → Formalism.NuclearRankWeightBounds.D.NuclearBound → Formalism.NuclearRankWeightBounds.D.RankBlock →
    Formalism.NuclearRankWeightBounds.D.LogSumExp → Formalism.NuclearRankWeightBounds.D.WeightedOff → Formalism.NuclearRankWeightBounds.D.Decay := by
  intro hCB hNB hRB hLSE hWO N s ep h Y hs0 hY hzero hh
  have hW := hWO N s ep h Y hY hzero hh
  set H := hs Y with hH
  set r := Real.sqrt (2 * (q0 ep : ℝ)) with hr
  set c := min 1 (r * H)⁻¹ with hc
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := le_min zero_le_one (inv_nonneg.mpr (mul_nonneg hr0 hH0))
  have hbound : ∑ j, |hY.eigenvalues j| ≤ r * H := by
    refine (hNB N Y hY).trans ?_
    apply mul_le_mul_of_nonneg_right _ hH0
    apply Real.sqrt_le_sqrt
    exact_mod_cast hRB N ep Y hzero
  have key : ∀ i ∈ Ico 1 N, 0 < (lead (NormedSpace.exp Y) i).re ∧
      c * (∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2) / 4
        ≤ Real.log (lead (NormedSpace.exp Y) i).re := by
    intro i hi
    have hiN : i ≤ N := (mem_Ico.mp hi).2.le
    obtain ⟨w, hw0, hw1, hlead, hmean, hsec⟩ := hCB N Y hY i hiN
    have hdiag : ∑ a ∈ univ.filter (fun a : Fin N => a.val < i), (Y a a).re = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      simp [hzero a a rfl]
    rw [hdiag] at hmean hsec
    have hre : (lead (NormedSpace.exp Y) i).re = ∑ J ∈ powersetCard i (univ : Finset (Fin N)),
        w J * Real.exp (∑ j ∈ J, hY.eigenvalues j) := by
      rw [hlead, Complex.ofReal_re]
    have hy : ∀ J : Finset (Fin N), |∑ j ∈ J, hY.eigenvalues j| ≤ r * H := by
      intro J
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans ?_ hbound
      exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ J) (fun _ _ _ => abs_nonneg _)
    rw [hre]
    constructor
    · calc (0:ℝ) < Real.exp (-(r * H)) := Real.exp_pos _
        _ = ∑ J ∈ powersetCard i (univ : Finset (Fin N)), w J * Real.exp (-(r * H)) := by
          rw [← Finset.sum_mul, hw1, one_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro J _
          apply mul_le_mul_of_nonneg_left _ (hw0 J)
          exact Real.exp_le_exp.mpr (neg_le_of_abs_le (hy J))
    · have e : ∀ f : Finset (Fin N) → ℝ,
          ∑ J : ↥(powersetCard i (univ : Finset (Fin N))), f J.1
            = ∑ J ∈ powersetCard i (univ : Finset (Fin N)), f J :=
        fun f => Finset.sum_coe_sort _ f
      have e1 := e (fun J => w J)
      have e2 := e (fun J => w J * (∑ j ∈ J, hY.eigenvalues j))
      have e3 := e (fun J => w J * (∑ j ∈ J, hY.eigenvalues j) ^ 2)
      have e4 := e (fun J => w J * Real.exp (∑ j ∈ J, hY.eigenvalues j))
      have := hLSE (↥(powersetCard i (univ : Finset (Fin N)))) (fun J => w J.1)
        (fun J => ∑ j ∈ J.1, hY.eigenvalues j) (r * H) (fun J => hw0 _)
        (by rw [e1, hw1]) (by rw [e2, hmean]) (fun J => hy _)
      rw [e3, e4, hsec, zero_pow two_ne_zero, zero_add] at this
      exact this
  have hprod : ∏ i ∈ Ico 1 N, (lead (NormedSpace.exp Y) i).re ^ (-(s i))
      = Real.exp (∑ i ∈ Ico 1 N, Real.log (lead (NormedSpace.exp Y) i).re * (-(s i))) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.rpow_def_of_pos (key i hi).1 _
  rw [hprod, Real.exp_le_exp]
  have h1 : ∑ i ∈ Ico 1 N, Real.log (lead (NormedSpace.exp Y) i).re * (-(s i))
      ≤ ∑ i ∈ Ico 1 N, (c * (∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2) / 4) * (-(s i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonpos_right (key i hi).2 (neg_nonpos.mpr (hs0 i))
  have h2 : ∑ i ∈ Ico 1 N, (c * (∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2) / 4) * (-(s i))
      = -(c / 4) * ∑ i ∈ Ico 1 N, s i * ∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h3 : c * H ^ 2 = min (H ^ 2) (H / r) := by
    rw [hc, min_mul_of_nonneg _ _ (sq_nonneg H), one_mul]
    congr 1
    rcases eq_or_lt_of_le hH0 with h0 | h0
    · rw [← h0]; simp
    · rcases eq_or_lt_of_le hr0 with r0 | r0
      · rw [← r0]; simp
      · field_simp
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ -(c / 4) * (h * H ^ 2 / 2) := mul_le_mul_of_nonpos_left hW (by linarith)
    _ = -(h * (c * H ^ 2)) / 8 := by ring
    _ = _ := by rw [h3]

end Formalism.NuclearRankWeightBounds.P
end

-- bundled from Formalism.LogSumExpBounds.CharacterSumPhase.LogSumExpBoundHolds
section
namespace Formalism.NuclearRankWeightBounds.P

open Finset

lemma exp_ge_quad {z : ℝ} (hz : |z| ≤ 1) : 1 + z + z ^ 2 / 3 ≤ Real.exp z := by
  rcases le_or_gt 0 z with h0 | h0
  · have := Real.quadratic_le_exp_of_nonneg h0
    nlinarith [sq_nonneg z]
  · have h := Real.exp_bound hz (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    have h2 := (abs_le.mp h).1
    have ha : |z| = -z := abs_of_neg h0
    rw [ha] at h2 hz
    have hz1 : -1 ≤ z := by linarith
    nlinarith [sq_nonneg z, mul_nonneg (mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ z + 1)) (by linarith : (0:ℝ) ≤ -z),
      pow_two_nonneg (z ^ 2), mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ z + 1),
      mul_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg z)) (by linarith : (0:ℝ) ≤ z + 1)]

theorem log_sum_exp_bound_holds : Formalism.NuclearRankWeightBounds.D.LogSumExp := by
  intro ι _ w y M hw hw1 hmean hy
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  obtain ⟨j0⟩ := hne
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hy j0)
  set S := ∑ j, w j * Real.exp (y j) with hS
  set V := ∑ j, w j * y j ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
  rcases eq_or_lt_of_le hM0 with hM | hM
  · subst hM
    have hy0 : ∀ j, y j = 0 := fun j => abs_nonpos_iff.mp (hy j)
    have : S = 1 := by simp [hS, hy0, hw1]
    rw [this]
    simp
  · set t := min 1 M⁻¹ with ht
    have ht0 : 0 < t := lt_min one_pos (inv_pos.mpr hM)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htM : t * M ≤ 1 := by
      calc t * M ≤ M⁻¹ * M := mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
        _ = 1 := inv_mul_cancel₀ hM.ne'
    have hty : ∀ j, |t * y j| ≤ 1 := by
      intro j
      rw [abs_mul, abs_of_pos ht0]
      calc t * |y j| ≤ t * M := mul_le_mul_of_nonneg_left (hy j) ht0.le
        _ ≤ 1 := htM
    have hVM : V ≤ M ^ 2 := by
      calc V ≤ ∑ j, w j * M ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (hw j)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hy j) 2
        _ = M ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]
    set T := ∑ j, w j * Real.exp (t * y j) with hT
    have hT1 : 1 + t ^ 2 * V / 3 ≤ T := by
      calc 1 + t ^ 2 * V / 3 = ∑ j, w j * (1 + t * y j + (t * y j) ^ 2 / 3) := by
            simp only [mul_add, Finset.sum_add_distrib, mul_one, hw1]
            have e1 : ∑ j, w j * (t * y j) = t * ∑ j, w j * y j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
            have e2 : ∑ j, w j * ((t * y j) ^ 2 / 3) = t ^ 2 * V / 3 := by
              rw [hV, Finset.mul_sum, Finset.sum_div]
              exact Finset.sum_congr rfl (fun j _ => by ring)
            rw [e1, e2, hmean]; ring
        _ ≤ T := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (exp_ge_quad (hty j)) (hw j))
    have hu : t ^ 2 * V ≤ 1 := by
      calc t ^ 2 * V ≤ t ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hVM (sq_nonneg _)
        _ = (t * M) ^ 2 := by ring
        _ ≤ 1 := by
          have : 0 ≤ t * M := mul_nonneg ht0.le hM.le
          nlinarith
    have hTpos : 0 < T := by
      have : 0 ≤ t ^ 2 * V := mul_nonneg (sq_nonneg _) hV0
      linarith
    have hlogT : t ^ 2 * V / 4 ≤ Real.log T := by
      set u := t ^ 2 * V / 3 with hu'
      have hu0 : 0 ≤ u := by positivity
      have hlog1 : 1 - (1 + u)⁻¹ ≤ Real.log (1 + u) := Real.one_sub_inv_le_log_of_pos (by linarith)
      have hmono : Real.log (1 + u) ≤ Real.log T := Real.log_le_log (by linarith) hT1
      have : t ^ 2 * V / 4 ≤ 1 - (1 + u)⁻¹ := by
        rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring]
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    have hJ : T ^ (1 / t) ≤ S := by
      have h := Real.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ) w (fun j => Real.exp (t * y j))
        (fun j _ => hw j) hw1 (fun j _ => (Real.exp_pos _).le) (p := 1 / t)
        (by rw [le_div_iff₀ ht0]; linarith)
      refine h.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Real.exp_mul]
      congr 2
      field_simp
    have hlogJ : (1 / t) * Real.log T ≤ Real.log S := by
      rw [← Real.log_rpow hTpos]
      exact Real.log_le_log (Real.rpow_pos_of_pos hTpos _) hJ
    have key : t * V / 4 ≤ (1 / t) * Real.log T := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ht0]
      nlinarith
    linarith

end Formalism.NuclearRankWeightBounds.P
end

-- bundled from Formalism.LogSumExpBounds.CharacterSumPhase.NuclearNormBoundHolds
section
namespace Formalism.NuclearRankWeightBounds.P

open Finset Matrix

theorem sum_sq_eigenvalues {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Y.IsHermitian) :
    ∑ j, hY.eigenvalues j ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hY.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef
  set D : Matrix (Fin N) (Fin N) ℂ := diagonal (RCLike.ofReal ∘ hY.eigenvalues) with hDdef
  have hsp : Y = U * D * star U := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have hu : star U * U = 1 := Unitary.coe_star_mul_self hY.eigenvectorUnitary
  have h1 : (Y * Y).trace = (D * D).trace := by
    have : Y * Y = U * (D * D) * star U := by
      rw [hsp]
      simp only [mul_assoc]
      rw [← mul_assoc (star U) U, hu, one_mul]
    rw [this, trace_mul_cycle, hu, one_mul]
  have h2 : (D * D).trace = ∑ j, ((hY.eigenvalues j ^ 2 : ℝ) : ℂ) := by
    rw [hDdef, diagonal_mul_diagonal, trace_diagonal]
    simp [pow_two]
  have h3 : (Y * Y).trace = ∑ a, ∑ b, ((‖Y a b‖ ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [show Y * Y = Yᴴ * Y by rw [hY.eq]]
    simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show star (Y a b) = (starRingEnd ℂ) (Y a b) from rfl, Complex.conj_mul']
    push_cast; ring
  have h4 : ((∑ j, hY.eigenvalues j ^ 2 : ℝ) : ℂ) = ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum]
    rw [← h3, h1, h2]
  exact_mod_cast h4

theorem nuclear_norm_bound_holds : Formalism.NuclearRankWeightBounds.D.NuclearBound := by
  intro N Y hY
  classical
  set μ := hY.eigenvalues
  have hrank : (Y.rank : ℝ) = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) ^ 2 := by
    rw [hY.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    simp only [ite_pow, one_pow, ne_eq, zero_pow two_ne_zero]
    rw [Finset.sum_boole]
  have hhs : Formalism.NuclearRankWeightBounds.D.hs Y = Real.sqrt (∑ j, |μ j| ^ 2) := by
    unfold Formalism.NuclearRankWeightBounds.D.hs
    rw [← sum_sq_eigenvalues Y hY]
    simp only [sq_abs]
    rfl
  have hsum : ∑ j, |μ j| = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) * |μ j| := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : μ j = 0 <;> simp [h]
  rw [hrank, hhs, hsum]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

end Formalism.NuclearRankWeightBounds.P
end

-- bundled from Formalism.LogSumExpBounds.CharacterSumPhase.RankLeOfSupport
section
namespace Formalism.NuclearRankWeightBounds.P

open Matrix Finset

lemma rank_add_le' {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have h : LinearMap.range (A + B).mulVecLin
      ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    intro x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hx
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup (LinearMap.mem_range.2 ⟨v, rfl⟩) (LinearMap.mem_range.2 ⟨v, rfl⟩)
  exact (Submodule.finrank_mono h).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma rank_le_of_support {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (S S' : Finset (Fin N))
    (h : ∀ a b, A a b ≠ 0 → a ∈ S ∧ b ∈ S') : A.rank ≤ min S.card S'.card := by
  refine le_min ?_ ?_
  · apply Matrix.rank_le_card_of_support_subset A S
    intro a ha
    by_contra hn
    apply ha
    funext b
    by_contra hb
    exact hn (h a b hb).1
  · rw [← Matrix.rank_transpose]
    apply Matrix.rank_le_card_of_support_subset Aᵀ S'
    intro b hb'
    by_contra hn
    apply hb'
    funext a
    by_contra ha
    exact hn (h a b ha).2

theorem rank_block_holds : Formalism.NuclearRankWeightBounds.D.RankBlock := by
  intro N ep Y hY
  classical
  set T := (univ : Finset (Fin N)).filter (fun a => ep a = true) with hT
  set F := (univ : Finset (Fin N)).filter (fun a => ep a = false) with hF
  set P : Matrix (Fin N) (Fin N) ℂ := diagonal (fun a => if ep a = true then 1 else 0) with hP
  set Q : Matrix (Fin N) (Fin N) ℂ := diagonal (fun a => if ep a = true then 0 else 1) with hQ
  have hsplit : Y = Y * P + Y * Q := by
    ext a b
    simp only [hP, hQ, Matrix.add_apply, Matrix.mul_diagonal]
    split_ifs <;> simp
  have h1 : (Y * P).rank ≤ min F.card T.card := by
    apply rank_le_of_support _ F T
    intro a b hab
    simp only [hP, Matrix.mul_diagonal] at hab
    cases hb : ep b
    · simp [hb] at hab
    · have hY' : Y a b ≠ 0 := by simpa [hb] using hab
      cases ha : ep a
      · simp [hT, hF, ha, hb]
      · exact absurd (hY a b (by rw [ha, hb])) hY'
  have h2 : (Y * Q).rank ≤ min T.card F.card := by
    apply rank_le_of_support _ T F
    intro a b hab
    simp only [hQ, Matrix.mul_diagonal] at hab
    cases hb : ep b
    · have hY' : Y a b ≠ 0 := by simpa [hb] using hab
      cases ha : ep a
      · exact absurd (hY a b (by rw [ha, hb])) hY'
      · simp [hT, hF, ha, hb]
    · simp [hb] at hab
  have h3 : Y.rank ≤ (Y * P).rank + (Y * Q).rank := by
    calc Y.rank = (Y * P + Y * Q).rank := congrArg Matrix.rank hsplit
      _ ≤ _ := rank_add_le' _ _
  have hq : Formalism.NuclearRankWeightBounds.D.q0 ep = min T.card F.card := rfl
  rw [hq]
  have := min_comm F.card T.card
  omega

end Formalism.NuclearRankWeightBounds.P
end

-- bundled from Formalism.LogSumExpBounds.CharacterSumPhase.WeightedOffDiagonalHolds
section
namespace Formalism.NuclearRankWeightBounds.P

open Finset Formalism.NuclearRankWeightBounds.D

theorem weighted_off_diagonal_holds : Formalism.NuclearRankWeightBounds.D.WeightedOff := by
  intro N s ep h Y hY hz hh
  classical
  obtain ⟨T, hT⟩ : ∃ T : Fin N → Fin N → ℝ,
      T = fun a b => ∑ i ∈ Ico 1 N, if a.val < i ∧ i ≤ b.val then s i else 0 := ⟨_, rfl⟩
  have hsym : ∀ a b, ‖Y b a‖ = ‖Y a b‖ := by
    intro a b
    rw [← hY.apply b a, norm_star]
  have hTlt : ∀ a b : Fin N, a < b → T a b = ∑ i ∈ Ico (a.val + 1) (b.val + 1), s i := by
    intro a b hab
    have hab' : a.val < b.val := hab
    have hb := b.isLt
    rw [hT]
    simp only
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  have hTgt : ∀ a b : Fin N, a < b → T b a = 0 := by
    intro a b hab
    have hab' : a.val < b.val := hab
    rw [hT]
    simp only
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    omega
  have hpt : ∀ a b, h * ‖Y a b‖ ^ 2 ≤ ‖Y a b‖ ^ 2 * T a b + ‖Y b a‖ ^ 2 * T b a := by
    intro a b
    by_cases he : ep a = ep b
    · simp [hz a b he, hz b a he.symm]
    rw [hsym a b]
    rcases lt_trichotomy a b with hab | hab | hab
    · have h3 := hh b a hab (fun e => he e.symm)
      rw [hTgt a b hab, mul_zero, add_zero, mul_comm, hTlt a b hab]
      exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    · exact absurd (congrArg ep hab) he
    · have h3 := hh a b hab he
      rw [hTgt b a hab, mul_zero, zero_add, mul_comm, hTlt b a hab]
      exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  have hi : ∀ i : ℕ, (∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
      ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2)
      = ∑ a, ∑ b, if a.val < i ∧ i ≤ b.val then ‖Y a b‖ ^ 2 else 0 := by
    intro i
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    by_cases ha : a.val < i <;> simp [ha]
  have hrhs : (∑ i ∈ Ico 1 N, s i *
      ∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2)
      = ∑ a, ∑ b, ‖Y a b‖ ^ 2 * T a b := by
    simp_rw [hi, hT, Finset.mul_sum]
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have hhs : hs Y ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity)
  have hswap : (∑ a, ∑ b, ‖Y b a‖ ^ 2 * T b a) = ∑ a, ∑ b, ‖Y a b‖ ^ 2 * T a b :=
    Finset.sum_comm
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (univ : Finset (Fin N))) =>
    Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin N))) => hpt a b))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  rw [hrhs, hhs]
  linarith

end Formalism.NuclearRankWeightBounds.P
end


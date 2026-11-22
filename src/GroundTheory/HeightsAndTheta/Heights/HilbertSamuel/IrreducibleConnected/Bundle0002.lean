import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PClopenPieceSheetCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Matrix Filter Topology

theorem ClopenPieceSheetCount.proof : ClopenPieceSheetCount.Statement := by
  intro n d N A Z Ω O F hΩo hΩc hcov hO hF hXOF

  set f : (Fin d → ℂ) → ℕ := fun y => {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.ncard with hf_def

  have hloc : ∀ y ∈ Ω, ∀ᶠ w in 𝓝 y, f w = f y := by
    intro y hy
    obtain ⟨hfin, _hcard, hsec⟩ := hcov y hy
    set S : Set (Fin n → ℂ) := {x | x ∈ Z ∧ A *ᵥ x = y} with hS
    have hsec' : ∀ x ∈ S, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          ContinuousOn g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U :=
      fun x hx => hsec x hx.1 hx.2
    choose! U V g hU hyU _hV _hxV hg hgy hAg hZV using hsec'
    have hca : ∀ x ∈ S, ContinuousAt (g x) y := fun x hx =>
      (hg x hx).continuousAt ((hU x hx).mem_nhds (hyU x hx))

    have hgZ : ∀ x ∈ S, ∀ w ∈ U x, g x w ∈ Z := by
      intro x hx w hw
      have : g x w ∈ g x '' U x := ⟨w, hw, rfl⟩
      rw [← hZV x hx] at this
      exact this.1

    have e1 : ∀ᶠ w in 𝓝 y, w ∈ Ω := hΩo.mem_nhds hy
    have e2 : ∀ᶠ w in 𝓝 y, ∀ x ∈ S, w ∈ U x :=
      (eventually_all_finite hfin).2 fun x hx => (hU x hx).mem_nhds (hyU x hx)
    have e3 : ∀ᶠ w in 𝓝 y, ∀ p ∈ S ×ˢ S, p.1 ≠ p.2 → g p.1 w ≠ g p.2 w := by
      refine (eventually_all_finite (hfin.prod hfin)).2 fun p hp => ?_
      by_cases hne : p.1 = p.2
      · exact Eventually.of_forall fun _ h => absurd hne h
      · have h := ((hca p.1 hp.1).ne_iff_eventually_ne (hca p.2 hp.2)).1
          (by rw [hgy p.1 hp.1, hgy p.2 hp.2]; exact hne)
        exact h.mono fun w hw _ => hw
    have e4 : ∀ᶠ w in 𝓝 y, ∀ x ∈ S, x ∉ O → g x w ∉ F := by
      refine (eventually_all_finite hfin).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · exact Eventually.of_forall fun _ h => absurd hxO h
      · have hxF : x ∉ F := by
          intro hxF
          have hxX : x ∈ {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} := ⟨hx.1, by rw [hx.2]; exact hy⟩
          have : x ∈ {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ O := by rw [hXOF]; exact ⟨hxX, hxF⟩
          exact hxO this.2
        have := (hca x hx).preimage_mem_nhds (hF.isOpen_compl.mem_nhds (by rw [hgy x hx]; exact hxF))
        filter_upwards [this] with w hw _ using hw
    have e5 : ∀ᶠ w in 𝓝 y, ∀ x ∈ S, x ∈ O → g x w ∈ O := by
      refine (eventually_all_finite hfin).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · have := (hca x hx).preimage_mem_nhds (hO.mem_nhds (by rw [hgy x hx]; exact hxO))
        filter_upwards [this] with w hw _ using hw
      · exact Eventually.of_forall fun _ h => absurd h hxO
    filter_upwards [e1, e2, e3, e4, e5] with w hwΩ hwU hwne hwF hwO

    set G : (Fin n → ℂ) → Fin n → ℂ := fun x => g x w with hG
    have hGinj : Set.InjOn G S := by
      intro a ha b hb hab
      by_contra hne
      exact hwne (a, b) ⟨ha, hb⟩ hne hab
    have hGmaps : G '' S ⊆ {x | x ∈ Z ∧ A *ᵥ x = w} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hgZ x hx w (hwU x hx), hAg x hx w (hwU x hx)⟩
    obtain ⟨hfinw, hcardw, _⟩ := hcov w hwΩ
    have hGeq : G '' S = {x | x ∈ Z ∧ A *ᵥ x = w} := by
      refine Set.eq_of_subset_of_ncard_le hGmaps ?_ hfinw
      rw [hGinj.ncard_image, hcardw, _hcard]

    have hT : {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w} = G '' {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y} := by
      ext z
      constructor
      · rintro ⟨hzZ, hzO, hzw⟩
        have hz : z ∈ G '' S := by rw [hGeq]; exact ⟨hzZ, hzw⟩
        obtain ⟨x, hx, rfl⟩ := hz
        refine ⟨x, ⟨hx.1, ?_, hx.2⟩, rfl⟩
        by_contra hxO
        apply hwF x hx hxO
        have hX : G x ∈ {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} := ⟨hzZ, by rw [hzw]; exact hwΩ⟩
        have : G x ∈ {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ F := by rw [← hXOF]; exact ⟨hX, hzO⟩
        exact this.2
      · rintro ⟨x, ⟨hxZ, hxO, hxy⟩, rfl⟩
        have hx : x ∈ S := ⟨hxZ, hxy⟩
        exact ⟨hgZ x hx w (hwU x hx), hwO x hx hxO, hAg x hx w (hwU x hx)⟩
    simp only [hf_def]
    have hsub : {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y} ⊆ S := fun x hx => ⟨hx.1, hx.2.2⟩
    rw [hT, (hGinj.mono hsub).ncard_image]

  have hcont : ContinuousOn f Ω := by
    intro y hy
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, nhds_discrete ℕ, tendsto_pure]
    exact hloc y hy
  rcases Ω.eq_empty_or_nonempty with hE | ⟨y₀, hy₀⟩
  · exact ⟨0, fun y hy => by rw [hE] at hy; exact absurd hy (Set.notMem_empty y)⟩
  · exact ⟨f y₀, fun y hy => hΩc.constant hcont hy hy₀⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PEntirePolynomialGrowth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Metric

theorem entire_polynomialGrowth_one_var (M : ℕ) : ∀ (g : ℂ → ℂ) (C : ℝ), Differentiable ℂ g →
    (∀ z, ‖g z‖ ≤ C * (1 + ‖z‖) ^ M) →
    ∃ q : Polynomial ℂ, q.natDegree ≤ M ∧ ∀ z, g z = q.eval z := by
  induction M with
  | zero =>
    intro g C hg hb
    refine ⟨Polynomial.C (g 0), by simp, fun z => ?_⟩
    rw [Polynomial.eval_C]
    refine hg.apply_eq_apply_of_bounded ?_ z 0
    refine isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩
    rintro _ ⟨w, rfl⟩
    simpa using hb w
  | succ M ih =>
    intro g C hg hb
    set h := dslope g 0 with hh
    have hdiff : Differentiable ℂ h := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hg.differentiableOn
    obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ B :=
      (isCompact_closedBall 0 1).exists_bound_of_continuousOn hdiff.continuous.continuousOn
    have hrep : ∀ z, g z = g 0 + z * h z := fun z => by
      have := sub_smul_dslope g 0 z
      rw [smul_eq_mul, sub_zero] at this
      linear_combination -this
    set C' := max C 0 with hC'def
    have hC' : 0 ≤ C' := le_max_right _ _
    have hb' : ∀ z, ‖g z‖ ≤ C' * (1 + ‖z‖) ^ (M + 1) := fun z =>
      (hb z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hgrowth : ∀ z, ‖h z‖ ≤ (max B 0 + 2 * C' + ‖g 0‖) * (1 + ‖z‖) ^ M := by
      intro z
      have hg0 := norm_nonneg (g 0)
      have hBm := le_max_left B 0
      have hB0 := le_max_right B 0
      rcases le_or_gt ‖z‖ 1 with hz | hz
      · have h1 : 1 ≤ (1 + ‖z‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg z])
        have := hB z (by simpa using hz)
        nlinarith
      · have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
        have hhz : h z = (g z - g 0) / z := by
          rw [hh, dslope_of_ne _ hz0, slope_def_field, sub_zero]
        rw [hhz, norm_div, div_le_iff₀ (by positivity)]
        have e1 := norm_sub_le (g z) (g 0)
        have e2 := hb' z
        have hP : 1 ≤ (1 + ‖z‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg z])
        have hs : (1 + ‖z‖) ^ (M + 1) = (1 + ‖z‖) ^ M * (1 + ‖z‖) := pow_succ _ _
        rw [hs] at e2
        have k1 : 0 ≤ C' * (1 + ‖z‖) ^ M * (‖z‖ - 1) :=
          mul_nonneg (mul_nonneg hC' (by positivity)) (by linarith)
        have k2 : 0 ≤ ‖g 0‖ * ((1 + ‖z‖) ^ M * ‖z‖ - 1) :=
          mul_nonneg hg0 (by nlinarith)
        have k3 : 0 ≤ max B 0 * (1 + ‖z‖) ^ M * ‖z‖ := by positivity
        nlinarith
    obtain ⟨q, hqdeg, hq⟩ := ih h (max B 0 + 2 * C' + ‖g 0‖) hdiff hgrowth
    refine ⟨Polynomial.C (g 0) + Polynomial.X * q, ?_, fun z => ?_⟩
    · calc (Polynomial.C (g 0) + Polynomial.X * q).natDegree
          ≤ max (Polynomial.C (g 0)).natDegree (Polynomial.X * q).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ M + 1 := by
            refine max_le (by simp) (Polynomial.natDegree_mul_le.trans ?_)
            have := Polynomial.natDegree_X_le (R := ℂ)
            omega
    · rw [hrep z, hq z]; simp

theorem EntirePolynomialGrowth.proof : EntirePolynomialGrowth.Statement := by
  intro d
  induction d with
  | zero =>
    intro f C M _ _
    refine ⟨MvPolynomial.C (f 0), fun y => ?_⟩
    rw [MvPolynomial.eval_C]
    congr 1
    exact Subsingleton.elim _ _
  | succ d ih =>
    intro f C M hf hb
    set C' := max C 0 with hC'def
    have hC' : 0 ≤ C' := le_max_right _ _
    have hb' : ∀ y, ‖f y‖ ≤ C' * (1 + ‖y‖) ^ M := fun y =>
      (hb y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hcons : ∀ (c : ℂ) (w : Fin d → ℂ), ‖(Fin.cons c w : Fin (d + 1) → ℂ)‖ ≤ ‖c‖ + ‖w‖ := by
      intro c w
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [norm_nonneg]
      · simp only [Fin.cons_succ]
        linarith [norm_le_pi_norm w i, norm_nonneg c]
    have hdc : ∀ w : Fin d → ℂ, Differentiable ℂ (fun z : ℂ => (Fin.cons z w : Fin (d + 1) → ℂ)) := by
      intro w
      refine differentiable_pi.2 fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; fun_prop
      · simp only [Fin.cons_succ]; fun_prop
    have hdw : ∀ c : ℂ, Differentiable ℂ (fun w : Fin d → ℂ => (Fin.cons c w : Fin (d + 1) → ℂ)) := by
      intro c
      refine differentiable_pi.2 fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; fun_prop
      · simp only [Fin.cons_succ]; fun_prop
    have hp : ∀ j : ℕ, ∃ p : MvPolynomial (Fin d) ℂ,
        ∀ w, f (Fin.cons (j : ℂ) w) = eval w p := by
      intro j
      refine ih _ (C' * (1 + (j : ℝ)) ^ M) M (hf.comp (hdw _)) fun w => ?_
      have hn := hcons (j : ℂ) w
      rw [Complex.norm_natCast] at hn
      calc ‖f (Fin.cons (j : ℂ) w)‖
          ≤ C' * (1 + ‖(Fin.cons (j : ℂ) w : Fin (d + 1) → ℂ)‖) ^ M := hb' _
        _ ≤ C' * ((1 + (j : ℝ)) * (1 + ‖w‖)) ^ M := by
            gcongr
            nlinarith [norm_nonneg w, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        _ = C' * (1 + (j : ℝ)) ^ M * (1 + ‖w‖) ^ M := by rw [mul_pow, mul_assoc]
    choose p hp using hp
    have hz : ∀ w : Fin d → ℂ, ∃ q : Polynomial ℂ, q.natDegree ≤ M ∧
        ∀ z, f (Fin.cons z w) = q.eval z := by
      intro w
      refine entire_polynomialGrowth_one_var M _ (C' * (1 + ‖w‖) ^ M) (hf.comp (hdc w)) fun z => ?_
      have hn := hcons z w
      calc ‖f (Fin.cons z w)‖ ≤ C' * (1 + ‖(Fin.cons z w : Fin (d + 1) → ℂ)‖) ^ M := hb' _
        _ ≤ C' * ((1 + ‖w‖) * (1 + ‖z‖)) ^ M := by
            gcongr
            nlinarith [norm_nonneg w, norm_nonneg z]
        _ = C' * (1 + ‖w‖) ^ M * (1 + ‖z‖) ^ M := by rw [mul_pow, mul_assoc]
    refine ⟨∑ j ∈ Finset.range (M + 1),
      Polynomial.aeval (X 0 : MvPolynomial (Fin (d + 1)) ℂ)
        (Lagrange.basis (Finset.range (M + 1)) (fun j : ℕ => (j : ℂ)) j) * rename Fin.succ (p j),
      fun y => ?_⟩
    obtain ⟨q, hqd, hq⟩ := hz (Fin.tail y)
    have hinj : Set.InjOn (fun j : ℕ => (j : ℂ)) (Finset.range (M + 1) : Set ℕ) :=
      Nat.cast_injective.injOn
    have hdeg : q.degree < (Finset.range (M + 1)).card := by
      rw [Finset.card_range]
      exact (Polynomial.degree_le_of_natDegree_le hqd).trans_lt (by exact_mod_cast Nat.lt_succ_self M)
    have key := Lagrange.eq_interpolate hinj hdeg
    have hev : ∀ P : Polynomial ℂ,
        eval y (Polynomial.aeval (X 0 : MvPolynomial (Fin (d + 1)) ℂ) P) = P.eval (y 0) := by
      intro P
      have hid : (eval y).comp (algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ)) = RingHom.id ℂ := by
        ext; simp
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, MvPolynomial.eval_X, hid]
      rfl
    conv_lhs => rw [← Fin.cons_self_tail y, hq (y 0), key]
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hev, eval_rename, Polynomial.eval_mul, Polynomial.eval_C, ← hq, hp, mul_comm]
    rfl

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PMonicRootGrowth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Finset

theorem norm_eval_le_sum_norm_coeff_mul {d : ℕ} (a : MvPolynomial (Fin d) ℂ) (y : Fin d → ℂ) :
    ‖eval y a‖ ≤ (∑ s ∈ a.support, ‖coeff s a‖) * (1 + ‖y‖) ^ a.totalDegree := by
  have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  rw [eval_eq, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun s hs ↦ ?_)
  rw [norm_mul, norm_prod]
  gcongr
  calc ∏ i ∈ s.support, ‖y i ^ s i‖
      ≤ ∏ i ∈ s.support, (1 + ‖y‖) ^ s i := by
        gcongr with i
        rw [norm_pow]
        gcongr
        exact (norm_le_pi_norm y i).trans (le_add_of_nonneg_left zero_le_one)
    _ = (1 + ‖y‖) ^ (s.sum fun _ e ↦ e) := prod_pow_eq_pow_sum _ _ _
    _ ≤ (1 + ‖y‖) ^ a.totalDegree := pow_le_pow_right₀ h1 (le_totalDegree hs)

theorem norm_le_one_add_sum_norm_coeff_of_monic {q : Polynomial ℂ} (hq : q.Monic) {τ : ℂ}
    (hτ : q.IsRoot τ) : ‖τ‖ ≤ 1 + ∑ i ∈ range q.natDegree, ‖q.coeff i‖ := by
  have key := hτ.norm_lt_cauchyBound hq.ne_zero
  have hs : Polynomial.cauchyBound q ≤ (∑ i ∈ range q.natDegree, ‖q.coeff i‖₊) + 1 := by
    unfold Polynomial.cauchyBound
    rw [hq.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi ↦ single_le_sum (f := fun i ↦ ‖q.coeff i‖₊) (fun _ _ ↦ by positivity) hi
  have h' : ((‖τ‖₊ : NNReal) : ℝ) ≤ (((∑ i ∈ range q.natDegree, ‖q.coeff i‖₊) + 1 : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (key.trans_le hs).le
  push_cast at h'
  linarith

theorem MonicRootGrowth.proof : MonicRootGrowth.Statement := by
  intro d m hm
  set n := m.natDegree
  set S : ℕ → ℝ := fun i ↦ ∑ s ∈ (m.coeff i).support, ‖coeff s (m.coeff i)‖
  refine ⟨1 + ∑ i ∈ range n, S i, (range n).sup fun i ↦ (m.coeff i).totalDegree, fun y τ hτ ↦ ?_⟩
  have hmap : (m.map (eval y)).Monic := hm.map _
  have hdeg : (m.map (eval y)).natDegree = n := hm.natDegree_map _
  have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  set M := (range n).sup fun i ↦ (m.coeff i).totalDegree
  have hM : (1 : ℝ) ≤ (1 + ‖y‖) ^ M := one_le_pow₀ h1
  have hb := norm_le_one_add_sum_norm_coeff_of_monic hmap hτ
  rw [hdeg] at hb
  simp only [Polynomial.coeff_map] at hb
  calc ‖τ‖ ≤ 1 + ∑ i ∈ range n, ‖eval y (m.coeff i)‖ := hb
    _ ≤ 1 * (1 + ‖y‖) ^ M + ∑ i ∈ range n, S i * (1 + ‖y‖) ^ M := by
        gcongr with i hi
        · simpa using hM
        · refine (norm_eval_le_sum_norm_coeff_mul _ y).trans ?_
          gcongr
          exact le_sup (f := fun i ↦ (m.coeff i).totalDegree) hi
    _ = (1 + ∑ i ∈ range n, S i) * (1 + ‖y‖) ^ M := by rw [add_mul, sum_mul]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StPieceCoefficientsHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix

def PieceCoefficientsHolomorphic.Statement : Prop :=
  ∀ (n d N : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (Z : Set (Fin n → ℂ)) (c : Fin n → ℂ)
    (Q : MvPolynomial (Fin d) ℂ) (O F : Set (Fin n → ℂ)),
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 →
      {x | x ∈ Z ∧ A *ᵥ x = y}.Finite ∧ {x | x ∈ Z ∧ A *ᵥ x = y}.ncard = N ∧
      ∀ x ∈ Z, A *ᵥ x = y → ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U) →
    IsOpen O → IsClosed F →
    {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O = {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F →
    ∀ i : ℕ, DifferentiableOn ℂ
      (fun y : Fin d → ℂ => (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i) {y | eval y Q ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StPrimeCoverPieceSheets
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix

def PrimeCoverPieceSheets.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d → ComplexSets.IsFiniteProjection W A →
      ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧ ∀ R : MvPolynomial (Fin d) ℂ, R ≠ 0 →
        ∀ (O F : Set (Fin n → ℂ)) (k : ℕ), IsOpen O → IsClosed F →
          {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P * R) ≠ 0} ∩ O =
            {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P * R) ≠ 0} ∩ F →
          (∀ y : Fin d → ℂ, eval y (P * R) ≠ 0 →
            {x | x ∈ ComplexSets.zeroSet W ∧ x ∈ O ∧ A *ᵥ x = y}.ncard = k) →
          k = 0 ∨ k = ComplexSets.projDegree W A

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StatementsUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def UnbranchedPartConnected.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d → ComplexSets.IsFiniteProjection W A →
      ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧ ∀ R : MvPolynomial (Fin d) ℂ, R ≠ 0 →
        IsPreconnected {x : Fin n → ℂ | x ∈ ComplexSets.zeroSet W ∧ eval (A.mulVec x) (P * R) ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
end


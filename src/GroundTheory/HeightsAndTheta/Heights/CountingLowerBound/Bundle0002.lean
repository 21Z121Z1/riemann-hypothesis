import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMinkowskiCovolumeBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Module

universe u

theorem MinkowskiCovolumeBound.proof : MinkowskiCovolumeBound.Statement.{u} := by
  intro V _ _ _ _ _ hm L _ _
  set m := finrank ℝ V with hm_def
  set lam := firstMinimum L with hlam
  set c := lam / √(m : ℝ) with hc

  have hlow : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖ := by
    intro v hv hv0
    exact csInf_le ⟨0, fun x ⟨_, _, _, hx⟩ => hx ▸ norm_nonneg _⟩ ⟨v, hv, hv0, rfl⟩
  have hlam0 : 0 ≤ lam := Real.sInf_nonneg (fun x ⟨_, _, _, hx⟩ => hx ▸ norm_nonneg _)
  have hcov : 0 ≤ ZLattice.covolume L := (ZLattice.covolume_pos L).le
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hc0' : 0 ≤ c := div_nonneg hlam0 (Real.sqrt_nonneg _)
  rcases hc0'.eq_or_lt with hc0 | hc0
  · rw [← hc0, zero_pow (by omega)]
    exact hcov
  by_contra hlt
  push Not at hlt

  let b := stdOrthonormalBasis ℝ V
  let f : V → (Fin m → ℝ) := fun x => WithLp.ofLp (b.repr x)
  have hf : MeasurePreserving f volume volume :=
    (PiLp.volume_preserving_ofLp (Fin m)).comp b.measurePreserving_repr
  let S : Set V := f ⁻¹' Metric.ball 0 c
  have hS_vol : volume S = ENNReal.ofReal ((2 * c) ^ m) := by
    rw [hf.measure_preimage measurableSet_ball.nullMeasurableSet, Real.volume_pi_ball _ hc0,
      Fintype.card_fin]
  have hS_symm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simpa [S, f, Metric.mem_ball, dist_zero_right, norm_neg] using hx
  have hS_conv : Convex ℝ S := by
    have hlin : IsLinearMap ℝ f := by
      constructor
      · intro x y; simp [f]
      · intro a x; simp [f]
    exact (convex_ball (0 : Fin m → ℝ) c).is_linear_preimage hlin

  let bZ := Free.chooseBasis ℤ L
  have fund := ZLattice.isAddFundamentalDomain bZ (volume : Measure V)
  have hcovF := ZLattice.covolume_eq_measure_fundamentalDomain L volume fund
  have hF_fin : volume (ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hbig : volume (ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ)) * 2 ^ finrank ℝ V
      < volume S := by
    rw [hS_vol, ← ENNReal.ofReal_toReal hF_fin, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_lt_ofReal_iff (pow_pos (by positivity) _), mul_pow, ← hm_def,
      mul_comm _ (2 ^ m)]
    have : (volume (ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ))).toReal
        = ZLattice.covolume L := by rw [hcovF]; rfl
    rw [this]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  have : Countable L.toAddSubgroup := (inferInstance : Countable L)
  obtain ⟨x, hx0, hxS⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (L := L.toAddSubgroup) fund
      hS_symm hS_conv hbig

  have hxL : (x : V) ∈ L := x.2
  have hxne : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hcoord : ∀ i, |b.repr (x : V) i| < c := by
    intro i
    have := hxS
    simp only [S, f, Set.mem_preimage, mem_ball_zero_iff] at this
    exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (WithLp.ofLp (b.repr (x : V))) i) this
  have hnormsq : ‖(x : V)‖ ^ 2 < lam ^ 2 := by
    rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖b.repr (x : V) i‖ ^ 2 < ∑ _i : Fin m, c ^ 2 := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
          · intro i _
            rw [Real.norm_eq_abs]
            exact pow_lt_pow_left₀ (hcoord i) (abs_nonneg _) (by norm_num)
      _ = lam ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc, div_pow,
            Real.sq_sqrt hm0.le]
          field_simp
  have := hlow _ hxL hxne
  nlinarith [norm_nonneg (x : V)]

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PPackingCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open MeasureTheory Metric

noncomputable section

theorem PackingCount.card_mul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Finset E) {lam R : ℝ} (hlam : 0 < lam) (hR : 0 ≤ R)
    (hT : ∀ x ∈ T, ‖x‖ < R) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → lam ≤ ‖x - y‖) :
    (T.card : ℝ) * (lam / 2) ^ Module.finrank ℝ E ≤ (R + lam / 2) ^ Module.finrank ℝ E := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  set d := Module.finrank ℝ E
  have hd : Set.PairwiseDisjoint (↑T : Set E) (fun x => ball x (lam / 2)) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have := hsep x hx y hy hxy
    linarith
  have hsub : (⋃ x ∈ T, ball x (lam / 2)) ⊆ ball (0 : E) (R + lam / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    rw [mem_ball] at hz ⊢
    have h1 : dist x 0 < R := by rw [dist_zero_right]; exact hT x hx
    have h2 := dist_triangle z x 0
    linarith
  have h2 := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hd (fun x _ => measurableSet_ball)] at h2
  rw [Finset.sum_congr rfl (fun x _ => Measure.addHaar_ball_of_pos μ x (half_pos hlam))] at h2
  rw [Finset.sum_const, nsmul_eq_mul, Measure.addHaar_ball_of_pos μ (0 : E) (r := R + lam / 2) (by positivity),
    ← mul_assoc] at h2
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ (0 : E) one_pos).ne'
  have hc1 : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hc0 hc1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
    (Nat.cast_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  exact h2

theorem PackingCount.proof : PackingCount.Statement := by
  intro V _ _ L W lam r a h
  classical
  have : FiniteDimensional ℝ W :=
    Module.finite_of_finrank_pos (by rw [h.finrank_eq]; exact h.one_le_a)
  have hlam := h.lam_pos
  have hr : 0 < r := lt_of_lt_of_le hlam h.lam_le_r
  set B : ℝ := (1 + 2 * r / lam) ^ a with hB
  set S : Set V := {v | v ∈ L ∧ ‖v‖ < r} with hS

  have key : ∀ T : Finset V, ↑T ⊆ S → (T.card : ℝ) ≤ B := by
    intro T hT
    have hW : ∀ v ∈ T, v ∈ W := fun v hv => h.short_mem v (hT hv).1 (hT hv).2
    set T' : Finset W := T.subtype (· ∈ W)
    have hcard : T'.card = T.card := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem hW]
    have hbd := PackingCount.card_mul_le T' hlam hr.le
      (fun x hx => by
        rw [Finset.mem_subtype] at hx
        rw [Submodule.coe_norm]
        exact (hT hx).2)
      (fun x hx y hy hxy => by
        rw [Finset.mem_subtype] at hx hy
        rw [Submodule.coe_norm, Submodule.coe_sub]
        apply h.lam_le_norm _ (h.sub_mem _ (hT hx).1 _ (hT hy).1)
        intro h0
        exact hxy (Subtype.ext (sub_eq_zero.mp h0)))
    rw [hcard, h.finrank_eq] at hbd
    have hpos : 0 < (lam / 2) ^ a := by positivity
    rw [← le_div_iff₀ hpos, ← div_pow] at hbd
    have he : (r + lam / 2) / (lam / 2) = 1 + 2 * r / lam := by
      field_simp
      ring
    rwa [he] at hbd
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨T, hT, hTc⟩ := (Set.not_finite.mp hinf).exists_subset_card_eq (⌈B⌉₊ + 1)
    have := key T hT
    rw [hTc] at this
    push_cast at this
    linarith [Nat.le_ceil B]
  have hsub : {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r} ⊆ S := fun v hv => ⟨hv.1, hv.2.2⟩
  have hSB : (S.ncard : ℝ) ≤ B := by
    rw [Set.ncard_eq_toFinset_card S hfin]
    exact key _ (by simp)
  have hB3 : B ≤ (3 * r / lam) ^ a := by
    apply pow_le_pow_left₀ (by positivity)
    have : lam ≤ r := h.lam_le_r
    rw [show (1 : ℝ) + 2 * r / lam = (lam + 2 * r) / lam by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hlam.le
  refine ⟨hfin.subset hsub, ?_⟩
  calc (({v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r} : Set V).ncard : ℝ) ≤ S.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
    _ ≤ B := hSB
    _ ≤ (3 * r / lam) ^ a := hB3

end

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PReductionSmallFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem ReductionSmallFirst.proof : ReductionSmallFirst.Statement := by
  intro K1 Ca Cc hK1 hCa hCc
  refine ⟨2 * (Ca + 1 / 2 + Cc + K1), ?_⟩
  intro A0 b0 hh sl rest vol J f j' n N j La h
  have hfj : 0 < f * j' := mul_pos h.f_pos h.j'_pos
  have hn := h.n_succ_pos
  have hv := h.vol_pos
  have hJ := h.J_pos
  have hLa := h.one_le_La
  have hN : 0 < N := lt_of_lt_of_le one_pos h.one_le_N
  have hden : 0 < (n + 1) * vol * J := by positivity

  have hrest : rest / ((n + 1) * vol * J) ≤ Cc * f * j' := by
    rw [div_le_iff₀ hden]
    calc rest ≤ |rest| := le_abs_self rest
      _ ≤ Cc * f * j' * (n + 1) * vol * J := h.rest_bound
      _ = Cc * f * j' * ((n + 1) * vol * J) := by ring

  have hhh : hh / ((n + 1) * J) ≤ f * j' / 2 * La :=
    h.hh_upper.trans (mul_le_mul_of_nonneg_left h.log_le_La (by positivity))
  have hCcLa : Cc * (f * j') ≤ Cc * (f * j') * La := by
    have : 0 ≤ Cc * (f * j') := by positivity
    nlinarith

  have hAb : -((Ca + 1 / 2 + Cc) * La) ≤ A0 + b0 := by
    have hsl := h.sl_lower
    have key : f * j' * (-((Ca + 1 / 2 + Cc) * La)) ≤ f * j' * (A0 + b0) := by
      rw [h.identity]
      have e1 : f * j' * (-((Ca + 1 / 2 + Cc) * La))
          = -(Ca * f * j' * La) - f * j' / 2 * La - Cc * (f * j') * La := by ring
      have e2 : Cc * f * j' = Cc * (f * j') := by ring
      rw [e1]
      rw [e2] at hrest
      linarith
    exact le_of_mul_le_mul_left key hfj

  have hsum : j * A0 + N * b0 ≤ K1 * N * La := (le_abs_self _).trans h.bound_sum

  have hNj : -(N * ((Ca + 1 / 2 + Cc + K1) * La)) ≤ (N - j) * A0 := by
    have e : (N - j) * A0 = N * (A0 + b0) - (j * A0 + N * b0) := by ring
    have hm : N * (-((Ca + 1 / 2 + Cc) * La)) ≤ N * (A0 + b0) :=
      mul_le_mul_of_nonneg_left hAb hN.le
    rw [e]
    have e3 : K1 * N * La = N * (K1 * La) := by ring
    rw [e3] at hsum
    nlinarith
  by_cases hA : 0 ≤ A0
  · have : 0 ≤ 2 * (Ca + 1 / 2 + Cc + K1) * La := by positivity
    linarith
  · replace hA : A0 < 0 := lt_of_not_ge hA
    have hhalf : (N - j) * A0 ≤ N / 2 * A0 :=
      mul_le_mul_of_nonpos_right h.half_N_le hA.le
    have key : N * (-(2 * (Ca + 1 / 2 + Cc + K1) * La)) ≤ N * A0 := by nlinarith
    have := le_of_mul_le_mul_left key hN
    linarith

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PReductionSmallLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem ReductionSmallLast.b0_le_small_block_last {K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ}
    (h : ReductionSmallLast.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La) :
    b0 ≤ (1 / 2 + Ca + Cc) * La := by
  have hfj : 0 < f * j' := mul_pos h.f_pos h.j'_pos
  have hden : 0 < (n + 1) * vol * J := mul_pos (mul_pos h.n_succ_pos h.vol_pos) h.J_pos
  have hrest : rest / ((n + 1) * vol * J) ≤ Cc * (f * j') := by
    rw [div_le_iff₀ hden]
    have := (le_abs_self rest).trans h.rest_bound
    linarith
  have hhh : hh / ((n + 1) * J) ≤ f * j' / 2 * La :=
    h.hh_upper.trans (mul_le_mul_of_nonneg_left h.log_le_La (by positivity))
  have hCc : 0 ≤ Cc := by
    have h0 : 0 ≤ Cc * (f * j' * ((n + 1) * vol * J)) := by
      have := (abs_nonneg rest).trans h.rest_bound
      linarith
    exact nonneg_of_mul_nonneg_left h0 (mul_pos hfj hden)
  have hCcLa : Cc * (f * j') ≤ Cc * (f * j') * La :=
    le_mul_of_one_le_right (mul_nonneg hCc hfj.le) h.one_le_La
  have key : f * j' * b0 ≤ f * j' * ((1 / 2 + Ca + Cc) * La) := by
    rw [h.identity]
    nlinarith [h.sl_lower]
  exact le_of_mul_le_mul_left key hfj

theorem ReductionSmallLast.proof : ReductionSmallLast.Statement := by
  intro K1 Ca Cc hK1 hCa hCc
  refine ⟨2 * (K1 + (1 / 2 + Ca + Cc)), ?_⟩
  intro A0 b0 hh sl rest vol J f j' n N j La h
  have hb0 := ReductionSmallLast.b0_le_small_block_last h
  have hN : 0 < N := lt_of_lt_of_le one_pos h.one_le_N
  have hLa : 0 < La := lt_of_lt_of_le one_pos h.one_le_La
  have hsum : -(K1 * N * La) ≤ j * A0 + N * b0 := (abs_le.mp h.bound_sum).1
  have hNb0 : N * b0 ≤ N * ((1 / 2 + Ca + Cc) * La) := mul_le_mul_of_nonneg_left hb0 hN.le
  set K := K1 + (1 / 2 + Ca + Cc) with hKdef
  have hK : 0 ≤ K := by positivity

  have hexp : N * (K * La) = K1 * N * La + N * ((1 / 2 + Ca + Cc) * La) := by
    rw [hKdef]; ring
  have hjA : -(N * (K * La)) ≤ j * A0 := by linarith

  have hNj : N * (K * La) ≤ j * (2 * K * La) := by
    have hKLa : 0 ≤ K * La := mul_nonneg hK hLa.le
    nlinarith [h.half_N_le_j]
  have : j * (-(2 * K * La)) ≤ j * A0 := by linarith
  have := le_of_mul_le_mul_left this h.j_pos
  linarith

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PShortVectorsOrthogonal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

noncomputable section

universe u

theorem ShortVectorsOrthogonal.rpow_neg_half_mul_self {vr : ℝ} (hvr : 0 < vr) :
    vr ^ (-(1 / 2 : ℝ)) * vr ^ (-(1 / 2 : ℝ)) = vr⁻¹ := by
  rw [← Real.rpow_add hvr]
  norm_num [Real.rpow_neg_one]

theorem ShortVectorsOrthogonal.proof : ShortVectorsOrthogonal.Statement := by
  intro L _ len E a vr h v w hv hw
  set r := vr ^ (-(1 / 2 : ℝ)) with hr
  have hvr := h.vr_pos
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hvr _
  have hrr : vr * (r * r) = 1 := by
    rw [hr, ShortVectorsOrthogonal.rpow_neg_half_mul_self hvr, mul_inv_cancel₀ hvr.ne']
  have hv0 := h.len_nonneg v
  have hw0 := h.len_nonneg w
  have hprod : len v * len w < r * r := by
    calc len v * len w ≤ len v * r := mul_le_mul_of_nonneg_left hw.le hv0
      _ < r * r := mul_lt_mul_of_pos_right hv hr_pos
  have hbound : |(E (a v) w : ℝ)| < 1 := by
    calc |(E (a v) w : ℝ)| ≤ len (a v) * len w := h.abs_E_le (a v) w
      _ ≤ (vr * len v) * len w := mul_le_mul_of_nonneg_right (h.len_a_le v) hw0
      _ = vr * (len v * len w) := by ring
      _ < vr * (r * r) := mul_lt_mul_of_pos_left hprod hvr
      _ = 1 := hrr
  have hint : |E (a v) w| < 1 := by exact_mod_cast hbound
  exact Int.abs_lt_one_iff.mp hint

end

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PTailBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory

universe u

theorem TailBound.proof (h1 : MeanCountBound.Statement.{u}) :
    TailBound.Statement.{u} := by
  intro X _ μ lam cnt a ka r hH x hx
  have hprob := hH.isProbability
  set t := exp (-x) * r with ht_def
  have ht_pos : 0 < t := mul_pos (exp_pos _) hH.r_pos
  have ht_le : t ≤ r := by
    have : exp (-x) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    nlinarith [hH.r_pos]
  have hS : MeasurableSet {z | lam z < t} := measurableSet_lt hH.lam_meas measurable_const

  have hmarkov : μ.real {z | lam z < t} ≤ meanCount μ cnt t := by
    rw [← integral_indicator_one hS, meanCount]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hS) (hH.integrable t ht_pos) ?_
    intro z
    by_cases hz : z ∈ {z | lam z < t}
    · rw [Set.indicator_of_mem hz]
      exact hH.one t ht_pos ht_le z hz
    · rw [Set.indicator_of_notMem hz]
      exact hH.cnt_nonneg t z

  have hscale : meanCount μ cnt t = exp (-x) ^ ka * meanCount μ cnt r :=
    hH.scaling (exp (-x)) r (exp_pos _) hH.r_pos
  have hpow : exp (-x) ^ ka = exp (-(ka * x)) := by
    rw [← exp_mul]; ring_nf
  have hmean := h1 X μ lam cnt a ka r hH
  have hbound : μ.real {z | lam z < t} ≤ 2 * 36 ^ a * exp (-(ka * x)) := by
    calc μ.real {z | lam z < t} ≤ meanCount μ cnt t := hmarkov
      _ = exp (-(ka * x)) * meanCount μ cnt r := by rw [hscale, hpow]
      _ ≤ exp (-(ka * x)) * (2 * 36 ^ a) :=
          mul_le_mul_of_nonneg_left hmean (exp_pos _).le
      _ = 2 * 36 ^ a * exp (-(ka * x)) := by ring
  have hone : μ.real {z | lam z < t} ≤ 1 := measureReal_le_one
  exact le_min hone hbound

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PTelescopeMetric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

theorem TelescopeMetric.le_first {n : ℕ} {I : ℕ → ℝ} (h : ∀ i, i < n → I (i + 1) ≤ I i) :
    ∀ i, i ≤ n → I i ≤ I 0 := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ k ih =>
    intro hk
    exact (h k (by omega)).trans (ih (by omega))

theorem TelescopeMetric.proof : TelescopeMetric.Statement := by
  intro n A A' I h
  have hsum : ∑ i ∈ Finset.range (n + 1), I i ≤ (n + 1) * I 0 := by
    have := Finset.sum_le_sum (s := Finset.range (n + 1)) (f := I) (g := fun _ => I 0)
      (fun i hi => TelescopeMetric.le_first h.antitone i (by
        simpa [Finset.mem_range, Nat.lt_succ_iff] using hi))
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have := h.sum_eq
  linarith

end GroundTheory.Heights₂.Heights.LowerBound
end


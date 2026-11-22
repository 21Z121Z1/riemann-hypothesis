import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0105
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0107
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0108
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegFixedBallMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegFixedBallMass

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_weight_mono (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {w w' : (Fin n → ℂ) → ℝ} (hw : ∀ x, w x ≤ w' x)
    (y : Fin (d + 1) → ℂ) :
    chartDens J A w (vecCons (logReg u ε) fun _ => euclPot) y ≤
      chartDens J A w' (vecCons (logReg u ε) fun _ => euclPot) y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with h
  · have h0 := hN n d J A u ε x h.choose hε h.choose_spec
    rw [hx.2] at h0
    exact mul_le_mul_of_nonneg_right (hw x) h0
  · exact le_rfl

end RegFixedBallMass

open RegFixedBallMass in

theorem RegFixedBallMass.proof (hN : RegDensNonneg.Statement) (hS : StokesOnChart.Statement)
    (hL : LogIntegrable.Statement) (hC : ChartMassCompact.Statement) : RegFixedBallMass.Statement := by
  intro n d J A u R hJ hdim hA hu
  obtain ⟨θ, hθs, hθ01, hθU, V, -, hBV, hθV⟩ :=
    exists_cutoff_near (S := Metric.closedBall (0 : Fin n → ℂ) R) Metric.isClosed_closedBall
      Metric.isOpen_ball (Metric.closedBall_subset_ball (lt_add_one R))
  have hθR : tsupport θ ⊆ Metric.closedBall 0 (R + 1) := hθU.trans Metric.ball_subset_closedBall
  have hθc : HasCompactSupport θ :=
    (isCompact_closedBall (0 : Fin n → ℂ) (R + 1)).of_isClosed_subset (isClosed_tsupport θ) hθR
  have hθw : ∀ x, (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x ≤ θ x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
    · rw [Set.indicator_of_mem hx, hθV x (hBV hx)]
    · rw [Set.indicator_of_notMem hx]
      exact (hθ01 x).1
  have hηs : ∀ i : Fin d, SmoothNear (zeroSet J) ((fun _ => euclPot) i) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
  have hθη : ∀ i : Fin (d + 1), SmoothNear (zeroSet J) (vecCons θ (fun _ => euclPot) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hθs
    · simpa using hηs i
  have hu2 : linForm ((2 : ℂ) • u) ∉ J := by
    have he : linForm ((2 : ℂ) • u) = C 2 * linForm u := by
      simp [linForm, Finset.mul_sum, ← mul_assoc, C_mul]
    intro hm
    apply hu
    have := J.mul_mem_left (C (1 / 2 : ℂ)) (he ▸ hm)
    rwa [← mul_assoc, ← C_mul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, C_1, one_mul] at this
  obtain ⟨P, hP, hPy⟩ := LelongRegularise.exists_poly_of_linEval_eq_zero hJ hA hu
  have hgood : ∀ᵐ y : Fin (d + 1) → ℂ, ∀ x ∈ fibre J A y, linEval u x ≠ 0 := by
    filter_upwards [LelongRegularise.ae_eval_ne_zero P hP] with y hy x hx h0
    exact hy (hPy y x hx h0)
  have hTi := (hL n (d + 1) J A u _ (R + 1) hJ hdim hA hu hθη).add
    (hL n (d + 1) J A ((2 : ℂ) • u) _ (R + 1) hJ hdim hA hu2 hθη)
  refine ⟨∫ y, (chartAbsDens J A ((Metric.closedBall 0 (R + 1)).indicator fun x => Real.log ‖linEval u x‖)
      (vecCons θ fun _ => euclPot) + chartAbsDens J A ((Metric.closedBall 0 (R + 1)).indicator
        fun x => Real.log ‖linEval ((2 : ℂ) • u) x‖) (vecCons θ fun _ => euclPot)) y, fun ε hε => ?_⟩
  have hgs : ∀ i : Fin (d + 1), SmoothNear (zeroSet J) (vecCons (logReg u ε) (fun _ => euclPot) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε.1)
    · simpa using hηs i
  have hGi : Integrable (chartDens J A θ (vecCons (logReg u ε) fun _ => euclPot)) :=
    (hC n (d + 1) J A θ _ hJ hdim hA hθs.continuous.continuousOn hgs (Or.inl hθc)).mono'
      (SheetSumMeasurable.proof n (d + 1) J A θ _ hJ hdim hA hθs.continuous.measurable
        hgs).1.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using abs_chartDens_le J A θ _ y)
  have hFi : Integrable (chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => euclPot)) :=
    hGi.mono' (RegBallMass.measurable_chartDens_indicator hJ hdim hA u hε.1
        Metric.isClosed_closedBall.measurableSet).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        have h0 := (RegBallMass.chartDens_indicator_mono hN hA u hε.1
          (subset_refl (Metric.closedBall (0 : Fin n → ℂ) R)) y).1
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact chartDens_weight_mono hN hA u hε.1 hθw y)
  refine ⟨hFi, ?_⟩
  calc ∫ y, chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (logReg u ε) fun _ => euclPot) y
      ≤ ∫ y, chartDens J A θ (vecCons (logReg u ε) fun _ => euclPot) y :=
        integral_mono hFi hGi fun y => chartDens_weight_mono hN hA u hε.1 hθw y
    _ = ∫ y, chartDens J A (logReg u ε) (vecCons θ fun _ => euclPot) y :=
        hS n d J A θ (logReg u ε) (fun _ => euclPot) hJ hdim hA (smoothNear_of_contDiff hθs)
          (smoothNear_of_contDiff (contDiff_logReg u hε.1)) hηs (Or.inl hθc)
    _ ≤ ‖∫ y, chartDens J A (logReg u ε) (vecCons θ fun _ => euclPot) y‖ := Real.le_norm_self _
    _ ≤ _ := norm_integral_le_of_norm_le hTi (by
        filter_upwards [hgood] with y hy
        exact LelongRegularise.norm_chartDens_le hA _ hθR hε.1 hε.2 hy)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegMassNearSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

theorem RegMassNearSmall.proof (hCmp : RegFormCompare.Statement) (hBall : RegBallMass.Statement)
    (hCov : SmallSetBallCover.Statement) : RegMassNearSmall.Statement := by
  classical
  intro n d J I u φ f hJ hdim hu hφ hIdim hf hfc δ hδ
  by_cases h : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ ε _ => by simp [varInt, h, hδ.le]⟩
  set A := h.choose
  have hA : IsFiniteProjection J A := h.choose_spec
  have hfin : ∀ y, (fibre J A y).Finite := fun y => (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
  set K := tsupport f
  obtain ⟨C₁, hC₁, h₁⟩ := hCmp n d J A φ f hJ hdim hA hφ hf hfc
  obtain ⟨C₂, hC₂, h₂⟩ := hBall n d J A u K hJ hdim hA hu hfc
  obtain ⟨C₃, hC₃, h₃⟩ := hCov n d I K hIdim hfc
  have hM : 0 ≤ C₁ * C₂ * C₃ := by positivity
  set r := min 1 (δ / (C₁ * C₂ * C₃ + 1))
  have hr : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  obtain ⟨T, hTK, hcov, hcard⟩ := h₃ r hr
  have hUo : IsOpen ((⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ) :=
    (isOpen_biUnion fun (c : Fin n → ℂ) _ => Metric.isOpen_ball).union hfc.isClosed.isOpen_compl
  refine ⟨(⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ, hUo, fun x hx => ?_, fun χ _ hχ1 hχU ε hε => ?_⟩
  · by_cases hxK : x ∈ K
    · exact Or.inl (hcov ⟨hx, hxK⟩)
    · exact Or.inr hxK
  set ψ : Fin (d + 1) → (Fin n → ℂ) → ℝ := vecCons (logReg u ε) fun _ => euclPot
  set w : (Fin n → ℂ) → ℝ := fun x => ∑ c ∈ T, (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x with hw
  have hi0 : ∀ c x : Fin n → ℂ, 0 ≤ (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x :=
    fun c x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hw0 : ∀ x, 0 ≤ w x := fun x => Finset.sum_nonneg fun c _ => hi0 c x
  have hvw : ∀ x ∈ K, |χ x| ≤ w x := by
    intro x hxK
    by_cases h0 : χ x = 0
    · rw [h0, abs_zero]
      exact hw0 x
    rcases hχU (subset_tsupport χ h0) with hxB | hxK'
    · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 hxB
      calc |χ x| ≤ 1 := hχ1 x
        _ = (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x := (Set.indicator_of_mem hxc (fun _ => (1 : ℝ))).symm
        _ ≤ w x := Finset.single_le_sum (f := fun c => (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x)
            (fun c _ => hi0 c x) hc
    · exact absurd hxK hxK'
  have hsum : chartDens J A w ψ =
      fun y => ∑ c ∈ T, chartDens J A ((Metric.ball c r).indicator fun _ => 1) ψ y := by
    funext y
    simp only [chartDens, sheetSum]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [hw, Finset.sum_mul]
  have hball := fun c (hc : c ∈ T) => h₂ ε hε c (hTK hc).2 r hr
  have hint : Integrable (chartDens J A w ψ) := by
    rw [hsum]
    exact integrable_finsetSum _ fun c hc => (hball c hc).1
  have hT : ∫ y, chartDens J A w ψ y ≤ T.card * (C₂ * r ^ (2 * d)) := by
    rw [hsum, integral_finsetSum _ fun c hc => (hball c hc).1, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c hc => (hball c hc).2
  rw [varInt, dif_pos h]
  calc |chartInt J A (fun x => χ x * f x) (vecCons (logReg u ε) φ)|
      ≤ ∫ y, C₁ * chartDens J A w ψ y := by
        refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
          (Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul C₁) (Eventually.of_forall fun y => ?_))
        exact (VarIntAdd.abs_chartDens_le hfin _ _ y).trans (h₁ u ε hε.1 χ w hw0 hvw y)
    _ = C₁ * ∫ y, chartDens J A w ψ y := integral_const_mul _ _
    _ ≤ C₁ * (T.card * (C₂ * r ^ (2 * d))) := mul_le_mul_of_nonneg_left hT hC₁
    _ = C₁ * C₂ * (T.card * r ^ (2 * d)) := by ring
    _ ≤ C₁ * C₂ * (C₃ * r ^ 2) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ (C₁ * C₂ * C₃ + 1) * r := by
        nlinarith [mul_le_mul_of_nonneg_left hr.2 (mul_nonneg hM hr.1.le), hr.1]
    _ ≤ (C₁ * C₂ * C₃ + 1) * (δ / (C₁ * C₂ * C₃ + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = δ := mul_div_cancel₀ _ (by positivity)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCMUnmixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

theorem sliceCMUnmixed_local (h : CMQuotientUnmixed.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (m : Ideal R) [m.IsPrime] {d : ℕ} (J : Ideal R) (ℓ : Fin d → R) (hℓ : ∀ i, ℓ i ∈ m)
    (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (π : Localization.AtPrime m →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J.map (algebraMap R (Localization.AtPrime m)))
    (hB : ringKrullDim B = (d + 1 : ℕ))
    (hS : ringKrullDim (Localization.AtPrime m ⧸
      (J ⊔ Ideal.span (Set.range ℓ)).map (algebraMap R (Localization.AtPrime m))) = (1 : ℕ)) :
    ∀ P ∈ associatedPrimes R (R ⧸ (J ⊔ Ideal.span (Set.range ℓ))), P ≤ m →
      P ∈ (J ⊔ Ideal.span (Set.range ℓ)).minimalPrimes ∧ P ≠ m := by
  intro P hP hPm
  obtain ⟨I, hI⟩ : ∃ I, I = J ⊔ Ideal.span (Set.range ℓ) := ⟨_, rfl⟩
  rw [← hI] at hP hS ⊢
  have hJI : J ≤ I := hI ▸ le_sup_left
  let x : Fin d → B := fun i => π (algebraMap R (Localization.AtPrime m) (ℓ i))

  have hspan : Ideal.span (Set.range x) = (I.map (algebraMap R (Localization.AtPrime m))).map π := by
    rw [hI, Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker π).2 hker.ge, bot_sup_eq,
      Ideal.map_map, Ideal.map_span, ← Set.range_comp]
    rfl
  have hker_le : ∀ Q : Ideal R, J ≤ Q → RingHom.ker π ≤ Q.map (algebraMap R (Localization.AtPrime m)) :=
    fun Q hQ => hker ▸ Ideal.map_mono hQ
  have hcomap : ∀ Q : Ideal R, J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π =
        Q.map (algebraMap R (Localization.AtPrime m)) := fun Q hQ => by
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 (hker_le Q hQ)]

  have hdimx : ringKrullDim (B ⧸ Ideal.span (Set.range x)) = (1 : ℕ) := by
    let f : Localization.AtPrime m →+* B ⧸ Ideal.span (Set.range x) := (Ideal.Quotient.mk _).comp π
    have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
    have hkf : RingHom.ker f = I.map (algebraMap R (Localization.AtPrime m)) := by
      ext c
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap,
        hcomap I hJI]
    rw [← ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf),
      ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hkf), hS]
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => by
    have : IsLocalHom π := IsLocalHom.of_surjective π hπ
    exact map_nonunit π _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m (ℓ i)).2
      (hℓ i))
  have hsum : ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B := by
    rw [hdimx, hB, ← Nat.cast_add, Nat.add_comm]

  obtain ⟨hPp, y, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmemP : ∀ s, s ∈ P ↔ s * r ∈ I := fun s => by
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot,
      show s • Ideal.Quotient.mk I r = Ideal.Quotient.mk I (s * r) from rfl, Ideal.Quotient.eq_zero_iff_mem]
  have hIP : I ≤ P := fun s hs => (hmemP s).2 (I.mul_mem_right r hs)
  have hdisj : ∀ Q : Ideal R, Q ≤ m → Disjoint (m.primeCompl : Set R) Q :=
    fun Q hQ => Set.disjoint_left.2 fun u hu huQ => hu (hQ huQ)
  have hprime : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).IsPrime := fun Q hQ hQm hJQ => by
    have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) Q hQ (hdisj Q hQm)
    exact Ideal.map_isPrime_of_surjective hπ (hker_le Q hJQ)
  have hback : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      (((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π).comap
        (algebraMap R (Localization.AtPrime m)) = Q := fun Q hQ hQm hJQ => by
    rw [hcomap Q hJQ]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ hQ (hdisj Q hQm)
  obtain ⟨p, hp⟩ : ∃ p, p = (P.map (algebraMap R (Localization.AtPrime m))).map π := ⟨_, rfl⟩
  have hpP : p.IsPrime := hp ▸ hprime P hPp hPm (hJI.trans hIP)

  have hass : p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)) := by
    refine isAssociatedPrime_iff.2 ⟨hpP, Ideal.Quotient.mk _ (π (algebraMap R (Localization.AtPrime m) r)), ?_⟩
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
      show π a • Ideal.Quotient.mk (Ideal.span (Set.range x)) (π (algebraMap R (Localization.AtPrime m) r)) =
        Ideal.Quotient.mk _ (π (a * algebraMap R (Localization.AtPrime m) r)) by rw [map_mul]; rfl,
      Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap, ← Ideal.mem_comap, hcomap I hJI, hp,
      hcomap P (hJI.trans hIP)]
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl a
    rw [← IsLocalization.mk'_one (M := m.primeCompl) (Localization.AtPrime m) r, ← IsLocalization.mk'_mul,
      mul_one, IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
    simp_rw [hmemP, mul_assoc]
  obtain ⟨hmin, hdimp⟩ := h B d x hxm hsum p hass
  refine ⟨⟨⟨hPp, hIP⟩, fun Q ⟨hQp, hIQ⟩ hQP => ?_⟩, fun hPeq => ?_⟩
  · have hQm : Q ≤ m := hQP.trans hPm
    have hJQ : J ≤ Q := hJI.trans hIQ
    have h1 : Ideal.span (Set.range x) ≤ (Q.map (algebraMap R (Localization.AtPrime m))).map π := by
      rw [hspan]
      exact Ideal.map_mono (Ideal.map_mono hIQ)
    have h2 : (Q.map (algebraMap R (Localization.AtPrime m))).map π ≤ p :=
      hp ▸ Ideal.map_mono (Ideal.map_mono hQP)
    have h3 := hmin.2 ⟨hprime Q hQp hQm hJQ, h1⟩ h2
    rw [← hback P hPp hPm (hJI.trans hIP), ← hback Q hQp hQm hJQ, ← hp]
    exact Ideal.comap_mono (Ideal.comap_mono h3)
  · have hpmax : p.IsMaximal := by
      have := Ideal.map_eq_top_or_isMaximal_of_surjective π hπ
        (maximalIdeal.isMaximal (Localization.AtPrime m))
      rw [hPeq, Localization.AtPrime.map_eq_maximalIdeal] at hp
      rw [← hp] at this
      exact this.resolve_left hpP.ne_top
    let := Ideal.Quotient.field p
    have h0 : ringKrullDim (B ⧸ p) = 0 := ringKrullDim_eq_zero_of_field (B ⧸ p)
    rw [hdimp, hdimx] at h0
    exact absurd h0 (by simp)

theorem SliceCMUnmixed.proof (h : CMQuotientUnmixed.Statement) : SliceCMUnmixed.Statement := by
  intro n d J L q hCM hdimB hdimS P hP hPm
  have : IsCohenMacaulayLocalRing (localRingAt J q) := hCM
  have hℓ : ∀ i, linPoly L i - C ((L *ᵥ q) i) ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := by
    intro i
    rw [RingHom.mem_ker, map_sub, eval_linPoly, eval_C, sub_self]
  have hsl : sliceIdeal J L q = J ⊔ Ideal.span (Set.range fun i => linPoly L i - C ((L *ᵥ q) i)) := rfl
  rw [hsl] at hP hdimS ⊢
  have h1 := sliceCMUnmixed_local h (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) J
    (fun i => linPoly L i - C ((L *ᵥ q) i)) hℓ (localRingAt J q)
  have h2 := h1 (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective Ideal.mk_ker
  have h3 := h2 hdimB hdimS
  exact h3 P hP hPm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLelongError
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix

noncomputable section

namespace SliceLelongError

theorem deriv_smoothTransition_eq_zero {s : ℝ} (hs : s < 0 ∨ 1 < s) :
    deriv Real.smoothTransition s = 0 ∧ deriv (deriv Real.smoothTransition) s = 0 := by
  have hloc : deriv Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    rcases hs with hs | hs
    · filter_upwards [Iio_mem_nhds hs] with r hr
      have hc : Real.smoothTransition =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (show r < 0 from hr)] with q hq
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hq)
      rw [hc.deriv_eq, deriv_const]
    · filter_upwards [Ioi_mem_nhds hs] with r hr
      have hc : Real.smoothTransition =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (show 1 < r from hr)] with q hq
        exact Real.smoothTransition.one_of_one_le (le_of_lt hq)
      rw [hc.deriv_eq, deriv_const]
  exact ⟨hloc.eq_of_nhds, by rw [hloc.deriv_eq, deriv_const]⟩

theorem continuous_derivs :
    Continuous (deriv Real.smoothTransition) ∧ Continuous (deriv (deriv Real.smoothTransition)) := by
  have h1 := contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))
  exact ⟨h1.2.continuous, (contDiff_infty_iff_deriv.mp h1.2).2.continuous⟩

theorem exists_bound_derivs : ∃ M₁ M₂ : ℝ, (∀ s, |deriv Real.smoothTransition s| ≤ M₁) ∧
    ∀ s, |deriv (deriv Real.smoothTransition) s| ≤ M₂ := by
  have hsupp : ∀ f : ℝ → ℝ, (∀ s, s < 0 ∨ 1 < s → f s = 0) → HasCompactSupport f := fun f hf =>
    HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun s hs => hf s (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs; exact hs)
  obtain ⟨M₁, hM₁⟩ := continuous_derivs.1.bounded_above_of_compact_support
    (hsupp _ fun s hs => (deriv_smoothTransition_eq_zero hs).1)
  obtain ⟨M₂, hM₂⟩ := continuous_derivs.2.bounded_above_of_compact_support
    (hsupp _ fun s hs => (deriv_smoothTransition_eq_zero hs).2)
  exact ⟨M₁, M₂, fun s => by simpa [Real.norm_eq_abs] using hM₁ s,
    fun s => by simpa [Real.norm_eq_abs] using hM₂ s⟩

theorem bound_aux {P Q A B k : ℝ} (hk : 0 ≤ k) (hP : |P| ≤ A)
    (hQ : |Q| ≤ B * (2 * (k + 1) - (k + 1) + 1)) :
    |-(k + 1)⁻¹ * P + (k + 1)⁻¹ ^ 2 * Q| ≤ (|A| + 2 * |B|) / (k + 1) := by
  have hk1 : 0 < k + 1 := by linarith
  have ha : 0 < (k + 1)⁻¹ := inv_pos.mpr hk1
  have ha1 : (k + 1)⁻¹ * (k + 1) = 1 := inv_mul_cancel₀ hk1.ne'
  have hale : (k + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hP' : |P| ≤ |A| := hP.trans (le_abs_self A)
  have hQ' : |Q| ≤ |B| * (k + 2) := hQ.trans (by
    rw [show 2 * (k + 1) - (k + 1) + 1 = k + 2 by ring]
    exact mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith))
  have key : (k + 1)⁻¹ ^ 2 * (k + 2) ≤ 2 * (k + 1)⁻¹ := by nlinarith
  calc |-(k + 1)⁻¹ * P + (k + 1)⁻¹ ^ 2 * Q|
      ≤ (k + 1)⁻¹ * |P| + (k + 1)⁻¹ ^ 2 * |Q| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos (pow_pos ha 2)]
    _ ≤ (k + 1)⁻¹ * |A| + (k + 1)⁻¹ ^ 2 * (|B| * (k + 2)) := by gcongr
    _ ≤ (|A| + 2 * |B|) / (k + 1) := by
        rw [div_eq_mul_inv]
        nlinarith [mul_le_mul_of_nonneg_left key (abs_nonneg B), abs_nonneg A]

theorem proof (h₁ : SliceCutChain.Statement) (h₂ : SliceWeightBound.Statement)
    (h₃ : SliceBandEnergy.Statement) : SliceLelongError.Statement := by
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨M₁, M₂, hM₁, hM₂⟩ := exists_bound_derivs
  obtain ⟨C₂, hC₂⟩ := h₂ n e h J F u ℓ hJ hF hu hℓ
  obtain ⟨C₃, hC₃⟩ := h₃ n e h J F u ℓ hJ hF hu hℓ hℓW
  have hL : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) :=
    Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable
  refine squeeze_zero_norm (a := fun k : ℕ => (|C₂ * M₁| + 2 * |C₃ * M₂|) / ((k : ℝ) + 1))
    (fun k => ?_) (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hw : Measurable fun x : Fin n → ℂ => 2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1) :=
    measurable_const.sub (hL.div_const _)
  have e1 := hC₂ (fun x => deriv Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) M₁
    (continuous_derivs.1.measurable.comp hw) fun x => hM₁ _
  have e2 := hC₃
    (fun x => deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))) M₂
    ((k : ℝ) + 1) (2 * ((k : ℝ) + 1)) (continuous_derivs.2.measurable.comp hw) (fun x => hM₂ _)
    (by linarith) fun x hx => by
      by_contra hb
      rw [not_and_or, not_le, not_le] at hb
      refine hx (deriv_smoothTransition_eq_zero ?_).2
      rcases hb with hb | hb
      · have : Real.log (h.dualNorm x) / ((k : ℝ) + 1) < 1 := (div_lt_one hk).mpr hb
        right; linarith
      · have : 2 < Real.log (h.dualNorm x) / ((k : ℝ) + 1) := (lt_div_iff₀ hk).mpr hb
        left; linarith
  rw [Real.norm_eq_abs, h₁ n e h J F u ℓ k hJ hF hu hℓ]
  exact bound_aux (Nat.cast_nonneg k) e1 e2

end SliceLelongError

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeCollarMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Matrix ComplexSets

noncomputable section

theorem TubeCollarMass.proof (hC : TubeCollarCompare.Statement) (hM : ChartMassCompare.Statement)
    (hF : MassFinite.Statement) : TubeCollarMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  obtain ⟨C, hCle⟩ := hC n d J A P R hJ hdim hA hP
  have hψ : ∀ k : Fin (d + 1), SmoothNear (zeroSet J) ((fun _ => euclPot) k) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)

  have hI : Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ))
      (fun _ : Fin (d + 1) => euclPot)) := by
    obtain ⟨K, hK, hle⟩ := hM n (d + 1) J A (fun _ => euclPot) R hJ hdim hA hψ
    have hmeas := (SheetSumMeasurable.proof n (d + 1) J A
      ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) (fun _ => euclPot) hJ hdim hA
      (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hbd : Bornology.IsBounded
        (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
      (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
    obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
    have h1 := hle (fun _ => 1) measurable_const
    simp only [enorm_one, setLIntegral_one] at h1
    refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
    exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hF n (d + 1) J hJ hdim R')

  have hl : Measurable (logAbsSq P) :=
    Real.measurable_log.comp ((MvPolynomial.continuous_eval P).norm.pow 2).measurable
  refine (hI.const_mul C).mono'
    (((measurable_tubeDens hA P R _).indicator (measurableSet_le measurable_const hl)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y)]
  exact hCle y

end

end GroundTheory.Heights₂.Heights
end


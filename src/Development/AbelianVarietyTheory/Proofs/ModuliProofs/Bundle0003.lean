import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialMapMaximalIdealIsPrime
section
open scoped TensorProduct

namespace GlobalTheory

theorem valuationRing_exists_dvd_all {O ι : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    (f : ι → O) (s : Finset ι) (hs : s.Nonempty) : ∃ i ∈ s, ∀ j ∈ s, f i ∣ f j := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, by simp, by simp⟩
  | cons a s ha hs ih =>
    obtain ⟨i, hi, h⟩ := ih
    rcases ValuationRing.dvd_total (f a) (f i) with h1 | h1
    · refine ⟨a, by simp, fun j hj => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact dvd_rfl
      · exact h1.trans (h j hj)
    · refine ⟨i, by simp [hi], fun j hj => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact h1
      · exact h j hj

theorem mvPolynomial_map_maximalIdeal_isPrime (O : Type) [CommRing O] [IsLocalRing O] (g : ℕ) :
    ((IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)).IsPrime := by
  have h : (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)
      = RingHom.ker (MvPolynomial.map (σ := Fin g) (IsLocalRing.residue O)) := by
    ext F
    rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
  rw [h]
  exact RingHom.ker_isPrime _

theorem mvPolynomial_exists_content (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] (g : ℕ)
    (F : MvPolynomial (Fin g) O) (hF : F ≠ 0) :
    ∃ (π : O) (F' : MvPolynomial (Fin g) O), F = MvPolynomial.C π * F' ∧
      F' ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) := by
  obtain ⟨i, hi, h⟩ := valuationRing_exists_dvd_all (fun m => F.coeff m) F.support
    (MvPolynomial.support_nonempty.2 hF)
  have hd : MvPolynomial.C (F.coeff i) ∣ F := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    by_cases hm : m ∈ F.support
    · exact h m hm
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      exact dvd_zero _
  obtain ⟨F', hF'⟩ := hd
  refine ⟨F.coeff i, F', hF', fun hmem => ?_⟩
  have h1 := MvPolynomial.mem_map_C_iff.1 hmem i
  have h2 : F.coeff i = F.coeff i * F'.coeff i := by
    conv_lhs => rw [hF', MvPolynomial.coeff_C_mul]
  have h3 : F'.coeff i = 1 :=
    (mul_left_cancel₀ (MvPolynomial.mem_support_iff.1 hi) ((mul_one _).trans h2)).symm
  rw [h3] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem mvPolynomial_content_valuationRing :
    ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] (g : ℕ), ((IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)).IsPrime ∧ (∀ F : MvPolynomial (Fin g) O, F ≠ 0 → ∃ (π : O) (F' : MvPolynomial (Fin g) O), F = MvPolynomial.C π * F' ∧ F' ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)) ∧ ∀ (π : O) (u F : MvPolynomial (Fin g) O), u ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) → MvPolynomial.C π ∣ u * F → MvPolynomial.C π ∣ F := by
  intro O _ _ _ g
  have hp := mvPolynomial_map_maximalIdeal_isPrime O g
  refine ⟨hp, mvPolynomial_exists_content O g, fun π u F hu hdvd => ?_⟩
  by_cases hF : F = 0
  · rw [hF]; exact dvd_zero _
  obtain ⟨π', F', rfl, hF'⟩ := mvPolynomial_exists_content O g F hF
  have huF : u * F' ∉ (IsLocalRing.maximalIdeal O).map
      (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) := fun h => (hp.mem_or_mem h).elim hu hF'
  rw [MvPolynomial.mem_map_C_iff, not_forall] at huF
  obtain ⟨m, hm⟩ := huF
  have hunit : IsUnit ((u * F').coeff m) := by
    by_contra hn
    exact hm ((IsLocalRing.mem_maximalIdeal _).2 hn)
  have h1 : π ∣ π' * (u * F').coeff m := by
    have := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).1 hdvd m
    rwa [mul_left_comm, MvPolynomial.coeff_C_mul] at this
  have h2 : π ∣ π' := (hunit.dvd_mul_right).1 h1
  exact Dvd.dvd.mul_right (map_dvd _ h2) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPowerSeriesVariablesSyzygySocle
section
open scoped TensorProduct

namespace GlobalTheory

open MvPowerSeries Finsupp in
theorem coeff_mul_X_ite {k : Type} [CommRing k] {g : ℕ} (f : MvPowerSeries (Fin g) k)
    (j : Fin g) (m : Fin g →₀ ℕ) :
    coeff m (f * X j) = if m j ≠ 0 then coeff (m - single j 1) f else 0 := by
  classical
  rw [X_def, coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

open MvPowerSeries Finsupp in
theorem mvPowerSeries_X_syzygy {k : Type} [CommRing k] {g : ℕ}
    (r : Fin g → MvPowerSeries (Fin g) k) (hr : ∑ i, r i * X i = 0) :
    ∃ s : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k), s.transpose = -s ∧ (∀ i, s i i = 0) ∧
      r = s.mulVec (fun i => X i) := by
  classical
  let t : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k) := fun i j n =>
    if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0
  have ht : ∀ i j n, coeff n (t i j) =
      if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0 := fun _ _ _ => rfl
  refine ⟨t - t.transpose, by simp [Matrix.transpose_sub], fun i => by simp, ?_⟩
  funext i
  ext m
  have h1 : ∀ j, coeff m (t i j * X j) =
      if m j ≠ 0 ∧ j < i ∧ ∀ l < j, m l = 0 then coeff m (r i) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht]
    by_cases hj : m j = 0
    · simp [hj]
    · have e : m - single j 1 + single j 1 = m :=
        tsub_add_cancel_of_le (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
      have e2 : (∀ l < j, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < j, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, hl.ne']
      simp only [e, e2, hj, ne_eq, not_false_eq_true, if_true, true_and]
  have h2 : ∀ j, coeff m (t j i * X j) =
      if (∀ l < i, m l = 0) ∧ j ≠ i then coeff (m + single i 1) (r j * X j) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht, coeff_mul_X_ite]
    by_cases hji : j = i
    · simp [hji]
    have e0 : (m + single i 1 : Fin g →₀ ℕ) j = m j := by
      simp [Finsupp.single_apply, Ne.symm hji]
    rw [e0]
    by_cases hj : m j = 0
    · simp [hj]
    have e : m - single j 1 + single i 1 = m + single i 1 - single j 1 :=
      tsub_add_eq_add_tsub (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
    rw [e]
    rcases lt_or_gt_of_ne hji with h | h
    · have : ¬ ∀ l < i, m l = 0 := fun H => hj (H j h)
      simp [this, h.not_gt]
    · have e2 : (∀ l < i, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < i, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, (hl.trans h).ne']
      simp only [e2, hj, h, hji, ne_eq, not_false_eq_true, if_true, true_and, and_true]
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.transpose_apply, sub_mul,
    map_sum, map_sub, h1, h2, Finset.sum_sub_distrib]
  by_cases hi : ∀ l < i, m l = 0
  · rw [Finset.sum_eq_zero (fun j _ => if_neg (fun H => H.1 (hi j H.2.1)))]
    have h3 := congrArg (coeff (m + single i 1)) hr
    rw [map_sum, map_zero, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), coeff_mul_X_ite] at h3
    simp only [iff_true_intro hi, true_and]
    rw [← Finset.sum_filter, Finset.filter_ne']
    simp only [Finsupp.add_apply, single_eq_same, add_tsub_cancel_right] at h3
    rw [if_pos (by omega)] at h3
    linear_combination h3
  · simp only [hi, false_and, if_false, Finset.sum_const_zero, sub_zero]
    push_neg at hi
    obtain ⟨l, hl, hml⟩ := hi
    obtain ⟨j, hj, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Fin g)) {j | m j ≠ 0} ⟨l, hml⟩
    have hj0 : ∀ a < j, m a = 0 := fun a ha => by
      by_contra h; exact hmin a h ha
    rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨hj, lt_of_le_of_lt (not_lt.1 (hmin l hml)) hl, hj0⟩]
    · intro b _ hb
      refine if_neg fun H => ?_
      rcases lt_or_gt_of_ne hb with h | h
      · exact H.1 (hj0 b h)
      · exact hj (H.2.2 j h)
    · simp

open MvPowerSeries Finsupp in
theorem mvPowerSeries_prod_X_pow_notMem {k : Type} [CommRing k] [Nontrivial k] {g : ℕ} (N : ℕ) :
    ∏ i, (X i : MvPowerSeries (Fin g) k) ^ N ∉
      Ideal.span (Set.range fun i => (X i : MvPowerSeries (Fin g) k) ^ (N + 1)) := by
  classical
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  have hp : ∀ s : Finset (Fin g), ∏ i ∈ s, (X i : MvPowerSeries (Fin g) k) ^ N =
      monomial (∑ i ∈ s, single i N) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  have := congrArg (coeff (∑ i : Fin g, single i N)) hc
  rw [hp, coeff_monomial_same, map_sum, Finset.sum_eq_zero] at this
  · exact zero_ne_one this
  · intro i _
    refine X_pow_dvd_iff.1 (dvd_mul_left _ _) _ ?_
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem mvPowerSeries_variables_syzygy_socle :
    ∀ (k : Type) [Field k] (g : ℕ) (x : Fin g → MvPowerSeries (Fin g) k), (∀ i, x i = MvPowerSeries.X i) → (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) ∧ ∀ N : ℕ, ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)) := by
  intro k _ g x hx
  obtain rfl : x = fun i => MvPowerSeries.X i := funext hx
  exact ⟨fun r hr => mvPowerSeries_X_syzygy r hr, fun N => mvPowerSeries_prod_X_pow_notMem N⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormCardQuotientSpan
section
namespace GlobalTheory.NormDetIndex

open Module Submodule

theorem norm_card_quotient_span (l : ℕ) [Fact (Nat.Prime l)] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span ({x} : Set ℤ_[l])) : ℕ) : ℚ_[l])‖ = ‖x‖ := by
  have h1 : Ideal.span ({x} : Set ℤ_[l]) = RingHom.ker (PadicInt.toZModPow (p := l) x.valuation) := by
    rw [PadicInt.ker_toZModPow, Ideal.span_singleton_eq_span_singleton]
    refine Associated.symm ⟨PadicInt.unitCoeff hx, ?_⟩
    rw [mul_comm]
    exact (PadicInt.unitCoeff_spec hx).symm
  have h2 : Function.Surjective (PadicInt.toZModPow (p := l) x.valuation) :=
    ZMod.ringHom_surjective _
  rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective h2).toEquiv, Nat.card_zmod,
    PadicInt.norm_eq_zpow_neg_valuation hx, Nat.cast_pow, Padic.norm_p_pow]

theorem norm_eq_of_associated (l : ℕ) [Fact (Nat.Prime l)] {x y : ℤ_[l]} (h : Associated x y) :
    ‖x‖ = ‖y‖ := by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul, PadicInt.isUnit_iff.mp u.isUnit, mul_one]

theorem norm_det_eq_norm_index (l : ℕ) [Fact (Nat.Prime l)] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℚ_[l])‖ := by
  set N := LinearMap.range M.mulVecLin with hN
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hM hv
  let e : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective _ hinj
  let b : Basis κ ℤ_[l] (κ → ℤ_[l]) := Pi.basisFun _ _
  have h : finrank ℤ_[l] N = finrank ℤ_[l] (κ → ℤ_[l]) := e.symm.finrank_eq
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  let e' : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := b'.equiv ab (Equiv.refl _)
  have h1 : M.det = LinearMap.det (N.subtype ∘ₗ (e : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) := by
    rw [← LinearMap.det_toLin' M]
    rfl
  have h2 : LinearMap.det (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    have ha : (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) (b' j) = a j • b' j := by
      change ((b'.equiv ab (Equiv.refl _) (b' j) : N) : κ → ℤ_[l]) = _
      rw [b'.equiv_apply, Equiv.refl_apply]
      exact smithNormalFormBotBasis_def b h j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have h3 : N.toAddSubgroup.index
      = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span ({a i} : Set ℤ_[l])) := by
    change Nat.card ((κ → ℤ_[l]) ⧸ N) = _
    rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  rw [h1, norm_eq_of_associated l (LinearMap.associated_det_comp_equiv N.subtype e e'), h2, h3,
    Nat.cast_prod, norm_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ =>
    (norm_card_quotient_span l (smithNormalFormCoeffs_ne_zero b h i)).symm

end GlobalTheory.NormDetIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SetIntegralFderivEqZeroOfLatticePeriodic
section
open Complex Matrix
open scoped ContDiff BigOperators Real
open MeasureTheory Module
open scoped Pointwise

namespace GlobalTheory

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in

theorem setIntegral_comp_add_of_lattice_periodic [SecondCountableTopology E]
    (L : Submodule ℤ E) [Countable L] {D : Set E}
    (hD : IsAddFundamentalDomain L D μ) {F : E → ℂ} (hF : ∀ (l : L) z, F (z + l) = F z) (c : E) :
    ∫ z in D, F (z + c) ∂μ = ∫ z in D, F z ∂μ := by
  have : VAddInvariantMeasure L E μ := ⟨fun g s _ => measure_preimage_add μ (g : E) s⟩
  have hpres := measurePreserving_add_right μ c
  have hD' : IsAddFundamentalDomain L ((fun x => x + c) '' D) μ :=
    hD.image_of_equiv (Equiv.addRight c)
      (measurePreserving_add_right μ (-c)).quasiMeasurePreserving (Equiv.refl _)
      (fun g x => add_assoc _ _ _)
  rw [← hpres.setIntegral_image_emb (MeasurableEquiv.addRight c).measurableEmbedding]
  refine (hD'.setIntegral_eq hD fun g x => ?_)
  show F ((g : E) + x) = F x
  rw [add_comm]
  exact hF g x

theorem setIntegral_fderiv_eq_zero_of_lattice_periodic
    (L : Submodule ℤ E) [Countable L] {D : Set E}
    (hD : IsAddFundamentalDomain L D μ) (hm : MeasurableSet D) (hb : Bornology.IsBounded D)
    {F : E → ℂ} (hF1 : ContDiff ℝ 1 F) (hF : ∀ (l : L) z, F (z + l) = F z) (v : E) :
    ∫ z in D, fderiv ℝ F z v ∂μ = 0 := by
  have hcont : Continuous (fderiv ℝ F) := hF1.continuous_fderiv one_ne_zero
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hK : IsCompact (Metric.closedBall (0 : E) (R + ‖v‖)) := isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hfin : μ D < ⊤ := hb.measure_lt_top
  have : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hfin.ne
  have hint : ∀ G : E → ℂ, Continuous G → Integrable G (μ.restrict D) := fun G hG =>
    (hG.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) R)).mono_set hR
  have hmem : ∀ z ∈ D, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      z + t • v ∈ Metric.closedBall (0 : E) (R + ‖v‖) := by
    intro z hz t ht
    rw [mem_closedBall_zero_iff]
    have h1 : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 (hR hz)
    have ht' : ‖t‖ < 1 := by simpa using ht
    have h2 : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul]
      nlinarith [norm_nonneg v, norm_nonneg t]
    calc ‖z + t • v‖ ≤ ‖z‖ + ‖t • v‖ := norm_add_le _ _
      _ ≤ R + ‖v‖ := add_le_add h1 h2
  have hderiv : ∀ (z : E) (t : ℝ),
      HasDerivAt (fun s : ℝ => F (z + s • v)) (fderiv ℝ F (z + t • v) v) t := by
    intro z t
    have hd : HasFDerivAt F (fderiv ℝ F (z + t • v)) (z + t • v) :=
      (hF1.differentiable one_ne_zero _).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => z + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add z
    exact hd.comp_hasDerivAt t hl
  have hmeas : ∀ᶠ s in nhds (0 : ℝ), AEStronglyMeasurable (fun z => F (z + s • v)) (μ.restrict D) :=
    Filter.Eventually.of_forall fun s =>
      (hF1.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hint0 : Integrable (fun z => F (z + (0 : ℝ) • v)) (μ.restrict D) :=
    hint _ (hF1.continuous.comp (continuous_id.add continuous_const))
  have hmeas' : AEStronglyMeasurable (fun z => fderiv ℝ F (z + (0 : ℝ) • v) v) (μ.restrict D) :=
    ((hcont.comp (continuous_id.add continuous_const)).clm_apply continuous_const).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(μ.restrict D), ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖fderiv ℝ F (z + s • v) v‖ ≤ M * ‖v‖ := by
    refine (ae_restrict_iff' hm).2 (Filter.Eventually.of_forall fun z hz s hs => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM _ (hmem z hz s hs)) (norm_nonneg _))
  have hdiff : ∀ᵐ z ∂(μ.restrict D), ∀ s ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F (z + t • v)) (fderiv ℝ F (z + s • v) v) s :=
    Filter.Eventually.of_forall fun z s _ => hderiv z s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := μ.restrict D)
    (F := fun (s : ℝ) (z : E) => F (z + s • v)) (x₀ := 0) (bound := fun _ => M * ‖v‖)
    (F' := fun (s : ℝ) (z : E) => fderiv ℝ F (z + s • v) v)
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) hmeas hint0 hmeas' hbound (integrable_const _) hdiff
  have hconst : (fun s : ℝ => ∫ z in D, F (z + s • v) ∂μ) = fun _ => ∫ z in D, F z ∂μ :=
    funext fun s => setIntegral_comp_add_of_lattice_periodic μ L hD hF (s • v)
  have h3 : HasDerivAt (fun _ : ℝ => ∫ z in D, F z ∂μ)
      (∫ z in D, fderiv ℝ F (z + (0 : ℝ) • v) v ∂μ) 0 := by
    rw [← hconst]
    exact key.2
  simpa using h3.unique (hasDerivAt_const _ _)

theorem const_eq_zero_of_sum_fderiv_lattice_periodic
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    {F : ι → E → ℂ} {a : ι → ℂ} {v : ι → E} {C : ℂ}
    (hF : ∀ k, ContDiff ℝ 1 (F k) ∧ ∀ (l : L) z, F k (z + l) = F k z)
    (hC : ∀ z, ∑ k, a k * fderiv ℝ (F k) z (v k) = C) : C = 0 := by
  classical
  let μ : Measure E := Measure.addHaar
  let b := Module.Free.chooseBasis ℤ L
  have hD : IsAddFundamentalDomain L (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) μ :=
    ZLattice.isAddFundamentalDomain b μ
  have hm : MeasurableSet (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_measurableSet _
  have hb : Bornology.IsBounded (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_isBounded _
  set D := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) with hDdef
  have hzero : ∀ k, ∫ z in D, fderiv ℝ (F k) z (v k) ∂μ = 0 := fun k =>
    setIntegral_fderiv_eq_zero_of_lattice_periodic μ L hD hm hb (hF k).1 (hF k).2 (v k)
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hint : ∀ k, IntegrableOn (fun z => a k * fderiv ℝ (F k) z (v k)) D μ := fun k =>
    ((continuous_const.mul
      (((hF k).1.continuous_fderiv one_ne_zero).clm_apply continuous_const)).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : E) R)).mono_set hR
  have hsum : ∫ z in D, (∑ k, a k * fderiv ℝ (F k) z (v k)) ∂μ = 0 := by
    rw [integral_finsetSum _ (fun k _ => hint k)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_const_mul, hzero k, mul_zero]
  simp_rw [hC] at hsum
  rw [setIntegral_const] at hsum
  have : VAddInvariantMeasure L E μ := ⟨fun g s _ => measure_preimage_add μ (g : E) s⟩
  have hne : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)
  have hfin : μ D ≠ ⊤ := hb.measure_lt_top.ne
  rcases smul_eq_zero.1 hsum with h | h
  · exact absurd h (ENNReal.toReal_ne_zero.2 ⟨hne, hfin⟩)
  · exact h

end General

theorem const_eq_zero_of_sum_fderiv_periodic :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (n : ℕ) (F : Fin n → (Fin g → ℂ) → ℂ) (a : Fin n → ℂ) (v : Fin n → (Fin g → ℂ)) (C : ℂ),
      (∀ k, ContDiff ℝ 1 (F k) ∧ ∀ (l : Λ) z, F k (z + l) = F k z) →
      (∀ z, ∑ k, a k * fderiv ℝ (F k) z (v k) = C) → C = 0 := by
  intro g Λ hdisc hspan n F a v C hF hC
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  exact const_eq_zero_of_sum_fderiv_lattice_periodic Λ hF hC

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfFlatOfFormallyUnramified
section
open scoped TensorProduct

namespace GlobalTheory

theorem isBezout_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W] [IsBezout W]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : IsBezout B := by
  refine ⟨fun J hJ => ?_⟩
  have hfin : Module.Finite B J := Module.Finite.iff_fg.2 hJ
  have htB : Submodule.torsion W B = ⊥ :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.1 inferInstance
  have hW : Module.Flat W J := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have hx : (x : B) ∈ Submodule.torsion W B := ⟨a, congrArg Subtype.val ha⟩
    rw [htB, Submodule.mem_bot] at hx
    exact (Submodule.mem_bot W).2 (Subtype.ext hx)
  have hB : Module.Flat B J := Algebra.FormallyUnramified.flat_of_restrictScalars W B J
  have hfree : Module.Free B J := Module.free_of_flat_of_isLocalRing
  rw [← Submodule.rank_le_one_iff_isPrincipal]
  exact (Submodule.rank_le J).trans (Module.rank_self B).le

theorem isAlgebraic_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W]
    [CommRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : Algebra.IsAlgebraic W B := by
  let K := FractionRing W
  have hfin : Module.Finite K (K ⊗[W] B) := Algebra.FormallyUnramified.finite_of_free K _
  have halg : Algebra.IsAlgebraic K (K ⊗[W] B) := inferInstance
  have hK : Algebra.IsAlgebraic W K := IsLocalization.isAlgebraic K (nonZeroDivisors W)
  have halgW : Algebra.IsAlgebraic W (K ⊗[W] B) := Algebra.IsAlgebraic.trans W K _
  exact Algebra.IsAlgebraic.of_injective
    (Algebra.TensorProduct.includeRight (R := W) (A := K) (B := B))
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective W K))

theorem valuationRing_of_flat_of_formallyUnramified :
    ∀ (W B : Type) [CommRing W] [IsDomain W] [ValuationRing W] [CommRing B] [IsDomain B]
      [IsLocalRing B] [Algebra W B] [Module.Flat W B] [Algebra.EssFiniteType W B]
      [Algebra.FormallyUnramified W B], ValuationRing B ∧ Algebra.IsAlgebraic W B := by
  intro W B _ _ _ _ _ _ _ _ _ _
  have := isBezout_of_flat_of_formallyUnramified W B
  exact ⟨inferInstance, isAlgebraic_of_flat_of_formallyUnramified W B⟩

end GlobalTheory
end


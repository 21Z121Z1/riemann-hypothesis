import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveEmbedOrbit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

namespace CurveEmbedOrbit

theorem sameOrbit_refl {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_symm {K : Type} {ι : K → Type} {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) : SameOrbit w z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => ?_⟩
  rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]

theorem sameOrbit_trans {K : Type} {ι : K → Type} {z w u : (Σ k, ι k) → ℂ} (h1 : SameOrbit z w)
    (h2 : SameOrbit w u) : SameOrbit z u := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), funext fun p => by simp only; ring⟩

theorem eq_of_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} (hB : Birational y) {σ τ : Ω →+* ℂ}
    (hst : SameOrbit (fun p => σ (y p)) (fun p => τ (y p))) : σ = τ := by
  obtain ⟨c, hc, hcy⟩ := hst
  ext s
  obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
  have key : ∀ ρ : Ω →+* ℂ, ρ s * eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) h) =
      eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) g) := fun ρ => by
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp, hgs, map_mul]
  have e1 := key σ
  have e2 := key τ
  rw [hcy, CurveOrbit.eval_smul _ _ hh, CurveOrbit.eval_smul _ _ hg] at e1
  have hE : eval (fun p => τ (y p)) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    rw [CurveOrbit.eval_comp]
    exact (map_ne_zero τ).mpr hh0
  have hC : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  apply mul_right_cancel₀ (mul_ne_zero hC hE)
  linear_combination e1 - (∏ k, c k ^ d k) * e2

end CurveEmbedOrbit

open CurveEmbedOrbit in

theorem CurveEmbedOrbit.proof : CurveEmbedOrbit.Statement := by
  intro K _ ι _ Ω _ y R hP hB hR hRu
  classical
  obtain ⟨j, -, hj⟩ := exists_chart hP
  have hex : ∀ t : R, ∃ σ : Ω →+* ℂ, SameOrbit (t : (Σ k, ι k) → ℂ) (fun p => σ (y p)) :=
    fun t => CurveOrbit.exists_sameOrbit hP hB (hR t t.2)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro t s hts
    have h1 : SameOrbit (t : (Σ k, ι k) → ℂ) s :=
      sameOrbit_trans (hf t) (by rw [hts]; exact sameOrbit_symm (hf s))
    exact Subtype.ext ((hRu t (hR t t.2)).unique ⟨t.2, sameOrbit_refl _⟩ ⟨s.2, h1⟩)
  have hsurj : Function.Surjective f := by
    intro τ
    obtain ⟨t, ⟨htR, hzt⟩, -⟩ := hRu _ (CurveOrbit.mem_mcPts τ y hj)
    exact ⟨⟨t, htR⟩, eq_of_sameOrbit hB
      (sameOrbit_trans (sameOrbit_symm (hf ⟨t, htR⟩)) (sameOrbit_symm hzt))⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveFieldNumber
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

noncomputable section

theorem CurveFieldNumber.proof (hR1 : RegularityFunctionFieldNumber.Statement) : CurveFieldNumber.Statement := by
  intro K _ ι _ Ω _ y hA hB
  set P := mCoordIdeal y with hPdef
  have : P.IsPrime := hA.2.1.1
  obtain ⟨hF, hN⟩ := hR1 K ι P hA
  let L := FractionRing (MvPolynomial K Ω)

  let j : MRing ι ⧸ P →+* L :=
    (algebraMap (MvPolynomial K Ω) L).comp (RingHom.kerLift (mConeMap y : MRing ι →+* MvPolynomial K Ω))
  have hj : Function.Injective j :=
    (IsFractionRing.injective (MvPolynomial K Ω) L).comp (RingHom.kerLift_injective _)
  let Φ : FractionRing (MRing ι ⧸ P) →+* L := IsFractionRing.lift hj
  let c : Ω →+* L := (algebraMap (MvPolynomial K Ω) L).comp MvPolynomial.C
  have hΦ : ∀ f, Φ (algebraMap _ _ (Ideal.Quotient.mk P f)) = algebraMap _ L (mConeMap y f) := fun f =>
    (IsFractionRing.lift_algebraMap hj _).trans (congrArg (algebraMap (MvPolynomial K Ω) L)
      (RingHom.kerLift_mk (mConeMap y : MRing ι →+* MvPolynomial K Ω) f))

  have hform : ∀ {g : MRing ι} {a : K → ℕ}, IsMultiHomog g a →
      Φ (algebraMap _ _ (Ideal.Quotient.mk P g)) = c (aeval y g) * algebraMap _ L (∏ k, (X k : MvPolynomial K Ω) ^ a k) := by
    intro g a hg
    rw [hΦ, LowerBoundFree.mConeMap_of_isMultiHomog y hg, map_mul]; rfl
  have hT : ∀ a : K → ℕ, algebraMap (MvPolynomial K Ω) L (∏ k, (X k : MvPolynomial K Ω) ^ a k) ≠ 0 := fun a =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).2 (Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ (X_ne_zero k))

  have hmem : ∀ {g : MRing ι} {a : K → ℕ}, IsMultiHomog g a → aeval y g = 0 → g ∈ P := by
    intro g a hg h0
    show mConeMap y g = 0
    rw [LowerBoundFree.mConeMap_of_isMultiHomog y hg, h0, map_zero, zero_mul]

  have heq : (funField P).map Φ = c.range := by
    apply le_antisymm
    · rw [Subring.map_le_iff_le_comap, funField, Subring.closure_le]
      rintro x ⟨u, v, a, hv, hu, hvf, rfl⟩
      have hvP : v ∉ P := fun h => nonZeroDivisors.ne_zero hv ((Ideal.Quotient.eq_zero_iff_mem).2 h)
      have hvy : aeval y v ≠ 0 := fun h => hvP (hmem hvf h)
      refine ⟨aeval y u / aeval y v, ?_⟩
      have h1 := congrArg Φ (IsLocalization.mk'_spec (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩)
      rw [map_mul, hform hvf, hform hu] at h1
      have hcv : c (aeval y v) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hvy
      rw [map_div₀, div_eq_iff hcv]
      exact mul_right_cancel₀ (hT a) (by rw [← h1]; ring)
    · rintro _ ⟨s, rfl⟩
      obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
      have hhP : h ∉ P := fun hP => by
        have : mConeMap y h = 0 := hP
        rw [LowerBoundFree.mConeMap_of_isMultiHomog y hh] at this
        exact mul_ne_zero ((map_ne_zero_iff _ (MvPolynomial.C_injective K Ω)).2 hh0)
          (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) this
      obtain ⟨x, hx⟩ := exists_funField_mul_eq hg hh hhP
      refine ⟨x, x.2, ?_⟩
      have h1 := congrArg Φ hx
      rw [map_mul, hform hh, hform hg, hgs, map_mul] at h1
      have hch : c (aeval y h) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hh0
      exact mul_right_cancel₀ (mul_ne_zero hch (hT d)) (by rw [h1]; ring)

  have hc : Function.Injective c.rangeRestrict := fun a b h => c.injective (congrArg Subtype.val h)
  let e : funField P ≃+* Ω :=
    ((Subring.equivMapOfInjective (funField P) Φ Φ.injective).trans (RingEquiv.subringCongr heq)).trans
      (RingEquiv.ofBijective c.rangeRestrict ⟨hc, c.rangeRestrict_surjective⟩).symm
  exact @NumberField.of_ringEquiv _ _ hF.toField _ e hN

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveVerticalIndex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem span_toAddSubgroup (y : (Σ k, ι k) → Ω) (x : Ω) :
    (Submodule.span (curveRing y) {x}).toAddSubgroup = curveMul y x := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, curveMul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩

omit [∀ k, Fintype (ι k)] in

theorem genIndex_eq_card (y : (Σ k, ι k) → Ω) (a : K → ℤ) {x : Ω} (hx : x ∈ curveSectionMod y a) :
    genIndex (chartLat y a 1) (curveMul y x) = Nat.card (curveSectionQuot y a x) := by
  have hle : curveMul y x ≤ chartLat y a 1 := by
    rw [← span_toAddSubgroup]
    intro z hz
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) hz
  rw [genIndex, AddSubgroup.relIndex_eq_one.mpr hle, Nat.cast_one, div_one, ← span_toAddSubgroup]
  rfl

end CurveVerticalIndex

theorem CurveVertIndex.proof (hF : CurveSectionQuotFinite.Statement) (hV : CurveVertPointLength.Statement)
    (hR : CurveVertPointResidue.Statement) : CurveVertIndex.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  have := hF K ι Ω y s d hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV K ι Ω y s d hP hs hsP
  rw [CurveVerticalIndex.genIndex_eq_card y _ (HilbertSamuel.LiftBirationalAmple.chartLat_form hs),
    LogCardLength.proof (curveRing y) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)), vertR]
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal y) s,
          (locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W)) := by
        refine finsum_mem_congr rfl fun W hW => ?_
        rw [if_neg (IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι _ s d hP hs hsP W hW), hmult W hW,
          ← hR K ι Ω y s d hP hs hsP W hW]
        congr 3
    _ = ∑ᶠ m ∈ {m : Ideal (curveRing y) |
          m.IsMaximal ∧ locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0},
          (locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ m)) :=
        finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl
    _ = _ := by
        refine finsum_mem_inter_support_eq _ _ {m : Ideal (curveRing y) | m.IsMaximal} ?_
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, fun h0 => h2 (by simp [h0])⟩, h2⟩⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjPotMassPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

theorem ProjPotMassPos.isPotential_congr {e : ℕ} {X : Type} [TopologicalSpace X]
    {A : FinHolAtlas e X} {P Q : LocPot X} (hU : ∀ x, P.U x = Q.U x)
    (hφ : ∀ x, ∀ z ∈ P.U x, P.φ x z = Q.φ x z) (hP : IsPotential A P) : IsPotential A Q := by
  obtain ⟨hs, hd⟩ := hP
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have h := hs x j
    rw [hU x] at h
    refine h.congr fun w hw => ?_
    simp only [Function.comp_apply]
    exact (hφ x _ ((hU x).symm ▸ hw.2)).symm
  · rw [← hU x, ← hU x'] at hy
    obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hd x x' y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    rw [← hU x, ← hU x'] at hz
    rw [← hφ x z hz.1.2, ← hφ x' z hz.2]
    exact hGe z hz

theorem ProjPotMassPos.isPotential_multiprojPot {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X}
    {BV : FinHolAtlas n V} (hH : HoloMap BV R.A Subtype.val) :
    IsPotential BV (multiprojPot R V) := by
  let L : HermLine ι := CurveDegreeVert.fsLine (fun _ : K => 2)
  have hL : L.h = fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ ((2 : ℕ) : ℤ) := by
    funext z
    simp only [L, CurveDegreeVert.fsLine, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]
  have h1 := isPotentialPullback R.A BV Subtype.val hH (potOf R L)
    (isPotential_potOf R (CurveDegreeVert.isSmoothHerm_fsLine _))
  refine ProjPotMassPos.isPotential_congr (P := (potOf R L).pullback Subtype.val hH.1) (fun _ => rfl) (fun y z hz => ?_) h1
  have hm := (R.mem y.1 z.1 hz).1
  show Real.log (L.h (R.lift y.1 z.1)) = ∑ k, Real.log (∑ i, ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2)
  have hpos : ∀ k, 0 < ∑ i, ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2 := fun k => by
    obtain ⟨i, hi⟩ := hm k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
      (Finset.single_le_sum (f := fun i => ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ i))
  rw [hL]
  simp only [zpow_natCast, Real.sq_sqrt (hpos _).le]
  exact Real.log_prod (fun k _ => (hpos k).ne')

theorem ProjPotMassPos.of_found (hD : ProjPotDens.Statement) : ProjPotMassPos.Statement := by
  intro K _ ι _ P J n R V BV hH hV C hC hCF
  obtain ⟨x, hxC, hxF⟩ := hCF
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  have hPot : ∀ _ : Fin n, IsPotential BV (multiprojPot R V) := fun _ =>
    ProjPotMassPos.isPotential_multiprojPot hH
  have hCont := locDensCont BV (fun _ => multiprojPot R V) hPot
  have hDs := hD K ι P J n R V BV hH
  have hMI : MIntegrable BV (fun _ => multiprojPot R V) (C.indicator fun _ => (1 : ℝ)) := by
    intro i Kc hK hKc
    have hS : IsOpen ((BV.chart i).target ∩ (BV.chart i).symm ⁻¹' C) :=
      (BV.chart i).isOpen_inter_preimage_symm hC
    refine IntegrableOn.congr_fun ((((hCont i).mono hK).integrableOn_compact hKc).indicator
      hS.measurableSet) (fun y hy => ?_) hKc.measurableSet
    by_cases hyC : (BV.chart i).symm y ∈ C
    · rw [Set.indicator_of_mem (show y ∈ (BV.chart i).target ∩ (BV.chart i).symm ⁻¹' C from
        ⟨hK hy, hyC⟩), Set.indicator_of_mem hyC, one_mul]
    · rw [Set.indicator_of_notMem (show y ∉ (BV.chart i).target ∩ (BV.chart i).symm ⁻¹' C from
        fun h => hyC h.2), Set.indicator_of_notMem hyC, zero_mul]
  have hPn : Nonempty (ChartPartition BV) := existsPartition BV
  unfold mInt
  rw [dif_pos hPn]
  unfold integralWith
  set χ := hPn.some
  have hnn : ∀ i, ∀ y ∈ (BV.chart i).target, 0 ≤ χ.χ i ((BV.chart i).symm y) *
      C.indicator (fun _ => (1 : ℝ)) ((BV.chart i).symm y) *
        locDens BV (fun _ => multiprojPot R V) i y := fun i y hy =>
    mul_nonneg (mul_nonneg (χ.nonneg i _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      (hDs i y hy).1
  obtain ⟨j, hj⟩ : ∃ j, 0 < χ.χ j x := by
    by_contra h
    push Not at h
    have h1 := χ.sum_eq_one x
    have h2 : ∑ j, χ.χ j x ≤ 0 := Finset.sum_nonpos fun j _ => h j
    linarith
  refine Finset.sum_pos' (fun i _ => setIntegral_nonneg (BV.chart i).open_target.measurableSet
    (hnn i)) ⟨j, Finset.mem_univ _, ?_⟩
  have hxj : x ∈ (BV.chart j).source := χ.tsupport_subset j (subset_tsupport _ hj.ne')
  set u := BV.chart j x
  have hut : u ∈ (BV.chart j).target := (BV.chart j).map_source hxj
  have hsu : (BV.chart j).symm u = x := (BV.chart j).left_inv hxj
  have hχc : ContinuousAt (fun y => χ.χ j ((BV.chart j).symm y)) u := by
    have h := (χ.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at h
    exact h.continuousAt ((BV.chart j).open_target.mem_nhds hut)
  have hev : ∀ᶠ y in 𝓝 u, y ∈ (BV.chart j).target ∧ 0 < χ.χ j ((BV.chart j).symm y) *
      C.indicator (fun _ => (1 : ℝ)) ((BV.chart j).symm y) *
        locDens BV (fun _ => multiprojPot R V) j y := by
    have hC' : ∀ᶠ y in 𝓝 u, (BV.chart j).symm y ∈ C :=
      ((BV.chart j).continuousAt_symm hut).preimage_mem_nhds (by rw [hsu]; exact hC.mem_nhds hxC)
    have hD' : ∀ᶠ y in 𝓝 u, 0 < locDens BV (fun _ => multiprojPot R V) j y :=
      ((hCont j).continuousAt ((BV.chart j).open_target.mem_nhds hut)).eventually
        (lt_mem_nhds ((hDs j u hut).2 (by rw [hsu]; exact hxF)))
    have hχ' : ∀ᶠ y in 𝓝 u, 0 < χ.χ j ((BV.chart j).symm y) :=
      hχc.eventually (lt_mem_nhds (show 0 < χ.χ j ((BV.chart j).symm u) by rw [hsu]; exact hj))
    filter_upwards [(BV.chart j).open_target.mem_nhds hut, hC', hD', hχ'] with y h1 h2 h3 h4
    refine ⟨h1, mul_pos (mul_pos h4 ?_) h3⟩
    rw [Set.indicator_of_mem h2]
    exact one_pos
  obtain ⟨W, hWs, hWo, huW⟩ := mem_nhds_iff.mp hev
  have hint := integrableOn_weight BV χ (fun _ => multiprojPot R V) _ hMI j
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem (BV.chart j).open_target.measurableSet (hnn j)) hint]
  refine lt_of_lt_of_le (hWo.measure_pos volume ⟨u, huW⟩) (measure_mono fun y hy => ?_)
  exact ⟨(hWs hy).2.ne', (hWs hy).1⟩

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def CurveVertPointChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        (curvePtIdeal y W).IsMaximal ∧
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧
          (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) ∧
        ∀ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k)

def CurveVertPointInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)

def CurveVertPointSurj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ m : Ideal (curveRing y), m.IsMaximal →
        locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0 →
          ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m

def CurveVertPointMultChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        ∀ a b : curveRing y, b ∉ curvePtIdeal y W →
          (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
            multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
              locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a})

def CurveSectionQuotLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ (m : Ideal (curveRing y)) (c : ∀ k, ι k), m.IsPrime → (∀ k, y ⟨k, c k⟩ ≠ 0) →
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) →
        ∀ a b : curveRing y, b ∉ m → (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
          locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) =
            locLen m (curveRing y ⧸ Ideal.span {a})

end

end GroundTheory.Heights₂.Heights.Targets
end


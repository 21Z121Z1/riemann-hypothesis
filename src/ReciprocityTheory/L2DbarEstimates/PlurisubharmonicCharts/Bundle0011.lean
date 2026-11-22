import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0010

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxK
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  {A : WeightedAtlas n Y ι La}

namespace CutData

variable {Sf : Finset Y} (D : CutData A Sf)

theorem dbar_eq_zero (la' : La) (c : Y → ℂ) (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hT : y ∉ ⋃ P ∈ Sf, D.T P) (ξ : Fin n → ℂ) :
    A.dbarAt j (A.F0 la' Sf A.pick D.χ c) y ξ = 0 := by
  classical
  set G : V n → ℂ := fun v => ∑ P ∈ Sf,
    (if y ∈ D.K P then c P * A.g la' j (A.pick P) ((A.chart j).symm v) else 0)
  have hloc : ∀ P ∈ Sf, ∀ᶠ v in 𝓝 (A.chart j y),
      c P * (D.χ P ((A.chart j).symm v) : ℂ) * A.g la' j (A.pick P) ((A.chart j).symm v) =
        (if y ∈ D.K P then c P * A.g la' j (A.pick P) ((A.chart j).symm v) else 0) := by
    intro P hP
    by_cases hK : y ∈ D.K P
    · obtain ⟨u, hu2, rfl⟩ := hK
      have hu1 : u ∈ ball (A.chart (A.pick P) P) (D.r1 P) := by
        by_contra h
        exact hT (mem_biUnion hP ⟨u, ⟨hu2, h⟩, rfl⟩)
      have huT := (D.sub P hP hu2).1
      have hyP : (A.chart (A.pick P)).symm u ∈ (A.chart (A.pick P)).source :=
        (A.chart (A.pick P)).map_target huT
      have hb : A.chart (A.pick P) ((A.chart (A.pick P)).symm u) ∈
          ball (A.chart (A.pick P) P) (D.r1 P) := by rwa [(A.chart (A.pick P)).right_inv huT]
      filter_upwards [D.eventually_χ_one j hj hyP hb] with v hv
      rw [if_pos ⟨u, hu2, rfl⟩, hv.2]; simp
    · filter_upwards [D.eventually_χ_zero hP j hj hK] with v hv
      rw [if_neg hK, hv]; simp
  have hev : (A.F0 la' Sf A.pick D.χ c j ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j y)] G := by
    filter_upwards [(Filter.eventually_all_finset Sf).2 hloc] with v hv
    exact Finset.sum_congr rfl hv
  refine A.dbarAt_eq_zero_of_holo j _ y hev ?_ ξ
  refine DifferentiableAt.fun_sum fun P hP => ?_
  by_cases hK : y ∈ D.K P
  · simp only [if_pos hK]
    have hyP := ((D.K_sub hP) hK).1
    exact ((A.holo_g la' j (A.pick P)).differentiableAt
      ((A.isOpen_ovl j _).mem_nhds (A.mem_ovl hj hyP))).const_mul _
  · simp only [if_neg hK]; exact differentiableAt_const _

end CutData

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalc
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

def jz {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (i : ι)
    (y : Y) : V n →L[ℂ] V n :=
  fderiv ℂ (A.zLoc w0 s i) (A.chart i y)

theorem holo_flat_iff {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (u : Y → ℂ) :
    Holo n (flatStein A hD hF).z (fun y : A.Mset w0 s De => u y) ↔
      ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm)
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by
  constructor
  · intro hH i v hv
    set m : A.Mset w0 s De := ⟨(A.chart i).symm v, hv.2⟩
    have hmi : (m : Y) ∈ (A.chart i).source := (A.chart i).map_target hv.1
    have hcm : A.chart i m = v := (A.chart i).right_inv hv.1
    obtain ⟨e, he, hme⟩ := exists_chart n (flatStein A hD hF).z
      (flatStein A hD hF).isLocalHomeomorph m
    have hfw := fc_chart_fwd A hD e he m hme i hmi
    rw [hcm] at hfw
    have hZ := fc_zLoc_chart A hD e he m hme i hmi
    rw [hcm] at hZ
    have hd1 : DifferentiableAt ℂ ((fun y : A.Mset w0 s De => u y) ∘ e.symm)
        (A.zLoc w0 s i v) := by
      rw [hZ]
      exact (hH e he).differentiableAt (e.open_target.mem_nhds (e.map_source hme))
    have hd2 : DifferentiableAt ℂ (A.zLoc w0 s i) v :=
      ((fc_zLoc_contDiffOn A hD i).differentiableOn (by simp)).differentiableAt
        ((fc_isOpen_O A hD i).mem_nhds hv)
    refine ((hd1.comp v hd2).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hfw] with v' hv'
    simp only [Function.comp_apply]
    rw [hv']
  · intro hd e he w hw
    have hme : e.symm w ∈ e.source := e.map_target hw
    have hem : e (e.symm w) = w := e.right_inv hw
    have hmi : ((e.symm w : A.Mset w0 s De) : Y) ∈ (A.chart (A.pick (e.symm w : Y))).source :=
      A.mem_pick _
    obtain ⟨G, hG, hGx, hGe⟩ := fc_chart_inv A hD hF e he _ hme _ hmi
    rw [hem] at hG hGx hGe
    have hd1 : DifferentiableAt ℂ (u ∘ (A.chart (A.pick (e.symm w : Y))).symm) (G w) := by
      rw [hGx]
      exact (hd _).differentiableAt ((fc_isOpen_O A hD _).mem_nhds (fc_mem_O A _ _ hmi))
    refine ((hd1.comp w (hG.differentiableAt (by simp))).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hGe] with w' hw'
    simp only [Function.comp_apply]
    rw [hw']

theorem lintegral_flat {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (φ : Y → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ y in A.Mset w0 s De, φ y ∂A.mu =
      ∫⁻ x : A.Mset w0 s De, φ x * ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick x) x) /
        ‖(jz A w0 s (A.pick x) x).det‖ ^ 2) ∂vol n (flatStein A hD hF).z := by
  have hMm : MeasurableSet (A.Mset w0 s De) := (isOpen_Mset A hD).measurableSet
  have hz := (flatStein A hD hF).isLocalHomeomorph
  have hρ : Measurable fun m => ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) :=
    ENNReal.measurable_ofReal.comp (fc_rho_continuous A hD hF).measurable
  have hmeas : A.mu.comap Subtype.val =
      (vol n (flatStein A hD hF).z).withDensity fun m => ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) := by
    choose e he hxe using fun x : A.Mset w0 s De => exists_chart n _ hz x
    let U : A.Mset w0 s De → Set (A.Mset w0 s De) := fun x =>
      (e x).source ∩ Subtype.val ⁻¹' (A.chart (A.pick x)).source
    have hUo : ∀ x, IsOpen (U x) := fun x =>
      (e x).open_source.inter ((A.chart _).open_source.preimage continuous_subtype_val)
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
    have huniv : ⋃ t : T, U t = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : x ∈ ⋃ i ∈ T, U i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxe x, A.mem_pick _⟩
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, hxt⟩
    haveI := hTc.to_subtype
    refine Measure.ext_of_iUnion_eq_univ huniv fun t => ?_
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      withDensity_apply _ (hB.inter (hUo t).measurableSet)]
    exact fc_mu_piece A hD hF (e t) (he t) (A.pick (t : Y)) (B ∩ U t)
      (hB.inter (hUo t).measurableSet) (fun m hm => hm.2.1) (fun m hm => hm.2.2)
  rw [← lintegral_subtype_comap hMm, hmeas]
  exact (lintegral_withDensity_eq_lintegral_mul _ hρ (hφ.comp measurable_subtype_coe)).trans
    (lintegral_congr fun x => mul_comm _ _)

end

end ReciprocityTheory.L2DbarEstimates.Y
end


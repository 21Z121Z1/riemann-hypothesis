import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNullB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0614
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionAcrossDenseNonvanishing
section
namespace GlobalTheory.OTY

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y Set
open scoped ENNReal ContDiff

noncomputable section

section L2ExtNz

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {Λ : La} {τ : ι → Y → ℂ}

theorem nz_coeff_ne_iff (hτ : A.IsSec Λ τ) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    τ i y ≠ 0 ↔ y ∈ nz A τ := by
  show τ i y ≠ 0 ↔ τ (A.pick y) y ≠ 0
  rw [hτ.2 (A.pick y) i y trivial (A.mem_pick y) hy]
  have hg := A.g_ne Λ (A.pick y) i y (A.mem_pick y) hy
  constructor
  · intro h; exact mul_ne_zero hg h
  · intro h h0; exact h (by rw [h0, mul_zero])

theorem nz_isOpen_of_isSec (hτ : A.IsSec Λ τ) : IsOpen (nz A τ) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  have hc : ContinuousOn (τ (A.pick y)) (A.chart (A.pick y)).source := by
    simpa using fn_contOn_sec A hτ (A.pick y)
  refine ⟨(A.chart (A.pick y)).source ∩ τ (A.pick y) ⁻¹' {0}ᶜ, ?_,
    hc.isOpen_inter_preimage (A.chart _).open_source isOpen_compl_singleton, ⟨A.mem_pick y, hy⟩⟩
  rintro x ⟨hxs, hx⟩
  exact (nz_coeff_ne_iff A hτ hxs).1 hx

theorem nz_coeff_diff (hτ : A.IsSec Λ τ) (i : ι) :
    DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
  simpa using hτ.1 i

theorem nz_coeff_ne_iff' (hτ : A.IsSec Λ τ) {i : ι} {v : V n} (hv : v ∈ (A.chart i).target) :
    (τ i ∘ (A.chart i).symm) v ≠ 0 ↔ (A.chart i).symm v ∈ nz A τ :=
  nz_coeff_ne_iff A hτ ((A.chart i).map_target hv)

theorem nz_loc (hτ : A.IsSec Λ τ) {la : La} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la (nz A τ) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ nz A τ, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤)
    (i : ι) {v : V n} (hv : v ∈ (A.chart i).target) :
    ∃ r > 0, Metric.ball v r ⊆ (A.chart i).target ∧
      ∫⁻ u in Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0},
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2) < ⊤ := by
  have hMo : IsOpen (nz A τ) := nz_isOpen_of_isSec A hτ
  obtain ⟨U, hU, hfin⟩ := hloc ((A.chart i).symm v)
  obtain ⟨U', hU'U, hU'o, hyU'⟩ := mem_nhds_iff.1 hU
  have hTo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U') :=
    (A.chart i).isOpen_inter_preimage_symm hU'o
  obtain ⟨r0, hr0, hB0⟩ := Metric.isOpen_iff.1 hTo v ⟨hv, hyU'⟩
  have hK : Metric.closedBall v (r0 / 2) ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U' :=
    (Metric.closedBall_subset_ball (by linarith)).trans hB0
  have hqc : ContinuousOn (fun u => Real.exp (A.ph la i ((A.chart i).symm u) -
      A.ph A.kap i ((A.chart i).symm u))) (Metric.closedBall v (r0 / 2)) :=
    (Real.continuous_exp.comp_continuousOn
      ((A.smooth_ph la i).continuousOn.sub (A.smooth_ph A.kap i).continuousOn)).mono
      (hK.trans inter_subset_left)
  obtain ⟨C, hC⟩ := (isCompact_closedBall v (r0 / 2)).exists_bound_of_continuousOn hqc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC v (Metric.mem_closedBall_self (by linarith)))
  have hBt : Metric.ball v (r0 / 2) ⊆ (A.chart i).target :=
    (Metric.ball_subset_closedBall.trans hK).trans inter_subset_left
  refine ⟨r0 / 2, by linarith, hBt, ?_⟩
  have hSm : MeasurableSet ((A.chart i).source ∩ nz A τ ∩ U') :=
    (((A.chart i).open_source.inter hMo).inter hU'o).measurableSet
  have hgc : ContinuousOn (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)))
      ((A.chart i).source ∩ nz A τ ∩ U') :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (((fn_contOn_sec A hFs i).mono inter_subset_left).norm.pow 2 |>.mul
        (Real.continuous_exp.comp_continuousOn
          ((fn_contOn_ph A la i).mono (inter_subset_left.trans inter_subset_left)).neg))
  have hmg : Measurable (((A.chart i).source ∩ nz A τ ∩ U').indicator
      (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)))) := by
    classical
    rw [← Set.piecewise_eq_indicator]
    exact hgc.measurable_piecewise continuousOn_const hSm
  have hmeas : MeasurableSet (Metric.ball v (r0 / 2) \ {u | (τ i ∘ (A.chart i).symm) u = 0}) := by
    have : IsOpen (Metric.ball v (r0 / 2) ∩ (τ i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) :=
      ((nz_coeff_diff A hτ i).continuousOn.mono hBt).isOpen_inter_preimage Metric.isOpen_ball
        isOpen_compl_singleton
    exact this.measurableSet
  calc ∫⁻ u in Metric.ball v (r0 / 2) \ {u | (τ i ∘ (A.chart i).symm) u = 0},
        ENNReal.ofReal (‖F i ((A.chart i).symm u)‖ ^ 2)
      ≤ ∫⁻ u in Metric.ball v (r0 / 2) \ {u | (τ i ∘ (A.chart i).symm) u = 0},
        ENNReal.ofReal C * (fnRho A i u * ((A.chart i).source ∩ nz A τ ∩ U').indicator
          (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) ((A.chart i).symm u)) := by
        refine setLIntegral_mono' hmeas fun u hu => ?_
        have hut : u ∈ (A.chart i).target := hBt hu.1
        have hsu : (A.chart i).symm u ∈ (A.chart i).source := (A.chart i).map_target hut
        have hM : (A.chart i).symm u ∈ nz A τ := (nz_coeff_ne_iff' A hτ hut).1 hu.2
        have hU' : (A.chart i).symm u ∈ U' := (hK (Metric.ball_subset_closedBall hu.1)).2
        have hmem : (A.chart i).symm u ∈ (A.chart i).source ∩ nz A τ ∩ U' := ⟨⟨hsu, hM⟩, hU'⟩
        rw [Set.indicator_of_mem (s := (A.chart i).source ∩ nz A τ ∩ U') hmem]
        unfold fnRho
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hC0]
        apply ENNReal.ofReal_le_ofReal
        have hq := hC u (Metric.ball_subset_closedBall hu.1)
        rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hq
        have e0 : Real.exp (A.ph la i ((A.chart i).symm u) - A.ph A.kap i ((A.chart i).symm u)) *
            Real.exp (A.ph A.kap i ((A.chart i).symm u)) *
            Real.exp (-A.ph la i ((A.chart i).symm u)) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add]; simp
        calc ‖F i ((A.chart i).symm u)‖ ^ 2
            = Real.exp (A.ph la i ((A.chart i).symm u) - A.ph A.kap i ((A.chart i).symm u)) *
              (Real.exp (A.ph A.kap i ((A.chart i).symm u)) *
                (‖F i ((A.chart i).symm u)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm u)))) := by
              linear_combination (-‖F i ((A.chart i).symm u)‖ ^ 2) * e0
          _ ≤ _ := mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ ∫⁻ u in (A.chart i).target,
        ENNReal.ofReal C * (fnRho A i u * ((A.chart i).source ∩ nz A τ ∩ U').indicator
          (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) ((A.chart i).symm u)) :=
        lintegral_mono_set (sdiff_subset.trans hBt)
    _ = ENNReal.ofReal C * ∫⁻ x in (A.chart i).source, ((A.chart i).source ∩ nz A τ ∩ U').indicator
          (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) x ∂A.mu := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, fn_lint A i hmg]
    _ ≤ ENNReal.ofReal C * ∫⁻ x in U ∩ nz A τ, ENNReal.ofReal (A.nsq la F x) ∂A.mu := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc _ ≤ ∫⁻ x, ((A.chart i).source ∩ nz A τ ∩ U').indicator
              (fun x => ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x))) x ∂A.mu :=
              setLIntegral_le_lintegral _ _
          _ = ∫⁻ x in (A.chart i).source ∩ nz A τ ∩ U',
              ENNReal.ofReal (‖F i x‖ ^ 2 * Real.exp (-A.ph la i x)) ∂A.mu := lintegral_indicator hSm _
          _ = ∫⁻ x in (A.chart i).source ∩ nz A τ ∩ U',
              ENNReal.ofReal (A.nsq la F x) ∂A.mu :=
              setLIntegral_congr_fun hSm fun x hx => by rw [fn_nsq_eq A hFs hx.1.1 hx.1.2]
          _ ≤ _ := lintegral_mono_set fun x (hx : x ∈ (A.chart i).source ∩ nz A τ ∩ U') =>
              (⟨hU'U hx.2, hx.1.2⟩ : x ∈ U ∩ nz A τ)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem nz_sub_closure (hτ : A.IsSec Λ τ) (hdense : Dense (nz A τ)) (i : ι) {O : Set (V n)}
    (hO : IsOpen O) (hOt : O ⊆ (A.chart i).target) :
    O ⊆ closure (O ∩ {u | (τ i ∘ (A.chart i).symm) u ≠ 0}) := by
  intro p hp
  rw [_root_.mem_closure_iff]
  intro o ho hpo
  have hWo : IsOpen ((A.chart i).source ∩ A.chart i ⁻¹' (o ∩ O)) :=
    (A.chart i).continuousOn.isOpen_inter_preimage (A.chart i).open_source (ho.inter hO)
  have hpt := hOt hp
  have hmem : (A.chart i).symm p ∈ (A.chart i).source ∩ A.chart i ⁻¹' (o ∩ O) := by
    refine ⟨(A.chart i).map_target hpt, ?_⟩
    show A.chart i ((A.chart i).symm p) ∈ o ∩ O
    rw [(A.chart i).right_inv hpt]; exact ⟨hpo, hp⟩
  obtain ⟨x, hxW, hxM⟩ := hdense.inter_open_nonempty _ hWo ⟨_, hmem⟩
  refine ⟨A.chart i x, hxW.2.1, hxW.2.2, ?_⟩
  show (τ i ∘ (A.chart i).symm) (A.chart i x) ≠ 0
  rw [nz_coeff_ne_iff' A hτ ((A.chart i).map_source hxW.1), (A.chart i).left_inv hxW.1]
  exact hxM

theorem l2_extension_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ la : La) (τ F : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.IsSecOn la (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq la F y) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec la G ∧ ∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y := by
  intro n Y _ _ _ _ _ ι La _ A Λ la τ F hτ hdense hFs hfin
  have hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ nz A τ, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤ :=
    fun y => ⟨univ, univ_mem, by simpa using hfin⟩
  have hex : ∀ i, ∀ v ∈ (A.chart i).target, ∃ r > 0, Metric.ball v r ⊆ (A.chart i).target ∧
      ∃ U : V n → ℂ, DifferentiableOn ℂ U (Metric.ball v r) ∧
        EqOn U (F i ∘ (A.chart i).symm)
          (Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0}) := by
    intro i v hv
    obtain ⟨r, hr, hBt, hfin'⟩ := nz_loc A hτ hFs hloc i hv
    have hu : DifferentiableOn ℂ (F i ∘ (A.chart i).symm)
        (Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0}) :=
      (hFs.1 i).mono fun u (hu : u ∈ Metric.ball v r \ {u | (τ i ∘ (A.chart i).symm) u = 0}) =>
        ⟨hBt hu.1, (nz_coeff_ne_iff' A hτ (hBt hu.1)).1 hu.2⟩
    obtain ⟨U, hU, hUeq⟩ := ReciprocityTheory.L2DbarEstimates.ext n v r (τ i ∘ (A.chart i).symm)
      (F i ∘ (A.chart i).symm) ((nz_coeff_diff A hτ i).mono hBt) hu hfin'
    exact ⟨r, hr, hBt, U, hU, hUeq⟩
  choose! R hR hRt U hU hUeq using hex
  have hagree : ∀ i, ∀ v ∈ (A.chart i).target,
      EqOn (fun u => U i u u) (U i v) (Metric.ball v (R i v)) := by
    intro i v hv u hu
    have hut := hRt i v hv hu
    have hO : IsOpen (Metric.ball v (R i v) ∩ Metric.ball u (R i u)) :=
      Metric.isOpen_ball.inter Metric.isOpen_ball
    have hOt : Metric.ball v (R i v) ∩ Metric.ball u (R i u) ⊆ (A.chart i).target :=
      inter_subset_left.trans (hRt i v hv)
    have key := Set.EqOn.of_subset_closure
      (s := (Metric.ball v (R i v) ∩ Metric.ball u (R i u)) ∩
        {x | (τ i ∘ (A.chart i).symm) x ≠ 0})
      (f := U i v) (g := U i u) ?_ ((hU i v hv).continuousOn.mono inter_subset_left)
      ((hU i u hut).continuousOn.mono inter_subset_right) inter_subset_left
      (nz_sub_closure A hτ hdense i hO hOt)
    · exact (key ⟨hu, Metric.mem_ball_self (hR i u hut)⟩).symm
    · intro x hx
      rw [hUeq i v hv ⟨hx.1.1, hx.2⟩, hUeq i u hut ⟨hx.1.2, hx.2⟩]
  have hGcd : ∀ i, DifferentiableOn ℂ (fun u => U i u u) (A.chart i).target := by
    intro i v hv
    have hev : (fun u => U i u u) =ᶠ[𝓝 v] U i v :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds v (hR i v hv)) (hagree i v hv)
    exact (((hU i v hv).differentiableAt (Metric.ball_mem_nhds v (hR i v hv))).congr_of_eventuallyEq
      hev).differentiableWithinAt
  have hGcF : ∀ i, ∀ v ∈ (A.chart i).target, (A.chart i).symm v ∈ nz A τ →
      U i v v = F i ((A.chart i).symm v) := by
    intro i v hv hM
    exact hUeq i v hv ⟨Metric.mem_ball_self (hR i v hv), (nz_coeff_ne_iff' A hτ hv).2 hM⟩
  have hGF : ∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source →
      U i (A.chart i y) (A.chart i y) = F i y := by
    intro i y hyM hys
    rw [hGcF i _ ((A.chart i).map_source hys) (by rw [(A.chart i).left_inv hys]; exact hyM),
      (A.chart i).left_inv hys]
  refine ⟨fun i y => U i (A.chart i y) (A.chart i y), ⟨fun i => ?_, ?_⟩, hGF⟩
  · refine ((hGcd i).mono inter_subset_left).congr fun u hu => ?_
    simp [(A.chart i).right_inv hu.1]
  · intro i j y _ hyi hyj
    have hcont : ∀ k, ContinuousOn (fun y => U k (A.chart k y) (A.chart k y)) (A.chart k).source :=
      fun k => (hGcd k).continuousOn.comp (A.chart k).continuousOn
        fun x hx => (A.chart k).map_source hx
    have hgc : ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
      refine ((A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono inter_subset_left)
        fun x hx => ?_).congr fun x hx => ?_
      · show A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source
        refine ⟨(A.chart i).map_source hx.1, ?_⟩
        show (A.chart i).symm (A.chart i x) ∈ (A.chart j).source
        rw [(A.chart i).left_inv hx.1]; exact hx.2
      · simp [(A.chart i).left_inv hx.1]
    have hO : IsOpen ((A.chart i).source ∩ (A.chart j).source) :=
      (A.chart i).open_source.inter (A.chart j).open_source
    refine Set.EqOn.of_subset_closure
      (s := ((A.chart i).source ∩ (A.chart j).source) ∩ nz A τ)
      (f := fun y => U i (A.chart i y) (A.chart i y))
      (g := fun y => A.g la i j y * U j (A.chart j y) (A.chart j y)) ?_
      ((hcont i).mono inter_subset_left) (hgc.mul ((hcont j).mono inter_subset_right))
      inter_subset_left (hdense.open_subset_closure_inter hO) ⟨hyi, hyj⟩
    intro x hx
    simp only
    rw [hGF i x hx.2 hx.1.1, hGF j x hx.2 hx.1.2]
    exact hFs.2 i j x hx.2 hx.1.1 hx.1.2

end L2ExtNz

end

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LebesgueSelfdualForDotCharacter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev

theorem isEtLevOver_eq_of_mkQ_eq {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ} {T : Over S}
    {l : D.La → (T ⟶ o.A)} (h : IsEtLevOver o w0 r l) {z z' : D.La}
    (hz : (wSub D w0 r).mkQ z = (wSub D w0 r).mkQ z') : l z = l z' := by
  have hm : z - z' ∈ wSub D w0 r := by
    rw [← Submodule.Quotient.mk_eq_zero]; simpa [sub_eq_zero] using hz
  have := h.1 z' (z - z')
  rw [add_sub_cancel, h.2.2.1 _ hm, _root_.mul_one] at this
  exact this

theorem isEtLevOver_levAct (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T : Over S)
    (l : D.La → (T ⟶ o.A)) (g : LevGrp D w0 r) (h : IsEtLevOver o w0 r l) :
    IsEtLevOver o w0 r (fun y => l (levAct g y)) := by
  have hq := fun {z z' : D.La} (hz : (wSub D w0 r).mkQ z = (wSub D w0 r).mkQ z') =>
    isEtLevOver_eq_of_mkQ_eq h hz
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun gg hgg => ?_⟩⟩
  · rw [← h.1]; apply hq
    simp only [mkQ_levAct, map_add]
  · rw [← h.2.1]; apply hq
    simp only [mkQ_levAct, map_smul]
  · have : levAct g x ∈ wSub D w0 r := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct,
        Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
    exact h.2.2.1 _ this
  · have h1 := (h.2.2.2 k x).1 _ hy
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct] at h1
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    exact (LinearEquiv.map_eq_zero_iff g).1 h1
  · obtain ⟨y, hy⟩ := (h.2.2.2 k x).2 gg hgg
    refine ⟨levAct g.symm y, ?_⟩
    rw [← hy]; congr 1; apply hq
    simp only [mkQ_levAct, LinearEquiv.apply_symm_apply]

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftMulNearOneLuSplitSmallChart
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.LUNear

open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf Metric

theorem lmulC_split_near_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r),
      IsOrth X x → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : X.Ψ → Matrix (Fin r) (Fin r) ℂ,
        (∀ τ a b, ‖m τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε) →
          ∃ z : V (nd X), ‖z‖ < δ ∧ ∃ b ∈ Bor X.Ψ r, X.lmulC m x = rmul (cpt X x z) b := by
  intro E _ _ _ r X x hx δ hδ
  have hdom : x ∈ X.dom := KU.orth_dom X hx
  have hU : IsOpen (cellL X x) :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (Delta_diff (x0 := x)).continuous continuous_const)
  have hxU : x ∈ cellL X x := ⟨hdom, by rw [orthogonalFrame_delta_eq_one hx]; exact one_ne_zero⟩
  have hz0 : zF X x x = 0 := by
    have h := (uniq_all hx (z := 0) (ExtFPf.oneF_mem X)).2.1
    rwa [PoinPf.cpt_zero, ExtFPf.rmul_oneF] at h
  have hzc : ContinuousAt (zF X x) x :=
    ((zF_diffOn (x0 := x)).continuousOn).continuousAt (hU.mem_nhds hxU)
  have hS : {y | y ∈ cellL X x ∧ ‖zF X x y‖ < δ} ∈ 𝓝 x := by
    refine Filter.inter_mem (hU.mem_nhds hxU) ?_
    have : ∀ᶠ y in 𝓝 x, ‖zF X x y‖ < δ :=
      hzc.norm.eventually (Iio_mem_nhds (by show ‖zF X x x‖ < δ; rw [hz0, norm_zero]; exact hδ))
    exact this

  let g : Frame X.Ψ r → Frame X.Ψ r := fun M τ a c => ∑ k, M τ a k * x τ k c
  have hg : Continuous g := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    refine continuous_finset_sum _ fun k _ => ?_
    fun_prop
  have hg1 : g (ExtFPf.oneF X) = x := by
    funext τ a c
    simp [g, ExtFPf.oneF, Matrix.one_apply]
  have hpre : g ⁻¹' {y | y ∈ cellL X x ∧ ‖zF X x y‖ < δ} ∈ 𝓝 (ExtFPf.oneF X) := by
    refine hg.continuousAt.preimage_mem_nhds ?_
    rw [hg1]; exact hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε, hε, fun m hm => ?_⟩
  let M : Frame X.Ψ r := fun τ a c => m τ a c
  have hM : M ∈ ball (ExtFPf.oneF X) ε := by
    rw [mem_ball, dist_pi_lt_iff hε]; intro τ
    rw [dist_pi_lt_iff hε]; intro a
    rw [dist_pi_lt_iff hε]; intro c
    rw [dist_eq_norm]
    exact hm τ a c
  have hgM : X.lmulC m x = g M := by
    funext τ a c
    rfl
  obtain ⟨⟨hyd, hyΔ⟩, hyz⟩ := hball hM
  refine ⟨zF X x (g M), hyz, bF X x (g M), bF_mem hyd hyΔ, ?_⟩
  rw [hgM]
  exact split_eq hx (g M)

end GlobalTheory.LUNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtWeightAddNsmulLargeOnCompact
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.LeviLarge

theorem contDiffAt_ph {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (la : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) :
    ContDiffAt ℝ 2 (A.ph la i ∘ (A.chart i).symm) (A.chart i y) :=
  ((A.smooth_ph la i).contDiffAt
    ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hy))).of_le (WithTop.coe_le_coe.2 le_top)

theorem leviAt_ph_nsmul {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (G H : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source)
    (ξ : Fin n → ℂ) : ∀ k : ℕ,
    A.leviAt i (A.ph (G + k • H) i) y ξ = A.leviAt i (A.ph G i) y ξ + k * A.leviAt i (A.ph H i) y ξ
  | 0 => by simp
  | k + 1 => by
    have e : A.ph (G + (k + 1) • H) i =ᶠ[𝓝 y] fun x => A.ph (G + k • H) i x + A.ph H i x := by
      filter_upwards [(A.chart i).open_source.mem_nhds hy] with x hx
      rw [succ_nsmul, ← add_assoc, A.ph_add _ _ i x hx]
    rw [leviAt_congr A i _ _ y hy e ξ,
      leviAt_add A i _ _ y (contDiffAt_ph A _ i hy) (contDiffAt_ph A _ i hy) ξ,
      leviAt_ph_nsmul A G H i hy ξ k]
    push_cast; ring

theorem re_leviV_lower {n : ℕ} (g : V n → ℂ) (u : V n) (B : ℝ)
    (hFu : ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ ≤ B) (ξ : Fin n → ℂ) :
    -(2 * B) * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n g u ξ).re := by
  have hS0 : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : ∀ j k, ‖ξ j‖ * ‖ξ k‖ ≤ 2 * ∑ j, ‖ξ j‖ ^ 2 := by
    intro j k
    have h1 : ‖ξ j‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : ‖ξ k‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    nlinarith [sq_nonneg (‖ξ j‖ - ‖ξ k‖), norm_nonneg (ξ j), norm_nonneg (ξ k)]
  have hnorm : ‖leviV n g u ξ‖ ≤ ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ * (2 * ∑ j, ‖ξ j‖ ^ 2) := by
    unfold leviV
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
    rw [norm_mul, norm_mul, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hS j k) (norm_nonneg _)
  have h3 : ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ * (2 * ∑ j, ‖ξ j‖ ^ 2) =
      (∑ j, ∑ k, ‖wd n j (wdb n k g) u‖) * (2 * ∑ j, ‖ξ j‖ ^ 2) := by
    rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]
  have h4 := Complex.abs_re_le_norm (leviV n g u ξ)
  have h5 := neg_abs_le (leviV n g u ξ).re
  have h6 := mul_le_mul_of_nonneg_right hFu (by positivity : (0:ℝ) ≤ 2 * ∑ j, ‖ξ j‖ ^ 2)
  linarith

theorem curv_large : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (i : ι) (K : Set (V n)) (t : ℝ), IsCompact K → K ⊆ (A.chart i).target → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ v ∈ K, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt i (A.ph (G + k • H) i) ((A.chart i).symm v) ξ := by
  intro n Y _ _ _ _ _ ι La _ A H G hH i K t hK hKU
  have hU : IsOpen (A.chart i).target := (A.chart i).open_target
  have hsm : ∀ la : La, ContDiffOn ℝ ∞ (fun v => ((A.ph la i ((A.chart i).symm v) : ℝ) : ℂ))
      (A.chart i).target :=
    fun la => Complex.ofRealCLM.contDiff.comp_contDiffOn (A.smooth_ph la i)
  obtain ⟨c, hc, hcK⟩ := levi_pos_compact hU (hsm H) hK hKU (fun u hu ζ hζ => by
    have hyu := (A.chart i).map_target (hKU hu)
    have hne : ζ.ofLp ≠ 0 := by simpa using hζ
    have := hH i _ hyu ζ.ofLp hne
    simpa [WeightedAtlas.leviAt, (A.chart i).right_inv (hKU hu)] using this)
  have hF : ContinuousOn (fun u => ∑ j, ∑ k,
      ‖wd n j (wdb n k (fun v => ((A.ph G i ((A.chart i).symm v) : ℝ) : ℂ))) u‖) K :=
    continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
      ((continuousOn_wd_wdb hU (hsm G) j k).mono hKU).norm
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨⌈(t + 2 * B) / c⌉₊, fun k hk v hv ξ => ?_⟩
  have hy := (A.chart i).map_target (hKU hv)
  rw [leviAt_ph_nsmul A G H i hy ξ k]
  simp only [WeightedAtlas.leviAt, (A.chart i).right_inv (hKU hv)]
  have hFu := (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hB v hv)
  have hG := re_leviV_lower _ v B hFu ξ
  have hc' := hcK v hv (WithLp.toLp 2 ξ)
  rw [EuclideanSpace.norm_sq_eq] at hc'
  simp only [PiLp.toLp_apply, WithLp.ofLp_toLp] at hc'
  have hk' : (t + 2 * B) / c ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hkc : t + 2 * B ≤ k * c := by rwa [div_le_iff₀ hc] at hk'
  have hS0 : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg (α := ℝ) k)
  have h2 := mul_le_mul_of_nonneg_right hkc hS0
  nlinarith

end GlobalTheory.OTY.LeviLarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerEqOneOfCuspidal
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module Matrix

variable {F : Type} [Field F] {r : ℕ}

section Nonvanishing

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

end Nonvanishing

section Embedding

variable {d d' : ℕ}

def incl (F : Type) [Field F] (f : Fin d → Fin r) : Matrix (Fin r) (Fin d) F :=
  (1 : Matrix (Fin r) (Fin r) F).submatrix id f

variable (b : Fin r → ℕ) (c : ℕ)

end Embedding

section Main

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

theorem leviWh_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → leviWh ψ b σ = 1 := by
  first
  | exact @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | (apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one ..)

end Main

end GlobalTheory.FinGL.LeviWh
end
end


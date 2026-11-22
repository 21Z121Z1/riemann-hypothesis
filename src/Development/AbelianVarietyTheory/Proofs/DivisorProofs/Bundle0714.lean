import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0671
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitFormalChartEvSubConstantCoeffDvdStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counit_formalChart_ev_sub_constantCoeff_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  first | exact @GlobalTheory.FrNil.counit_ev_sub_constantCoeff | exact GlobalTheory.FrNil.counit_ev_sub_constantCoeff | (intros; apply GlobalTheory.FrNil.counit_ev_sub_constantCoeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijective
section
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

theorem small_descent_H2_bijective (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull2 := by
  refine GlobalTheory.CatCoh.Desc.pull2_bijective (O κ s) ?_ (IsSmall κ s U) ?_ ?_
  · intro T b
    obtain ⟨T', l, h1, h2, h3, h4⟩ := GlobalTheory.ThickLoc.exists_localization R I κ X s T b
    exact ⟨T', l, by simpa only [mp_O] using h1, by simpa only [mp_O] using h2,
      by simpa only [mp_O] using h3, by simpa only [mp_O] using h4⟩
  · rintro S S' φ ⟨i, hi⟩
    exact ⟨i, Thick.Hom.le_preimage φ hi⟩
  · intro T
    obtain ⟨n, b, hb, h⟩ := exists_finite_small_cover R I κ X s K U hU T
    exact ⟨n, b, hb, fun i S u hu => h i S u (by simpa only [mp_O] using hu)⟩

end GlobalTheory.Cris
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupPeriodClassesSumConst
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem cup_per_sum_const {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {n : ℕ} (p q : Fin n → Λ →+ Hol F.V) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc) (c : GlobalTheory.CatCoh.C1 K.Oc)
    (β : Λ → Λ → Hol F.V)
    (h : (∑ i, GlobalTheory.CatCoh.cup K.Oc (K.perCl (p i)) (K.perCl (q i))) = GlobalTheory.CatCoh.H2.mk K.Oc ℓ)
    (hℓ : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show T''.C from ℓ.1 T T' T'' φ ψ) =
      (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)) :
    ∃ c' : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      GlobalTheory.CatCoh.d1 K.Oc c' T T' T'' φ ψ =
        algebraMap (Hol F.V) (K.Oc.obj T'') (∑ i, p i φ.deg * q i ψ.deg - β φ.deg ψ.deg) := by
  simp only [Charts.perCl, GlobalTheory.CatCoh.cup_mk] at h
  rw [← map_sum, GlobalTheory.CatCoh.H2.mk_eq_mk] at h
  obtain ⟨f, hf⟩ := h
  refine ⟨f + c, fun T T' T'' φ ψ ↦ ?_⟩
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ
  have e2 := hℓ T T' T'' φ ψ
  rw [map_add, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, e]
  rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Submodule.coe_sum]
  simp only [Finset.sum_apply, GlobalTheory.CatCoh.cupZ_apply, Charts.perZ, Charts.mp_Oc] at e2 ⊢
  rw [e2, map_sub, map_sum]
  simp only [AlgHom.commutes, map_mul]
  ring

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureLowerBoundOnCoverBalls
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.CoverCurv

theorem curv_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ t : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, CurvGe C (G + k • H) t := by
  intro n Y _ _ _ _ _ ι La _ A C H G hH t
  have hk : ∀ a : Fin C.m, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ v ∈ Metric.closedBall (C.c a) (C.r a),
      ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤
        A.leviAt (C.idx a) (A.ph (G + k • H) (C.idx a)) ((A.chart (C.idx a)).symm v) ξ :=
    fun a => GlobalTheory.T.leviAt_weight_add_nsmul_large_on_compact n Y ι La A H G hH (C.idx a) _ t
      (isCompact_closedBall (C.c a) (C.r a)) (C.sub a)
  choose k0 hk0 using hk
  refine ⟨Finset.univ.sup k0, fun k hk a v hv ξ => ?_⟩
  exact hk0 a k (le_trans (Finset.le_sup (Finset.mem_univ a)) hk) v
    (Metric.ball_subset_closedBall hv) ξ

end GlobalTheory.OTY.CoverCurv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegularStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k : ℕ, 0 < m → Reg (Nat.card F) m k → IsChar ℂ ℂ (cusp θ m k) ∧ ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  first | (exact @GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (exact GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (intros; apply GlobalTheory.Shin.isChar_cusp_and_norm_of_reg  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyGluedSectionLe
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.GlueEnergy

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] {A : WeightedAtlas n Y ι La}

theorem exists_bound (C : Cover A) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a b j, ∀ v ∈ ball (C.c b) (C.r b),
    ‖wdb n j (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ)) v‖ ≤ B := by
  have h : ∀ p : Fin C.m × Fin C.m × Fin n, ∃ B : ℝ, ∀ v ∈ closedBall (C.c p.2.1) (C.r p.2.1),
      ‖wdb n p.2.2 (fun x => (C.chi p.1 ((A.chart (C.idx p.2.1)).symm x) : ℂ)) v‖ ≤ B := by
    rintro ⟨a, b, j⟩
    apply (isCompact_closedBall _ _).exists_bound_of_continuousOn
    refine ContinuousOn.mono ?_ (C.sub b)
    have h1 : ContDiffOn ℝ ∞ (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ))
        (A.chart (C.idx b)).target :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (C.smooth a (C.idx b))
    have h2 := h1.continuousOn_fderiv_of_isOpen (A.chart (C.idx b)).open_target (by simp)
    unfold wdb
    exact ((h2.clm_apply continuousOn_const).add
      (continuousOn_const.mul (h2.clm_apply continuousOn_const))).div_const _
  choose B hB using h
  refine ⟨∑ p, |B p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun a b j v hv => ?_⟩
  exact ((hB (a, b, j) v (ball_subset_closedBall hv)).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun p => |B p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem wdb_eq_zero (C : Cover A) (a : Fin C.m) (i : ι) (j : Fin n) (v : V n)
    (hv : v ∈ (A.chart i).target)
    (h : (A.chart i).symm v ∉
      (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :
    wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
  have h1 : (A.chart i).symm v ∉ tsupport (C.chi a) := fun h' => h (C.supp a h')
  have h2 := notMem_tsupport_iff_eventuallyEq.mp h1
  have h3 := ((A.chart i).continuousAt_symm hv).eventually h2
  have h4 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => 0 :=
    h3.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]
  unfold wdb
  rw [h4.fderiv_eq]
  simp

theorem sq_sum_le {m : ℕ} (x d : Fin m → ℂ) (B : ℝ) (e : Fin m → ℝ)
    (h : ∀ a, ‖x a * d a‖ ^ 2 ≤ B ^ 2 * e a) :
    ‖∑ a, x a * d a‖ ^ 2 ≤ m * B ^ 2 * ∑ a, e a := by
  calc ‖∑ a, x a * d a‖ ^ 2 ≤ (∑ a, ‖x a * d a‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ m * ∑ a, ‖x a * d a‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖x a * d a‖)
    _ ≤ m * ∑ a, B ^ 2 * e a := by gcongr with a; exact h a
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem energy_glue_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n1 C la (glue C la u) ≤ ENNReal.ofReal K * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨B, hB0, hB⟩ := exists_bound C
  refine ⟨C.m * (n * (C.m * B ^ 2)), by positivity, fun la F0 u hF hu => ?_⟩
  set D : Fin C.m → ι → Y → ℂ := fun a i y =>
    A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y) - F0 i y with hD
  set U : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hU
  have hUo : ∀ a, IsOpen (U a) := fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hbt : ∀ b, ball (C.c b) (C.r b) ⊆ (A.chart (C.idx b)).target := fun b =>
    ball_subset_closedBall.trans (C.sub b)
  set W : Fin C.m → Fin C.m → Set (V n) := fun b a =>
    ball (C.c b) (C.r b) ∩ ((A.chart (C.idx b)).target ∩ (A.chart (C.idx b)).symm ⁻¹' U a) with hW
  have hWo : ∀ b a, IsOpen (W b a) := fun b a =>
    isOpen_ball.inter ((A.chart (C.idx b)).isOpen_inter_preimage_symm (hUo a))
  have hDc : ∀ b a, ContinuousOn (D a (C.idx b) ∘ (A.chart (C.idx b)).symm) (W b a) := by
    intro b a
    have hov : W b a ⊆ ovl A.chart (C.idx b) (C.idx a) := fun v hv => ⟨hv.2.1, hv.2.2.1⟩
    have h1 := (A.holo_g (A.kap + la) (C.idx b) (C.idx a)).continuousOn.mono hov
    have h2 := (A.holo_trans (C.idx b) (C.idx a)).continuousOn.mono hov
    have h3 := (hu a).continuousOn.comp h2 (fun v hv => hv.2.2.2)
    have h4 := (hF.1 (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact (h1.mul h3).sub h4
  have hcomp : ∀ a i y, y ∈ (A.chart i).source → y ∈ (A.chart (C.idx a)).source →
      D a (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D a i y := by
    intro a i y hi ha
    simp only [hD]
    rw [A.g_cocycle _ (A.pick y) i (C.idx a) y (A.mem_pick y) hi ha,
      hF.2 (A.pick y) i y (A.mem_pick y) hi]
    ring
  set f : Fin C.m → Fin C.m → V n → ℝ≥0∞ := fun b a v => ENNReal.ofReal
    (‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2 *
      Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) with hf
  have hk : ∀ b a, ∫⁻ y in (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' W b a,
      ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu = ∫⁻ v in W b a, f b a v := by
    intro b a
    refine GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx b) (W b a) (D a) (hWo b a).measurableSet
      (fun v hv => hv.2.1) (fun y hy hy' => hcomp a _ y hy ?_)
      ((hDc b a).aemeasurable (hWo b a).measurableSet)
    have := hy'.2.2.1
    rwa [(A.chart (C.idx b)).left_inv hy] at this
  have hWaa : ∀ a, W a a = ball (C.c a) (C.r a) := by
    intro a
    refine Set.inter_eq_left.mpr fun v hv => ⟨hbt a hv, (A.chart _).map_target (hbt a hv), ?_⟩
    show A.chart (C.idx a) ((A.chart (C.idx a)).symm v) ∈ ball (C.c a) (C.r a)
    rwa [(A.chart (C.idx a)).right_inv (hbt a hv)]
  have hE : ∀ b a, ∫⁻ v in W b a, f b a v ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro b a
    calc _ = _ := (hk b a).symm
      _ ≤ ∫⁻ y in (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' W a a,
          ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu := by
        apply lintegral_mono_set
        intro y hy
        rw [hWaa]
        have := hy.2.2.2
        rwa [Set.mem_preimage, (A.chart (C.idx b)).left_inv hy.1] at this
      _ = _ := hk a a
      _ = _ := by
        rw [hWaa]
        refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
        have hs := (A.chart (C.idx a)).map_target (hbt a hv)
        have h1 : A.g (A.kap + la) (C.idx a) (C.idx a) ((A.chart (C.idx a)).symm v) = 1 := by
          have h2 := A.g_cocycle (A.kap + la) _ _ _ _ hs hs hs
          have h3 := A.g_ne (A.kap + la) _ _ _ hs hs
          exact (mul_right_eq_self₀.mp h2.symm).resolve_right h3
        simp only [hf, hD]
        rw [h1, one_mul, (A.chart (C.idx a)).right_inv (hbt a hv), norm_sub_rev]
  have hfm : ∀ b a, AEMeasurable ((W b a).indicator (f b a))
      (volume.restrict (ball (C.c b) (C.r b))) := by
    intro b a
    refine AEMeasurable.restrict ?_
    rw [aemeasurable_indicator_iff (hWo b a).measurableSet]
    refine ContinuousOn.aemeasurable ?_ (hWo b a).measurableSet
    have h4 := (A.smooth_ph la (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (((hDc b a).norm.pow 2).mul (Real.continuous_exp.comp_continuousOn h4.neg))
  have hpt : ∀ b, ∀ v ∈ ball (C.c b) (C.r b), ENNReal.ofReal
      ((∑ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) ≤
      ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a, (W b a).indicator (f b a) v := by
    intro b v hv
    set e : Fin C.m → ℝ := fun a => (W b a).indicator
      (fun v => ‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2) v with he
    have he0 : ∀ a, 0 ≤ e a := fun a => Set.indicator_nonneg (fun _ _ => by positivity) _
    have h1 : ∀ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2 ≤
        C.m * B ^ 2 * ∑ a, e a := by
      intro j
      rw [GlobalTheory.T.dbar_glueSectionByPartition_eq n Y ι La A C la u (C.idx b) v (F0 (C.idx b) ((A.chart (C.idx b)).symm v))
        j hu (hbt b hv)]
      apply sq_sum_le
      intro a
      by_cases hm : v ∈ W b a
      · simp only [he, Set.indicator_of_mem hm, hD]
        rw [norm_mul, mul_pow]
        gcongr
        exact hB a b j v hv
      · rw [wdb_eq_zero C a (C.idx b) j v (hbt b hv) (fun h => hm ⟨hv, hbt b hv, h⟩)]
        simp only [zero_mul, norm_zero]
        have := he0 a
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    have h2 : ∑ a, (W b a).indicator (f b a) v = ENNReal.ofReal ((∑ a, e a) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
        (fun a _ => mul_nonneg (he0 a) (Real.exp_pos _).le)]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hm : v ∈ W b a
      · simp only [he, hf, Set.indicator_of_mem hm]
      · simp [he, Set.indicator_of_notMem hm]
    rw [h2, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    apply ENNReal.ofReal_le_ofReal
    gcongr
    calc _ ≤ ∑ _j : Fin n, C.m * B ^ 2 * ∑ a, e a := Finset.sum_le_sum fun j _ => h1 j
      _ = _ := by simp [mul_assoc]
  unfold n1
  calc _ ≤ ∑ _b : Fin C.m, ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a,
        ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
        refine Finset.sum_le_sum fun b _ => ?_
        refine (setLIntegral_mono' measurableSet_ball (hpt b)).trans ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finset_sum' _ (fun a _ => hfm b a)]
        refine mul_le_mul_right (Finset.sum_le_sum fun a _ => ?_) _
        refine le_trans (setLIntegral_le_lintegral _ _) ?_
        rw [lintegral_indicator (hWo b a).measurableSet]
        exact hE b a
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (C.m : ℝ)) (by positivity), ENNReal.ofReal_natCast, mul_assoc]

end GlobalTheory.OTY.GlueEnergy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrameStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame : ∀ (B : Type) [CommRing B] [Algebra ℂ B] (g : ℕ) (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) → (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) → (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) → ∀ k : Fin g → B, (∀ a b, d a (k b) = d b (k a)) → dOne ℂ B (∑ a, k a • ω a) = 0 := by
  first | exact @GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | exact GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | (intros; apply GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrixStatement
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  first | exact @GlobalTheory.SUChartSection.det_secM_eq_one | exact GlobalTheory.SUChartSection.det_secM_eq_one | (intros; apply GlobalTheory.SUChartSection.det_secM_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDiff

theorem restr_inL_inR {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) (i : Fin d) :
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) (fun _ => 0))
        (pderiv R (Sum.inr i) (inL f)) = 0 ∧
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) (fun _ => 0))
        (pderiv R (Sum.inr i) (inR f)) = C (lin f i) := by
  classical
  have hl : ∀ s : Fin d, constantCoeff (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
    fun s => by simp
  have hr : ∀ s : Fin d, constantCoeff (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
    fun s => by simp
  have hρ : HasSubst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) (fun _ : Fin d => 0)) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  constructor
  · unfold inL
    rw [GlobalTheory.T.pderiv_subst_chain_rule _ hl f (Sum.inr i),
      Finset.sum_eq_zero (fun j _ => by rw [pderiv_X_of_ne (by simp), mul_zero]),
      ← substAlgHom_apply hρ, map_zero]
  · unfold inR
    rw [GlobalTheory.T.pderiv_subst_chain_rule _ hr f (Sum.inr i), Finset.sum_eq_single i
      (fun j _ hj => by rw [pderiv_X_of_ne (by simpa using hj), mul_zero]) (by simp),
      pderiv_X_self, mul_one, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hr) hρ]
    have e : (fun s : Fin d => subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R))
        (fun _ : Fin d => 0)) (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) R)) = 0 := by
      funext s; simp [subst_X hρ]
    rw [e, subst_zero_eq_C_constantCoeff, Algebra.algebraMap_self, map_id, RingHom.id_apply,
      ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    simp [lin]

end GlobalTheory.QLogDiff

namespace GlobalTheory.QLogDiff

theorem pderiv_map_eq {R S σ : Type} [CommRing R] [CommRing S] (h : R →+* S)
    (f : MvPowerSeries σ R) (i : σ) : pderiv S i (map h f) = map h (pderiv R i f) := by
  ext n; simp [coeff_pderiv, coeff_map]

theorem in_add {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B}
    {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) : In N (f + g) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  obtain ⟨b, hb, eb⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add, ea, eb, map_add]⟩

theorem coeff_inr_of_unit {B : Type} [CommRing B] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hu : op μ (fun i => (X i : MvPowerSeries (Fin d) B)) (fun _ => 0) = fun i => X i)
    (hc : ∀ i, swap (μ i) = μ i) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr i) 1) (μ j) = if i = j then 1 else 0 := by
  classical
  have hs : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) (fun i : Fin d => X i)) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  have hw : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
      (fun i => X (Sum.inl i))) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  have key : subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) (fun i : Fin d => X i)) (μ j) = X j := by
    have h1 := congrFun hu j
    simp only [op, at2] at h1
    rw [← hc j, swap, at2, subst_comp_subst_apply hw hs]
    have e : (fun s => subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) (fun i : Fin d => X i))
        (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
          (fun i => X (Sum.inl i)) s)) = Sum.elim (fun i => X i) (fun _ => 0) := by
      funext s; cases s <;> simp [subst_X hs]
    rw [e]; exact h1
  have := (GlobalTheory.T.coeff_subst_restrict_sum_variables (μ j)).2 (Finsupp.single i 1)
  rw [key, Finsupp.mapDomain_single] at this
  rw [← this, coeff_X]
  simp [Finsupp.single_left_inj one_ne_zero]

theorem dIn_of_QL : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B),
    IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), QL μ N f → DIn N f := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ N f hf
  classical
  obtain ⟨-, hlin, hcob⟩ := hf
  have hμ0 : ∀ j, constantCoeff (up Q μ j) = 0 := fun j => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ.const j, map_zero]
  have haμ : HasSubst (up Q μ) := hasSubst_of_constantCoeff_zero hμ0
  obtain ⟨ρ, hρe⟩ : ∃ ρ : Fin d ⊕ Fin d → MvPowerSeries (Fin d) Q,
    ρ = Sum.elim (fun j => (X j : MvPowerSeries (Fin d) Q)) (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨ρB, hρBe⟩ : ∃ ρ : Fin d ⊕ Fin d → MvPowerSeries (Fin d) B,
    ρ = Sum.elim (fun j => (X j : MvPowerSeries (Fin d) B)) (fun _ => 0) := ⟨_, rfl⟩
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hρe])
  have hρB : HasSubst ρB := hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hρBe])
  have hmapρ : (fun s => map (algebraMap B Q) (ρB s)) = ρ := by
    funext s; cases s <;> simp [hρe, hρBe]
  have hmapsub : ∀ g : MvPowerSeries (Fin d ⊕ Fin d) B,
      map (algebraMap B Q) (subst ρB g) = subst ρ (map (algebraMap B Q) g) := by
    intro g; rw [map_subst hρB, hmapρ]
  have hunit : ∀ j, subst ρ (up Q μ j) = X j := by
    intro j
    have h1 := congrFun hμ.unit j
    simp only [op, at2] at h1
    rw [← hρBe] at h1
    have h2 := congrArg (map (algebraMap B Q)) h1
    rw [hmapsub, map_X] at h2
    exact h2
  let M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B) :=
    fun j i => subst ρB (pderiv B (Sum.inr i) (μ j))
  have hM : ∀ j i, constantCoeff (M j i) = if j = i then 1 else 0 := by
    intro j i
    have h2 := (GlobalTheory.T.coeff_subst_restrict_sum_variables (R := B) (pderiv B (Sum.inr i) (μ j))).1 0
    rw [← hρBe] at h2
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [M]
    rw [h2, Finsupp.mapDomain_zero, coeff_pderiv, zero_add, coeff_inr_of_unit μ hμ.unit hμ.comm i j]
    simp [eq_comm]
  let g : Fin d → MvPowerSeries (Fin d) Q := fun i => subst ρ (pderiv Q (Sum.inr i) (subst (up Q μ) f))
  have hvg : ∀ i, ∑ j, pderiv Q j f * map (algebraMap B Q) (M j i) = g i := by
    intro i
    simp only [g, M]
    rw [GlobalTheory.T.pderiv_subst_chain_rule (up Q μ) hμ0 f (Sum.inr i), ← substAlgHom_apply hρ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, substAlgHom_apply, substAlgHom_apply, subst_comp_subst_apply haμ hρ, hmapsub]
    have e : (fun s => subst ρ (up Q μ s)) = X := funext hunit
    rw [e, subst_self, id, up, pderiv_map_eq]
  have hg : ∀ i, In N (g i) := by
    intro i
    have hsplit : subst (up Q μ) f = cob1 (up Q μ) f + inL f + inR f := by
      unfold cob1; abel
    have l4 := restr_inL_inR f i
    rw [← hρe] at l4
    simp only [g]
    rw [hsplit, map_add, map_add, ← substAlgHom_apply hρ, map_add, map_add]
    simp only [substAlgHom_apply]
    rw [l4.1, l4.2, add_zero]
    refine in_add ?_ ?_
    · intro α
      have h2 := (GlobalTheory.T.coeff_subst_restrict_sum_variables (R := Q) (pderiv Q (Sum.inr i) (cob1 (up Q μ) f))).1 α
      rw [← hρe] at h2
      rw [h2, coeff_pderiv]
      obtain ⟨b, hb, e⟩ := hcob (Finsupp.mapDomain Sum.inl α + Finsupp.single (Sum.inr i) 1)
      refine ⟨b, hb, ?_⟩
      rw [e, Finsupp.mapDomain_of_notMem_range _ _ (by simp), Nat.cast_zero, zero_add, mul_one]
    · intro α
      obtain ⟨b, hb, e⟩ := hlin i
      by_cases h0 : α = 0
      · exact ⟨b, hb, by rw [h0, coeff_zero_C, e]⟩
      · exact ⟨0, N.zero_mem, by rw [coeff_C, if_neg h0, map_zero]⟩
  have hv := GlobalTheory.T.coeffsInIdeal_solution_of_unipotent_series_matrix N M hM (fun j => pderiv Q j f) g hvg hg
  intro α i
  by_cases hi : α i = 0
  · exact ⟨0, N.zero_mem, by rw [hi, Nat.cast_zero, zero_mul, map_zero]⟩
  · have hle : Finsupp.single i 1 ≤ α := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨b, hb, e⟩ := hv i (α - Finsupp.single i 1)
    refine ⟨b, hb, ?_⟩
    rw [← e, coeff_pderiv, tsub_add_cancel_of_le hle, Finsupp.tsub_apply, Finsupp.single_eq_same,
      mul_comm, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi), Nat.cast_one, sub_add_cancel]

end GlobalTheory.QLogDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualIsConnOfIsEtPDivGroupStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_isConn_of_isEt_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt → G.dual.IsConn := by
  first | exact @GlobalTheory.PDivGroup.dual_isConn_of_isEt | exact GlobalTheory.PDivGroup.dual_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.dual_isConn_of_isEt <;> assumption)
end


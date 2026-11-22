import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEstimateLhsTransfer
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lhs_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ T : ℝ) (θ : ℝ → ℝ) (F0 : U → ℂ), Continuous θ → Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - β i x * GlobalTheory.OTY.TwEst.ext0 U F0 x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖(θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x - F0 x‖ ^ 2 * (wT T (δ * psi A L s x) * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x)))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hqm hpsi δ T θ F0 hθ hF0
  have hm : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hwc : Continuous (wT T) := by
    unfold wT
    refine continuous_const.div (by fun_prop) fun x => ?_
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    linarith
  have hw0 : ∀ x, 0 ≤ wT T x := by
    intro x
    unfold wT
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    positivity
  have key := htr (fun y => (θ (δ * psi A L s y) : ℂ) *
      GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y - GlobalTheory.OTY.TwEst.ext0 U F0 y)
    (fun y => wT T (δ * psi A L s y) * Real.exp (-psi A L s y))
    (((Complex.measurable_ofReal.comp (hθ.measurable.comp hm)).mul hqm).sub hF0)
    ((hwc.measurable.comp hm).mul (Real.measurable_exp.comp hpsi.neg))
    (fun y _ => mul_nonneg (hw0 _) (Real.exp_pos _).le)
  refine Eq.trans ?_ (key.trans ?_)
  · refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
    have h1 : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y
        = GlobalTheory.OTY.TwEst.quot A h β y :=
      GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
    have h2 : (θ (δ * psi A L s y) : ℂ) * h (A.pick y) y
        - β (A.pick y) y * GlobalTheory.OTY.TwEst.ext0 U F0 y
        = β (A.pick y) y * ((θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β y
          - GlobalTheory.OTY.TwEst.ext0 U F0 y) := by
      rw [hq y hy]; ring
    simp only [h1]
    congr 1
    unfold WeightedAtlas.nsq
    simp only [h2, norm_mul, mul_pow]
    ring
  · refine lintegral_congr fun x => ?_
    simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    congr 2
    rw [neg_add, Real.exp_add]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEstimateRhsLeManifold
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.rhs_le_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ δ T : ℝ, ∫⁻ x in {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1}, ENNReal.ofReal (‖GlobalTheory.OTY.TwEst.quot A h β x‖ ^ 2 * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x))) ∂vol n (fun y : U => z y) ≤ ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ T
  set S : Set Y := {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1} with hS
  have hδ : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const hδ).inter (measurableSet_le hδ measurable_const)
  have hw : Measurable (S.indicator fun y => Real.exp (-psi A L s y)) :=
    (Real.measurable_exp.comp hpsi.neg).indicator hSm
  have key := htr _ _ hm hw (fun y _ => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y)
  have hS' : MeasurableSet {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} :=
    measurable_subtype_coe hSm
  rw [← lintegral_indicator hS']
  refine le_trans (le_of_eq ?_) (le_trans key.ge ?_)
  · refine lintegral_congr fun x => ?_
    rw [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    by_cases hx : (x : Y) ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx), ← Real.exp_add]
      congr 3
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx)]
      simp
  · rw [← lintegral_indicator hSm, ← lintegral_indicator hU.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem hy]
      by_cases hx : y ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have h0 := GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
        simp only at h0
        rw [h0]
        apply le_of_eq
        congr 2
        unfold WeightedAtlas.nsq
        rw [hq y hy, norm_mul]
        ring
      · rw [Set.indicator_of_notMem hx]
        simp
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPer

theorem ex_add_lattice {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left} (u : HolUnif A L g) (l : u.Λ) (z : Fin g → ℂ) :
    u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem pre_val_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ U, IsOpen (pre u.ex U)) ∧ (∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U)) ∧ (∀ U (l : u.Λ) (z : Fin g → ℂ), z + l ∈ pre u.ex U ↔ z ∈ pre u.ex U) ∧ (∀ U b (l : u.Λ) (z : Fin g → ℂ), val u.ex U b (z + l) = val u.ex U b z) ∧ (∀ U V, pre u.ex (U ⊓ V) = pre u.ex U ∩ pre u.ex V) ∧ (∀ U V, V ≤ U → pre u.ex V ⊆ pre u.ex U) ∧ (∀ (K : Type) (W : K → A.left.Opens) z, z ∈ pre u.ex (⨆ i, W i) ↔ ∃ i, z ∈ pre u.ex (W i)) ∧ (∀ U z, z ∈ pre u.ex U → ∃ W : A.left.affineOpens, W.1 ≤ U ∧ z ∈ pre u.ex W.1) ∧ (∀ U V (h : V ≤ U) (b : Sec (str A) U), ∀ z ∈ pre u.ex V, val u.ex V (Sec.res (str A) h b) z = val u.ex U b z) ∧ (∀ U, ∀ z ∈ pre u.ex U, ∃ e : Sec (str A) U →ₐ[ℂ] ℂ, ∀ b, val u.ex U b z = e b) ∧ (∀ U b z, z ∈ pre u.ex (A.left.basicOpen b) ↔ val u.ex U b z ≠ 0) ∧ ∀ z, z ∈ pre u.ex ⊤ := by
  intro A _ g L u
  refine ⟨fun U ↦ (u.hol U 0).1, fun U b ↦ (u.hol U b).2, fun U l z ↦ ?_, fun U b l z ↦ ?_, fun U V ↦ ?_,
    fun U V h z hz ↦ top_le_preimage_mono _ h hz, fun K W z ↦ ?_, fun U z hz ↦ ?_,
    fun U V h b z hz ↦ valAt'_map (u.ex z).left (homOfLE h).op b hz, fun U z hz ↦ ?_,
    fun U b z ↦ top_le_preimage_basicOpen_iff _ U b, fun z ↦ le_top (α := (Sp ℂ).Opens)⟩
  · simp only [pre, Set.mem_setOf_eq, ex_add_lattice]
  · simp only [val, ex_add_lattice]
  · ext z
    exact top_le_preimage_inf _ U V
  · refine (top_le_preimage_iff_mem (u.ex z).left _).trans (TopologicalSpace.Opens.mem_iSup.trans ?_)
    exact exists_congr fun i ↦ (top_le_preimage_iff_mem (u.ex z).left _).symm
  · have h1 := (top_le_preimage_iff_mem (u.ex z).left _).1 hz
    obtain ⟨W, hW, h2, h3⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 A.left.isBasis_affineOpens) h1
    exact ⟨⟨W, hW⟩, h3, (top_le_preimage_iff_mem (u.ex z).left _).2 h2⟩
  · refine ⟨{ toRingHom := valAtHom (u.ex z).left U hz, commutes' := fun a ↦ ?_ }, fun b ↦ valAt'_eq_valAtHom _ hz b⟩
    refine (valAt'_eq_valAtHom (u.ex z).left hz _).symm.trans ?_
    refine valAt'_constFn (u.ex z).left (str A) ?_ U a hz
    exact (congrArg _ (Category.comp_id _)).trans (Over.w (u.ex z))

end GlobalTheory.CechPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRules
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPer

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left}

theorem holUnif_ex_left_comp_str (u : HolUnif A L g) (w : Fin g → ℂ) : (u.ex w).left ≫ str A = 𝟙 (Sp ℂ) := by
  have := Over.w (u.ex w)
  simp [str, this]

theorem holUnif_val_algebraMap (u : HolUnif A L g) (U : A.left.Opens) (w : Fin g → ℂ) (hw : w ∈ pre u.ex U) (c : ℂ) :
    val u.ex U (algebraMap ℂ (Sec (str A) U) c) w = c := by
  show valAt' (u.ex w).left U (((str A).appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c
  rw [valAt'_appLE (u.ex w).left (str A) ⊤ U le_top _ hw, holUnif_ex_left_comp_str]
  exact valAt'_id_top c

theorem holUnif_val_mul (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a * b) = fun w => val u.ex U a w * val u.ex U b w :=
  funext fun w => valAt'_mul (u.ex w).left U a b

theorem holUnif_val_add (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a + b) = fun w => val u.ex U a w + val u.ex U b w :=
  funext fun w => valAt'_add (u.ex w).left U a b

theorem holUnif_differentiableAt_val (u : HolUnif A L g) (U : A.left.Opens) (b : Sec (str A) U) {z : Fin g → ℂ}
    (hz : z ∈ pre u.ex U) : DifferentiableAt ℂ (val u.ex U b) z :=
  (u.hol U b).2.differentiableAt (((u.hol U b).1).mem_nhds hz)

theorem exists_isEv (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    ∃ E, IsEv u.ex U z E := by
  let N := (Fin g → ℂ) →L[ℂ] ℂ
  let e : Sec (str A) U →+* ℂ := valAtHom (u.ex z).left U hz
  have he : ∀ a, e a = val u.ex U a z := fun a => (valAt'_eq_valAtHom (u.ex z).left hz a).symm
  letI : Module (Sec (str A) U) N := Module.compHom N e
  haveI : IsScalarTower ℂ (Sec (str A) U) N := ⟨fun c a n => by
    show e (c • a) • n = c • (e a • n)
    rw [Algebra.smul_def, map_mul, mul_smul, he (algebraMap ℂ _ c), holUnif_val_algebraMap u U z hz]⟩
  have hc : ∀ (c : ℂ) (b : Sec (str A) U), val u.ex U (c • b) =ᶠ[nhds z] fun w => c * val u.ex U b w := by
    intro c b
    filter_upwards [((u.hol U b).1).mem_nhds hz] with w hw
    rw [Algebra.smul_def, holUnif_val_mul]
    exact congrArg (· * val u.ex U b w) (holUnif_val_algebraMap u U w hw c)
  let Dl : Sec (str A) U →ₗ[ℂ] N :=
    { toFun := fun b => fderiv ℂ (val u.ex U b) z
      map_add' := fun a b =>
        (congrArg (fun f => fderiv ℂ f z) (holUnif_val_add u U a b)).trans
          (fderiv_add (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz))
      map_smul' := fun c b =>
        (hc c b).fderiv_eq.trans (fderiv_const_mul (holUnif_differentiableAt_val u U b hz) c) }
  let D' : Derivation ℂ (Sec (str A) U) N :=
    { Dl with
      map_one_eq_zero' := by
        show fderiv ℂ (val u.ex U 1) z = 0
        have h1 : val u.ex U (1 : Sec (str A) U) =ᶠ[nhds z] fun _ => (1 : ℂ) := by
          filter_upwards [((u.hol U 1).1).mem_nhds hz] with w hw
          exact valAt'_one (u.ex w).left hw
        exact h1.fderiv_eq.trans (fderiv_const_apply 1)
      leibniz' := fun a b => by
        show fderiv ℂ (val u.ex U (a * b)) z = e a • fderiv ℂ (val u.ex U b) z + e b • fderiv ℂ (val u.ex U a) z
        rw [he, he]
        exact (congrArg (fun f => fderiv ℂ f z) (holUnif_val_mul u U a b)).trans
          (fderiv_mul (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz)) }
  refine ⟨D'.liftKaehlerDifferential.restrictScalars ℂ, fun a b => ?_⟩
  show D'.liftKaehlerDifferential (a • KaehlerDifferential.D ℂ (Sec (str A) U) b) = _
  rw [LinearMap.map_smul, Derivation.liftKaehlerDifferential_comp_D]
  show e a • fderiv ℂ (val u.ex U b) z = _
  rw [he]

theorem isEv_evForm (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    IsEv u.ex U z (evForm u.ex U z) := by
  have h := exists_isEv u U hz
  rw [evForm, dif_pos h]
  exact h.choose_spec

theorem evForm_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens),
    ∀ z ∈ pre u.ex U, IsEv u.ex U z (evForm u.ex U z) ∧
      (∀ (a : Sec (str A) U) ξ, evForm u.ex U z (a • ξ) = val u.ex U a z • evForm u.ex U z ξ) ∧
      ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
  intro A _ g L u U z hz
  have hE := isEv_evForm u U hz
  have hone : val u.ex U (1 : Sec (str A) U) z = 1 := valAt'_one (u.ex z).left hz
  have hD : ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
    intro b
    have := hE 1 b
    rwa [one_smul, hone, one_smul] at this
  refine ⟨hE, fun a ξ => ?_, hD⟩
  have hspan := KaehlerDifferential.span_range_derivation ℂ (Sec (str A) U)
  have hξ : ξ ∈ Submodule.span (Sec (str A) U) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U))) := by
    rw [hspan]; exact Submodule.mem_top
  revert a
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    intro a
    rw [hE a b, hD]
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | smul s x _ hx =>
    intro a
    rw [smul_smul, hx, hx, smul_smul, holUnif_val_mul]

end GlobalTheory.CechPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivDiagIm
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem yF_expand {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (w : V (nd X)) (τ : X.Ψ) (k j : Fin r) :
    yF X w τ k j = (∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m j) + gsB X w τ k j := by
  simp only [yF, yM, Matrix.mul_apply, mat, Matrix.of_apply]
  have hk : gsB X w τ k j = ∑ m, if k = m then gsB X w τ m j else 0 := by simp
  rw [Finset.sum_filter, hk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases lt_trichotomy m k with h | h | h
  · simp [h, h.ne']
  · subst h; simp [nmat]
  · have h1 : ¬ m < k := not_lt.2 h.le
    have h2 : k ≠ m := h.ne
    simp [nmat, h1, h2]

theorem diagreal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (_hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    (dY X z τ a a).im = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  have hY : ∀ k j : Fin r, DifferentiableAt ℝ (fun w => yF X w τ k j) 0 := by
    intro k j
    exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hd τ) k) j
  have hN : ∀ k m : Fin r, DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ k m) 0 := fun k m =>
    ((PoinPf.diff_nmat X τ k m) 0).restrictScalars ℝ
  have hB : ∀ n : ℕ, ∀ k : Fin r, k.val = n → DifferentiableAt ℝ (fun w => gsB X w τ k a) 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk
      have hrepr : (fun w => gsB X w τ k a) = fun w => yF X w τ k a -
          ∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m a := by
        funext w; rw [yF_expand]; ring
      rw [hrepr]
      refine (hY k a).sub (DifferentiableAt.fun_sum fun m hm => (hN k m).mul (ih m.val ?_ m rfl))
      have := (Finset.mem_filter.1 hm).2
      rw [Fin.lt_def] at this
      omega
  have hN0 : ∀ m : Fin r, m < a → nmat X 0 τ a m = 0 := by
    intro m hm
    have := congrFun (congrFun (PoinPf.nmat_zero X τ) a) m
    simp only [mat, Matrix.of_apply, Matrix.one_apply, hm.ne', if_false] at this
    exact this
  have hB0 : ∀ m : Fin r, m < a → gsB X 0 τ m a = 0 := by
    intro m hm
    rw [gsB_zero, Matrix.one_apply, if_neg hm.ne]
  have hsum : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    have h : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
        (∑ m ∈ Finset.univ.filter (· < a), (nmat X 0 τ a m • fderiv ℝ (fun w => gsB X w τ m a) 0 +
          gsB X 0 τ m a • fderiv ℝ (fun w : V (nd X) => nmat X w τ a m) 0)) 0 :=
      HasFDerivAt.fun_sum (fun m _ => (hN a m).hasFDerivAt.mul (hB m.val m rfl).hasFDerivAt)
    convert h using 1
    symm
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' := (Finset.mem_filter.1 hm).2
    rw [hN0 m hm', hB0 m hm', zero_smul, zero_smul, add_zero]
  have him : HasFDerivAt (fun w => (yF X w τ a a).im) (0 : V (nd X) →L[ℝ] ℝ) 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) hsum
    rw [ContinuousLinearMap.comp_zero] at h
    have hf : (fun w => (yF X w τ a a).im) =
        ⇑Complex.imCLM ∘ fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a := by
      funext w
      simp only [Function.comp_apply, Complex.imCLM_apply]
      rw [yF_expand, Complex.add_im, gsB_diag, Complex.ofReal_im, add_zero]
    rw [hf]; exact h
  let L : (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : HasFDerivAt (fun w => (yF X w τ a a).im) (Complex.imCLM.comp (L.comp (dY X))) 0 :=
    Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) (L.hasFDerivAt.comp (0 : V (nd X)) hd.hasFDerivAt)
  have := congrArg (fun L => L z) (hc.unique him)
  simpa [L] using this

end GlobalTheory.SUChartSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivSkew
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem yF_gram_entry (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {R : ℝ}
    (hR : ∀ w ∈ Metric.ball (0 : V (nd X)) R, cpt X x w ∈ X.dom) {w : V (nd X)}
    (hw : w ∈ Metric.ball (0 : V (nd X)) R) (τ : X.Ψ) (a b : Fin r) :
    ∑ k, yF X w τ k a * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) * conj (yF X w τ k b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
  have h1 := FrameDegreeData.ortho_bOf X (hR w hw) τ
  rw [bOf_cpt X hx w] at h1
  have h2 : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [h2, FrameDegreeData.gram_mul, hx τ] at h1
  have h3 := congrFun (congrFun h1 a) b
  rw [Matrix.mul_apply] at h3
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply] at h3
  rw [← h3]
  rfl

theorem dY_skew (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    dY X z τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (dY X z τ a b) = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  obtain ⟨R, hR, hdom⟩ := exists_ball X hx
  set ε : Fin r → ℂ := fun k => ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) with hε
  have hY : HasFDerivAt (yF X) (dY X) 0 := hd.hasFDerivAt
  let P : Fin r → Fin r → (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ := fun k c =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) c).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) k).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : ∀ k c, HasFDerivAt (fun w => yF X w τ k c) ((P k c).comp (dY X)) 0 :=
    fun k c => (P k c).hasFDerivAt.comp 0 hY
  have hcc : ∀ k c, HasFDerivAt (fun w => conj (yF X w τ k c))
      ((Complex.conjCLE.toContinuousLinearMap).comp ((P k c).comp (dY X))) 0 :=
    fun k c => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp 0 (hc k c)
  have hf := HasFDerivAt.sum (u := Finset.univ) fun k _ => ((hc k a).mul_const (ε k)).mul (hcc k b)
  have hconst : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b))
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    refine (hasFDerivAt_const (if a = b then ε a else 0) (0 : V (nd X))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with w hw
    exact yF_gram_entry X hx hdom hw τ a b
  have hf' : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b)) _ 0 :=
    hf.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [Finset.sum_apply])
  have key := congrArg (fun L => L z) (hf'.unique hconst)
  have h0 : ∀ k c, yF X 0 τ k c = if k = c then 1 else 0 := by
    intro k c
    show yM X 0 τ k c = _
    rw [yM_zero, Matrix.one_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, h0] at key
  simp only [ite_mul, one_mul, zero_mul, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_smul, zero_smul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, P, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at key
  linear_combination key

end GlobalTheory.SUChartSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedL2EstimateTwistedSections
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.cutoff_quot_wint_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ : ℝ) (θ : ℝ → ℝ), Continuous θ → (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) → wint n (fun y : U => z y) (fun x : U => (θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x) (fun x : U => GlobalTheory.OTY.TwEst.wt A E β z x) ≤ ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ θ hθ hθ1
  have hma : Measurable (fun y : Y => (θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y) :=
    (Complex.measurable_ofReal.comp (hθ.measurable.comp (hpsi.const_mul δ))).mul hm
  have key := htr _ (fun _ => 1) hma measurable_const (fun _ _ => zero_le_one)
  simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe, one_mul, mul_one] at key
  unfold wint
  rw [← key]
  refine le_trans (setLIntegral_mono' hU.measurableSet ?_) (setLIntegral_le_lintegral U _)
  intro y hy
  apply ENNReal.ofReal_le_ofReal
  have e : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y = GlobalTheory.OTY.TwEst.quot A h β y :=
    GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
  rw [e]
  unfold WeightedAtlas.nsq
  rw [hq y hy, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hθ1 _).1]
  obtain ⟨h0, h1⟩ := hθ1 (δ * psi A L s y)
  have h2 : θ (δ * psi A L s y) ^ 2 ≤ 1 := by nlinarith
  set t := θ (δ * psi A L s y)
  set b := ‖β (A.pick y) y‖
  set q := ‖GlobalTheory.OTY.TwEst.quot A h β y‖
  generalize hc : Real.exp _ = c
  have hc0 : 0 ≤ c := hc ▸ (Real.exp_pos _).le
  have h3 : 0 ≤ (b * q) ^ 2 * c := by positivity
  calc b ^ 2 * c * (t * q) ^ 2 = t ^ 2 * ((b * q) ^ 2 * c) := by ring
    _ ≤ 1 * ((b * q) ^ 2 * c) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := one_mul _
end


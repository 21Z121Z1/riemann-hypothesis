import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericLevelOfFrameBlockAndCharacterStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericLevelOfFrame_block_and_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), IsGenericLevel ψ ϖ P → ((∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J → ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧ (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb → IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J, (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧ ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J, (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) := by
  first | exact @GlobalTheory.GenericShape.generic_shape | exact GlobalTheory.GenericShape.generic_shape | (intros; apply GlobalTheory.GenericShape.generic_shape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarCompactOpenRatioEqZpowOfTopNilpotentStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_compactOpen_ratio_eq_zpow_of_topNilpotent : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ), q.Prime → (∀ u : G, ∀ U ∈ 𝓝 (1 : G), ∃ m : ℕ, u ^ (q ^ m) ∈ U) → ∀ H₁ H₂ : Subgroup G, IsCO H₁ → IsCO H₂ → ∃ z : ℤ, (μ H₁).toReal / (μ H₂).toReal = (q : ℝ) ^ z := by
  first | exact @GlobalTheory.VolPow.vol_div_eq_zpow | exact GlobalTheory.VolPow.vol_div_eq_zpow | (intros; apply GlobalTheory.VolPow.vol_div_eq_zpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMeasurePiChangeConstantStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_pi_change_constant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι] (ν νs : Measure k) (d : ι → kˣ), ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ F : (ι → k) → ℂ, ∫ e, F e ∂(Measure.pi fun _ => ν) = C * ∫ e, F (fun i => (d i : k) * e i) ∂(Measure.pi fun _ => νs) := by
  first | exact @GlobalTheory.IdealChain.integral_scale_change_haar | exact GlobalTheory.IdealChain.integral_scale_change_haar | (intros; apply GlobalTheory.IdealChain.integral_scale_change_haar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermFormEqOfImEqOnSpanningLattice
section
namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable def hermFormImPullback {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm (h y) (h w)).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul])

theorem hermForm_eq_of_im_eq_on_spanning_lattice :
    ∀ {g : ℕ} {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)), Submodule.span ℝ (Set.range P) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (h h' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h (P a)) (h (P b))).im = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' (P a)) (h' (P b))).im) → ∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y) := by
  intro g L _ P hsp Hm h h' hab
  have hB : hermFormImPullback Hm h = hermFormImPullback Hm h' := by
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨a, rfl⟩
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨b, rfl⟩
    exact hab a b
  have him : ∀ x y, (hermForm Hm (h x) (h y)).im = (hermForm Hm (h' x) (h' y)).im := by
    intro x y
    exact LinearMap.congr_fun₂ hB x y
  intro x y
  have hI : ∀ (k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (hermForm Hm (k (Complex.I • x)) (k y)).im = (hermForm Hm (k x) (k y)).re := by
    intro k
    simp [hermForm, map_smul, smul_dotProduct]
  apply Complex.ext
  · rw [← hI h, ← hI h']
    exact him _ _
  · exact him x y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTranslateIndicator
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.StepAvg

open MeasureTheory ValuativeRel Matrix Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
private lemma measurableSet_Cgrp_of_isCO {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J) (h : GL (n ⊕ Fin c) k) :
    MeasurableSet (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
  have hJ' : IsOpen (J : Set (GL (n ⊕ Fin c) k)) ∧ IsCompact (J : Set (GL (n ⊕ Fin c) k)) := hJ
  have hset : (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)) =
      (_root_.GlobalTheory.RootEx.R k n c 1 : Set (GL (n ⊕ Fin c) k)) ∩
        (fun x => h⁻¹ * x * h) ⁻¹' (J : Set (GL (n ⊕ Fin c) k)) := by
    ext x
    exact _root_.GlobalTheory.StepData.mem_Cgrp
  have hopen : IsOpen ((fun x : GL (n ⊕ Fin c) k => h⁻¹ * x * h) ⁻¹' (J : Set (GL (n ⊕ Fin c) k))) :=
    hJ'.1.preimage (by fun_prop)
  rw [hset]
  exact (_root_.GlobalTheory.RootEx.VolN.isClosed_R 1).measurableSet.inter hopen.measurableSet

open MeasureTheory ValuativeRel Matrix Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
private lemma integral_indicator_embed_mul_unipotent_lemma (ν : Measure k) [ν.IsAddHaarMeasure]
    {J : Subgroup (GL (n ⊕ Fin c) k)} (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J) (h : GL (n ⊕ Fin c) k)
    (x : GL n k) :
    ∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
        (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
          (_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k))
        ∂(_root_.GlobalTheory.RootEx.volN ν n c 1) =
      (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h) : Set (GL n k)).indicator
        (fun _ => (((_root_.GlobalTheory.RootEx.volN ν n c 1)
          ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal
            : ℂ)) x := by
  haveI := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN (c := c) (n := n) ν 1
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set E := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  by_cases hx : x ∈ _root_.GlobalTheory.StepData.prX C
  · obtain ⟨u₁, hu₁N, hu₁C⟩ := _root_.GlobalTheory.StepData.mem_prX.mp hx
    let w : _root_.GlobalTheory.RootEx.N k n c 1 :=
      ⟨E x⁻¹ * u₁⁻¹ * (E x⁻¹)⁻¹, _root_.GlobalTheory.RootEx.Radical.conj_mem x⁻¹
        (Subgroup.inv_mem _ hu₁N)⟩
    have key : ∀ u : _root_.GlobalTheory.RootEx.N k n c 1,
        (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (E x * (u : GL (n ⊕ Fin c) k)) =
          ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
            Set (_root_.GlobalTheory.RootEx.N k n c 1))).indicator (fun _ => (1 : ℂ)) (w * u) := by
      intro u
      have hwu : ((w * u : _root_.GlobalTheory.RootEx.N k n c 1) : GL (n ⊕ Fin c) k) =
          (u₁ * E x)⁻¹ * (E x * u) := by
        simp only [w, Subgroup.coe_mul, map_inv, inv_inv, _root_.mul_inv_rev, mul_assoc]
      have hiff : E x * (u : GL (n ⊕ Fin c) k) ∈ C ↔
          w * u ∈ C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) := by
        rw [Subgroup.mem_subgroupOf, hwu, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hu₁C)]
      by_cases hu : E x * (u : GL (n ⊕ Fin c) k) ∈ C
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show w * u ∈ _ from hiff.mp hu)]
      · rw [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show w * u ∉ ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
            Set (_root_.GlobalTheory.RootEx.N k n c 1))) from fun h' => hu (hiff.mpr h'))]
    have hmeas : MeasurableSet ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
        Set (_root_.GlobalTheory.RootEx.N k n c 1))) :=
      measurable_subtype_coe (measurableSet_Cgrp_of_isCO hJ h)
    simp_rw [key]
    rw [integral_mul_left_eq_self (fun u => ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
        Set (_root_.GlobalTheory.RootEx.N k n c 1))).indicator (fun _ => (1 : ℂ)) u) w,
      integral_indicator_const _ hmeas, Set.indicator_of_mem hx, measureReal_def, Complex.real_smul,
      mul_one]
  · rw [Set.indicator_of_notMem hx]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
    refine Set.indicator_of_notMem (fun hu => hx ?_) _
    refine _root_.GlobalTheory.StepData.mem_prX.mpr ⟨E x * u * (E x)⁻¹,
      _root_.GlobalTheory.RootEx.Radical.conj_mem x u.2, ?_⟩
    convert hu using 1
    simp [E]

open MeasureTheory ValuativeRel Matrix Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in

theorem _root_.GlobalTheory.StepAvg.integral_translate_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c → ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J → ∀ (h : GL (n ⊕ Fin c) k), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h)) → ∀ (m : Measure (GL n k)) [m.IsHaarMeasure], ∀ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : _root_.GlobalTheory.RootEx.N k n c 1, (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * _root_.GlobalTheory.RootEx.embX c g₀)) ∂(_root_.GlobalTheory.RootEx.volN ν n c 1)) ∂m = ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ * ((_root_.GlobalTheory.RootEx.volN ν n c 1 ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal * (m (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h))).toReal) : ℝ) : ℂ) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c hc J hJ h hpr m _ u₀ hu₀ g₀
  haveI := _root_.GlobalTheory.RootEx.VolN.isMulRightInvariant_volN (c := c) (n := n) ν 1
  haveI := _root_.GlobalTheory.SplitFlip.isMulRightInvariant_of_haar (k := k) m
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set E := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  set V : ℂ := (((_root_.GlobalTheory.RootEx.volN ν n c 1)
    (C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal : ℂ)
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) =
      (_root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← _root_.GlobalTheory.SplitWeil.nabs_mul, ← map_mul, inv_mul_cancel, map_one,
      _root_.GlobalTheory.SplitWeil.nabs_one]
  have hpos := _root_.GlobalTheory.SplitWeil.nabs_pos k (Matrix.GeneralLinearGroup.det g₀)
  have ha0 : _root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) ^
      (-((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ))) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ := by
    rw [hinv, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv,
      show ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) = (((c : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast]
    rfl
  have inner : ∀ g : GL n k,
      ∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
          (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
            (E g * (u : GL (n ⊕ Fin c) k) * (u₀ * E g₀)) ∂(_root_.GlobalTheory.RootEx.volN ν n c 1) =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ •
          (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator (fun _ => V) (g * g₀) := by
    intro g
    have e1 : ∀ u : _root_.GlobalTheory.RootEx.N k n c 1,
        E g * (u : GL (n ⊕ Fin c) k) * (u₀ * E g₀) =
          E (g * g₀) * (E g₀⁻¹ * ((u * ⟨u₀, hu₀⟩ : _root_.GlobalTheory.RootEx.N k n c 1) :
            GL (n ⊕ Fin c) k) * (E g₀⁻¹)⁻¹) := by
      intro u
      simp only [map_mul, map_inv, inv_inv, Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]
    simp_rw [e1]
    rw [integral_mul_right_eq_self (fun u : _root_.GlobalTheory.RootEx.N k n c 1 =>
        (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
          (E (g * g₀) * (E g₀⁻¹ * (u : GL (n ⊕ Fin c) k) * (E g₀⁻¹)⁻¹))) ⟨u₀, hu₀⟩,
      _root_.GlobalTheory.RootEx.VolN.integral_conj_volN ν le_rfl hc g₀⁻¹
        (fun y => (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (E (g * g₀) * y)),
      integral_indicator_embed_mul_unipotent_lemma ν hJ h (g * g₀), ha0]
    all_goals simp only [C, V]
  have hpr' : IsOpen (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) ∧
      IsCompact (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) := hpr
  have hborel := (_root_.GlobalTheory.SplitWeil.volGL_haar k n ν).1
  have hmeas : MeasurableSet (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) := hpr'.1.measurableSet

  simp_rw [inner]
  rw [integral_smul, integral_mul_right_eq_self (fun g : GL n k =>
      (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator (fun _ => V) g) g₀,
    integral_indicator_const _ hmeas, measureReal_def]
  simp only [V, Complex.real_smul]
  push_cast
  ring

end GlobalTheory.StepAvg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCOPrXCgrp
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.PrCompactOpen

theorem eq_one_of_isCompact {G : Type} [Group G] [TopologicalSpace G] (f : G → ℝ)
    (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x * f y) (hp : ∀ x, 0 < f x)
    {P : Subgroup G} (hP : IsCompact (P : Set G)) {g : G} (hg : g ∈ P) : f g = 1 := by
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [mul_one, ← hm, one_mul]
    exact mul_left_cancel₀ (hp 1).ne' e
  have hpow : ∀ x : G, ∀ m : ℕ, f (x ^ m) = f x ^ m := by
    intro x m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih, pow_succ]
  obtain ⟨B, hB⟩ := (hP.image hc).bddAbove
  have hle : ∀ x ∈ P, f x ≤ 1 := by
    intro x hx
    by_contra hlt
    have hlt := not_le.mp hlt
    obtain ⟨m, hm'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop B).exists
    have : f (x ^ m) ≤ B := hB ⟨x ^ m, P.pow_mem hx m, rfl⟩
    rw [hpow] at this
    linarith
  have hprod : f g * f g⁻¹ = 1 := by rw [← hm, mul_inv_cancel, h1]
  have a := hle g hg
  have b := hle g⁻¹ (P.inv_mem hg)
  nlinarith [mul_le_mul_of_nonneg_left b (hp g).le, hp g⁻¹]

theorem isCO_prX_Cgrp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : IsCO J) (h : GL (n ⊕ Fin c) k) :
    IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h),
      valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  have := GlobalTheory.SplitWeil.t2Space k
  have key : ∀ F : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k, Continuous (fun x => (F x).val) →
      IsClosed {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} := by
    intro F hF
    have e : {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} = ⋂ r, ⋂ s, {x | lev 1 s ≤ lev 1 r →
        (r.isRight ∨ s.isRight) → (F x).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, GlobalTheory.RootEx.VolN.InR]
    rw [e]
    exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_imp isOpen_const
      (isClosed_imp isOpen_const (isClosed_eq (hF.matrix_elem r s) continuous_const))
  have hRcl : IsClosed (R k n c 1 : Set (GL (n ⊕ Fin c) k)) := by
    have e : (R k n c 1 : Set (GL (n ⊕ Fin c) k)) =
        {x | GlobalTheory.RootEx.VolN.InR 1 (id x)} ∩ {x | GlobalTheory.RootEx.VolN.InR 1 x⁻¹} := by
      ext x
      exact GlobalTheory.RootEx.VolN.mem_R_iff
    rw [e]
    exact (key id Units.continuous_val).inter (key (fun x => x⁻¹) Units.continuous_coe_inv)
  have hconj : {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} = (fun y => h * y * h⁻¹) '' (J : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨h⁻¹ * x * h, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      show h⁻¹ * (h * y * h⁻¹) * h ∈ J
      have e : h⁻¹ * (h * y * h⁻¹) * h = y := by group
      rw [e]
      exact hy
  have hCset : (Cgrp J h : Set (GL (n ⊕ Fin c) k)) =
      {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} ∩ (R k n c 1 : Set _) := by
    ext x
    exact GlobalTheory.StepData.mem_Cgrp.trans and_comm
  have hCc : IsCompact (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    rw [hCset, hconj]
    exact (hJ.2.image ((continuous_const.mul continuous_id).mul continuous_const)).inter_right hRcl
  have hOpen : IsOpen (prX (Cgrp J h) : Set (GL n k)) := by
    apply Subgroup.isOpen_of_mem_nhds
    have hV : IsOpen {g : GL n k | h⁻¹ * embX c g * h ∈ J} :=
      hJ.1.preimage ((continuous_const.mul GlobalTheory.QuotInt.continuous_embX).mul continuous_const)
    have h1V : (1 : GL n k) ∈ {g : GL n k | h⁻¹ * embX c g * h ∈ J} := by
      show h⁻¹ * embX c 1 * h ∈ J
      rw [map_one, mul_one, inv_mul_cancel]
      exact J.one_mem
    refine Filter.mem_of_superset (hV.mem_nhds h1V) ?_
    intro g hg
    refine GlobalTheory.StepData.mem_prX.mpr ⟨1, one_mem _, GlobalTheory.StepData.mem_Cgrp.mpr ⟨?_, ?_⟩⟩
    · rw [one_mul]
      exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    · rw [one_mul]
      exact hg
  have hblk : ∀ {A : GL (n ⊕ Fin c) k → Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}, Continuous A →
      Continuous (fun r => (A r).toBlocks₁₁) :=
    fun hA => continuous_pi fun i => continuous_pi fun j => hA.matrix_elem _ _
  have hΦ : Continuous (fun r : GL (n ⊕ Fin c) k =>
      ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
        MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) :=
    (hblk Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hblk Units.continuous_coe_inv))
  have himg : Units.embedProduct (Matrix n n k) '' (prX (Cgrp J h) : Set (GL n k)) =
      (fun r : GL (n ⊕ Fin c) k =>
        ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
          MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) ''
        (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨u, hu, huC⟩ := GlobalTheory.StepData.mem_prX.mp hg
      refine ⟨u * embX c g, huC, ?_⟩
      have hinv : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_right g hu, GlobalTheory.QuotInt.block_left g⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hrR, -⟩ := GlobalTheory.StepData.mem_Cgrp.mp hr
      obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hrR
      refine ⟨x, GlobalTheory.StepData.mem_prX.mpr ⟨embX c x * u * (embX c x)⁻¹,
        GlobalTheory.RootEx.Radical.conj_mem x hu, by rwa [inv_mul_cancel_right]⟩, ?_⟩
      have hinv : (embX c x * u)⁻¹ = u⁻¹ * embX c x⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_left x hu, GlobalTheory.QuotInt.block_right x⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
  have hcpt : IsCompact (prX (Cgrp J h) : Set (GL n k)) := by
    rw [Units.isEmbedding_embedProduct.isCompact_iff, himg]
    exact hCc.image hΦ
  refine ⟨⟨hOpen, hcpt⟩, fun g hg => ?_⟩
  have hdet : Continuous (fun g : GL n k => Matrix.GeneralLinearGroup.det g) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun g : GL n k => Matrix.GeneralLinearGroup.det g) =
          fun g : GL n k => (g : Matrix n n k).det := by
        funext g
        exact Matrix.GeneralLinearGroup.val_det_apply g
      rw [e]
      exact Units.continuous_val.matrix_det
    · have e : (fun g : GL n k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
          fun g : GL n k => ((g⁻¹ : GL n k) : Matrix n n k).det := by
        funext g
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      rw [e]
      exact Units.continuous_coe_inv.matrix_det
  have h1 := eq_one_of_isCompact (fun g : GL n k => nabs k (Matrix.GeneralLinearGroup.det g))
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).continuous.comp hdet)
    (fun x y => by
      simp only [map_mul]
      exact GlobalTheory.SplitWeil.nabs_mul k _ _)
    (fun x => GlobalTheory.SplitWeil.nabs_pos k _) hcpt hg
  refine ⟨(GlobalTheory.SplitWeil.nabs_eq_one_iff _).mp h1, ?_⟩
  show nabs k (Matrix.GeneralLinearGroup.det g) ^ ((c : ℤ) - 1) = 1
  rw [h1, _root_.one_zpow]

end GlobalTheory.PrCompactOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroupStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isCompact_twoBlockParahoricSubgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) ∧ IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  first | exact @GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric | exact GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric | (intros; apply GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixEntrywiseProductMeasureUniformizerPowerBoxStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [Fintype D] (c : A → D → ℤ),
    volM ν A D {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} =
      ν (𝒪[k] : Set k) ^ (Fintype.card A * Fintype.card D) *
        ENNReal.ofReal ((resCard k : ℝ) ^ (-∑ i, ∑ j, c i j)) := by
  first | exact @GlobalTheory.BoxVolume.volM_box | exact GlobalTheory.BoxVolume.volM_box | (intros; apply GlobalTheory.BoxVolume.volM_box <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMulStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  first | exact @GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | exact GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | (intros; apply GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumnStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_fourierJacobiSubgroup_iff_parabolic_mul_column : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ RFJ k n c ρ ↔ ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β) ∧ ∀ β : n → k, ∀ u ∈ N k n c (ρ + 1), colE c (ρ + 1) β * u * (colE c (ρ + 1) β)⁻¹ ∈ N k n c (ρ + 1) := by
  first | exact @GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff | exact GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff | (intros; apply GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntegralGLOfInParahoricDatumSupportMulBlockDiStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGL_of_inParahoricDatumSupport_mul_blockDiag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (z : Matrix (A ⊕ E) (A ⊕ D) k) (x : GL A k) (y : GL D k),
    InSupp z → InSupp (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)) → x ∈ KO k A := by
  first | exact @GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp | exact GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp | (intros; apply GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntriStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by
  first | exact @GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff | exact GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff | (intros; apply GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff <;> assumption)
end


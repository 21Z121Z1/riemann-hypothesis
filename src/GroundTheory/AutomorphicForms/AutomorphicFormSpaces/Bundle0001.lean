import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraRegularity
import GroundTheory.AutomorphicForms.Bundle0005
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero

-- bundled from GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
section
namespace GroundTheory.Automorphic

open Sobolev Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_kernel_eq_conv_of_aeval_laplacian [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {ι : Type*} [Fintype ι]
    (bL : Module.Basis ι ℝ h.lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic) (hPd : 0 < P.natDegree)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ U ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (h.laplacian bL) P f = 0 →
        ∀ g : G, (f : G → ℂ) g = ∫ y, (f : G → ℂ) (g * y) * κ y ∂μ := by
  let _ := h.chartedSpace
  set b := Module.finBasis ℝ 𝔤
  set d := Module.finrank ℝ 𝔤
  have hfc : ∀ f : h.smoothFuns (F := ℂ), ∀ g : G, Continuous fun y : G => (f : G → ℂ) (g * y) :=
    fun f g => (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous.comp
      (continuous_const.mul continuous_id)
  have hexpc : Continuous fun x : EuclideanSpace ℝ (Fin d) => h.expG (coordEquiv b x) :=
    h.continuous_expG.comp (coordEquiv b).continuous
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_expCoord μ b
  have hV : {x : EuclideanSpace ℝ (Fin d) | h.expG (coordEquiv b x) ∈ U} ∈ 𝓝 0 := by
    refine hexpc.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨ρ₀, hρ₀, hρ₀V⟩ := Metric.mem_nhds_iff.1 hV
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    have hsub : ∀ x y : EuclideanSpace ℝ (Fin d), x = y := by
      intro x y; ext i; exact absurd i.2 (by omega)
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens (fun _ => 1) contDiff_const (fun x _ => by
      rw [hsub x 0]; exact Metric.mem_closedBall_self hε.le)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f _ g => ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hρ₀V (by rw [hsub x 0]; exact Metric.mem_ball_self hρ₀)
    · have := hκ _ (hfc f g)
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [this, integral_euclideanSpace_of_eq_zero hd]
      simp
  ·
    set Q := P ^ (d + 1)
    have hQ : Q.Monic := hP.pow _
    have hQd : Q.natDegree = (d + 1) * P.natDegree := hP.natDegree_pow _
    obtain ⟨δ, hδ, A, a, hA, ha, hell, hop⟩ := h.exists_elliptic_aeval_laplacian bL b Q hQ
    set ρ := min (min δ ε) ρ₀
    have hρ : 0 < ρ := lt_min (lt_min hδ hε) hρ₀
    have hρδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 δ :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
    have hρε : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.closedBall 0 ε :=
      Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _)))
    have hρV : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 ρ₀ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hm1 : 1 ≤ 2 * Q.natDegree := by rw [hQd]; nlinarith
    have hnm : d < 2 * (2 * Q.natDegree) := by rw [hQd]; nlinarith
    obtain ⟨E, β, -, -, hEs, -, hβs, -, hβU, hid⟩ := exists_parametrix hd hm1 hnm Metric.isOpen_ball
      hA (fun α hα => (ha α hα).contDiffOn Metric.isOpen_ball.uniqueDiffOn) hell Metric.isOpen_ball
      (Metric.mem_ball_self hρ) hρδ
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens β hβs (hβU.trans hρε)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f hf g => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hρ₀V (hρV (hβU hx))
    · have hQf : Polynomial.aeval (h.laplacian bL) Q f = 0 := by
        rw [show Q = P ^ d * P from pow_succ P d, map_mul, Module.End.mul_apply, hf, map_zero]
      set ψ := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))
      have hψ : ContDiff ℝ ∞ ψ := h.contDiff_comp_coordEquiv f.2 g b
      have h1 := hid ψ hψ.contDiffOn
      have h0 : ∫ x, E x * diffOp A a ψ x = 0 := by
        rw [← integral_zero (EuclideanSpace ℝ (Fin d)) ℂ]
        congr 1
        funext x
        by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ
        · rw [hop f g x hx, hQf]; simp
        · rw [image_eq_zero_of_notMem_tsupport fun hE => hx (hρδ (hEs hE)), zero_mul]
      rw [h0, eq_comm, sub_eq_zero] at h1
      have hψ0 : ψ 0 = (f : G → ℂ) g := by simp [ψ]
      rw [← hψ0, h1]
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [hκ _ (hfc f g)]

noncomputable def convDeriv (X : 𝔤) (κ : G → ℂ) (y : G) : ℂ :=
  h.rightDeriv X (fun z => κ z⁻¹) y⁻¹

variable {h}

theorem continuous_of_isSmoothFun {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  let _ := h.chartedSpace
  exact ContMDiff.continuous hf

theorem isSmoothFun_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) :
    h.IsSmoothFun (fun z : G => κ z⁻¹) := by
  let _ := h.chartedSpace
  have := h.lieGroup ∞
  exact hκ.comp (contMDiff_inv 𝓘(ℝ, 𝔤) ∞)

theorem continuous_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.rightDeriv X fun z : G => κ z⁻¹) :=
  continuous_of_isSmoothFun (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)

theorem continuous_convDeriv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.convDeriv X κ) :=
  (continuous_rightDeriv_comp_inv hκ X).comp continuous_inv

theorem rightDeriv_eq_zero_of_eventually {f : G → ℂ} {g : G} (hf : ∀ᶠ z in 𝓝 g, f z = 0)
    (X : 𝔤) : h.rightDeriv X f g = 0 := by
  have hc : Continuous fun Y : 𝔤 => g * h.expG Y := continuous_const.mul h.continuous_expG
  have h0 : (fun Y : 𝔤 => f (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have : Tendsto (fun Y : 𝔤 => g * h.expG Y) (𝓝 0) (𝓝 g) := by
      simpa using hc.tendsto (0 : 𝔤)
    exact this.eventually hf
  simp only [rightDeriv, h0.fderiv_eq, fderiv_const_apply]
  rfl

theorem rightDeriv_comp_inv_eq_zero {κ : G → ℂ} {z : G} (hz : z⁻¹ ∉ tsupport κ) (X : 𝔤) :
    h.rightDeriv X (fun w : G => κ w⁻¹) z = 0 := by
  refine rightDeriv_eq_zero_of_eventually ?_ X
  have hopen : IsOpen (tsupport κ)ᶜ := (isClosed_tsupport κ).isOpen_compl
  have ht : Tendsto (fun w : G => w⁻¹) (𝓝 z) (𝓝 z⁻¹) := continuous_inv.tendsto z
  exact (ht.eventually (hopen.mem_nhds hz)).mono fun w hw =>
    (image_eq_zero_of_notMem_tsupport hw : κ w⁻¹ = 0)

theorem support_convDeriv_subset (X : 𝔤) (κ : G → ℂ) :
    Function.support (h.convDeriv X κ) ⊆ tsupport κ := by
  intro y hy
  by_contra hyκ
  exact hy (rightDeriv_comp_inv_eq_zero (by rwa [inv_inv]) X)

theorem hasCompactSupport_convDeriv {κ : G → ℂ} (hκc : HasCompactSupport κ) (X : 𝔤) :
    HasCompactSupport (h.convDeriv X κ) :=
  hκc.mono' (support_convDeriv_subset X κ)

theorem exists_bound_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    (X : 𝔤) : ∃ M, ∀ z, ‖h.rightDeriv X (fun w : G => κ w⁻¹) z‖ ≤ M := by
  have hDcs : HasCompactSupport (h.rightDeriv X fun w : G => κ w⁻¹) := by
    refine HasCompactSupport.intro (hκc.image continuous_inv) fun z hz => ?_
    refine rightDeriv_comp_inv_eq_zero (fun hk => hz ⟨z⁻¹, hk, inv_inv z⟩) X
  exact hDcs.exists_bound_of_continuous (continuous_rightDeriv_comp_inv hκ X)

theorem rightDeriv_eq_integral_convDeriv [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    {f : G → ℂ} (hf : h.IsSmoothFun f) (hconv : ∀ g, f g = ∫ y, f (g * y) * κ y ∂μ)
    (X : 𝔤) (g : G) :
    h.rightDeriv X f g = ∫ y, f (g * y) * h.convDeriv X κ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfc : Continuous f := continuous_of_isSmoothFun hf
  have hfg : Continuous fun y : G => f (g * y) := hfc.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => κ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)
  have hDc := continuous_rightDeriv_comp_inv hκ X

  have hshift : ∀ t : ℝ, f (g * h.expG (t • X)) =
      ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    rw [hconv (g * h.expG (t • X))]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_inv]

  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]

  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hκc).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hκ hκc X
  have hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y := by
      funext y; simp
    rw [this]
    exact Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ))
      (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => f (g * y) *
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖f (g * y)‖ * M)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      (hfg.mul (hκ'c.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable) hint0
    (hfg.mul (hDc.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))
  have hd1 : HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f g) 0 :=
    h.hasDerivAt_rightDeriv hf X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
section
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

set_option linter.unusedSectionVars false

theorem exists_finset_eval_eq_zero {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ S : Finset X, ∀ w ∈ W, (∀ x ∈ S, w x = 0) → w = 0 := by
  classical
  let kerS : Finset X → Submodule ℂ W := fun S =>
    ⨅ x ∈ S, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x).comp W.subtype)
  have mem_kerS : ∀ (S : Finset X) (w : W), w ∈ kerS S ↔ ∀ x ∈ S, (w : X → ℂ) x = 0 := by
    intro S w
    simp only [kerS, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearMap.coe_proj, Function.eval]
  have key : ∀ m : ℕ, ∀ S : Finset X, Module.finrank ℂ (kerS S) = m →
      ∃ S' : Finset X, kerS S' = ⊥ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro S hS
      by_cases h : kerS S = ⊥
      · exact ⟨S, h⟩
      · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
        have : ∃ x, (w : X → ℂ) x ≠ 0 := by
          by_contra hc
          push Not at hc
          exact hw0 (Subtype.ext (funext hc))
        obtain ⟨x, hx⟩ := this
        have hle : kerS (insert x S) ≤ kerS S := fun v hv =>
          (mem_kerS S v).2 fun y hy => (mem_kerS _ v).1 hv y (Finset.mem_insert_of_mem hy)
        have hne : kerS (insert x S) ≠ kerS S := by
          intro e
          rw [← e] at hw
          exact hx ((mem_kerS _ w).1 hw x (Finset.mem_insert_self x S))
        have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
        exact ih _ (hS ▸ hlt) _ rfl
  obtain ⟨S, hS⟩ := key _ ∅ rfl
  refine ⟨S, fun w hw h0 => ?_⟩
  have : (⟨w, hw⟩ : W) ∈ kerS S := (mem_kerS S _).2 h0
  rw [hS, Submodule.mem_bot] at this
  exact congrArg Subtype.val this

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

abbrev finPart (g : AdelicGLn.AdelicGL K n) : AdelicGLn.FiniteAdelicGL K n :=
  (AdelicGLn.prodEquiv K n g).2

theorem inv_mul_finEmb_mul (k : AdelicGLn.AdelicGL K n) (y : AdelicGLn.FiniteAdelicGL K n) :
    k⁻¹ * finEmb K n y * k = finEmb K n ((finPart k)⁻¹ * y * finPart k) := by
  apply (AdelicGLn.prodEquiv K n).injective
  rw [map_mul, map_mul, map_inv, prodEquiv_finEmb, prodEquiv_finEmb]
  ext <;> simp [finPart]

theorem finEmb_mem_maxCompact {y : AdelicGLn.FiniteAdelicGL K n}
    (hy : y ∈ AdelicGLn.integralFiniteGL K n) : finEmb K n y ∈ maxCompact := by
  rw [AdelicGLn.mem_integralFiniteGL_iff_forall] at hy
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (finEmb K n y) = 1 := by
      show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).1) w = 1
      rw [prodEquiv_finEmb, map_one]
      rfl
    rw [this]
    exact one_mem _
  · have : finAt v (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y v := by
      show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).2) v = _
      rw [prodEquiv_finEmb]
    rw [this]
    exact hy v

theorem rightTranslate_one' {M : Type*} [MulOneClass M] {F : Type*} (f : M → F) :
    rightTranslate (1 : M) f = f := by
  funext g
  simp only [rightTranslate, mul_one]

theorem rightTranslate_mul' {M : Type*} [Semigroup M] {F : Type*} (a b : M)
    (f : M → F) : rightTranslate (a * b) f = rightTranslate a (rightTranslate b f) := by
  funext g
  simp only [rightTranslate, mul_assoc]

theorem IsSmooth.eventually_mul_finEmb_mul {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsSmooth φ)
    (g k : AdelicGLn.AdelicGL K n) :
    ∀ᶠ y in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n), φ (g * finEmb K n y * k) = φ (g * k) := by
  have hc : Tendsto (fun y : AdelicGLn.FiniteAdelicGL K n => (finPart k)⁻¹ * y * finPart k)
      (𝓝 1) (𝓝 1) := by
    have : Continuous fun y : AdelicGLn.FiniteAdelicGL K n => (finPart k)⁻¹ * y * finPart k :=
      (continuous_const.mul continuous_id).mul continuous_const
    simpa using this.tendsto 1
  refine (hc.eventually (hφ.2 (g * k))).mono fun y hy => ?_
  rw [← hy, ← inv_mul_finEmb_mul]
  congr 1
  group

theorem exists_openSubgroup_rightInvariant {φ : AdelicGLn.AdelicGL K n → ℂ} (hs : IsSmooth φ)
    (hk : IsKFinite φ) :
    ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n),
      (U : Set (AdelicGLn.FiniteAdelicGL K n)) ⊆ AdelicGLn.integralFiniteGL K n ∧
        ∀ g, ∀ u ∈ U, φ (g * finEmb K n u) = φ g := by
  classical
  set Kc := (maxCompact : Subgroup (AdelicGLn.AdelicGL K n))
  set s : Set (AdelicGLn.AdelicGL K n → ℂ) :=
    range fun k : Kc => rightTranslate (k : AdelicGLn.AdelicGL K n) φ with hs_def
  set W := Submodule.span ℂ s
  have : FiniteDimensional ℂ W := hk
  obtain ⟨S, hS⟩ := exists_finset_eval_eq_zero W
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℂ s
  have hbfin : b.Finite := by
    have hli : LinearIndependent ℂ (fun x : b => (⟨(x : AdelicGLn.AdelicGL K n → ℂ),
        Submodule.subset_span (hbs x.2)⟩ : W)) := by
      apply LinearIndependent.of_comp W.subtype
      exact hbli
    exact Set.finite_coe_iff.1 hli.finite

  have hbk : ∀ w ∈ b, ∃ k : Kc, w = rightTranslate (k : AdelicGLn.AdelicGL K n) φ := by
    intro w hw
    obtain ⟨k, hk⟩ := hbs hw
    exact ⟨k, hk.symm⟩

  have hstab : ∀ u ∈ AdelicGLn.integralFiniteGL K n, ∀ w ∈ W,
      rightTranslate (finEmb K n u) w ∈ W := by
    intro u hu w hw
    refine Submodule.span_induction (p := fun w _ => rightTranslate (finEmb K n u) w ∈ W)
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      rw [← rightTranslate_mul']
      exact Submodule.subset_span ⟨⟨_, mul_mem (finEmb_mem_maxCompact hu) k.2⟩, rfl⟩
    · exact W.zero_mem
    · intro x y _ _ hx hy
      exact W.add_mem hx hy
    · intro c x _ hx
      exact W.smul_mem c hx

  have hnhds : ∀ᶠ u in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n),
      u ∈ AdelicGLn.integralFiniteGL K n ∧
        ∀ w ∈ hbfin.toFinset, ∀ x ∈ S, w (x * finEmb K n u) = w x := by
    have h0 : ∀ᶠ u in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n), u ∈ AdelicGLn.integralFiniteGL K n :=
      (AdelicGLn.isOpen_integralFiniteGL K n).mem_nhds (one_mem _)
    refine h0.and ?_
    rw [eventually_all_finset]
    intro w hw
    rw [eventually_all_finset]
    intro x _
    obtain ⟨k, rfl⟩ := hbk w (hbfin.mem_toFinset.1 hw)
    simpa only [rightTranslate] using hs.eventually_mul_finEmb_mul x k

  let H : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {u | u ∈ AdelicGLn.integralFiniteGL K n ∧
        ∀ w ∈ W, rightTranslate (finEmb K n u) w = w}
      one_mem' := ⟨one_mem _, fun w _ => by rw [map_one, rightTranslate_one']⟩
      mul_mem' := fun {u v} hu hv => ⟨mul_mem hu.1 hv.1, fun w hw => by
        rw [map_mul, rightTranslate_mul', hv.2 w hw, hu.2 w hw]⟩
      inv_mem' := fun {u} hu => ⟨inv_mem hu.1, fun w hw => by
        have := congrArg (rightTranslate (finEmb K n u⁻¹)) (hu.2 w hw)
        rw [← rightTranslate_mul', ← map_mul, inv_mul_cancel, map_one, rightTranslate_one'] at this
        exact this.symm⟩ }
  have hHnhds : (H : Set (AdelicGLn.FiniteAdelicGL K n)) ∈ 𝓝 1 := by
    refine Filter.mem_of_superset hnhds fun u hu => ⟨hu.1, fun w hw => ?_⟩

    rw [show W = Submodule.span ℂ b from hbspan.symm] at hw
    refine Submodule.span_induction (p := fun w _ => rightTranslate (finEmb K n u) w = w)
      ?_ ?_ ?_ ?_ hw
    · intro w hwb
      have hwW : w ∈ W := Submodule.subset_span (hbs hwb)
      have hd := W.sub_mem (hstab u hu.1 w hwW) hwW
      have := hS _ hd fun x hx => by
        simp only [Pi.sub_apply, rightTranslate]
        rw [hu.2 w (hbfin.mem_toFinset.2 hwb) x hx, sub_self]
      exact sub_eq_zero.1 this
    · rfl
    · intro x y _ _ hx hy
      rw [show rightTranslate (finEmb K n u) (x + y) =
        rightTranslate (finEmb K n u) x + rightTranslate (finEmb K n u) y from rfl, hx, hy]
    · intro c x _ hx
      rw [show rightTranslate (finEmb K n u) (c • x) = c • rightTranslate (finEmb K n u) x from rfl,
        hx]
  refine ⟨⟨H, Subgroup.isOpen_of_mem_nhds H hHnhds⟩, fun u hu => hu.1, fun g u hu => ?_⟩
  have hφW : φ ∈ W := Submodule.subset_span ⟨1, rightTranslate_one' φ⟩
  exact congrFun (hu.2 φ hφW) g

theorem continuous_of_isSmooth_of_isKFinite {φ : AdelicGLn.AdelicGL K n → ℂ} (hs : IsSmooth φ)
    (hk : IsKFinite φ) : Continuous φ := by
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant hs hk
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  let e : AdelicGLn.AdelicGL K n → AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n :=
    fun g => AdelicGLn.prodEquiv K n (g₀⁻¹ * g)
  have he : Continuous e :=
    (AdelicGLn.prodEquiv K n).continuous.comp (continuous_const.mul continuous_id)
  let F : AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n → ℂ :=
    fun p => φ (g₀ * infEmb K n (archEquiv K n p.1) * finEmb K n p.2)
  have hφF : φ = F ∘ e := by
    funext g
    simp only [F, e, Function.comp_apply, mul_assoc]
    rw [infEmb_mul_finEmb, mul_inv_cancel_left]
  have hslice : Continuous (archSlice φ g₀) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact (hs.1 g₀).continuous
  have hF : ContinuousAt F (e g₀) := by
    have hFeq : F =ᶠ[𝓝 (e g₀)] fun p => archSlice φ g₀ (archEquiv K n p.1) := by
      have he1 : e g₀ = 1 := by simp only [e, inv_mul_cancel, map_one]
      have hmem : (univ ×ˢ (U : Set (AdelicGLn.FiniteAdelicGL K n))) ∈ 𝓝 (e g₀) := by
        rw [he1]
        exact prod_mem_nhds univ_mem (U.isOpen.mem_nhds (one_mem U))
      filter_upwards [hmem] with p hp
      exact hU _ p.2 hp.2
    refine ContinuousAt.congr ?_ hFeq.symm
    exact (hslice.comp ((archEquiv K n).continuous.comp continuous_fst)).continuousAt
  rw [hφF]
  exact hF.comp he.continuousAt

theorem IsAutomorphicForm.continuous {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsAutomorphicForm φ) :
    Continuous φ :=
  continuous_of_isSmooth_of_isKFinite hφ.isSmooth hφ.isKFinite

end AutomorphicForm

end

end GroundTheory.Automorphic
end


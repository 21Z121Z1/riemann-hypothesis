import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictPosOfExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0268
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

theorem toCx_smul {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (c : B.LL) (x : (MtHL I hX a).V) :
    toCx I hX a (c • x) = B.embLL c • toCx I hX a x := by
  have h1 : toCx I hX a (c • x) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      (c • (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x)) := rfl
  rw [h1, LinearMap.map_smulₛₗ]
  rfl

theorem toCx_add {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x y : (MtHL I hX a).V) :
    toCx I hX a (x + y) = toCx I hX a x + toCx I hX a y := by
  have h1 : toCx I hX a (x + y) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      ((show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x) + (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from y)) := rfl
  rw [h1, map_add]
  rfl

noncomputable def toCxₛₗ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a where
  toFun := toCx I hX a
  map_add' := toCx_add I hX a
  map_smul' := toCx_smul I hX a

theorem toCxₛₗ_apply {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V) :
    toCxₛₗ I hX a x = toCx I hX a x := rfl

theorem toCx_linearIndependent {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) :=
  toMtilde_linearIndependent _ _ _ _ _ _ (MtHL I hX a).b.linearIndependent

theorem toCx_span {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  rw [eq_top_iff, ← toMtilde_span B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL hX, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hle : Submodule.span B.LL (Set.range (MtHL I hX a).b) ≤
      Submodule.comap (toCxₛₗ I hX a) (Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [(MtHL I hX a).b.span_eq] at hle
  exact hle (Submodule.mem_top (x := (x : (MtHL I hX a).V)))

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).Good :=
  MtildeH_good _ _ _ _ _ _
end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good_basis : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι), (MtHL I hX a).Good ∧ (∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, ∀ x, j x = toCx I hX a x) ∧ LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) ∧ Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  intro B X I hX a
  refine ⟨?_, ⟨{ toFun := toCx I hX a, map_add' := fun x y => ?_, map_smul' := fun c x => ?_ }, fun _ => rfl⟩,
    toCx_linearIndependent I hX a, toCx_span I hX a⟩
  · exact mtHL_good I hX a
  · exact toCx_add I hX a x y
  · exact toCx_smul I hX a c x

end GlobalTheory.Mem.Df
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMulFderivOfTsupport
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.ProjVar

section Parts

variable {D : ℕ} {O : Set (V D)} {u χ : V D → ℝ}

theorem continuous_mul_of_tsupport (hO : IsOpen O) (hu : ContinuousOn u O) (hχ : Continuous χ)
    (hs : tsupport χ ⊆ O) : Continuous fun v => u v * χ v :=
  (hu.mul hχ.continuousOn).continuous_of_tsupport_subset hO (tsupport_mul_subset_right.trans hs)

theorem integrable_mul_of_tsupport (hO : IsOpen O) (hu : ContinuousOn u O) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) : Integrable fun v => u v * χ v :=
  (continuous_mul_of_tsupport hO hu hχ hs).integrable_of_hasCompactSupport hc.mul_left

theorem contDiffOn_fderiv_apply (hO : IsOpen O) {n : ℕ∞ω} (hu : ContDiffOn ℝ (n + 1) u O) (a : V D) :
    ContDiffOn ℝ n (fun v => fderiv ℝ u v a) O :=
  (hu.fderiv_of_isOpen hO le_rfl).clm_apply contDiffOn_const

theorem integral_mul_fderiv_of_tsupport (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) (a : V D) :
    ∫ v, u v * fderiv ℝ χ v a = -∫ v, fderiv ℝ u v a * χ v :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_tsupport hO (contDiffOn_fderiv_apply hO (n := 0) hu a).continuousOn
      hχ.continuous hc hs)
    (integrable_mul_of_tsupport hO hu.continuousOn
      ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ a)
      ((tsupport_fderiv_apply_subset ℝ a).trans hs))
    (integrable_mul_of_tsupport hO hu.continuousOn hχ.continuous hc hs)
    (fun _ hv => (hu.contDiffAt (hO.mem_nhds (hs hv))).differentiableAt one_ne_zero)
    (fun v _ => hχ.differentiable one_ne_zero v)

theorem fderiv_fderiv_apply {v : V D} (hu : ContDiffAt ℝ 2 u v) (a : V D) :
    fderiv ℝ (fun w => fderiv ℝ u w a) v a = fderiv ℝ (fderiv ℝ u) v a a := by
  rw [fderiv_clm_apply ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    (differentiableAt_const _)]
  simp

theorem continuousOn_fderiv_fderiv (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) (a : V D) :
    ContinuousOn (fun v => fderiv ℝ (fderiv ℝ u) v a a) O :=
  (contDiffOn_fderiv_apply hO (n := 0) (contDiffOn_fderiv_apply hO (n := 1) hu a) a).continuousOn.congr
    fun _ hv => (fderiv_fderiv_apply (hu.contDiffAt (hO.mem_nhds hv)) a).symm

theorem integral_mul_fderiv_fderiv (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O)
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) (a : V D) :
    ∫ v, u v * fderiv ℝ (fderiv ℝ χ) v a a = ∫ v, fderiv ℝ (fderiv ℝ u) v a a * χ v := by
  have hχ' : ContDiff ℝ 1 fun v => fderiv ℝ χ v a :=
    contDiffOn_univ.1 (contDiffOn_fderiv_apply isOpen_univ (n := 1) hχ.contDiffOn a)
  have h₁ := integral_mul_fderiv_of_tsupport hO (hu.of_le one_le_two) hχ' (hc.fderiv_apply ℝ a)
    ((tsupport_fderiv_apply_subset ℝ a).trans hs) a
  have h₂ := integral_mul_fderiv_of_tsupport hO (contDiffOn_fderiv_apply hO (n := 1) hu a)
    (hχ.of_le one_le_two) hc hs a
  simp only [fderiv_fderiv_apply hχ.contDiffAt] at h₁
  rw [h₁, h₂, neg_neg]
  refine integral_congr_ae (.of_forall fun v => ?_)
  by_cases hv : v ∈ O
  · simp only [fderiv_fderiv_apply (hu.contDiffAt (hO.mem_nhds hv))]
  · simp only [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), mul_zero]

theorem exists_leviV_re_eq (ξ : Fin D → ℂ) : ∃ a b : V D, ∀ (f : V D → ℝ) (v : V D),
    ContDiffAt ℝ 2 f v → (leviV D (fun w => (f w : ℂ)) v ξ).re =
      4⁻¹ * (fderiv ℝ (fderiv ℝ f) v a a + fderiv ℝ (fderiv ℝ f) v b b) :=
  ⟨_, _, fun _ _ hf => by rw [← LocalMaximumSecondDerivative.leviV_re_eq hf ξ]; ring⟩

theorem continuousOn_leviV_re (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) (ξ : Fin D → ℂ) :
    ContinuousOn (fun v => (leviV D (fun w => (u w : ℂ)) v ξ).re) O :=
  have ⟨a, b, h⟩ := exists_leviV_re_eq ξ
  (continuousOn_const.mul ((continuousOn_fderiv_fderiv hO hu a).add
    (continuousOn_fderiv_fderiv hO hu b))).congr fun v hv => h u v (hu.contDiffAt (hO.mem_nhds hv))

theorem integral_mul_leviV_re (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O)
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) (ξ : Fin D → ℂ) :
    ∫ v, u v * (leviV D (fun w => (χ w : ℂ)) v ξ).re =
      ∫ v, (leviV D (fun w => (u w : ℂ)) v ξ).re * χ v := by
  obtain ⟨a, b, h⟩ := exists_leviV_re_eq ξ
  have I₁ (c : V D) : Integrable fun v => u v * fderiv ℝ (fderiv ℝ χ) v c c := by
    simp only [← fderiv_fderiv_apply hχ.contDiffAt]
    refine integrable_mul_of_tsupport hO hu.continuousOn ?_ ((hc.fderiv_apply ℝ c).fderiv_apply ℝ c)
      ((tsupport_fderiv_apply_subset ℝ c).trans ((tsupport_fderiv_apply_subset ℝ c).trans hs))
    simp only [fderiv_fderiv_apply hχ.contDiffAt]
    exact continuousOn_univ.1 (continuousOn_fderiv_fderiv isOpen_univ hχ.contDiffOn c)
  have I₂ (c : V D) : Integrable fun v => fderiv ℝ (fderiv ℝ u) v c c * χ v :=
    integrable_mul_of_tsupport hO (continuousOn_fderiv_fderiv hO hu c) hχ.continuous hc hs
  calc _ = ∫ v, 4⁻¹ * (u v * fderiv ℝ (fderiv ℝ χ) v a a + u v * fderiv ℝ (fderiv ℝ χ) v b b) :=
        integral_congr_ae (.of_forall fun v => by simp only [h χ v hχ.contDiffAt]; ring)
    _ = ∫ v, 4⁻¹ * (fderiv ℝ (fderiv ℝ u) v a a * χ v + fderiv ℝ (fderiv ℝ u) v b b * χ v) := by
        rw [integral_const_mul, integral_const_mul, integral_add (I₁ a) (I₁ b),
          integral_add (I₂ a) (I₂ b), integral_mul_fderiv_fderiv hO hu hχ hc hs,
          integral_mul_fderiv_fderiv hO hu hχ hc hs]
    _ = _ := by
        refine integral_congr_ae (.of_forall fun v => ?_)
        by_cases hv : v ∈ O
        · simp only [h u v (hu.contDiffAt (hO.mem_nhds hv))]; ring
        · simp only [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), mul_zero, add_zero]

theorem nonneg_of_integral_mul_nonneg (hO : IsOpen O) (hu : ContinuousOn u O)
    (h : ∀ χ : V D → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      (∀ v, 0 ≤ χ v) → 0 ≤ ∫ v, u v * χ v) {v : V D} (hv : v ∈ O) : 0 ≤ u v := by
  by_contra hlt
  rw [not_le] at hlt
  have hn : O ∩ {w | u w < 0} ∈ 𝓝 v := inter_mem (hO.mem_nhds hv)
    ((hu.continuousAt (hO.mem_nhds hv)).eventually_lt continuousAt_const hlt)
  obtain ⟨χ, hs, hc, hχ, hr, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hn
  have h0 (w) : 0 ≤ χ w := (hr ⟨w, rfl⟩).1
  have hs' := hs.trans inter_subset_left
  have hp : 0 < ∫ w, -u w * χ w :=
    (continuous_mul_of_tsupport hO hu.neg hχ.continuous hs').integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := v) hc.mul_left (fun w => by
        by_cases hw : w ∈ tsupport χ
        · exact mul_nonneg (neg_nonneg.2 (le_of_lt (hs hw).2)) (h0 w)
        · simp [image_eq_zero_of_notMem_tsupport hw]) (by simp [h1, hlt.ne])
  simp only [neg_mul, integral_neg] at hp
  linarith [h χ hχ hc hs' h0]

theorem posCurrent_iff_leviV (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) :
    PosCurrent O u ↔ ∀ v ∈ O, ∀ ξ, 0 ≤ (leviV D (fun w => (u w : ℂ)) v ξ).re := by
  have h2 {χ : V D → ℝ} (h : ContDiff ℝ ∞ χ) : ContDiff ℝ 2 χ := h.of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨fun h v hv ξ => nonneg_of_integral_mul_nonneg hO (continuousOn_leviV_re hO hu ξ)
    (fun χ h₁ h₂ h₃ h₄ => (h.2 χ h₁ h₂ h₃ h₄ ξ).trans_eq (integral_mul_leviV_re hO hu (h2 h₁) h₂ h₃ ξ)) hv,
    fun h => ⟨hu.continuousOn.locallyIntegrableOn hO.measurableSet, fun χ h₁ h₂ h₃ h₄ ξ => ?_⟩⟩
  rw [integral_mul_leviV_re hO hu (h2 h₁) h₂ h₃ ξ]
  refine integral_nonneg fun v => ?_
  by_cases hv : v ∈ O
  · exact mul_nonneg (h v hv ξ) (h₄ v)
  · simp [image_eq_zero_of_notMem_tsupport fun h => hv (h₃ h)]

end Parts

namespace Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv} {m : Met Y σ Δ} {ψ : Y.pts σ → ℝ}

theorem mSmooth.mPsh_iff_levi (h : mSmooth Y σ Δ m) (hψ : (Y.an σ).SmoothOn univ ψ) :
    mPsh Y σ Δ m ψ ↔ ∀ (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ) (y : Y.pts σ), y ∈ c.e.source →
      y ∈ eqnSet σ Δ g → ∀ ξ, 0 ≤ c.levi (fun z => m.wt g z + ψ z) y ξ := by
  refine forall₂_congr fun c g => ?_
  have ho : IsOpen (chartDom c Δ g) := isOpen_over _ (isOpen_eqnSet Δ g)
  have hs : (Y.an σ).SmoothOn (eqnSet σ Δ g) fun z => m.wt g z + ψ z := fun j =>
    ((h.2 g).mono (fun _ hz => ⟨trivial, hz⟩) j).add (hψ.mono (subset_univ _) j)
  rw [and_iff_right (.of_forall fun _ _ => h.1 trivial)]
  refine (posCurrent_iff_leviV ho ((hs.chart (isOpen_eqnSet Δ g) c).of_le
    (WithTop.coe_le_coe.2 le_top))).trans ⟨fun H y hy hg => H _ (mem_over _ hy hg), fun H v hv ξ => ?_⟩
  have := H _ (c.e.map_target hv.1) hv.2 ξ
  rwa [AlgChart.levi, c.e.right_inv hv.1] at this

theorem mSmooth.levi_frame (h : mSmooth Y σ Δ m) (hψ : (Y.an σ).SmoothOn univ ψ)
    {c : AlgChart Y.str σ Y.dim} {g g' : Y.Fnˣ} {y : Y.pts σ} (hy : y ∈ c.e.source)
    (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ g') (ξ : Fin Y.dim → ℂ) :
    c.levi (fun z => m.wt g' z + ψ z) y ξ = c.levi (fun z => m.wt g z + ψ z) y ξ :=
  AnRead.levi_eq_of_add_log (R := Y.an σ) (f := fun z => m.wt g z + ψ z)
    ((isOpen_eqnSet Δ g).inter (isOpen_eqnSet Δ g'))
    (fun j => ((h.2 g).mono (fun _ hz => ⟨trivial, hz.1⟩) j).add (hψ.mono (subset_univ _) j))
    (holoOn_tv Δ g g') (fun _ hz => tv_ne_zero hz.1 hz.2)
    (fun z hz => by rw [Met.wt_trans (h.1 trivial) hz.1 hz.2]; ring) hy ⟨hg, hg'⟩ ξ

variable {L : LB Y.X} {r : L.ι → Y.Fnˣ}

theorem mSmooth.mPsh_iff_semiPos (h : mSmooth Y σ Δ m) (hψ : (Y.an σ).SmoothOn univ ψ)
    (hp : Presents Δ L r) :
    mPsh Y σ Δ m ψ ↔ ((m.toWeight h.posSet_eq hp).addFn ψ).SemiPos (Y.an σ) := by
  rw [h.mPsh_iff_levi hψ]
  refine ⟨fun H i c y hy ξ => H _ (r i) y hy.1 (ptsIn_subset_eqnSet hp i hy.2) ξ,
    fun H c g y hy hg ξ => ?_⟩
  have hi := mem_pick hp.isLB y
  rw [h.levi_frame hψ hy (ptsIn_subset_eqnSet hp _ hi) hg]
  exact H.chart ((h.isSmooth_toWeight hp).addFn hψ) hy hi ξ

theorem smoothOn_zero : (Y.an σ).SmoothOn univ (0 : Y.pts σ → ℝ) := fun _ => contDiffOn_const

end Var

end GlobalTheory.ProjVar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.IpMt

theorem ipMt_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (jM : (I.per l u a).Mt →ₛₗ[starRingEnd ℂ] (I.per l u a).Wrow), (∀ F, jM F ∈ (I.fm l u a).ptC) → (∀ w F, (I.per l u a).period w F = (I.fm l u a).ipP (jM F) w) → (∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F)) ∧ ∀ F, F ≠ 0 → 0 < (I.ipMt l u a F F).re := by
  intro B X I hOk hP l Z u a jM hmem hper
  obtain ⟨j0, hinj, -, hmem0, hper0, hpos⟩ := PerConj.period_conj I hOk hP l Z u a
  have uniq : ∀ z ∈ (I.fm l u a).ptC, ∀ z' ∈ (I.fm l u a).ptC,
      (∀ w, (I.fm l u a).ipP z w = (I.fm l u a).ipP z' w) → z = z' := by
    intro z hz z' hz' h
    by_contra hne
    have h1 := hpos _ (sub_mem hz hz') (sub_ne_zero.2 hne)
    rw [map_sub (I.fm l u a).ipP, LinearMap.sub_apply, h, sub_self] at h1
    simp at h1
  have hj : ∀ G, I.jStd l u a G = jM G := by
    intro G
    have hex : ∃ z, z ∈ (I.fm l u a).ptC ∧ ∀ w, (I.per l u a).period w G = (I.fm l u a).ipP z w :=
      ⟨jM G, hmem G, fun w => hper w G⟩
    have hs := Classical.epsilon_spec hex
    exact uniq _ hs.1 _ (hmem G) fun w => (hs.2 w).symm.trans (hper w G)
  have hform : ∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F) := by
    intro F G
    rw [TC.ipMt, hj, hj]
  refine ⟨hform, fun F hF => ?_⟩
  have h0 : jM F = j0 F := uniq _ (hmem F) _ (hmem0 F) fun w => (hper w F).symm.trans (hper0 w F)
  have hne : jM F ≠ 0 := by
    rw [h0]
    exact fun h => hF (hinj (h.trans (map_zero j0).symm))
  rw [hform]
  exact hpos _ (hmem F) hne

theorem ipMt_sum {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (F G : (I.perIn u a).Mt B.fields.emb B.embLL) :
    I.ipMt l u a F G = letI := (I.perIn u a).clFin (l.per u a);
      ∑ c, (I.perIn u a).wt c * pairB (I.perIn u a).sgT
        (MvPolynomial.map (starRingEnd ℂ) (F.1 c.1 ((I.perIn u a).S'.rep c))) (G.1 c.1 ((I.perIn u a).S'.rep c)) := by
  have hE : ∀ τ x, embAt B.embLL B.fields.emb τ (letI := B.fields.starE; star x) =
      starRingEnd ℂ (embAt B.embLL B.fields.emb τ x) := fun τ x => (GlobalTheory.Mem.FieldsLaws.fields_ok B).conjE _ x
  have hH : ∀ b, (I.perIn u a).H b = ⊤ := fun _ => rfl
  have h := (ipMt_tie I hOk hP l Z u a (PerConj.jM (I.perIn u a) B.fields.emb B.embLL)
    (PerConj.jM_mem _ _ hE (l.per u a) hH)
    (PerConj.period_eq _ _ (l.ch u a) (l.per u a) (B.hcW u))).1 F G
  refine h.trans ?_
  refine (PerConj.petersson_apply B.fields.emb B.embLL (l.per u a) _ _).trans ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (PerConj.ipVal_cev _ _ _ _ _).trans (congrArg (fun p => pairB _ p _) (PerConj.polOf_cev _ _ _ _))

end GlobalTheory.Mem.Col2.IpMt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdeles
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory

theorem isCompact_matInt_set (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} := by
  have hO : IsCompact ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) :
      Set (FiniteAdeleRing (𝓞 F) F)) := PI.WAU.isCompact_Ohat (F := F)
  have h := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hO))
  have he : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} =
      Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n =>
        ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) : Set (FiniteAdeleRing (𝓞 F) F)))) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [he]
  exact h

theorem isCompact_KGL (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact (PIW.ClassFinD.KGL F n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  have hA := isCompact_matInt_set F n
  have hA' := (MulOpposite.opHomeomorph
    (M := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).symm.isCompact_preimage.2 hA
  have h := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).isCompact_preimage (hA.prod hA')
  convert h using 1
  ext g
  exact Iff.rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelVectorSumOfIsotypicPieces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.DecompKer

open Formalism.L2.NG (FinTyp)

def isoSetoid (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Setoid (FinTyp L n) where
  r π π' := π.Iso π'
  iseqv := ⟨fun π => Formalism.L2.NG.IsoRep.refl _, fun {π _} h => Formalism.L2.NG.IsoRep.symm π.stable h,
    fun h h' => Formalism.L2.NG.IsoRep.trans h h'⟩

theorem isotIn_le_of_iso {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) {π π' : FinTyp D.host.E n}
    (h : π.Iso π') : principalLevelFrame.isotIn (D := D) ρ C π' ≤ principalLevelFrame.isotIn (D := D) ρ C π := by
  obtain ⟨T, hT⟩ := h
  refine iSup₂_le fun Φ hΦ => ?_
  rintro _ ⟨f, rfl⟩
  have hE : principalLevelFrame.IsEqvA ρ π (Φ.comp T.toLinearMap) ∧ LinearMap.range (Φ.comp T.toLinearMap) ≤ C := by
    refine ⟨fun g a => ?_, ?_⟩
    · have e : T ⟨Formalism.L2.NG.rt D.host.E n g a, π.stable g a a.2⟩ =
          ⟨Formalism.L2.NG.rt D.host.E n g (T a), π'.stable g _ (T a).2⟩ :=
        Subtype.ext (hT g a _ rfl)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [e]
      exact hΦ.1 g (T a)
    · rintro _ ⟨a, rfl⟩
      exact hΦ.2 ⟨T a, rfl⟩
  refine Submodule.mem_iSup_of_mem (Φ.comp T.toLinearMap) (Submodule.mem_iSup_of_mem hE ⟨T.symm f, ?_⟩)
  simp

end GlobalTheory.DecompKer

open GlobalTheory.DecompKer in

theorem GlobalTheory.decomp_kernels_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∀ y ∈ principalLevelFrame.isotIn (D := D) ρ C π', B x y = 0) → ∀ (ι : Type) (O : ι → A →ₗ[ℂ] A), (∀ i π, ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, O i x ∈ principalLevelFrame.isotIn (D := D) ρ C π) → ∀ x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π, (∀ i, O i x = 0) → x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, (principalLevelFrame.isotIn (D := D) ρ C π ⊓ ⨅ i, LinearMap.ker (O i)) := by
  intro D n A _ _ ρ C B h1 h2 h3 h4 ι O hO x hx hOx
  classical
  let S := isoSetoid D.host.E n
  let q : Formalism.L2.NG.FinTyp D.host.E n → Quotient S := Quotient.mk S
  have hC : ∀ π, principalLevelFrame.isotIn (D := D) ρ C π ≤ C := fun π => iSup₂_le fun Φ h => h.2
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp hx
  set t := f.support.image q with ht
  let y : Quotient S → A := fun c => ∑ π ∈ f.support with q π = c, f π
  have hxy : (f.sum fun _ xi => xi) = ∑ c ∈ t, y c := by
    rw [Finsupp.sum]
    exact (Finset.sum_fiberwise_of_maps_to (fun π hπ => Finset.mem_image_of_mem q hπ) _).symm
  have hrep : ∀ π c, q π = c → c.out.Iso π := fun π c hq =>
    Quotient.exact (s := S) (by rw [Quotient.out_eq]; exact hq.symm)
  have hyI : ∀ c, y c ∈ principalLevelFrame.isotIn (D := D) ρ C c.out := by
    intro c
    refine Submodule.sum_mem _ fun π hπ => ?_
    exact isotIn_le_of_iso ρ C (hrep π c (Finset.mem_filter.mp hπ).2) (hf π)
  have hni : ∀ c c' : Quotient S, c ≠ c' → ¬ c.out.Iso c'.out := by
    intro c c' hne hI
    apply hne
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound hI
  have hB0 : ∀ u ∈ C, B u 0 = 0 := by
    intro u hu
    have := h1 u hu 0 C.zero_mem 0 C.zero_mem 1
    simp only [smul_zero, add_zero, one_mul] at this
    simpa using this
  have hOy : ∀ i, ∀ c ∈ t, O i (y c) = 0 := by
    intro i c hc
    set u := O i (y c) with hu
    have huI : u ∈ principalLevelFrame.isotIn (D := D) ρ C c.out := hO i c.out (y c) (hyI c)
    have huC : u ∈ C := hC _ huI

    let Z : Submodule ℂ A :=
      { carrier := {v | v ∈ C ∧ B u v = 0}
        zero_mem' := ⟨C.zero_mem, hB0 u huC⟩
        add_mem' := fun {a b} ha hb => ⟨C.add_mem ha.1 hb.1, by
          have := h1 u huC a ha.1 b hb.1 1
          rw [one_smul] at this
          rw [this, ha.2, hb.2]; simp⟩
        smul_mem' := fun c' a ha => ⟨C.smul_mem c' ha.1, by
          have := h1 u huC 0 C.zero_mem a ha.1 c'
          rw [zero_add] at this
          rw [this, hB0 u huC, ha.2]; simp⟩ }
    have hsum : ∑ c' ∈ t, O i (y c') = 0 := by
      rw [← map_sum, ← hxy]; exact hOx i
    have hrest : ∑ c' ∈ t.erase c, O i (y c') ∈ Z := by
      refine Submodule.sum_mem _ fun c' hc' => ?_
      have hne : c' ≠ c := (Finset.mem_erase.mp hc').1
      have hv : O i (y c') ∈ principalLevelFrame.isotIn (D := D) ρ C c'.out := hO i c'.out (y c') (hyI c')
      exact ⟨hC _ hv, h4 c.out c'.out (hni c c' (Ne.symm hne)) u huI _ hv⟩
    have hueq : u = -∑ c' ∈ t.erase c, O i (y c') := by
      rw [eq_neg_iff_add_eq_zero, hu, Finset.add_sum_erase t (fun c' => O i (y c')) hc, hsum]
    have huZ : u ∈ Z := by rw [hueq]; exact Z.neg_mem hrest
    by_contra hne
    have := h3 u huC hne
    rw [huZ.2] at this
    simp at this
  rw [hxy]
  refine Submodule.sum_mem _ fun c hc => ?_
  refine Submodule.mem_iSup_of_mem c.out (Submodule.mem_inf.mpr ⟨hyI c, ?_⟩)
  exact Submodule.mem_iInf _ |>.mpr fun i => LinearMap.mem_ker.mpr (hOy i c hc)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LambdaPrimeBasisRowTypePosAtReference
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3.LamPos

theorem lambdaPrime_basis_row_type_pos_at_reference : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, ∀ j ∈ Finset.Icc 1 D.R.m, 0 < D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ hH hL hI σ j hj
  obtain ⟨cOf, -, h2, -⟩ := hL
  obtain ⟨h1, hm⟩ := Finset.mem_Icc.1 hj
  have hi : j - 1 < D.R.m := by omega
  have hj' : ((⟨j - 1, hi⟩ : Fin D.R.m) : ℕ) + 1 = j := by simp only; omega
  have key := h2 ⟨j - 1, hi⟩ A3.A.μ0 (D.what₂.ft σ) (Or.inl Y.tup0) (hI σ ⟨j - 1, hi⟩)
  rw [Y.tup0, hj'] at key
  rw [key]
  exact hH.prim.posScal.2 _ _ _ _

end GlobalTheory.Mem.R3.LamPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoicesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeData_ok_of_trueColumnChoices : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  first | exact @GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | exact GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | (intros; apply GlobalTheory.Mem.Col2.LevelLaw.atIn_ok <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreservesRadicalPrincipalIdealsOfAffineSpaceCoveStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r → KeepsRad M M' φ f := by
  first | exact @GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | exact GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | (intros; apply GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover <;> assumption)
end


import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0223
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0222
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2LimitEqPointwiseLimitHolds
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem l2_limit_eq_pointwise_limit : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (a : ℕ → Mat n → V) (b : Mat n → V) (x : Lp V 2 μ), (∀ k, MemLp (fun y : G n => a k y.val) 2 μ) → Tendsto (fun k => cls μ (a k)) atTop (𝓝 x) → (∀ z ∈ GLs n, Tendsto (fun k => a k z) atTop (𝓝 (b z))) → MemLp (fun y : G n => b y.val) 2 μ ∧ cls μ b = x := by
  intro n _ _ μ _ V _ _ _ a b x hm hc hp
  have hin : TendstoInMeasure μ (fun k => (cls μ (a k) : G n → V)) atTop (x : G n → V) :=
    tendstoInMeasure_of_tendsto_Lp hc
  obtain ⟨ns, hns, hae⟩ := hin.exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂μ, ∀ k, (cls μ (a k) : G n → V) y = a k y.val :=
    ae_all_iff.2 fun k => coe_cls μ (hm k)
  have hbx : (fun y : G n => b y.val) =ᵐ[μ] x := by
    filter_upwards [hae, hall] with y h1 h2
    have hy : y.val ∈ GLs n := by
      have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
      exact hu.ne_zero
    have h3 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (b y.val)) :=
      (hp y.val hy).comp hns.tendsto_atTop
    have h4 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (x y)) := by
      simpa only [h2] using h1
    exact tendsto_nhds_unique h3 h4
  exact cls_of_ae μ hbx

end GlobalTheory.CompanionTheory.PresSobA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateCommutes
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def lTrL {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun y : G n => x * y) (measurePreserving_mul_left μ x)).toContinuousLinearMap

theorem memLp_lTr {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : MemLp (fun y : G n => lTr x f y.val) 2 μ :=
  hf.comp_measurePreserving (measurePreserving_mul_left μ x)

theorem lTrL_cls {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : lTrL μ V x (cls μ f) = cls μ (lTr x f) := by
  unfold cls
  rw [dif_pos hf, dif_pos (memLp_lTr μ x hf)]
  exact Lp.toLp_compMeasurePreserving hf (measurePreserving_mul_left μ x)

theorem ltComm_of_ltSob : LtSob → LtComm := by
  intro hL n _ _ μ _ E _ Ω T F c hS h x f f' hf hf' hff'
  obtain ⟨hLg, hU, hR, -, -, -, -, hCS, -, -, hM, -, -, -, hO, -⟩ := hS
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  have hcomm : lTrL μ E.V x * F.Φ h = F.Φ h * lTrL μ E.V x := by
    refine F.comm _ (fun m => ?_) h
    obtain ⟨f₀, hf₀, hc⟩ := hM m.1 m.2
    have hL₀ := hL n μ E.V hLg hU hR x f₀ hf₀
    have hmem : cls μ (lTr x f₀) ∈ Msob μ E.V := Submodule.subset_span ⟨_, hL₀.1, rfl⟩
    have hm₀ : cls μ f₀ ∈ Msob μ E.V := hc ▸ m.2
    have hm : m = ⟨cls μ f₀, hm₀⟩ := Subtype.ext hc.symm
    have hO₀ : Sob μ (Om f₀) := (hOps n μ E.V hLg hU hR f₀ hf₀).1
    have hf₀m : MemLp (fun y : G n => f₀ y.val) 2 μ := hf₀.2 []
    have hO₀m : MemLp (fun y : G n => Om f₀ y.val) 2 μ := hO₀.2 []
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · change cls μ (lTr x f₀) = lTrL μ E.V x m.1
      rw [← hc, lTrL_cls μ x hf₀m]
    · rw [hO _ hmem hL₀.1, hm, hO _ hm₀ hf₀, lTrL_cls μ x hO₀m]
      exact (hCl n μ E.V hU).2.2.1 _ _ hL₀.2
  have hfm : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []
  have hfm' : MemLp (fun y : G n => f' y.val) 2 μ := hf'.2 []
  rw [← lTrL_cls μ x hfm', hff', ← lTrL_cls μ x hfm]
  exact DFunLike.congr_fun hcomm (cls μ f)

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateSobolev
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTranslateSobolev

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem val_mem (x : G n) : x.val ∈ GLs n := by
  have h := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  exact h.ne_zero

def mulL (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := fun y z => Matrix.mul_add a y z
      map_smul' := fun c y => Matrix.mul_smul a c y }

@[simp] theorem mulL_apply (a y : Mat n) : mulL a y = a * y := rfl

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (lTr x f) (GLs n) :=
  hf.comp (mulL x.val).contDiff.contDiffOn (fun _ hy => mul_mem (val_mem x) hy)

theorem Rd_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n)
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (lTr x f) g = Rd X f (x.val * g) := by
  have hxg : x.val * g ∈ GLs n := mul_mem (val_mem x) hg
  have hd : DifferentiableAt ℝ f (mulL x.val g) :=
    (hf.contDiffAt ((isOpen_GLs n).mem_nhds hxg)).differentiableAt (by simp)
  have hc : fderiv ℝ (f ∘ mulL x.val) g = (fderiv ℝ f (mulL x.val g)).comp (mulL x.val) :=
    (hd.hasFDerivAt.comp g (mulL x.val).hasFDerivAt).fderiv
  show fderiv ℝ (f ∘ mulL x.val) g (g * X) = fderiv ℝ f (x.val * g) (x.val * g * X)
  rw [hc]
  simp [Matrix.mul_assoc]

theorem contDiffOn_Rw (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hR n).1 V (Rw w f) ih).1 (bs p)

theorem Rw_lTr (hR : RCalc) (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ∀ g ∈ GLs n, Rw w (lTr x f) g = Rw w f (x.val * g) := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have he : Rw w (lTr x f) =ᶠ[𝓝 g] lTr x (Rw w f) :=
      Filter.eventuallyEq_of_mem ((isOpen_GLs n).mem_nhds hg) (fun y hy => ih y hy)
    show Rd (bs p) (Rw w (lTr x f)) g = Rd (bs p) (Rw w f) (x.val * g)
    rw [← Rd_lTr x (contDiffOn_Rw hR hf w) (bs p) hg]
    show fderiv ℝ (Rw w (lTr x f)) g (g * bs p) = fderiv ℝ (lTr x (Rw w f)) g (g * bs p)
    rw [he.fderiv_eq]

end LeftTranslateSobolev

open LeftTranslateSobolev in

theorem ltSob : LtSob := by
  intro n _ _ μ _ V _ _ _ _ hR x f hf
  refine ⟨⟨contDiffOn_lTr x hf.1, fun w => ?_⟩, fun g hg => ?_⟩
  · have h := (hf.2 w).comp_measurePreserving (measurePreserving_mul_left μ x)
    have he : (fun y : G n => Rw w (lTr x f) y.val) = (fun y : G n => Rw w f y.val) ∘ (fun y => x * y) :=
      funext fun y => Rw_lTr hR x hf.1 w y.val (val_mem y)
    rw [he]
    exact h
  · have ht : ∀ s, gel s 2 (lTr x f) g = gel s 2 f (x.val * g) := fun s =>
      (((hR n).1 V f hf.1).2.2.2 s 2 x.val (val_mem x) g hg).1
    simp only [Om, Pi.smul_apply, Pi.add_apply, ht]

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpIntegralAePointwise
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.LpBochner

variable {Y V : Type} [MeasurableSpace Y] {ν : Measure Y}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem integrableOn_of_memLp_two {h : Y → V} (hh : MemLp h 2 ν) {s : Set Y} (hs : ν s ≠ ⊤) :
    IntegrableOn h s ν := by
  haveI : IsFiniteMeasure (ν.restrict s) := ⟨by simpa using hs.lt_top⟩
  have h2 : MemLp h 2 (ν.restrict s) := hh.restrict s
  exact memLp_one_iff_integrable.1 (h2.mono_exponent (by norm_num))

theorem integral_norm_restrict_le {h : Y → V} (hh : MemLp h 2 ν) {s : Set Y} (hs : ν s ≠ ⊤) :
    ∫ y in s, ‖h y‖ ∂ν ≤ ((ν s) ^ (1 / 2 : ℝ)).toReal * (eLpNorm h 2 ν).toReal := by
  haveI : IsFiniteMeasure (ν.restrict s) := ⟨by simpa using hs.lt_top⟩
  have hm : AEStronglyMeasurable h (ν.restrict s) := hh.1.restrict
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict s) (p := 1) (q := 2)
    (by norm_num) hm
  have h3 : eLpNorm h 2 (ν.restrict s) ≤ eLpNorm h 2 ν := eLpNorm_restrict_le _ _ _ _
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
    norm_num
  rw [hexp, Measure.restrict_apply_univ] at h1
  have hfin : (ν s) ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hs
  have h4 : eLpNorm h 1 (ν.restrict s) ≤ (ν s) ^ (1 / 2 : ℝ) * eLpNorm h 2 ν := by
    calc _ ≤ _ := h1
      _ ≤ eLpNorm h 2 ν * (ν s) ^ (1 / 2 : ℝ) := by gcongr
      _ = _ := mul_comm _ _
  have h5 : ∫ y in s, ‖h y‖ ∂ν = (eLpNorm h 1 (ν.restrict s)).toReal := by
    rw [integral_norm_eq_lintegral_enorm hm, eLpNorm_one_eq_lintegral_enorm]
  rw [h5, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hh.2.ne) h4

variable [CompleteSpace V]

def setIntegralCLM (ν : Measure Y) (s : Set Y) (hs : ν s ≠ ⊤) : Lp V 2 ν →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ y in s, h y ∂ν
      map_add' := fun f g => by
        have hf := integrableOn_of_memLp_two (Lp.memLp f) hs
        have hg := integrableOn_of_memLp_two (Lp.memLp g) hs
        rw [← integral_add hf hg]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))
      map_smul' := fun r f => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul r f)) }
    ((ν s) ^ (1 / 2 : ℝ)).toReal
    (fun h => by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine (integral_norm_restrict_le (Lp.memLp h) hs).trans ?_
      rw [Lp.norm_def])

theorem setIntegralCLM_apply (s : Set Y) (hs : ν s ≠ ⊤) (h : Lp V 2 ν) :
    setIntegralCLM ν s hs h = ∫ y in s, h y ∂ν := rfl

theorem bochner_Lp_ae (A : Type) [MeasurableSpace A] (α : Measure A) [SFinite α]
    [SigmaFinite ν] (c : A → Lp V 2 ν) (F : A → Y → V)
    (hc : Integrable c α) (hF : AEStronglyMeasurable (Function.uncurry F) (α.prod ν))
    (hcF : ∀ᵐ a ∂α, c a =ᵐ[ν] F a) :
    (⇑(∫ a, c a ∂α) : Y → V) =ᵐ[ν] fun y => ∫ a, F a y ∂α := by
  have hFs : ∀ s : Set Y, AEStronglyMeasurable (Function.uncurry F) (α.prod (ν.restrict s)) := by
    intro s
    refine hF.mono_measure ?_
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hint : ∀ s : Set Y, ν s ≠ ⊤ → Integrable (Function.uncurry F) (α.prod (ν.restrict s)) := by
    intro s hs
    rw [integrable_prod_iff (hFs s)]
    constructor
    · filter_upwards [hcF] with a ha
      exact (integrableOn_of_memLp_two (Lp.memLp (c a)) hs).congr (ae_restrict_of_ae ha)
    · refine Integrable.mono' (hc.norm.const_mul ((ν s) ^ (1 / 2 : ℝ)).toReal)
        (hFs s).norm.integral_prod_right' ?_
      filter_upwards [hcF] with a ha
      have hnn : 0 ≤ ∫ y, ‖Function.uncurry F (a, y)‖ ∂(ν.restrict s) :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn, Lp.norm_def]
      have : ∫ y, ‖Function.uncurry F (a, y)‖ ∂(ν.restrict s) = ∫ y in s, ‖c a y‖ ∂ν :=
        integral_congr_ae (ae_restrict_of_ae (ha.mono fun y hy => by simp [hy]))
      rw [this]
      exact integral_norm_restrict_le (Lp.memLp (c a)) hs
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s _ hs
    exact integrableOn_of_memLp_two (Lp.memLp _) hs.ne
  · intro s _ hs
    exact (hint s hs.ne).integral_prod_right
  · intro s hsm hs
    have h1 : ∫ y in s, (∫ a, c a ∂α) y ∂ν = ∫ a, ∫ y in s, c a y ∂ν ∂α := by
      rw [← setIntegralCLM_apply s hs.ne, ← ContinuousLinearMap.integral_comp_comm _ hc]
      rfl
    have h2 : ∫ a, ∫ y in s, c a y ∂ν ∂α = ∫ a, ∫ y in s, F a y ∂ν ∂α := by
      refine integral_congr_ae ?_
      filter_upwards [hcF] with a ha
      exact integral_congr_ae (ae_restrict_of_ae ha)
    rw [h1, h2]
    exact integral_integral_swap (hint s hs.ne)

theorem coe_integral_ae_eq : ∀ (A Y V : Type) [MeasurableSpace A] [MeasurableSpace Y] (α : Measure A) [SFinite α] (ν : Measure Y) [SigmaFinite ν] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (c : A → Lp V 2 ν) (F : A → Y → V), Integrable c α → AEStronglyMeasurable (Function.uncurry F) (α.prod ν) → (∀ᵐ a ∂α, c a =ᵐ[ν] F a) → (⇑(∫ a, c a ∂α) : Y → V) =ᵐ[ν] fun y => ∫ a, F a y ∂α := by
  intro A Y V _ _ α _ ν _ _ _ _ c F hc hF hcF
  exact bochner_Lp_ae A α c F hc hF hcF

end GlobalTheory.CompanionTheory.LpBochner
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivative
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.ExpCurve

section Entries

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  haveI : FiniteDimensional ℝ (Mat n) := inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
  haveI : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)
  have h : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n))
      (NormedSpace.exp (t • X) * X : Mat n) t := hasDerivAt_exp_smul_const X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

end Entries

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  exact hasDerivAt_exp_entry X t i j

theorem expC_continuous_hasDerivAt :
    ∀ (n : ℕ) (X : Mat n), Continuous (expC X) ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  intro n X
  refine ⟨?_, hasDerivAt_exp X⟩
  refine (GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG (n := n)).isInducing.continuous_iff.2 ?_
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp X t).continuousAt

end GlobalTheory.CompanionTheory.PresSobA.ExpCurve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem latK_mulVec {M : Matrix (Fin n) (Fin n) L} (h1 : ∀ i j, Valued.v (M i j) ≤ 1)
    (h2 : ∀ i j, j < i → Valued.v (M i j) < 1) (k : ℕ) {x : Fin n → L} (hx : x ∈ latK L n k) :
    M.mulVec x ∈ latK L n k := by
  have hx1 : ∀ j, Valued.v (x j) ≤ 1 := fun j => by
    have := hx j
    split_ifs at this with h
    · exact this
    · exact this.le
  intro i
  show if i.val < k then Valued.v ((M.mulVec x) i) ≤ 1 else Valued.v ((M.mulVec x) i) < 1
  have e : (M.mulVec x) i = ∑ j, M i j * x j := rfl
  rw [e]
  split_ifs with hik
  · refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' (hx1 j)).trans (h1 i j)
  · refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    by_cases hjk : j.val < k
    · have hji : j < i := by
        rw [Fin.lt_def]; omega
      exact (mul_le_of_le_one_right' (hx1 j)).trans_lt (h2 i j hji)
    · have := hx j
      rw [if_neg hjk] at this
      exact (mul_le_of_le_one_left' (h1 i j)).trans_lt this

theorem mem_iwU_iff (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) :
    g ∈ IwU σ n ↔ (∀ i j, Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1) ∧
      ∀ i j, j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1 := by
  constructor
  · intro hg
    have hg' : (g : GL (Fin n) L) ∈ IwGL L n := hg
    refine ⟨fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries hg' i j, fun i j hji => ?_⟩
    have h := (Subgroup.mem_iInf.1 hg') ⟨i.val, by omega⟩
    have hs : (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • latK L n i.val = latK L n i.val := h
    have he : (Pi.single j (1 : L) : Fin n → L) ∈ latK L n i.val := by
      intro k
      by_cases hk : k = j
      · subst hk
        have : k.val < i.val := hji
        simp [this]
      · have : (Pi.single j (1 : L) : Fin n → L) k = 0 := Pi.single_eq_of_ne hk _
        rw [this]
        split_ifs <;> simp
    have hm := Set.smul_mem_smul_set (a := Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) he
    rw [hs] at hm
    have hi := hm i
    rw [if_neg (lt_irrefl _)] at hi
    have e : ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • (Pi.single j (1 : L) : Fin n → L)) i =
        ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := by
      show (Matrix.mulVec ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (Pi.single j (1 : L) : Fin n → L)) i = _
      simp
    rwa [e] at hi
  · rintro ⟨h1, h2⟩
    have hinv := (GlobalTheory.LGrp.mem_GU_iff σ n (g : GL (Fin n) L)).1 g.2
    have h1' : ∀ i j, Valued.v (((g : GL (Fin n) L)⁻¹).val i j) ≤ 1 := fun i j => by
      rw [hinv, hσv]; exact h1 _ _
    have h2' : ∀ i j, j < i → Valued.v (((g : GL (Fin n) L)⁻¹).val i j) < 1 := fun i j hji => by
      rw [hinv, hσv]; exact h2 _ _ (Fin.rev_lt_rev.2 hji)
    show (g : GL (Fin n) L) ∈ IwGL L n
    refine Subgroup.mem_iInf.2 fun k => ?_
    show (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • latK L n k = latK L n k
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact latK_mulVec h1 h2 k hy
    · refine ⟨((g : GL (Fin n) L)⁻¹).val.mulVec x, latK_mulVec h1' h2' k hx, ?_⟩
      show ((g : GL (Fin n) L)).val.mulVec (((g : GL (Fin n) L)⁻¹).val.mulVec x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem iwU_diag (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ n} (hg : g ∈ IwU σ n) (i : Fin n) :
    Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1 := by
  classical
  obtain ⟨h1, h2⟩ := (mem_iwU_iff hσv g).1 hg
  obtain ⟨k1, k2⟩ := (mem_iwU_iff hσv g⁻¹).1 (inv_mem hg)
  have hprod : (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) i i = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; simp
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hprod
  have hrest : Valued.v (∑ j ∈ Finset.univ.erase i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
    rw [map_mul]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hji | hji
    · exact (mul_le_of_le_one_right' (k1 j i)).trans_lt (h2 i j hji)
    · exact (mul_le_of_le_one_left' (h1 i j)).trans_lt (k2 j i hji)
  have hmain : Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1 := by
    have e : ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
        (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
        1 - ∑ j ∈ Finset.univ.erase i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
          (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j i := by
      rw [← hprod]; ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by simpa using hrest), map_one]
  rw [map_mul] at hmain
  refine le_antisymm (h1 i i) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmain.symm
    _ ≤ _ := mul_le_of_le_one_right' (k1 i i)

end GlobalTheory.CompanionTheory.SatPow

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationRightTranslate
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem Mol_rR_eq (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (hU : Unimod) (φ : Mat n → ℝ) (h : G n) (x : Lp V 2 μ) (z : Mat n) :
    Mol μ φ (⇑(rR μ V h x)) z = Mol μ φ (⇑x) (z * h.val) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have he : MeasurableEmbedding (fun y : G n => y * h) := (Homeomorph.mulRight h).measurableEmbedding
  have h1 : Mol μ φ (⇑(rR μ V h x)) z = ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x (u * h) ∂μ := by
    unfold Mol
    refine integral_congr_ae ?_
    filter_upwards [rR_coe μ hU h x] with u hu
    rw [hu]
  rw [h1]
  unfold Mol
  rw [← hm.integral_comp he (fun u : G n => φ (z * h.val * (u⁻¹ : G n).val) • x u)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have : z * h.val * ((u * h)⁻¹ : G n).val = z * (u⁻¹ : G n).val := by
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp only [this]

end GlobalTheory.CompanionTheory.PresSobA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumLocalDegreesOverLStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_local_degrees_over_l : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) → ∑ v ∈ T, locDeg v = Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank | exact GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank | (intros; apply GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank <;> assumption)
end


import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0212
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0213
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0196
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0215
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACInt
section
open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem aCInt_of_proper (hP : ACProper) : ACInt := by
  intro k r Wp Wq _ _ _ _ D φ₀ hφ hφc g hg
  obtain ⟨P, hPc, hPm⟩ := hP k r Wp Wq D (tsupport φ₀) {g} hφc isCompact_singleton
    (Set.singleton_subset_iff.2 hg)
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have hfin : D.μSS P < ⊤ := by
    show ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) P < ⊤
    exact hPc.measure_lt_top
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hφ' : Continuous (fun x : Mt k r => φ₀ (Matrix.of x)) :=
    hφ.comp (continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i))
  have hmeasφ : Measurable (fun x : Mt k r => φ₀ (Matrix.of x)) := hφ'.measurable
  have hmeas : Measurable (fun p : B.SS k r => φ₀ (B.sgs p g)) := by
    have h1 : Measurable (fun p : B.SS k r => Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF (p, (g : Mt k r))) :=
      Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF_meas.comp (measurable_id.prodMk measurable_const)
    exact hmeasφ.comp h1
  have hind : Integrable (P.indicator fun _ : B.SS k r => M) D.μSS :=
    (integrable_indicator_iff hPc.isClosed.measurableSet).2 (integrableOn_const hfin.ne)
  refine hind.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  by_cases hpP : p ∈ P
  · rw [Set.indicator_of_mem hpP]; exact hM _
  · have h0 : φ₀ (B.sgs p g) = 0 := by
      by_contra hne
      exact hpP (hPm p hp g rfl (subset_tsupport _ hne))
    rw [h0, norm_zero, Set.indicator_of_notMem hpP]

theorem averaging_integrability_holds : ACInt := aCInt_of_proper averaging_properness_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACSmooth
section
open MeasureTheory Topology Matrix
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def linM {k r : ℕ} (A Bb : B.Mat k r) : Mt k r →ₗ[ℝ] Mt k r :=
  ((LinearMap.mulLeft ℝ A).comp (LinearMap.mulRight ℝ Bb) : B.Mat k r →ₗ[ℝ] B.Mat k r)

theorem linM_apply {k r : ℕ} (A Bb : B.Mat k r) (v : Mt k r) :
    (Matrix.of (linM A Bb v) : B.Mat k r) = A * Matrix.of v * Bb := by
  show A * ((Matrix.of v : B.Mat k r) * Bb) = _
  rw [Matrix.mul_assoc]

theorem aCSmooth_of_proper (hP : ACProper) : ACSmooth := by
  intro k r Wp Wq _ _ _ _ D φ₀ hφ hφc hφs g₀ hg₀

  obtain ⟨ε₀, hε₀, hball⟩ :=
    Metric.mem_nhds_iff.1 ((Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z').mem_nhds hg₀.2)
  have hε : 0 < ε₀ / 2 := by positivity
  have hCb : Metric.closedBall g₀ (ε₀ / 2) ⊆ Q.OmPlus k r D.z D.z' := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  have hC'c : IsCompact (Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r) :=
    (isCompact_closedBall g₀ (ε₀ / 2)).inter_right Formalism.FourierDecayAlt.P.B5.GV_closed
  have hC'O : Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r ⊆ JF.Om k r D.z D.z' := fun x hx => ⟨hx.2, hCb hx.1⟩
  obtain ⟨P, hPc, hPp⟩ := hP k r Wp Wq D (tsupport φ₀) _ hφc hC'c hC'O

  set Am : B.SS k r → B.Mat k r := fun p =>
    (Hpk k r * (Matrix.of p.1.1 : B.Mat k r)ᴴ * Hpk k r) * (Hpk k r * (Matrix.of p.1.2 : B.Mat k r)ᴴ * Hpk k r)
    with hAm
  set Bm : B.SS k r → B.Mat k r := fun p => (Matrix.of p.2.2 : B.Mat k r) * Matrix.of p.2.1 with hBm
  have hsgs : ∀ p, D.inSS p → ∀ g, B.sgs p g = Am p * g * Bm p := by
    intro p hp g
    show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 = _
    rw [Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.1.1, Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.2.1.1]
    simp only [hAm, hBm, Matrix.mul_assoc]
  have hof : Continuous (fun ν : Mt k r => (Matrix.of ν : B.Mat k r)) := continuous_id
  have hAc : Continuous Am := by
    have h1 : Continuous (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)) := hof.comp continuous_fst.fst
    have h2 : Continuous (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)) := hof.comp continuous_fst.snd
    exact ((continuous_const.mul h1.matrix_conjTranspose).mul continuous_const).mul
      ((continuous_const.mul h2.matrix_conjTranspose).mul continuous_const)
  have hBc : Continuous Bm := by
    have h3 : Continuous (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) := hof.comp continuous_snd.snd
    have h4 : Continuous (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) := hof.comp continuous_snd.fst
    exact h3.mul h4
  have hcont : Continuous (fun p : B.SS k r => B.gN (Am p) * B.gN (Bm p)) :=
    (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hAc).mul (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hBc)
  obtain ⟨M₁, hM₁⟩ := hPc.exists_bound_of_continuousOn hcont.continuousOn
  set L : B.SS k r → (Mt k r →L[ℝ] Mt k r) := fun p => LinearMap.toContinuousLinearMap (linM (Am p) (Bm p))
    with hLdef
  have hL : ∀ p (v : Mt k r), (Matrix.of (L p v) : B.Mat k r) = Am p * Matrix.of v * Bm p := fun p v =>
    linM_apply (Am p) (Bm p) v
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  have hnn0 : 0 ≤ nn := by positivity
  set ML : ℝ := nn * max M₁ 0 with hML
  have hML0 : 0 ≤ ML := mul_nonneg hnn0 (le_max_right _ _)
  have hLn : ∀ p ∈ P, ‖L p‖ ≤ ML := by
    intro p hp
    apply ContinuousLinearMap.opNorm_le_bound _ hML0
    intro v
    have e1 : ‖L p v‖ = ‖(Matrix.of (L p v) : B.Mat k r)‖ := rfl
    have e2 : ‖v‖ = ‖(Matrix.of v : B.Mat k r)‖ := rfl
    rw [e1, e2, hL]
    set g : B.Mat k r := Matrix.of v
    have hgA := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Am p)
    have hgB := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Bm p)
    have hgg := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg g
    have hgn : B.gN g ≤ nn * ‖g‖ :=
      Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_le_of_ent g ‖g‖ (norm_nonneg _) (fun i j => Matrix.norm_entry_le_entrywise_sup_norm g)
    have hAB : B.gN (Am p) * B.gN (Bm p) ≤ max M₁ 0 := by
      have := hM₁ p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgA hgB)] at this
      exact this.trans (le_max_left _ _)
    calc ‖Am p * g * Bm p‖ ≤ B.gN (Am p * g * Bm p) := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN _
      _ ≤ B.gN (Am p * g) * B.gN (Bm p) := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ (B.gN (Am p) * B.gN g) * B.gN (Bm p) :=
          mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) hgB
      _ = (B.gN (Am p) * B.gN (Bm p)) * B.gN g := by ring
      _ ≤ max M₁ 0 * (nn * ‖g‖) := mul_le_mul hAB hgn hgg (le_max_right _ _)
      _ = ML * ‖g‖ := by rw [hML]; ring

  set φ₁ : Mt k r → ℝ := fun v => φ₀ (Matrix.of v) with hφ₁def
  have hφ₁ : ContDiff ℝ ∞ φ₁ := hφ
  have hφ₁c : HasCompactSupport φ₁ := hφc
  have hK : ∀ i : ℕ, ∃ K : ℝ, ∀ x, ‖iteratedFDeriv ℝ i φ₁ x‖ ≤ K := fun i =>
    (hφ₁.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support (hφ₁c.iteratedFDeriv i)
  choose K hKb using hK

  set F : B.SS k r → Mt k r → ℝ := fun p y => P.indicator (fun p => φ₁ (L p y)) p with hF
  have hFin : ∀ p ∈ P, F p = φ₁ ∘ (L p) := fun p hp => by
    funext y; simp [hF, hp]
  have hFout : ∀ p ∉ P, F p = fun _ => 0 := fun p hp => by
    funext y; simp [hF, hp]

  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : IsFiniteMeasureOnCompacts D.μW := ⟨D.haarW.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨D.haarN.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨D.haarW'.finite_compact⟩
  have : IsFiniteMeasureOnCompacts (D.μW.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts (D.μW'.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts D.μSS := by
    show IsFiniteMeasureOnCompacts ((D.μW.prod D.μN).prod (D.μW'.prod D.μN))
    infer_instance
  have hPfin : D.μSS P ≠ ⊤ := (hPc.measure_lt_top (μ := D.μSS)).ne
  have hPm : MeasurableSet P := hPc.isClosed.measurableSet
  have hFm : ∀ y, AEStronglyMeasurable (fun p => F p y) D.μSS := by
    intro y
    have hc : Continuous (fun p => φ₁ (L p y)) := by
      have : (fun p => φ₁ (L p y)) = fun p => φ₀ (Am p * Matrix.of y * Bm p) := by
        funext p; simp only [hφ₁def]; rw [hL]
      rw [this]
      exact hφ.continuous.comp ((hAc.mul continuous_const).mul hBc)
    exact (hc.measurable.indicator hPm).aestronglyMeasurable
  have hsm : ContDiffOn ℝ ∞ (fun y => ∫ p, F p y ∂D.μSS) (Metric.ball (Matrix.of.symm g₀ : Mt k r) (ε₀ / 2)) := by
    rw [contDiffOn_infty]
    intro N
    set Kt : ℝ := (∑ i ∈ Finset.range (N + 1), |K i|) * (max ML 1) ^ N with hKt
    have hb : Integrable (P.indicator fun _ => Kt) D.μSS :=
      (integrableOn_const hPfin).integrable_indicator hPm
    refine (Formalism.FourierDecayAlt.P.Ux10.pint Metric.isOpen_ball (P.indicator fun _ => Kt) hb N ℝ F ?_ (fun y _ => hFm y) ?_).1
    · intro p
      by_cases hp : p ∈ P
      · rw [hFin p hp]
        exact (hφ₁.comp (L p).contDiff).contDiffOn.of_le (mod_cast le_top)
      · rw [hFout p hp]; exact contDiffOn_const
    · intro i hi y _ p
      by_cases hp : p ∈ P
      · rw [hFin p hp, ContinuousLinearMap.iteratedFDeriv_comp_right (L p) hφ₁ y (mod_cast le_top)]
        simp only [Set.indicator_of_mem hp]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have h1 : ‖iteratedFDeriv ℝ i φ₁ (L p y)‖ ≤ ∑ j ∈ Finset.range (N + 1), |K j| :=
          (hKb i _).trans ((le_abs_self _).trans
            (Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
        have h2 : ‖L p‖ ^ i ≤ (max ML 1) ^ N :=
          (pow_le_pow_left₀ (norm_nonneg _) ((hLn p hp).trans (le_max_left _ _)) i).trans
            (pow_le_pow_right₀ (le_max_right _ _) hi)
        exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _)
          (Finset.sum_nonneg fun j _ => abs_nonneg _)
      · rw [hFout p hp, iteratedFDeriv_fun_zero]
        simp [Set.indicator_of_notMem hp]
  refine ⟨Metric.ball g₀ (ε₀ / 2), fun g => ∫ p, F p (Matrix.of.symm g) ∂D.μSS, Metric.isOpen_ball,
    Metric.mem_ball_self hε, hsm, ?_⟩
  intro g hg hgG
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  by_cases hpP : p ∈ P
  · have e : φ₁ (L p (Matrix.of.symm g)) = φ₀ (Am p * g * Bm p) := by
      simp only [hφ₁def]; rw [hL]; rfl
    simp only [hF, Set.indicator_of_mem hpP, e, hsgs p hp g]
  · have h0 : φ₀ (B.sgs p g) = 0 := by
      by_contra hne
      exact hpP (hPp p hp g ⟨Metric.ball_subset_closedBall hg, hgG⟩ (subset_tsupport _ hne))
    simp [hF, hpP, h0]

theorem averaging_smoothness_holds : ACSmooth := aCSmooth_of_proper averaging_properness_holds

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def colsVm (k r m : ℕ) (j : Fin m) : Fin (2 * r + k + 1) := ⟨2 * r + k - (r - 1 - j.val), by omega⟩

def kvM (k r m : ℕ) (w : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  qminorOp (Q.EH k r) (colsVm k r m) (colsVm k r m) w F

def kvTop (k r : ℕ) (y : ℂ) : ℂ := (y - ((2 * r + k : ℕ) : ℂ) / 2) + ((r : ℕ) : ℂ) - 1

def pbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then pbOp ⟨i, h⟩ f else 0

def cbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbOp ⟨i, h⟩ f else 0

def cbiN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbiOp ⟨i, h⟩ f else 0

def kvP (r : ℕ) (w : ℂ) : ℕ → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X) × (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0 => (fun f => f, fun _ => 0)
  | m + 1 =>
    (fun f => (kvP r w m).1 (fun c => (w - (m : ℂ)) • f c - pbN r (r - m - 1) f c) -
        cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f)),
      (kvP r w m).1)

def kvC (r : ℕ) (w : ℂ) (m : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := (kvP r w m).1 f

def gaugeF (k r : ℕ) (c : Fin r → ℂ) : ℂ := Q.resG k r (Fin.last r) (fun _ => (1 : ℂ)) c 1

end defs

def TVCoef : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          drbF P.r c • kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g)

def TVGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) c

def TVCrd : Prop :=
  ∀ (k r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (y : ℂ) (Φ : (Fin r → ℂ) → X)
    (U : Set (Fin r → ℂ)) (c : Fin r → ℂ), IsOpen U → U ⊆ OmX r → c ∈ U →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c' => gaugeF k r c' • Φ c') U →
      gaugeF k r c • kvC r (kvTop k r y) r Φ c = (vABm r y r).1 (fun c' => gaugeF k r c' • Φ c') c

open scoped ContDiff in

theorem jDACapTodaV_of_parts (h1 : TVCoef) (h2 : TVGrp) (h3 : TVCrd) : JDACapTodaV := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have e1 := h1 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have e2 := h2 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (Gauge.OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Gauge.OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
    (Fin.last P.r)).1
  obtain ⟨U, F, hUo, hx0, hF, hFeq⟩ := hfam (c, g) ⟨hc, hcg⟩ hg
  have hemb : ContDiff ℝ ∞ (fun c' : Fin P.r → ℂ => (c', g)) := contDiff_id.prodMk contDiff_const
  set U' : Set (Fin P.r → ℂ) := {c' | (c', g) ∈ U} ∩ OmX P.r with hU'
  have hU'o : IsOpen U' := (hUo.preimage hemb.continuous).inter (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX P.r)
  have hgauge : ∀ c' : Fin P.r → ℂ, gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g) =
      Q.resG P.k P.r (Fin.last P.r) J c' g := by
    intro c'
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' := by
    refine ((hF.comp hemb.contDiffOn (fun c' hc' => hc'.1))).congr (fun c' hc' => ?_)
    rw [hgauge c']
    exact hFeq (c', g) hc'.1 hg
  have e3 := h3 P.k P.r (Wq →L[ℂ] Wp) y (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' c hU'o
    (fun _ h => h.2) ⟨hx0, hc⟩ hsm
  have hfun : (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) =
      fun c' => Q.resG P.k P.r (Fin.last P.r) J c' g := funext hgauge
  rw [hfun] at e3
  simp only [dMul, Q.crd, Q.cmp, if_true]
  rw [← e3]
  have hres : Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
      gaugeF P.k P.r c • capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) := by
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  rw [hres, e1, e2, smul_comm]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapARep
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

theorem exists_polyOp_qminor_sum {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : ι → Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) (a j) (b j) u F g := by
  have h := fun j => qminorWordSum k r t (a j) (b j) u
  choose L hL hE using h
  let Θ₁ : B.DiffOp k r Wp Wq :=
    s.toList.flatMap fun j => (L j).map fun cw => pTerm (fun g => β j g * cw.1) cw.2
  let T₀ : B.DTerm k r Wp Wq := pTerm (fun _ => 0) (List.replicate t 0)
  have hT₀ : T₀.word = List.replicate t 0 := pTerm_word (fun X hX => by
    rw [List.eq_of_mem_replicate hX]; exact inLie_zero)
  refine ⟨Θ₁ ++ [T₀], ?_, ?_, ?_⟩
  · intro Tm hTm
    rcases List.mem_append.1 hTm with h1 | h1
    · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h1
      obtain ⟨j, hj, cw, hcw, rfl⟩ := h1
      refine ⟨(pTerm_word_le _ _).trans (hL j cw hcw).2, fun g => β j g * cw.1, ?_, fun g => rfl, fun g => rfl⟩
      have := Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (hβ j hj) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const cw.1 0)
      simpa using this
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => rfl, fun g => rfl⟩
  · unfold B.opOrder
    apply foldr_max_eq
    · intro x hx
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨Tm, hTm | rfl, rfl⟩ := hx
      · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hTm
        obtain ⟨j, _, cw, hcw, rfl⟩ := hTm
        exact (pTerm_word_le _ _).trans (hL j cw hcw).2
      · rw [hT₀]; simp
    · simp only [List.mem_map, List.mem_append, List.mem_singleton]
      exact ⟨T₀, Or.inr rfl, by rw [hT₀]; simp⟩
  · intro UU F hF g hgU hg
    have hT₀a : T₀.coef g (B.Rw T₀.word F g) = 0 := by
      change ((0 : ℂ) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw T₀.word F g) = 0
      simp
    simp only [B.opApply, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hT₀a,
      add_zero, Θ₁]
    rw [sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE j _ UU F hF g hgU hg, List.map_map, ← sum_map_mul_smul]
    congr 1
    apply List.map_congr_left
    intro cw hcw
    simp only [Function.comp_apply]
    rw [pTerm_word (fun X hX => ((hL j cw hcw).1 X hX).1)]
    change ((β j g * cw.1) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw cw.2 F g) = _
    rfl

end Formalism.FourierDecayAlt.P.CutMP.QMinOp

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

noncomputable section

theorem capBeta_pd (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capBeta k r c) := by
  unfold capBeta
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a)))) fun a l => ?_
  simp only [Matrix.of_apply, herm, dotProduct, Matrix.mulVec]
  refine pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun j _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun c _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul (pd_entry _ _) (pd_const _ 0))

theorem capAlphaV_pd (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capAlphaV k r B) := by
  unfold capAlphaV
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)) fun a l => ?_
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine pd_sum _ fun m _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  refine pd_sum _ fun l _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem capelli_representation_holds : JDACapRep := by
  intro k r Wp Wq _ _ _ _ _ y
  classical
  have hκ : r ≤ (r + 1) * (2 * r + k + 1) := by nlinarith
  have ho : r ≤ 2 * r + k + 1 := by omega
  obtain ⟨Θ, hP, hO, hE⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun c : Fin r → Fin (2 * r + k + 1) => StrictMono c) (fun _ => C3.xR k r r le_rfl)
    (fun c => c) (capBeta k r) (fun c _ => capBeta_pd k r c) (Q.uC k r 0 y)
  obtain ⟨Θv, hPv, hOv, hEv⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun B : Fin r → Fin (2 * r + k + 1) => StrictMono fun l => C3.keyS k r (B l)) (fun B => B)
    (fun _ => C3.sR k r r le_rfl) (capAlphaV k r) (fun B _ => capAlphaV_pd k r B)
    (y - ((2 * r + k : ℕ) : ℂ) / 2 + (r : ℂ) - 1)
  refine ⟨Θ, Θv, QMinOp.polyOp_mono hP ho hκ, QMinOp.polyOp_mono hPv ho hκ, hO, hOv, fun F g hg hF => ?_,
    fun F g hg hF => ?_⟩
  · rw [hO] at hF
    rw [hE {g} F hF g rfl hg, Finset.sum_filter]
    rfl
  · rw [hOv] at hF
    rw [hEv {g} F hF g rfl hg, Finset.sum_filter]
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hg
    simp only [capAv, C3.AAvop, capAlphaV, hinv]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymbolW
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_lieW {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hW : ∀ X ∈ lieOf (UWset k r z), (Matrix.trace (ζ * X)).re = 0)
    (u v : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hv : inWb k r v)
    (huz : herm (Hpk k r) u z = 0) (hvz : herm (Hpk k r) v z = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  refine herm_zero_of_trace hζ u v (hW _ (xuv_lieW z u v hu hv huz hvz)) (hW _ ?_)
  refine xuv_lieW z u _ hu (inWb_smul _ hv) huz ?_
  rw [herm_smul_left, hvz, mul_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

end Formalism.FourierDecayAlt.P.CutMP.JfS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupVectorSpace
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_vector_space : GVGrp := by
  intro k r
  refine ⟨⟨⟨1 + 1, (1 / 2 : ℂ) • 1, ?_, ?_⟩, rfl⟩, fun g₀ hg₀ => ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_one, smul_add, ← add_smul]
    norm_num
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_add, ← add_smul]
    norm_num
  · have hdet : IsUnit g₀.det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hg₀
    refine ⟨Matrix.nonsing_inv_mul g₀ hdet, fun h hh => ⟨Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul hg₀ hh,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (Formalism.FourierDecayAlt.P.PBM.GV_inv_mem g₀ hg₀) hh, ?_⟩⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g₀ hdet, Matrix.one_mul]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end


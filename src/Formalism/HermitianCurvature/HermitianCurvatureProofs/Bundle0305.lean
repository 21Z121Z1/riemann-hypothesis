import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0304
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0190
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0105
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0293
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSQQAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0289
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0296

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDomCutInt
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section general

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jgq_continuousOn (D : B.RealPlaceData k r Wp Wq) {A : ℝ} {H : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hT : JF.TransportedAlt k r A 0) (hH : B.InCC A 0 H) :
    ContinuousOn (fun q => B.JF D H (B.gq D q)) (JF.QDom k r D.z D.z') := by
  exact (Formalism.FourierDecayAlt.Final.jf_jqSmooth k r Wp Wq D A 0 H hT hH).continuousOn

theorem aesm_weight_smul (D : B.RealPlaceData k r Wp Wq) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin r → ℂ) × ℂ → E} (hc : ContinuousOn g (JF.QDom k r D.z D.z')) :
    AEStronglyMeasurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q • g q) volume := by
  set s := JF.QDom k r D.z D.z' with hs_def
  have hs : MeasurableSet s := by
    have hseq : s = (⋂ a : Fin r, {q : (Fin r → ℂ) × ℂ | q.1 a ≠ 0}) ∩
        {q | Tz k r D.z * Tz k r D.z' < Complex.normSq q.2} := by
      ext q
      simp [hs_def, JF.QDom]
    rw [hseq]
    refine IsOpen.measurableSet (IsOpen.inter (isOpen_iInter_of_finite fun a => ?_) ?_)
    · exact isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
    · exact isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  have contW : Continuous (fun q : (Fin r → ℂ) × ℂ => (∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Mdim k r a - 2))) *
      (Complex.normSq q.2 - Tz k r D.z * Tz k r D.z') ^ (k - 1)) := by
    first | fun_prop | continuity
  have hw : ContinuousOn (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q) s := by
    refine contW.continuousOn.congr fun q hq => ?_
    unfold bcWeight
    rw [if_pos hq.2.le]
  have h1 : AEStronglyMeasurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q • g q)
      (volume.restrict s) := (hw.smul hc).aestronglyMeasurable hs
  have h2 := (aestronglyMeasurable_indicator_iff hs).mpr h1
  refine h2.congr ?_
  have hN1 : ∀ a : Fin r, volume {q : (Fin r → ℂ) × ℂ | q.1 a = 0} = 0 := by
    intro a
    have h0 : volume {x : Fin r → ℂ | x a = 0} = 0 := by
      have he : {x : Fin r → ℂ | x a = 0} = Function.eval a ⁻¹' {0} := rfl
      rw [he, MeasureTheory.volume_pi]
      first
        | exact MeasureTheory.Measure.pi_eval_preimage_null _ (measure_singleton 0)
        | exact MeasureTheory.Measure.pi_eval_preimage_null (measure_singleton 0)
    exact MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      MeasureTheory.Measure.quasiMeasurePreserving_fst h0
  have hN2 : volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = Tz k r D.z * Tz k r D.z'} = 0 := by
    have hsph : volume (Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r D.z * Tz k r D.z'))) = 0 := by
      first
        | exact MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) _
        | exact MeasureTheory.Measure.addHaar_sphere (0 : ℂ) _
    have h0 : volume {z : ℂ | Complex.normSq z = Tz k r D.z * Tz k r D.z'} = 0 := by
      refine measure_mono_null (fun z hz => ?_) hsph
      simp only [Set.mem_setOf_eq] at hz
      rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    exact MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      MeasureTheory.Measure.quasiMeasurePreserving_snd h0
  have hA : ∀ᵐ q ∂(volume : Measure ((Fin r → ℂ) × ℂ)), ∀ a : Fin r, q.1 a ≠ 0 :=
    ae_all_iff.mpr fun a => ae_iff.mpr (by simpa using hN1 a)
  have hB : ∀ᵐ q ∂(volume : Measure ((Fin r → ℂ) × ℂ)), Complex.normSq q.2 ≠ Tz k r D.z * Tz k r D.z' :=
    ae_iff.mpr (by simpa using hN2)
  filter_upwards [hA, hB] with q hqa hqb
  classical
  by_cases hq : q ∈ s
  · simp [Set.indicator_apply, hq]
  · simp only [Set.indicator_apply, hq, if_false]
    have hlt : Complex.normSq q.2 < Tz k r D.z * Tz k r D.z' := by
      have hn : ¬ (Tz k r D.z * Tz k r D.z' < Complex.normSq q.2) := fun h => hq ⟨hqa, h⟩
      exact lt_of_le_of_ne (not_lt.mp hn) hqb
    have hz : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 := by
      unfold bcWeight
      rw [if_neg (not_le.mpr hlt)]
    rw [hz, zero_smul]

end general

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rr0Int_integrable (p : KB.Pl P Wp Wq) (w : List C.Letter) {A : ℝ} {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hAB : B.AB P.k P.r ≤ A) (hT : JF.TransportedAlt P.k P.r A 0)
    (hH : ∀ j : ℕ, j ≤ 5 + (2 * P.r + P.k + 1) * w.length → B.InCC A j H) :
    Integrable (levelZeroRadialIntegral p w H) := by
  set D := p.T.base with hD
  set K := Formalism.FourierDecayAlt.P.CutMP.En.foldCV P.k P.r (M.sgn P p.l0) w H with hK
  have hKj : ∀ j ≤ 5, B.InCC A j K := fun j hj =>
    Formalism.FourierDecayAlt.P.CutMP.En.inCC_fold Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class A (M.sgn P p.l0) H w j (hH _ (by omega))
  have hHj : ∀ j ≤ 5, B.InCC A j H := fun j hj => hH j (by omega)
  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P.k P.r Wp Wq D A hAB
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨cH, hcH⟩ := hHj 4 (by norm_num)
  obtain ⟨cK, hcK⟩ := hKj 4 (by norm_num)
  have hNH := (hC0 H H cH cH (hHj 5 le_rfl) (hHj 5 le_rfl) hcH hcH).1
  have hNK := (hC0 K K cK cK (hKj 5 le_rfl) (hKj 5 le_rfl) hcK hcK).1
  have cH' := jgq_continuousOn D hT (hHj 0 (by norm_num))
  have cK' := jgq_continuousOn D hT (hKj 0 (by norm_num))
  set W := bcWeight P.k P.r (Tz P.k P.r D.z) (Tz P.k P.r D.z') with hW
  have hW0 : ∀ q, 0 ≤ W q := fun q => Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q
  have hcv := Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff (V := Wp) (W := Wq)
  have ca : ContinuousOn (fun q => B.hsVec (B.JF D H (B.gq D q))) (JF.QDom P.k P.r D.z D.z') :=
    hcv.continuous.comp_continuousOn cH'
  have cb : ContinuousOn (fun q => B.hsVec (B.JF D K (B.gq D q))) (JF.QDom P.k P.r D.z D.z') :=
    hcv.continuous.comp_continuousOn cK'
  have hform : levelZeroRadialIntegral p w H = fun q => W q • inner ℂ (B.hsVec (B.JF D H (B.gq D q)))
      (B.hsVec (B.JF D K (B.gq D q))) := by
    funext q
    rw [Complex.real_smul]
    rfl
  have hm : AEStronglyMeasurable (levelZeroRadialIntegral p w H) volume := by
    rw [hform]; exact aesm_weight_smul D (ca.inner cb)
  refine ⟨hm, ?_⟩

  have ma : AEMeasurable (fun q => ENNReal.ofReal (W q * ‖B.hsVec (B.JF D H (B.gq D q))‖ ^ 2)) volume := by
    have := (aesm_weight_smul D ((ca.norm.pow 2))).aemeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable (this.congr (ae_of_all _ fun q => rfl))
  have hle : ∀ q, ‖levelZeroRadialIntegral p w H q‖ₑ ≤ ENNReal.ofReal (W q * ‖B.hsVec (B.JF D H (B.gq D q))‖ ^ 2) +
      ENNReal.ofReal (W q * ‖B.hsVec (B.JF D K (B.gq D q))‖ ^ 2) := by
    intro q
    rw [hform, ← ofReal_norm, ← ENNReal.ofReal_add (mul_nonneg (hW0 q) (sq_nonneg _))
      (mul_nonneg (hW0 q) (sq_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    set a := ‖B.hsVec (B.JF D H (B.gq D q))‖
    set b := ‖B.hsVec (B.JF D K (B.gq D q))‖
    have hi : ‖inner ℂ (B.hsVec (B.JF D H (B.gq D q))) (B.hsVec (B.JF D K (B.gq D q)))‖ ≤ a * b :=
      norm_inner_le_norm _ _
    rw [norm_smul, Real.norm_of_nonneg (hW0 q)]
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have h2 : a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    nlinarith [hW0 q, mul_le_mul_of_nonneg_left (hi.trans h2) (hW0 q)]
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_add_left' ma]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · exact lt_top_iff_ne_top.2 hNH
  · exact lt_top_iff_ne_top.2 hNK

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFinal
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_main3 (hA : P5.ThmPActual) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      (∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
        DomCut p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w) →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ := thmBpAt_main2 hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3
    hexp hWG hLG hI5 hDom hBd
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3 hexp hWG hLG
    hI5 (limEvT_of_dom p hχ (ckOn_fpm p p₀ hf hid) Y N hDom) hBd

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def topD (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ) : ℝ :=
  TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c)

def NFTopForm (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ ε : ℝ, 0 < ε → (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re = ∫ c, topD p (D.cutF p.T.base χ F ε) w c

def NFTopPtw (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), topD p (D.cutF p.T.base χ F ε) w c = topD p F w c

def NFTopDom (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (topD p (D.cutF p.T.base χ F ε) w) volume) ∧
  ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖topD p (D.cutF p.T.base χ F ε) w c‖ ≤ h c

def NFTopId (p : KB.Pl P Wp Wq) (_χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∫ c, topD p F w c = (p.RR F 0 w [] []).re

theorem limEvT_of_NF (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ)
    (hT : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopForm p χ F w)
    (hP : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopPtw p χ F w)
    (hD : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopDom p χ F w)
    (hI : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopId p χ F w) : LimEvT p χ F Y N := by
  intro w hw hl
  obtain ⟨hmeas, h, hint, hbd⟩ := hD w hw hl
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun ε c => topD p (D.cutF p.T.base χ F ε) w c) (f := topD p F w) h hmeas hbd hint
    ((hP w hw hl).mono fun c hc => Filter.Tendsto.congr' (hc.mono fun ε he => he.symm) tendsto_const_nhds)
  rw [← hI w hw hl]
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hT w hw hl ε hε).symm

end place

def NFHyp (Cb Cc : ℝ) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ) : Prop :=
  C6.IsCut0 χ ∧ KB.InDDplus2 P p.l0 p.T.base Cb p.Θ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A₀ m f) ∧
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ∧
    N ≤ 2 * p₀

def NFTopFormAll : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopForm p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

def NFTopPtwAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopPtw p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

def NFTopDomAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopDom p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

def NFTopIdAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopId p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

theorem limEvT_fpm_of_NF (hA : P5.ThmPActual) (h1 : NFTopFormAll) (h2 : NFTopPtwAll) (h3 : NFTopDomAll) (h4 : NFTopIdAll) (Cb : ℝ) :
    ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
      NFHyp Cb Cc p f A₀ p₀ χ N →
      LimEvT p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  obtain ⟨C1, k1⟩ := h1 hA Cb
  obtain ⟨C2, k2⟩ := h2 Cb
  obtain ⟨C3, k3⟩ := h3 Cb
  obtain ⟨C4, k4⟩ := h4 Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH
  have mono : ∀ C, C ≤ max (max C1 C2) (max C3 C4) → NFHyp Cb C p f A₀ p₀ χ N := by
    intro C hC
    unfold NFHyp at hH ⊢
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
    refine ⟨a1, a2, a3, a4, le_trans ?_ a5, a6⟩
    gcongr
  exact limEvT_of_NF p χ _ Y N (k1 Wp Wq P p f A₀ p₀ χ Y N (mono C1 (by simp))) (k2 Wp Wq P p f A₀ p₀ χ Y N (mono C2 (by simp)))
    (k3 Wp Wq P p f A₀ p₀ χ Y N (mono C3 (by simp))) (k4 Wp Wq P p f A₀ p₀ χ Y N (mono C4 (by simp)))

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNormDegGCut
section
namespace Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

def Acc (k r : ℕ) : ℝ := ((64 * (2 * r + k + 1) ^ 3 : ℕ) : ℝ)

theorem AB_le_Acc (k r : ℕ) : B.AB k r ≤ Acc k r := by
  unfold B.AB Acc
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : (1 : ℝ) ≤ 2 * r + k + 1 := by linarith
  nlinarith [mul_nonneg hk hr, mul_nonneg (mul_nonneg hk hr) hr, mul_nonneg hk hk, mul_nonneg hr hr,
    mul_nonneg (mul_nonneg hk hk) hk, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg hk hk) hr,
    mul_nonneg (mul_nonneg hk hr) hr]

def NormSquareTransferIdentity : Prop :=
  ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TBB.jN2 p F = B.normSq p.T.base F

def CoefCC : Prop :=
  PI.KFinSmooth → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (u u' : Fin k → ℝ)
    (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq),
    A.Good Bs ε lam h u u' νq νq' → B.InCC (Acc k r) 5 (A.coef Bs.μG)

def BetaInfAbs : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 5 F →
    Integrable (fun p => B.xiTau D (1, 1) p * B.Ph D F F p) D.μSS →
    B.betaInf D F F = ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS

def BetaInfCoef : Prop :=
  SchurH → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (u u' : Fin k → ℝ)
    (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq),
    A.Good Bs ε lam h u u' νq νq' → A.l A.w0 ≠ 0 → A.l' A.w0 ≠ 0 →
    Integrable (fun p => B.xiTau Bs (1, 1) p * B.Ph Bs (A.coef Bs.μG) (A.coef Bs.μG) p) Bs.μSS ∧
    ∫ p, B.xiTau Bs (1, 1) p * B.Ph Bs (A.coef Bs.μG) (A.coef Bs.μG) p ∂Bs.μSS = ((A.deg Bs.μG : ℝ) : ℂ)

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem beta_eq_integral (D : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    B.beta D F F = ∫ q, (((Formalism.QuantumDeterminants.bcWeight P.k P.r (Formalism.QuantumDeterminants.Tz P.k P.r D.z) (Formalism.QuantumDeterminants.Tz P.k P.r D.z') q *
      ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2 : ℝ)) : ℂ) := by
  unfold B.beta Formalism.QuantumDeterminants.betaBig
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem normSq_of_beta (D : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (x : ℝ) (hx : x ≠ 0)
    (hβ : B.beta D F F = (x : ℂ)) : B.normSq D F = ENNReal.ofReal x := by
  set g : (Fin P.r → ℂ) × ℂ → ℝ := fun q => Formalism.QuantumDeterminants.bcWeight P.k P.r (Formalism.QuantumDeterminants.Tz P.k P.r D.z)
    (Formalism.QuantumDeterminants.Tz P.k P.r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2 with hg
  have hβ' := beta_eq_integral D F
  rw [hβ] at hβ'
  have hint : Integrable (fun q => ((g q : ℝ) : ℂ)) := by
    by_contra hn
    rw [integral_undef hn] at hβ'
    exact hx (by exact_mod_cast hβ')
  have hgi : Integrable g := by
    have := hint.re
    simpa using this
  have hx' : x = ∫ q, g q := by
    rw [integral_complex_ofReal] at hβ'
    exact_mod_cast hβ'
  unfold B.normSq Formalism.QuantumDeterminants.jNormSq
  rw [hx', ofReal_integral_eq_lintegral_ofReal hgi
    (Filter.Eventually.of_forall fun q => mul_nonneg (CutBP.bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _))]

theorem normDegG_of_leaves [CompleteSpace Wp] [CompleteSpace Wq] (hJ : NormSquareTransferIdentity) (hC : CoefCC) (hA : BetaInfAbs)
    (hB : BetaInfCoef) (hL : B2.LemmaBAny) (hSch : SchurH) (hK : PI.KFinSmooth) (p : KB.Pl P Wp Wq) :
    NormDegG p := by
  intro F lam0 q0 hF
  obtain ⟨c, hc, -, -, hβ, -, -⟩ := hL P.k P.r Wp Wq p.T.base (Acc P.k P.r) (AB_le_Acc _ _)
  refine ⟨(c : ℝ), by exact_mod_cast hc, fun μ hμ hP => ?_⟩
  have hG := hF μ hμ hP.1
  have hcc := hC hK P.k P.r Wp Wq p.T.base _ _ _ _ _ _ _ (F.A μ) hG
  obtain ⟨hI, hE⟩ := hB hSch P.k P.r Wp Wq p.T.base _ _ _ _ _ _ _ (F.A μ) hG hP.2.1 hP.2.2
  have hinf := hA P.k P.r Wp Wq p.T.base (Acc P.k P.r) _ (AB_le_Acc _ _) hcc hI
  have hdeg : 0 < (F.A μ).deg p.T.base.μG := degPos_of hSch p F lam0 q0 hF μ hμ hP
  have hbeta : B.beta p.T.base (F.J p.T.base μ) (F.J p.T.base μ) =
      (((c : ℝ) * (F.A μ).deg p.T.base.μG : ℝ) : ℂ) := by
    rw [JFam.J_of_hc _ F _ hP.1, hβ _ _ hcc hcc, hinf, hE]
    push_cast
    ring
  rw [hJ P Wp Wq p, normSq_of_beta p.T.base _ _ (mul_pos (by exact_mod_cast hc) hdeg).ne' hbeta]

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopR
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem rDIdentSpec_of_R (hR : RDSOpR) (hRv : RDSOpRv) : RDIdentSpec :=
  rDIdentSpec_of_open spectral_operator_A_adjoint hR hRv spectral_operator_A spectral_pairing_adjoint spectral_quadratic_adjoint spectral_xi_test spectral_pairing_identity

theorem thmPActualCpt_of_R (hR : RDSOpR) (hRv : RDSOpRv) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_spec (rDIdentSpec_of_R hR hRv)

end Formalism.FourierDecayAlt.P.CutSE
end


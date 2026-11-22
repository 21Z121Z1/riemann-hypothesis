import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTest
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0011

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneCOfCharts
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def JacOneCFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) →
      PolId X u' μinf νinf a Ω₂ c → c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹

theorem jacOneCFor_of {Pr : ChartPred} (hK : KPos) (hR : LocRatioFor Pr) : JacOneCFor Pr := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨V, W, hVW, hsh, hlim⟩ := hR X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  set L : ℕ → ENNReal := fun n => μinf (BoxT X u' a (V n) (W n)) with hL
  set B : ℕ → ENNReal := fun n => νinf (W n) with hB
  set M : ℕ → ENNReal := fun n => X.measG.μGinf (TubeG X u' (V n)) with hM
  set A : ℕ → ENNReal := fun n => ∫⁻ T in W n, c T ∂νinf with hA

  have key : ∀ n, L n = A n * M n := by
    intro n
    obtain ⟨hWm, hWs, -, -, hU, hBm, hBI, -, hTm, -, hMt⟩ := hVW n
    have h := hid ((BoxT X u' a (V n) (W n)).indicator 1) (measurable_one.indicator hBm) (W n)
      hWs hWm
    have hsub : BoxT X u' a (V n) (W n) ⊆
        gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' (W n)) ∩ IndI X := by
      intro y hy
      refine ⟨?_, hBI hy⟩
      obtain ⟨T, hTW, g, -, rfl⟩ := hy
      refine ⟨T, hTW, ?_⟩
      rw [gramR_smul, hC.2.2.2 T (hΩ₂ (hWs hTW))]
    rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm, Set.inter_eq_left.2 hsub] at h
    have hin : ∀ T ∈ W n, ∫⁻ g, (BoxT X u' a (V n) (W n)).indicator 1 (g • rmulT X (a T) (Y0 X u'))
        ∂X.measG.μGinf = M n := by
      intro T hTW
      have hs := pre_box X u' hT hC (V n) (hWs.trans hΩ₂) hU T hTW
      have e : (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
          (BoxT X u' a (V n) (W n)).indicator (1 : TupI X → ENNReal) (g • rmulT X (a T) (Y0 X u'))) =
          (TubeG X u' (V n)).indicator 1 := by
        funext g
        by_cases hg : g ∈ TubeG X u' (V n)
        · have h4 : g • rmulT X (a T) (Y0 X u') ∈ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_mem hg, Set.indicator_of_mem h4]; rfl
        · have h4 : g • rmulT X (a T) (Y0 X u') ∉ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem h4]
      rw [e, lintegral_indicator_one hTm]
    rw [setLIntegral_congr_fun hWm (fun T hT' => by rw [hin T hT'])] at h
    rw [lintegral_mul_const' _ _ hMt.ne] at h
    exact h
  have hAt : ∀ n, A n ≠ ⊤ := by
    intro n hA'
    obtain ⟨-, -, -, -, -, -, -, hLt, -, hM0, -⟩ := hVW n
    have : L n = ⊤ := by rw [key n, hA', ENNReal.top_mul hM0.ne']
    exact absurd this hLt.ne
  have e1 : ∀ n, (L n).toReal / ((B n).toReal * (M n).toReal) = (A n).toReal / (B n).toReal := by
    intro n
    obtain ⟨-, -, hB0, hBt, -, -, -, -, -, hM0, hMt⟩ := hVW n
    have hMr : 0 < (M n).toReal := ENNReal.toReal_pos hM0.ne' hMt.ne
    rw [key n, ENNReal.toReal_mul]
    field_simp
  have hlim' : Tendsto (fun n => (L n).toReal / ((B n).toReal * (M n).toReal)) atTop (𝓝 (KVal X u')⁻¹) := hlim

  have hge : ∀ b : ENNReal, b < c (TI X u' hT) → b.toReal ≤ (KVal X u')⁻¹ := by
    intro b hb
    have hU : c ⁻¹' Set.Ioi b ∈ 𝓝 (TI X u' hT) := hcc (Ioi_mem_nhds hb)
    refine ge_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hlow : b * B n ≤ A n :=
      calc b * B n = ∫⁻ _ in W n, b ∂νinf := (setLIntegral_const _ _).symm
        _ ≤ A n := lintegral_mono_ae ((ae_restrict_iff' hWm).2 (Eventually.of_forall fun T hT' =>
            (hn hT').le))
    rw [e1 n, le_div_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (hAt n) hlow

  have hle : ∀ b : ENNReal, c (TI X u' hT) < b → b ≠ ⊤ → (KVal X u')⁻¹ ≤ b.toReal := by
    intro b hb hbt
    have hU : c ⁻¹' Set.Iio b ∈ 𝓝 (TI X u' hT) := hcc (Iio_mem_nhds hb)
    refine le_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hup : A n ≤ b * B n :=
      calc A n ≤ ∫⁻ _ in W n, b ∂νinf := lintegral_mono_ae ((ae_restrict_iff' hWm).2
            (Eventually.of_forall fun T hT' => (hn hT').le))
        _ = b * B n := setLIntegral_const _ _
    rw [e1 n, div_le_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hbt hBt.ne) hup

  have hfin : c (TI X u' hT) ≠ ⊤ := by
    intro htop
    have h1 := hge (ENNReal.ofReal ((KVal X u')⁻¹ + 1)) (by rw [htop]; exact ENNReal.ofReal_lt_top)
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    linarith
  set c₀ : ℝ := (c (TI X u' hT)).toReal with hc₀
  have hle' : c₀ ≤ (KVal X u')⁻¹ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hcε : c₀ - ε ≤ 0
    · have : 0 < (KVal X u')⁻¹ := inv_pos.2 hK0
      linarith
    · push_neg at hcε
      have hb : ENNReal.ofReal (c₀ - ε) < c (TI X u' hT) := by
        rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      have := hge _ hb
      rw [ENNReal.toReal_ofReal hcε.le] at this
      linarith
  have hge' : (KVal X u')⁻¹ ≤ c₀ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hc0 : 0 ≤ c₀ := ENNReal.toReal_nonneg
    have hb : c (TI X u' hT) < ENNReal.ofReal (c₀ + ε) := by
      rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have := hle _ hb ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hceq : c₀ = (KVal X u')⁻¹ := le_antisymm hle' hge'
  rw [← ENNReal.ofReal_toReal hfin, ← hc₀, hceq, ENNReal.ofReal_inv_of_pos hK0]

theorem jacOneC_of_charts (hK : KPos) (hU : UnimodInf) (hW : WittNear) (hG : GoodChartEx) : JacOneC := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨Ω', a₂, hC₂, hgood⟩ := hG X u' ψ hT μinf νinf fibInf hP
  have hev : ∀ᶠ T in 𝓝 (TI X u' hT), ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u') := by
    obtain ⟨ι, _, κ, -, η, _, eT, eH, cμ, cν, Ψ', U, -, -, -, -, -, -, -, -, hev0, -⟩ := hgood
    filter_upwards [hev0, hC.1, hC₂.1] with T h1 h2 h3
    exact hW X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T ⟨h2, h3⟩ h1.1
  set Ω₃ := Ω₂ ∩ Ω' ∩ {T | ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')} with hΩ₃
  have hΩ₃n : Ω₃ ∈ 𝓝 (TI X u' hT) := inter_mem (inter_mem hΩ₂n hC₂.1) hev
  have hid₂ : PolId X u' μinf νinf a₂ Ω₃ c := by
    intro φ hφ S hS hSm
    rw [hid φ hφ S (hS.trans (Set.inter_subset_left.trans Set.inter_subset_left)) hSm]
    refine setLIntegral_congr_fun hSm (fun T hT' => ?_)
    obtain ⟨h, eh⟩ := (hS hT').2
    rw [eh]
    congr 1
    have e : ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
        φ (g • h • rmulT X (a₂ T) (Y0 X u')) = (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) (g * h) := by
      intro g; simp only [mul_smul]
    simp_rw [e]
    exact hU X u' ψ hT μinf νinf fibInf hP (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) h
  exact jacOneCFor_of hK (locRatioFor_of hK splitAsym_good) X u' ψ hT μinf νinf fibInf hP Ω' a₂ hC₂ hgood Ω₃
    (Set.inter_subset_left.trans Set.inter_subset_right) hΩ₃n c hcc hid₂

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPol
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def cTI {D : D7} (X : HidaSetting D) (a : MfI X) : MfI X :=
  Matrix.transpose (a.map (sigR (Ainf X.B.I.F) X.B.I.cm.sig))

def RmulFacts : Prop := ∀ {D : D7} (X : HidaSetting D),
    (∀ a : MfI X, Measurable (rmulT X a)) ∧ (∀ a b : MfI X, ∀ Y, rmulT X a (rmulT X b Y) = rmulT X (b * a) Y) ∧
    (∀ (g : GI X) (a : MfI X) (Y : TupI X), g • rmulT X a Y = rmulT X a (g • Y)) ∧
    (∀ (a : MfI X) (Y : TupI X), gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X a Y) =
      cTI X a * gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y * a) ∧
    (∀ a b : MfI X, cTI X (a * b) = cTI X b * cTI X a) ∧ cTI X 1 = 1 ∧
    (∀ K : Set (TupI X), IsCompact K → MeasurableSet K) ∧ (∀ a : MfI X, Continuous (rmulT X a))

def NearFacts : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a →
    ∃ Ω₁ ⊆ Ω, Ω₁ ∈ 𝓝 (TI X u' hT) ∧ ∀ T ∈ Ω₁, IsUnit (a T) ∧
      ∀ Y : TupI X, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y = (T : Matrix _ _ _) → Y ∈ IndI X

def FibAllT : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ T : HmI X, InvI X (fibInf T) ∧ LFI X (fibInf T)

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperOne
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ProperOne : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ K : Set (TupI X), IsCompact K →
      ∃ C : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J), IsCompact C ∧
        ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • Y0 X u' ∈ K → g ∈ C

def InvNbhd : Prop := ∀ {D : D7} (X : HidaSetting D),
    ∃ N ∈ 𝓝 (1 : MfI X), ∃ Nc : Set (MfI X), IsCompact Nc ∧ ∀ b ∈ N, ∃ c ∈ Nc, c * b = 1

theorem rmulT_rmulT {D : D7} (X : HidaSetting D) (b c : MfI X) (Y : TupI X) :
    rmulT X c (rmulT X b Y) = rmulT X (b * c) Y := by
  funext a i
  simp only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem smul_rmulT {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (b : MfI X)
    (Y : TupI X) : g • rmulT X b Y = rmulT X b (g • Y) := by
  change (fun a => ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) _).mulVec (rmulT X b Y a)) =
    rmulT X b (fun a => ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) _).mulVec (Y a))
  funext a i
  simp only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem continuous_right_mul_tuple {D : D7} (X : HidaSetting D) :
    Continuous (fun p : MfI X × TupI X => rmulT X p.1 p.2) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [rmulT]
  exact continuous_finsetSum _ fun c _ =>
    ((continuous_apply_apply c a).comp continuous_fst).mul ((continuous_apply_apply c i).comp continuous_snd)

theorem properOrb_of_one (h1 : ProperOne) (hI : InvNbhd) : ProperOrb := by
  intro D X u' ψ hT μinf νinf fibInf hH K hK _
  obtain ⟨N, hN, Nc, hNc, hNi⟩ := hI X
  have hK' : IsCompact ((fun p : MfI X × TupI X => rmulT X p.1 p.2) '' (Nc ×ˢ K)) :=
    (hNc.prod hK).image (continuous_right_mul_tuple X)
  obtain ⟨C, hC, hgC⟩ := h1 X u' ψ hT μinf νinf fibInf hH _ hK'
  refine ⟨N, hN, C, hC, fun b hb g hg => hgC g ?_⟩
  obtain ⟨c, hc, hcb⟩ := hNi b hb
  have hbc : b * c = 1 := mul_eq_one_comm.1 hcb
  refine ⟨(c, g • rmulT X b (Y0 X u')), ⟨hc, hg⟩, ?_⟩
  show rmulT X c (g • rmulT X b (Y0 X u')) = g • Y0 X u'
  rw [smul_rmulT, rmulT_rmulT, hbc, rmulT_one]

theorem constTest_of_polar_one (hP : PolarLoc) (h1 : ProperOne) (hI : InvNbhd) : ConstTest :=
  constTest_of_polar_prop hP (properOrb_of_one h1 hI)

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdCoord
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Coord

variable {F : Type} [Field F] [NumberField F]

def complReal (v : InfinitePlace F) (hv : v.IsReal) : v.Completion ≃ₜ ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toEquiv.toHomeomorphOfIsInducing (by
    have hf : (⇑(InfinitePlace.Completion.ringEquivRealOfIsReal hv).toEquiv) =
        ⇑(InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) :=
      funext fun x => InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv x
    rw [hf]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.isInducing)

theorem complReal_add (v : InfinitePlace F) (hv : v.IsReal) (x y : v.Completion) :
    complReal v hv (x + y) = complReal v hv x + complReal v hv y :=
  map_add (InfinitePlace.Completion.ringEquivRealOfIsReal hv) x y

def ainfReal (hF : ∀ v : InfinitePlace F, v.IsReal) : InfiniteAdeleRing F ≃ₜ (InfinitePlace F → ℝ) :=
  Homeomorph.piCongrRight fun v => complReal v (hF v)

theorem ainfReal_add (hF : ∀ v : InfinitePlace F, v.IsReal) (x y : InfiniteAdeleRing F) :
    ainfReal hF (x + y) = ainfReal hF x + ainfReal hF y := by
  funext v
  exact complReal_add v (hF v) (x v) (y v)

end Coord

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def tensCoord : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
  let e := (Module.Free.chooseBasis R (R ⊗[F] E)).equivFun
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem tensCoord_add (x y : R ⊗[F] E) : tensCoord R (x + y) = tensCoord R x + tensCoord R y :=
  map_add (Module.Free.chooseBasis R (R ⊗[F] E)).equivFun x y

end Tens

def flat4 (A B C P : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype P] :
    (A → B → C → P → ℝ) ≃ₜ EuclideanSpace ℝ (A × B × C × P) where
  toFun f := (EuclideanSpace.equiv (A × B × C × P) ℝ).symm (fun k => f k.1 k.2.1 k.2.2.1 k.2.2.2)
  invFun u a b c d := (EuclideanSpace.equiv (A × B × C × P) ℝ u) (a, b, c, d)
  left_inv f := by funext a b c d; simp
  right_inv u := by ext k; simp
  continuous_toFun := (EuclideanSpace.equiv (A × B × C × P) ℝ).symm.continuous.comp (continuous_pi fun k =>
    (continuous_apply k.2.2.2).comp ((continuous_apply k.2.2.1).comp ((continuous_apply k.2.1).comp
      (continuous_apply k.1))))
  continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_pi fun c => continuous_pi fun d =>
    (continuous_apply (a, b, c, d)).comp (EuclideanSpace.equiv (A × B × C × P) ℝ).continuous

theorem flatten_four_add (A B C P : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype P] (f g : A → B → C → P → ℝ) :
    flat4 A B C P (f + g) = flat4 A B C P f + flat4 A B C P g := by
  ext k
  simp [flat4]

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittNr
section
noncomputable section

namespace PI.AprimeInfW

open Matrix

section Gen

variable {A : Type} [CommRing A] (σ : A →+* A) {m M : Type} [Fintype m] [DecidableEq m] [Fintype M] [DecidableEq M]

theorem witt_span (hσ : ∀ x, σ (σ x) = x) (K : Matrix M M A) (hK : Formalism.UG.cT σ K = K) (Y : Matrix m M A)
    (Gi : Matrix m m A) (hGi1 : Gi * (Y.map σ * K * Yᵀ) = 1) (hGi2 : (Y.map σ * K * Yᵀ) * Gi = 1)
    (e : Matrix m m A) (he : Formalism.UG.cT σ e * (Y.map σ * K * Yᵀ) * e = Y.map σ * K * Yᵀ) :
    ∃ h h' : Matrix M M A, h * h' = 1 ∧ h' * h = 1 ∧ Formalism.UG.cT σ h * K * h = K ∧ Y * hᵀ = eᵀ * Y := by
  set Ys := Y.map σ with hYs
  set G := Ys * K * Yᵀ with hG
  have cT_add : ∀ {p q : Type} (P Q : Matrix p q A), Formalism.UG.cT σ (P + Q) = Formalism.UG.cT σ P + Formalism.UG.cT σ Q := by
    intro p q P Q; ext i j; simp [Formalism.UG.cT]
  have cT_sub : ∀ {p q : Type} (P Q : Matrix p q A), Formalism.UG.cT σ (P - Q) = Formalism.UG.cT σ P - Formalism.UG.cT σ Q := by
    intro p q P Q; ext i j; simp [Formalism.UG.cT]
  have cTYs : Formalism.UG.cT σ Ys = Yᵀ := by ext i j; simp [Formalism.UG.cT, hYs, hσ]
  have cTYt : Formalism.UG.cT σ Yᵀ = Ys := by ext i j; simp [Formalism.UG.cT, hYs]
  have hGh : Formalism.UG.cT σ G = G := by
    rw [hG, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTYt, hK, cTYs, Matrix.mul_assoc]
  have hGih : Formalism.UG.cT σ Gi = Gi := by
    have h1 : Formalism.UG.cT σ Gi * G = 1 := by
      rw [← hGh, ← Formalism.UG.cT_mul, hGi2, Formalism.UG.cT_one]
    calc Formalism.UG.cT σ Gi = Formalism.UG.cT σ Gi * (G * Gi) := by rw [hGi2, Matrix.mul_one]
      _ = Gi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hGiGx : ∀ x : Matrix m m A, Gi * (G * x) = x := fun x => by rw [← Matrix.mul_assoc, hGi1, Matrix.one_mul]

  set ei := Gi * Formalism.UG.cT σ e * G with hei
  have hei1 : ei * e = 1 := by
    rw [hei, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT σ e), he, hGi1]
  have hei2 : e * ei = 1 := mul_eq_one_comm.1 hei1

  have keyprod : ∀ C D : Matrix m m A, (Yᵀ * C * (Ys * K)) * (Yᵀ * D * (Ys * K)) = Yᵀ * (C * G * D) * (Ys * K) := by
    intro C D; simp only [hG, Matrix.mul_assoc]
  have E1 : ∀ C D : Matrix m m A, (1 + Yᵀ * C * (Ys * K)) * (1 + Yᵀ * D * (Ys * K)) =
      1 + Yᵀ * (C + D + C * G * D) * (Ys * K) := by
    intro C D
    rw [show Yᵀ * (C + D + C * G * D) * (Ys * K) = Yᵀ * C * (Ys * K) + Yᵀ * D * (Ys * K) +
        Yᵀ * (C * G * D) * (Ys * K) by simp only [Matrix.mul_add, Matrix.add_mul], ← keyprod]
    noncomm_ring
  have inner : ∀ x y : Matrix m m A, x * y = 1 →
      (x - 1) * Gi + (y - 1) * Gi + (x - 1) * Gi * G * ((y - 1) * Gi) = 0 := by
    intro x y hxy
    have h1 : (x - 1) * Gi * G * ((y - 1) * Gi) = (x - 1) * (y - 1) * Gi := by
      rw [Matrix.mul_assoc (x - 1) Gi G, hGi1, Matrix.mul_one, Matrix.mul_assoc]
    have h2 : (x - 1) * (y - 1) = x * y - x - y + 1 := by noncomm_ring
    rw [h1, h2, hxy]; noncomm_ring
  refine ⟨1 + Yᵀ * ((e - 1) * Gi) * (Ys * K), 1 + Yᵀ * ((ei - 1) * Gi) * (Ys * K), ?_, ?_, ?_, ?_⟩
  · rw [E1, inner e ei hei2]; simp
  · rw [E1, inner ei e hei1]; simp
  · have hcT : Formalism.UG.cT σ (1 + Yᵀ * ((e - 1) * Gi) * (Ys * K)) =
        1 + K * Yᵀ * (Gi * (Formalism.UG.cT σ e - 1)) * Ys := by
      rw [cT_add, Formalism.UG.cT_one]
      congr 1
      simp only [Formalism.UG.cT_mul, cT_sub, Formalism.UG.cT_one, hK, cTYs, cTYt, hGih, Matrix.mul_assoc]
    rw [hcT]
    have hin : (e - 1) * Gi + Gi * (Formalism.UG.cT σ e - 1) + Gi * (Formalism.UG.cT σ e - 1) * G * ((e - 1) * Gi) = 0 := by
      have h1 : Gi * (Formalism.UG.cT σ e - 1) * G * ((e - 1) * Gi) =
          Gi * (Formalism.UG.cT σ e * G * e) * Gi - Gi * Formalism.UG.cT σ e * (G * Gi) - Gi * (G * (e * Gi)) +
            Gi * (G * Gi) := by noncomm_ring
      rw [h1, he]
      simp only [hGi1, hGi2, hGiGx, Matrix.one_mul, Matrix.mul_one]
      noncomm_ring
    have expand : (1 + K * Yᵀ * (Gi * (Formalism.UG.cT σ e - 1)) * Ys) * K * (1 + Yᵀ * ((e - 1) * Gi) * (Ys * K)) =
        K + K * (Yᵀ * ((e - 1) * Gi + Gi * (Formalism.UG.cT σ e - 1) +
          Gi * (Formalism.UG.cT σ e - 1) * G * ((e - 1) * Gi)) * (Ys * K)) := by
      simp only [hG, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [expand, hin]; simp
  · have h1 : ((e - 1) * Gi * G)ᵀ = (e - 1)ᵀ := by rw [Matrix.mul_assoc, hGi1, Matrix.mul_one]
    calc Y * (1 + Yᵀ * ((e - 1) * Gi) * (Ys * K))ᵀ = Y + ((e - 1) * Gi * G)ᵀ * Y := by
          simp only [hG, Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_one,
            Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = eᵀ * Y := by
          rw [h1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul]; abel

end Gen

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem wittNear_span : WittNear := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTΩ hU
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  set R := Ainf X.B.I.F
  set σ := sigR (F := X.B.I.F) (E := X.B.I.E) R X.B.I.cm.sig with hσdef
  have hσ : ∀ x, σ (σ x) = x := sq_sig_inv R X.B.I.cm.sig (sig_invI X)
  set K := JR (F := X.B.I.F) R X.B.I.J with hKdef
  have hK : Formalism.UG.cT σ K = K := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hKdef, JR, hσdef]
    rw [← J_hermI X i j]
    simp [sigR, inclR]
  set Y : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin X.B.I.n) (R ⊗[X.B.I.F] X.B.I.E) := Y0 X u' with hY
  set G0 := gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) with hG0
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hu : IsUnit G0.det := isUnit_iff_ne_zero.2 hdet
  have hGY : Y.map σ * K * Yᵀ = G0.map (inclR R) := by
    rw [← sq_gramR_mat R X.B.I.cm.sig X.B.I.J Y K rfl]
    exact gramR_ratTup R X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
  set Gi := G0⁻¹.map (inclR (F := X.B.I.F) (E := X.B.I.E) R) with hGi
  have hGi1 : Gi * (Y.map σ * K * Yᵀ) = 1 := by
    rw [hGY, hGi, ← Matrix.map_mul, Matrix.nonsing_inv_mul G0 hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGi2 : (Y.map σ * K * Yᵀ) * Gi = 1 := by
    rw [hGY, hGi, ← Matrix.map_mul, Matrix.mul_nonsing_inv G0 hu, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨w, hw⟩ := hU
  set e : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (R ⊗[X.B.I.F] X.B.I.E) :=
    a T * (↑w⁻¹ : MfI X) with he_def
  have hgr : ∀ b : MfI X, gramR R X.B.I.cm.sig X.B.I.J (rmulT X b (Y0 X u')) =
      Formalism.UG.cT σ b * (Y.map σ * K * Yᵀ) * b := by
    intro b
    rw [← sq_gramR_mat R X.B.I.cm.sig X.B.I.J Y K rfl]
    exact sq_gramR_rmul R X.B.I.cm.sig X.B.I.J b Y
  have hTa : Formalism.UG.cT σ (a T) * (Y.map σ * K * Yᵀ) * a T =
      Formalism.UG.cT σ (a₂ T) * (Y.map σ * K * Yᵀ) * a₂ T := by
    rw [← hgr, ← hgr, hC.2.2.2 T hTΩ.1, hC₂.2.2.2 T hTΩ.2]
  have hww : Formalism.UG.cT σ (↑w⁻¹ : MfI X) * Formalism.UG.cT σ (↑w : MfI X) = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  have he : Formalism.UG.cT σ e * (Y.map σ * K * Yᵀ) * e = Y.map σ * K * Yᵀ := by
    rw [he_def, Formalism.UG.cT_mul]
    calc Formalism.UG.cT σ (↑w⁻¹ : MfI X) * Formalism.UG.cT σ (a T) * (Y.map σ * K * Yᵀ) *
          (a T * (↑w⁻¹ : MfI X))
        = Formalism.UG.cT σ (↑w⁻¹ : MfI X) *
          (Formalism.UG.cT σ (a T) * (Y.map σ * K * Yᵀ) * a T) * (↑w⁻¹ : MfI X) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hTa, ← hw]
          simp only [← Matrix.mul_assoc]
          rw [hww, Matrix.one_mul, Matrix.mul_assoc _ (↑w : MfI X), Units.mul_inv, Matrix.mul_one]
  obtain ⟨h, h', hh1, hh2, hhu, hhY⟩ := witt_span σ hσ K hK Y Gi hGi1 hGi2 e he
  let gl : GL (Fin X.B.I.n) (R ⊗[X.B.I.F] X.B.I.E) := ⟨h, h', hh1, hh2⟩
  have hmem : gl ∈ HR R X.B.I.cm.sig X.B.I.J := hhu
  refine ⟨⟨gl, hmem⟩, ?_⟩
  have key : (a₂ T)ᵀ * Y * hᵀ = (a T)ᵀ * Y := by
    rw [Matrix.mul_assoc, hhY, ← Matrix.mul_assoc, ← Matrix.transpose_mul, he_def, Matrix.mul_assoc, ← hw,
      Units.inv_mul, Matrix.mul_one]
  funext b i
  change rmulT X (a T) (Y0 X u') b i = Matrix.mulVec h (rmulT X (a₂ T) (Y0 X u') b) i
  have k2 := congrFun (congrFun key b) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at k2
  simp only [rmulT, Matrix.mulVec, dotProduct]
  rw [← k2]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

theorem jacOne_of_good (hK : KPos) (hU : UnimodInf) (hG : GoodChartEx) : JacOne :=
  jacOne_of_charts hK hU wittNear_span hG

end PI.AprimeInfW
end
end


import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0003
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.FormalDegreeBessel.Bundle0002

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableLoc
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem mem_level_zero_of_mem_group {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

def LocSm (g₀ : B.Mat k r) (h : B.Mat k r → E') : Prop :=
  ∃ (U : Set (B.Mat k r)) (F : B.Mat k r → E'), IsOpen U ∧ g₀ ∈ U ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧ ∀ x ∈ U, x ∈ B.GV k r → h x = F x

theorem locSm_of_ckOn {UU : Set (B.Mat k r)} {h : B.Mat k r → E'} (hh : B.CkOn ⊤ UU h) {g₀ : B.Mat k r}
    (hg : g₀ ∈ UU) : LocSm g₀ h := hh g₀ hg

theorem locSm_zero (g₀ : B.Mat k r) : LocSm g₀ (fun _ => (0 : E')) :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem locSm_add {g₀ : B.Mat k r} {h₁ h₂ : B.Mat k r → E'} (h1 : LocSm g₀ h₁) (h2 : LocSm g₀ h₂) :
    LocSm g₀ (fun x => h₁ x + h₂ x) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := h1
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := h2
  exact ⟨U₁ ∩ U₂, fun x => F₁ x + F₂ x, o₁.inter o₂, ⟨m₁, m₂⟩,
    (c₁.mono Set.inter_subset_left).add (c₂.mono Set.inter_subset_right),
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩

theorem locSm_smul {g₀ : B.Mat k r} {h : B.Mat k r → E'} (c : ℂ) (h1 : LocSm g₀ h) :
    LocSm g₀ (fun x => c • h x) := by
  obtain ⟨U, F, o, m, cd, e⟩ := h1
  exact ⟨U, fun x => c • F x, o, m, cd.const_smul c, fun x hx hxG => by simp only [e x hx hxG]⟩

theorem locSm_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] {g₀ : B.Mat k r}
    {a : B.Mat k r → (E' →L[ℂ] E₂)} {φ : B.Mat k r → E'} (ha : LocSm g₀ a) (hφ : LocSm g₀ φ) :
    LocSm g₀ (fun x => a x (φ x)) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := ha
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := hφ
  refine ⟨U₁ ∩ U₂, fun x => F₁ x (F₂ x), o₁.inter o₂, ⟨m₁, m₂⟩, ?_,
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩
  have c₁' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (F₁ x).restrictScalars ℝ) (U₁ ∩ U₂) :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E' E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (c₁.mono Set.inter_subset_left))
  exact c₁'.clm_apply (c₂.mono Set.inter_subset_right)

theorem locSm_listSum {ι : Type*} {g₀ : B.Mat k r} (l : List ι) (φ : ι → B.Mat k r → E')
    (h : ∀ i ∈ l, LocSm g₀ (φ i)) : LocSm g₀ (fun x => (l.map fun i => φ i x).sum) := by
  induction l with
  | nil => simpa using locSm_zero (E' := E') g₀
  | cons a l ih =>
    simpa using locSm_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem ckOn_Rw_top {f : B.Mat k r → E'} (hf : B.CkOn ⊤ (B.GV k r) f) (w : List (B.Mat k r))
    (hw : ∀ X ∈ w, B.inLie k r X) : B.CkOn ⊤ (B.GV k r) (B.Rw w f) := by
  induction w with
  | nil => exact hf
  | cons X w ih =>
    have ih' := ih (fun Y hY => hw Y (by simp [hY]))
    show B.CkOn ⊤ (B.GV k r) (RdV X (B.Rw w f))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV (m := ⊤) (hw X (by simp)) (by rw [top_add]; exact ih')

theorem locSm_smoothLev {O : Set (B.Mat k r)} {h : B.Mat k r → E'}
    (hh : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → LocSm g₀ h) : Q.SmoothLev k r 0 O h := by
  intro g₀ hg₀
  obtain ⟨U, F, o, m, c, e⟩ := hh g₀ hg₀.1.1 hg₀.2
  exact ⟨U, F, o, m, c, fun x hx hxG => e x hx hxG.1⟩

end loc

theorem extension_locality_holds : ExtLoc := by
  intro k r E' _ _ O J hO hJ g₀ hg₀ hg₀O
  obtain ⟨U₀, F, hU₀, hgU₀, hF, hFJ⟩ := hJ g₀ ⟨mem_level_zero_of_mem_group hg₀, hg₀O⟩
  have hV : U₀ ∩ O ∈ nhds g₀ := (hU₀.inter hO).mem_nhds ⟨hgU₀, hg₀O⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  let b : ContDiffBump g₀ := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩
  have hts : tsupport (fun x => b x • F x) ⊆ Metric.closedBall g₀ (2 * ε / 3) :=
    (tsupport_smul_subset_left _ _).trans b.tsupport_eq.subset
  have hcb : Metric.closedBall g₀ (2 * ε / 3) ⊆ U₀ ∩ O := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  refine ⟨fun x => b x • F x, Metric.ball g₀ (ε / 3), ?_, ?_, fun x hx => (hcb (hts hx)).2,
    Metric.isOpen_ball, Metric.mem_ball_self (by positivity), ?_⟩
  · intro g _
    refine ⟨Set.univ, fun x => b x • F x, isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    apply ContDiff.contDiffOn
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U₀
    · exact ((b.contDiff.contDiffOn).smul hF).contDiffAt (hU₀.mem_nhds hx)
    · have hx' : x ∉ tsupport (fun x => b x • F x) := fun h => hx (hcb (hts h)).1
      exact (contDiffAt_const (c := (0 : E'))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 hx')
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall g₀ (2 * ε / 3)) (isClosed_tsupport _) hts
  · intro x hx hxG
    have hb : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U₀ := (hball (Metric.ball_subset_ball (by linarith) hx)).1
    simp only [hb, one_smul]
    exact (hFJ x hxU (mem_level_zero_of_mem_group hxG)).symm

theorem smooth_operators_holds : SmoothOps := by
  intro k r Wp Wq _ _ _ _ _ D Θ O hO hOP hΘ f hf hs
  have hsupp : closure {g | g ∈ B.GV k r ∧ f g ≠ 0} ⊆ B.GPos D := by
    intro x hx
    have hxG : x ∈ B.GV k r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f := closure_mono (fun y hy => hy.2) hx
    exact hOP x (hs hxT) hxG
  constructor
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    exact locSm_clm (locSm_of_ckOn (hΘ T hT).1 (hOP g₀ hg₀O hg₀))
      (locSm_of_ckOn (ckOn_Rw_top hf T.word T.word_lie) hg₀)
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    apply locSm_smul
    have hc : B.CkOn ⊤ (B.GV k r) (fun x => T.coefAdj x (f x)) :=
      Formalism.FourierDecayAlt.P.B5.ckOn_coef (hΘ T hT).2 hf hsupp
    exact locSm_of_ckOn (ckOn_Rw_top hc T.word.reverse
      (fun X hX => T.word_lie X (List.mem_reverse.1 hX))) hg₀

theorem omP_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    OmP S T v = Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' := by
  ext g
  constructor
  · rintro ⟨hG, hD⟩
    refine ⟨fun l hl => ?_, hG⟩
    rcases Nat.eq_zero_or_pos l.val with h0 | hpos
    · have : l = ⟨0, by omega⟩ := Fin.ext h0
      rw [this]
      rw [show Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨0, by omega⟩ = 1 by
        unfold Dmin; exact Matrix.det_isEmpty]
      exact one_ne_zero
    · have := hD ⟨l.val - 1, by omega⟩
      have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (S.G.r + 2)) = l := Fin.ext (by simp; omega)
      simpa [e] using this
  · rintro ⟨hD, hG⟩
    exact ⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by have := a.isLt; simp only [Fin.val_mk]; omega)⟩

theorem positive_domain_condition_holds : OmPDom := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v
  refine ⟨?_, fun g hg hgG => ⟨hgG, hg.1⟩⟩
  rw [omP_eq]
  exact Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (T v).base.z_mem (T v).base.z'_mem

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gcut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gcut_ckOn_smul {m : ℕ∞} {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn m (B.GV k r) F) :
    B.CkOn m (B.GV k r) (fun g => a g • F g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hF g₀ hg₀
  refine ⟨U, fun g => a g • f' g, hU, hgU,
    ((ha.of_le (by exact_mod_cast le_top)).contDiffOn).smul hc, fun g hg hG => ?_⟩
  simp only [hff g hg hG]

theorem gcut_sum_const {X : Type*} (c : ℕ) (l : List X) :
    (((l.map (fun _ => c)).sum : ℕ) : ℝ) = (c : ℝ) * l.length := by
  have h : ∀ l : List X, (l.map (fun _ => c)).sum = c * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  rw [h]; push_cast; ring

theorem gcut_leib {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a) (c n : ℕ) (Ca : ℝ)
    (hWB : PI.UnitaryCorollaryDerivatives.WB (fun _ => c) a n Ca 0)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F) {A Bg : ℝ} (hc : (c : ℝ) ≤ Bg)
    (hFg : ∀ m : ℕ, B.InCC (A - Bg * m) m F) :
    B.InCC (A - Bg * n) n (fun g => a g • F g) := by
  choose cF hcF using hFg
  set K : ℝ := ∑ j ∈ Finset.range (n + 1), |cF j| with hK
  have hKj : ∀ j ≤ n, |cF j| ≤ K := fun j hj =>
    Finset.single_le_sum (f := fun j => |cF j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBg : 0 ≤ Bg := le_trans (Nat.cast_nonneg c) hc
  refine ⟨2 ^ n * (|Ca| * K), gcut_ckOn_smul ha (sCkOn_mono le_top hF), fun u v hu hv hl g hg => ?_⟩
  set L : ℂ →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) with hL
  set a' : B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun h => L (a h) with ha'
  have hfun : (fun g => a g • F g) = ap a' F := by funext h; simp [ap, ha', hL]
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hca : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a' := (L.restrictScalars ℝ).contDiff.comp ha
  have hP : Pr (∅ : Set (B.Mat k r)) (B.GV k r) ((wL u ++ wR v).length : ℕ) a' F :=
    ⟨PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff hca, sCkOn_mono le_top hF, fun _ _ h => absurd h (Set.notMem_empty _)⟩
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  have hLn : ∀ x : ℂ, ‖L x‖ ≤ ‖x‖ := by
    intro x
    have : L x = x • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := by simp [hL]
    rw [this, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_id_le)
  have hw : (wL u ++ wR v).length = u.length + v.length := len_LR u v
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg
    (|Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) (wL u ++ wR v) a' F hlie hP (by
      intro w₁ w₂ hs₁ hs₂ hl₁₂
      obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
      obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
      rw [len_LR, len_LR] at hl₁₂
      have hl₁ : u₁.length + v₁.length ≤ n := by
        have := hu₁.length_le; have := hv₁.length_le; omega
      have hl₂ : u₂.length + v₂.length ≤ n := by
        have := hu₂.length_le; have := hv₂.length_le; omega
      have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
      have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
      have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
      have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
      have ea : Dw (wL u₁ ++ wR v₁) a' g = L (Dw (wL u₁ ++ wR v₁) a g) :=
        PI.UnitaryCorollaryDerivatives.Dw_clm L _ (lie_LR (unit_lie hu₁') (unit_lie hv₁'))
          (PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff ha) g hg
      set L₁ : ℝ := ((u₁.length + v₁.length : ℕ) : ℝ) with hL₁
      set L₂ : ℝ := ((u₂.length + v₂.length : ℕ) : ℝ) with hL₂
      have b1 : ‖Dw (wL u₁ ++ wR v₁) a' g‖ ≤ |Ca| * B.gN g ^ (Bg * L₁) := by
        rw [ea]
        refine (hLn _).trans ?_
        rw [← dLR_eq]
        have h1 := hWB u₁ v₁ hu₁' hv₁' hl₁ g hg
        rw [gcut_sum_const, List.length_append, zero_add] at h1
        have h1' : ‖B.dLR u₁ v₁ a g‖ ≤ Ca * B.gN g ^ ((c : ℝ) * L₁) := by
          rw [hL₁]; exact h1
        have h2 : B.gN g ^ ((c : ℝ) * L₁) ≤ B.gN g ^ (Bg * L₁) :=
          Real.rpow_le_rpow_of_exponent_le hg1 (mul_le_mul_of_nonneg_right hc (by rw [hL₁]; positivity))
        calc _ ≤ Ca * B.gN g ^ ((c : ℝ) * L₁) := h1'
          _ ≤ |Ca| * B.gN g ^ ((c : ℝ) * L₁) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _)
          _ ≤ |Ca| * B.gN g ^ (Bg * L₁) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have b2 : ‖Dw (wL u₂ ++ wR v₂) F g‖ ≤ K * B.gN g ^ (Bg * L₂ - A) := by
        rw [← dLR_eq]
        have h1 := (hcF (u₂.length + v₂.length)).2 u₂ v₂ hu₂' hv₂' le_rfl g hg
        have e : B.gN g ^ (Bg * L₂ - A) * B.gN g ^ (A - Bg * L₂) = 1 := by
          rw [← Real.rpow_add hp]; simp
        have h4 : ‖B.dLR u₂ v₂ F g‖ = B.gN g ^ (Bg * L₂ - A) * (B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ F g‖) := by
          rw [← mul_assoc, e, one_mul]
        rw [h4]
        have h5 : B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ F g‖ ≤ K := by
          refine le_trans ?_ (hKj _ hl₂)
          refine le_trans ?_ (le_abs_self _)
          simpa [hL₂] using h1
        calc _ ≤ B.gN g ^ (Bg * L₂ - A) * K := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp.le _)
          _ = K * B.gN g ^ (Bg * L₂ - A) := mul_comm _ _
      have hsum : Bg * L₁ + (Bg * L₂ - A) = Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A := by
        rw [← hl₁₂, hL₁, hL₂]; push_cast; ring
      calc ‖Dw (wL u₁ ++ wR v₁) a' g‖ * ‖Dw (wL u₂ ++ wR v₂) F g‖
          ≤ (|Ca| * B.gN g ^ (Bg * L₁)) * (K * B.gN g ^ (Bg * L₂ - A)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hp.le _))
        _ = |Ca| * K * (B.gN g ^ (Bg * L₁) * B.gN g ^ (Bg * L₂ - A)) := by ring
        _ = |Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) := by
            rw [← Real.rpow_add hp, hsum])
  rw [hfun, dLR_eq]
  have hlen : ((wL u ++ wR v).length : ℕ) ≤ n := by rw [hw]; exact hl
  have e2 : B.gN g ^ (A - Bg * n) * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) ≤ 1 := by
    rw [← Real.rpow_add hp]
    refine Real.rpow_le_one_of_one_le_of_nonpos hg1 ?_
    have : (((wL u ++ wR v).length : ℕ) : ℝ) ≤ n := by exact_mod_cast hlen
    nlinarith
  have e3 : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hlen
  have hCK : 0 ≤ |Ca| * K := mul_nonneg (abs_nonneg _) hK0
  calc B.gN g ^ (A - Bg * n) * ‖Dw (wL u ++ wR v) (ap a' F) g‖
      ≤ B.gN g ^ (A - Bg * n) * (2 ^ (wL u ++ wR v).length *
          (|Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
    _ = 2 ^ (wL u ++ wR v).length * (|Ca| * K) *
          (B.gN g ^ (A - Bg * n) * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) := by ring
    _ ≤ 2 ^ (wL u ++ wR v).length * (|Ca| * K) * 1 :=
        mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hCK)
    _ ≤ 2 ^ n * (|Ca| * K) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right e3 hCK

theorem gcut_graded (z z' : Fin (2 * r + k + 1) → ℂ) (h : ℝ → ℝ) (ε : ℝ) (hh : U.IsCutG ε h) {A Bg : ℝ}
    (hBg : 2 * ((r : ℝ) + 1) ≤ Bg) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F)
    (hFg : ∀ m : ℕ, B.InCC (A - Bg * m) m F) :
    B.CkOn ⊤ (B.GV k r) (fun g => ((h (Gf k r z z' g) : ℝ) : ℂ) • F g) ∧
      ∀ m : ℕ, B.InCC (A - Bg * m) m (fun g => ((h (Gf k r z z' g) : ℝ) : ℂ) • F g) := by
  have hW := PI.UnitaryCorollaryDerivatives.gfWB_of PI.UnitaryCorollaryDerivatives.generating_function_polynomial PI.UnitaryCorollaryDerivatives.polynomial_bound PI.UnitaryCorollaryDerivatives.compact_region_estimate
  have hcd := (hW k r z z' h ε 0 hh).1
  refine ⟨gcut_ckOn_smul hcd hF, fun m => ?_⟩
  obtain ⟨C, hC⟩ := (hW k r z z' h ε m hh).2
  exact gcut_leib hcd (2 * (r + 1)) m C hC hF (by push_cast; linarith) hFg

end gcut

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def JfFF (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ v, B.JF (T v).base (f v) ∈
    Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

end defs

def JfSmoothDS : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → JfFF S T f

def ModelPlaceBuilt3 : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → JfFF S T f → (∀ v, (S.G.place (S.pl v)).Ok) →
    Sz.IsWord S.G.k S.de → Sz.IsWord S.G.k S.de' → ∀ c : LE.Cut, c.χ = χ → ∀ v : Fin S.f,
      ∃ (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
        (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
        (lam : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : ℝ),
        JC.IsModelPlace S T f χ v L j lam c Cm σ

def RegFF3 : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → JfFF S T f →
    ∀ v, B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧ ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

section proofs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gf_SgS (Bs : B.RealPlaceData k r Wp Wq) {s s' : Q.Mx k r} (hs : s ∈ Sset k r Bs.z) (hs' : s' ∈ Sset k r Bs.z')
    (g : Q.Mx k r) : Gf k r Bs.z Bs.z' (s * g * s') = Gf k r Bs.z Bs.z' g := by
  unfold Gf
  rw [dInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem s hs s' hs' g,
    dInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem s hs s' hs' g]

theorem one_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) : (1 : Q.Mx k r) ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, (nSubgroup k r).1, by simp⟩

theorem n_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {n : Q.Mx k r} (hn : n ∈ Q.Nlev k r 0) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, n, hn.1, by simp⟩

theorem h_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {h : Q.Mx k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

theorem cut_mem_FFl (Bs : B.RealPlaceData k r Wp Wq) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (ε : ℝ)
    {Dm : Set (Q.Mx k r)} {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm) :
    (fun g => ((χ (Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • J g) ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    refine ⟨U, fun g => ((χ (Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • F g, hU, hgU, ?_, ?_⟩
    · have hc : ContDiff ℝ (⊤ : ℕ∞) (fun g : Q.Mx k r => ((χ (Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (hχ.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').div_const ε))
      exact hc.contDiffOn.smul hF
    · intro g hgU hgG
      simp only [hFJ g hgU hgG]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (n * g) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (n_mem_Sset Bs.z hn) (one_mem_Sset Bs.z') g
      simpa using this
    simp only [e, hL g hg n hn]
    rw [smul_comm]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (g * n) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (one_mem_Sset Bs.z) (n_mem_Sset Bs.z' hn) g
      simpa using this
    simp only [e, hR g hg n hn]
    rw [smul_comm]
  · intro g hg h hh h' hh'
    have e : Gf k r Bs.z Bs.z' (h * g * h') = Gf k r Bs.z Bs.z' g :=
      gf_SgS Bs (h_mem_Sset Bs.z hh) (h_mem_Sset Bs.z' hh') g
    simp only [e, hU g hg h hh h' hh']
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end proofs

theorem regularity_smooth_forms_holds : RegFF3 := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB hJ v
  refine ⟨hJ v, fun ε _ => ?_⟩
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := hB.1.2.2.2.1.1.1
  have e : B.JF (T v).base (D.cutF (T v).base χ (f v) ε) =
      fun g => ((χ (Gf S.G.k S.G.r (T v).base.z (T v).base.z' g / ε) : ℝ) : ℂ) • B.JF (T v).base (f v) g :=
    funext fun g => Formalism.FourierDecayAlt.P.JCTx2.JF_cutF (T v).base χ (f v) ε g
  rw [e]
  exact cut_mem_FFl (T v).base hχ ε (hJ v)

section bridge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuiltPlace_mono3 {Cc₁ Cc₂ : ℝ} (h : Cc₁ ≤ Cc₂) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ : ℝ} (hB : JCT.IsBuiltPlace Cc₂ S T f χ ν' m₀ top A₀) : JCT.IsBuiltPlace Cc₁ S T f χ ν' m₀ top A₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hB
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, le_trans h h9, h10, h11, ?_, h13⟩
  · intro v
    have hv := h8 v
    have hX : 0 ≤ (S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
        (S.Ntop : ℝ) ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h hX]
  · have hX : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
        ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
    have := mul_le_mul_of_nonneg_right h hX
    nlinarith

end bridge

theorem modelPlaceBuilt2_of_3 (hJ : JfSmoothDS) (h3 : ModelPlaceBuilt3) : JCT.ModelPlaceBuilt2 := by
  obtain ⟨C₁, hC₁⟩ := hJ
  obtain ⟨C₂, hC₂⟩ := h3
  refine ⟨max C₁ C₂, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB
  exact hC₂ E Wp Wq S T f χ ν' m₀ top A₀ (isBuiltPlace_mono3 (le_max_right _ _) hB)
    (hC₁ E Wp Wq S T f χ ν' m₀ top A₀ (isBuiltPlace_mono3 (le_max_left _ _) hB))

end

end Formalism.FourierDecayAlt.P.CutMP
end


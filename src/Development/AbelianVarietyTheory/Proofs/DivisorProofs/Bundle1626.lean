import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0084
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0086
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsC1DensityForLinePair
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AngleGlue
open GlobalTheory.Twist (resM app_resM)
variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E L L' : X.Modules} {r : ℕ} (h : Met p σ E r)

theorem contDiffAt_form (H : h.IsCInf) {U : X.Opens} (s₁ s₂ : Γ(E, U)) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) {D : ℕ} (c : AlgChart p σ D) (hc : y ∈ c.e.source) :
    ContDiffAt ℝ ∞ (fun v => h.form s₁ s₂ (c.e.symm v)) (c.e y) :=
  (H.gram ![s₁, s₂] hy 0 1).contDiffAt_chart c hc

theorem contDiffAt_re_form (H : h.IsCInf) {U : X.Opens} (s₁ s₂ : Γ(E, U)) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) {D : ℕ} (c : AlgChart p σ D) (hc : y ∈ c.e.source) :
    ContDiffAt ℝ ∞ (fun v => (h.form s₁ s₂ (c.e.symm v)).re) (c.e y) :=
  Complex.reCLM.contDiff.contDiffAt.comp _ (contDiffAt_form h H s₁ s₂ hy c hc)

theorem re_form_pos {l : L ⟶ E} (hl : IsSubbundle l) (hL : IsVB L 1) {U : X.Opens} (t : Γ(L, U))
    (ht : IsFrame (fun _ : Fin 1 => t)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    0 < (h.form (l.app U t) (l.app U t) y).re :=
  (Complex.pos_iff.1 (((h.restrict hl hL).posDef ⟨U, fun _ => t, ht⟩ y hy).diag_pos (i := 0))).1

theorem form_eq_of_resM {U U₂ W : X.Opens} (hW : W ≤ U) (hW₂ : W ≤ U₂) (x₁ x₂ : Γ(E, U))
    (y₁ y₂ : Γ(E, U₂)) (f₁ f₂ : Γ(X, W)) (e₁ : resM E hW₂ y₁ = f₁ • resM E hW x₁)
    (e₂ : resM E hW₂ y₂ = f₂ • resM E hW x₂) (z : CxPts p σ) (hz : z ∈ ptsIn p σ W) :
    h.form y₁ y₂ z = ev p σ W f₁ z * starRingEnd ℂ (ev p σ W f₂ z) * h.form x₁ x₂ z := by
  have key (s t : Γ(E, W)) (f : Γ(X, W)) :
      h.form s (f • t) z = starRingEnd ℂ (ev p σ W f z) * h.form s t z := by
    rw [← h.conj_form, h.form_smul_left, map_mul, h.conj_form]
  rw [← h.form_resM y₁ y₂ hW₂ hz, e₁, e₂, h.form_smul_left, key, h.form_resM _ _ hW hz]
  ring

theorem exists_eq_smul {U U₂ : X.Opens} (t : Γ(L, U)) (ht : IsFrame (fun _ : Fin 1 => t))
    (s : Γ(L, U₂)) : ∃ f : Γ(X, U ⊓ U₂),
      resM L (inf_le_right : U ⊓ U₂ ≤ U₂) s = f • resM L (inf_le_left : U ⊓ U₂ ≤ U) t := by
  refine ⟨(ht.basis (inf_le_left : U ⊓ U₂ ≤ U)).repr (resM L inf_le_right s) 0, ?_⟩
  have := (ht.basis (inf_le_left : U ⊓ U₂ ≤ U)).sum_repr (resM L inf_le_right s)
  rw [Fin.sum_univ_one, IsFrame.basis_apply] at this
  exact this.symm

theorem exists_app_eq_smul (l : L ⟶ E) {U U₂ : X.Opens} (t : Γ(L, U))
    (ht : IsFrame (fun _ : Fin 1 => t)) (s : Γ(L, U₂)) : ∃ f : Γ(X, U ⊓ U₂),
      resM E (inf_le_right : U ⊓ U₂ ≤ U₂) (l.app U₂ s) =
        f • resM E (inf_le_left : U ⊓ U₂ ≤ U) (l.app U t) := by
  obtain ⟨f, hf⟩ := exists_eq_smul t ht s
  exact ⟨f, by rw [← app_resM, hf, Scheme.Modules.Hom.app_smul, app_resM]⟩

variable {l : L ⟶ E} {l' : L' ⟶ E}

theorem angleForm_frames (H : h.IsCInf) (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (hL : IsVB L 1) (hL' : IsVB L' 1) (n : ℕ) {U U₂ : X.Opens} (t : Γ(L, U)) (t' : Γ(L', U))
    (s : Γ(L, U₂)) (s' : Γ(L', U₂)) (ht : IsFrame (fun _ : Fin 1 => t))
    (ht' : IsFrame (fun _ : Fin 1 => t')) (hs : IsFrame (fun _ : Fin 1 => s))
    (hs' : IsFrame (fun _ : Fin 1 => s')) (c : AlgChart p σ 1) {y : CxPts p σ}
    (hc : y ∈ c.e.source) (hy : y ∈ ptsIn p σ U) (hy₂ : y ∈ ptsIn p σ U₂) (ξ : EuclideanSpace ℂ (Fin 1)) :
    angleForm n (fun v => (h.form (l.app U₂ s) (l.app U₂ s) (c.e.symm v)).re)
      (fun v => (h.form (l'.app U₂ s') (l'.app U₂ s') (c.e.symm v)).re)
      (fun v => h.form (l'.app U₂ s') (l.app U₂ s) (c.e.symm v)) ξ (c.e y) =
    angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
      (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
      (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) ξ (c.e y) := by
  obtain ⟨f, hf⟩ := exists_app_eq_smul l t ht s
  obtain ⟨g, hg⟩ := exists_app_eq_smul l' t' ht' s'
  have hW : y ∈ ptsIn p σ (U ⊓ U₂) := mem_ptsIn_inf.2 ⟨hy, hy₂⟩
  have hN : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ (U ⊓ U₂) :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn (U ⊓ U₂))).mem_nhds
      (ChartGlue.mem_over c.e hc hW)) fun _ hv => hv.2
  have hre (a b : ℂ) : (a * starRingEnd ℂ a * b).re = ‖a‖ ^ 2 * b.re := by
    rw [Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  have ef := form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ f f hf hf
  have eg := form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g g hg hg
  have eq := form_eq_of_resM h inf_le_left inf_le_right _ _ _ _ g f hg hf
  have e0 := c.e.left_inv hc
  have hpos₂ := re_form_pos h hl hL s hs hy₂
  have hpos₂' := re_form_pos h hl' hL' s' hs' hy₂
  refine GlobalTheory.CurveDens.angleForm_frame_indep _ n _ _ _ _ _ _ (fun v => ev p σ (U ⊓ U₂) f (c.e.symm v))
    (fun v => ev p σ (U ⊓ U₂) g (c.e.symm v)) ξ (c.e y)
    ((contDiffAt_re_form h H _ _ hy c hc).differentiableAt (by simp))
    ((contDiffAt_re_form h H _ _ hy c hc).differentiableAt (by simp))
    ((contDiffAt_form h H _ _ hy c hc).differentiableAt (by simp))
    (by simp only [e0]; exact re_form_pos h hl hL t ht hy)
    (by simp only [e0]; exact re_form_pos h hl' hL' t' ht' hy)
    (c.differentiableAt_ev f hc hW) (c.differentiableAt_ev g hc hW) ?_ ?_ ?_ ?_ ?_
  · simp only [e0]
    intro h0
    rw [ef _ hW, h0] at hpos₂
    simp at hpos₂
  · simp only [e0]
    intro h0
    rw [eg _ hW, h0] at hpos₂'
    simp at hpos₂'
  · filter_upwards [hN] with v hv
    rw [ef _ hv, hre]
  · filter_upwards [hN] with v hv
    rw [eg _ hv, hre]
  · filter_upwards [hN] with v hv
    rw [eq _ hv]

theorem apply_single_eq_det_smul (A : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    A (EuclideanSpace.single 0 1) = A.det • EuclideanSpace.single 0 1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 1) ℂ).toBasis,
    Matrix.det_unique]
  ext i
  simp [LinearMap.toMatrix_apply, Subsingleton.elim i 0]

end GlobalTheory.AngleGlue

open GlobalTheory.Twist (resM)

theorem GlobalTheory.angleForm_global : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (V L L' : X.Modules) (r : ℕ) (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V), h.IsCInf → IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 → ∀ n : ℕ, ∃ m : AlgChart p σ 1 → CxPts p σ → ℂ, (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) ∧ (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) ∧ ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) → IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → m c y = angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re) (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re) (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single 0 1) (c.e y) := by
  intro k _ X p σ V L L' r h l l' H hl hl' hL hL' n
  let W : CxPts p σ → X.Opens := fun y => (hL.pick y).U ⊓ (hL'.pick y).U
  let T : ∀ y, Γ(L, W y) := fun y => resM L inf_le_left ((hL.pick y).e 0)
  let T' : ∀ y, Γ(L', W y) := fun y => resM L' inf_le_right ((hL'.pick y).e 0)
  have hT : ∀ y, IsFrame (fun _ : Fin 1 => T y) := fun y => by
    have := (hL.pick y).isFrame.res (inf_le_left : W y ≤ _)
    convert this using 2 with i
    rw [Subsingleton.elim i 0]
  have hT' : ∀ y, IsFrame (fun _ : Fin 1 => T' y) := fun y => by
    have := (hL'.pick y).isFrame.res (inf_le_right : W y ≤ _)
    convert this using 2 with i
    rw [Subsingleton.elim i 0]
  have hW : ∀ y, y ∈ ptsIn p σ (W y) := fun y => mem_ptsIn_inf.2 ⟨hL.mem_pick y, hL'.mem_pick y⟩
  refine ⟨fun c y => angleForm n
    (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
    (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
    (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
    (EuclideanSpace.single 0 1) (c.e y), ?_, ?_, ?_⟩
  · intro c y hc
    have e0 := c.e.left_inv hc
    have hG := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
      (EuclideanSpace.single 0 1) (c.e y)).2.1
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      ((GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c hc).of_le (by norm_cast))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [(ChartGlue.isOpen_over c.e (isOpen_ptsIn (W y))).mem_nhds
      (ChartGlue.mem_over c.e hc (hW y))] with v hv
    have := GlobalTheory.AngleGlue.angleForm_frames h H hl hl' hL hL' n (T y) (T' y) (T (c.e.symm v))
      (T' (c.e.symm v)) (hT y) (hT' y) (hT _) (hT' _) c (c.e.map_target hv.1) hv.2 (hW _)
      (EuclideanSpace.single 0 1)
    exact this.trans (by rw [c.e.right_inv hv.1])
  · intro c c' y hc hc'
    have e0 := c.e.left_inv hc
    have e0' := c'.e.left_inv hc'
    have hN := (ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hc hc')
    have hφz : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e e0
    have hφ : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) := (c.holo_trans c').differentiableAt hN
    have step1 := GlobalTheory.CurveDens.angleForm_frame_indep _ n
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c.e.symm v)).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c.e.symm v)).re)
      (fun v => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm ((c'.e ∘ c.e.symm) v))).re)
      (fun v => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y))
        (c'.e.symm ((c'.e ∘ c.e.symm) v))).re)
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c.e.symm v))
      (fun v => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm ((c'.e ∘ c.e.symm) v)))
      (fun _ => 1) (fun _ => 1) (EuclideanSpace.single 0 1) (c.e y)
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      ((GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      ((GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c hc).differentiableAt (by simp))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by simp only [e0]; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
      (differentiableAt_const _) (differentiableAt_const _) one_ne_zero one_ne_zero
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
      (by filter_upwards [hN] with v hv; simp [c'.e.left_inv hv.2])
    have step2 := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun w => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm w)).re)
      (fun w => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c'.e.symm w)).re)
      (fun w => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm w))
      (EuclideanSpace.single 0 1) (c.e y)).2.2 (c'.e ∘ c.e.symm) hφ
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_re_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; exact (GlobalTheory.AngleGlue.contDiffAt_form h H _ _ (hW y) c' hc').differentiableAt (by simp))
      (by rw [hφz]; simp only [e0']; exact GlobalTheory.AngleGlue.re_form_pos h hl hL _ (hT y) (hW y))
      (by rw [hφz]; simp only [e0']; exact GlobalTheory.AngleGlue.re_form_pos h hl' hL' _ (hT' y) (hW y))
    have step3 := (GlobalTheory.CurveDens.angleForm_props _ n
      (fun w => (h.form (l.app (W y) (T y)) (l.app (W y) (T y)) (c'.e.symm w)).re)
      (fun w => (h.form (l'.app (W y) (T' y)) (l'.app (W y) (T' y)) (c'.e.symm w)).re)
      (fun w => h.form (l'.app (W y) (T' y)) (l.app (W y) (T y)) (c'.e.symm w))
      (EuclideanSpace.single 0 1) (c'.e y)).1 (ChartGlue.transDet c.e c'.e y)
    rw [hφz, GlobalTheory.AngleGlue.apply_single_eq_det_smul] at step2
    exact step1.symm.trans (step2.trans step3)
  · intro U t t' ht ht' c y hc hy
    exact GlobalTheory.AngleGlue.angleForm_frames h H hl hl' hL hL' n t t' (T y) (T' y) ht ht' (hT y)
      (hT' y) c hc hy (hW y) _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffRoots
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

theorem exists_coeff_roots (c : Coeff l) {z w : ℂ} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) (hw : ∃ m : ℕ, 0 < m ∧ w ^ m = 1) :
    ∃ c' : Coeff l, c.F ≤ c'.F ∧ z ∈ c'.F ∧ w ∈ c'.F := by
  have hi : ∀ x : ℂ, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → IsIntegral ℚ x := by
    rintro x ⟨m, hm, h⟩
    exact IsIntegral.of_pow hm (h ▸ isIntegral_one)
  have := c.fin
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({z, w} : Set ℂ)) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro x (rfl | rfl)
      · exact hi _ hz
      · exact hi _ hw)
  have hle : c.F ≤ c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ) := le_sup_left
  have hle' : IntermediateField.adjoin ℚ ({z, w} : Set ℂ) ≤ c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ) := le_sup_right
  exact ⟨⟨c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ), inferInstance, fun τ a => hle (c.conj τ a), hle c.zeta_mem,
    c.le.trans hle⟩, hle, hle' (IntermediateField.subset_adjoin _ _ (by simp)),
    hle' (IntermediateField.subset_adjoin _ _ (by simp))⟩

theorem exists_coef_ext {K K' : Type} [Field K] [Field K'] (j : K →+* K') {σ : K →+* ℂ} (σ' : K' →+* ℂ)
    (hσ : ∀ a, σ' (j a) = σ a) {I : Type} [Fintype I] (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) : ∃ c₁ : VV K' lam →ₛₗ[σ'] W, ∀ (v : VV K lam) (v' : VV K' lam),
      (v' : Pol K' I n) = MvPolynomial.map j (v : Pol K I n) → c₁ v' = c₀ v := by
  classical
  obtain ⟨p, hp⟩ := LinearMap.exists_extend (p := VV K lam) (LinearMap.id : VV K lam →ₗ[K] VV K lam)
  have hp' : ∀ v : VV K lam, p v = v := fun v => LinearMap.congr_fun hp v
  let C : Pol K' I n →ₛₗ[σ'] W :=
    { toFun := fun F => Finsupp.sum ((MvPolynomial.basisMonomials _ K').repr F)
        fun m a => σ' a • c₀ (p (MvPolynomial.monomial m 1))
      map_add' := fun F F' => by
        rw [map_add]
        exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
      map_smul' := fun a F => by
        rw [map_smul, Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
        simp [mul_smul] }
  have hC : ∀ m a, C (MvPolynomial.monomial m a) = σ' a • c₀ (p (MvPolynomial.monomial m 1)) := fun m a => by
    have e : MvPolynomial.monomial m a = a • MvPolynomial.basisMonomials _ K' m := by
      simp [MvPolynomial.smul_monomial]
    rw [e, map_smulₛₗ]
    congr 1
    show Finsupp.sum ((MvPolynomial.basisMonomials _ K').repr (MvPolynomial.basisMonomials _ K' m))
      (fun m a => σ' a • c₀ (p (MvPolynomial.monomial m 1))) = _
    rw [Module.Basis.repr_self, Finsupp.sum_single_index (by simp), map_one, one_smul]
  have key : ∀ F : Pol K I n, C (MvPolynomial.map j F) = c₀ (p F) := by
    intro F
    induction F using MvPolynomial.induction_on' with
    | monomial m a =>
      rw [MvPolynomial.map_monomial, hC, hσ, ← map_smulₛₗ, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    | add F F' h h' => rw [map_add, map_add, h, h', map_add, map_add]
  exact ⟨C.comp (VV K' lam).subtype, fun v v' h => by
    show C v' = _
    rw [h, key, hp']⟩

theorem covPin_covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) {u : c'.F} (hu : u ≠ 0)
    (h : d.IsLev ∧ d.l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) :
    (covBC hle d u).IsLev ∧ (covBC hle d u).l₂.A = 1 ∧
      ∃ _ : StarRing (𝓞 E), IsNab (covBC hle d u).Xo₂ (covBC hle d u).c₂ (covBC hle d u).nab₂ := by
  obtain ⟨h1, h2, s, h3⟩ := h
  exact ⟨GlobalTheory.LevelCoverDatum.isLev_smul (ddBC hle d) (GlobalTheory.FieldBCModel.isLev_ddBC hle d h1) u hu, h2, s,
    GlobalTheory.FieldBCModel.isNab_nabBC (le_covCoeff hle d) d.nab₂ h3⟩

theorem phiHat_covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F) (φ : (Fin n → LevQc Dw d.l₂) → c.F)
    (w : c.F) (q : Fin n → LevQ Dw d.l₂) (h : d.eF w = phiHat d.c₂ (fun x => d.eF (φ x)) q) :
    (covBC hle d u).eF (incF c c' hle w) =
      phiHat (covBC hle d u).c₂ (fun x => (covBC hle d u).eF (incF c c' hle (φ x))) q := by
  have e := congrArg (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d)) h
  refine Eq.trans (Subtype.ext rfl) (e.trans ?_)
  unfold phiHat
  have hz : zetaM (covCoeff hle d) = incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (zetaM d.c₂) := by
    unfold zetaM; rw [map_pow]; rfl
  refine (AddMonoidHom.map_finsum_of_injective
    (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d)).toAddMonoidHom (RingHom.injective _) _).trans ?_
  refine finsum_congr fun x => ?_
  show incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (_ * _) = _
  rw [map_mul, map_zpow₀, ← hz]
  rfl

theorem epIs_map (hle : c.F ≤ c'.F) {bad : ℕ} {B : Ideal (𝓞 E) → c.F} {epF : Submodule (𝓞 E) (Fin n → E) → c.F}
    (h : EpIs (Dw := Dw) c bad B epF) :
    EpIs (Dw := Dw) c' bad (fun I => incF c c' hle (B I)) (fun L => incF c c' hle (epF L)) := by
  intro L cc h1 h2 h3 h4 h5
  obtain ⟨q, a, b, e⟩ := h L cc h1 h2 h3 h4 h5
  exact ⟨q, a, b, by simp only [e, map_mul, map_inv₀, map_ratCast]⟩

theorem isThClsD_covBC_one (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) {u : c'.F} (hu : u = 1) {Cl : Type} [Fintype Cl]
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F)
    {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    {Vs' : Type} [AddCommGroup Vs'] [Module c'.F Vs'] (io' : Vs' →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (x : Cl → Vs) (x' : Cl → Vs') (hx : ∀ k, io' (x' k) = MvPolynomial.map (incF c c' hle) (io (x k)))
    (hd : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a m)
    (h : IsThClsD Xo c d w La Nc gam vol ep io x f) :
    IsThClsD Xo c' (covBC hle d u) (fun k q => incF c c' hle (w k q)) La Nc gam (incF c c' hle vol)
      (fun k => incF c c' hle (ep k)) io' x' (rulBC hle f) := by
  subst hu
  have h' := (GlobalTheory.ClassSumFieldChange.isThClsD_ddBC_iff E H Dw l Xo c c' hle n d Cl w La Nc gam vol ep Vs io Vs' io' x x'
    hx hd a m f hf).2 h
  intro k _ _ _ i hk y y₂ hy
  obtain ⟨vc, h1, h2⟩ := @h' k _ _ _ i hk y y₂ hy
  refine ⟨vc, h1, h2.trans ?_⟩
  have e : (covBC hle d 1).cδ = (ddBC hle d).cδ := one_smul (covCoeff hle d).F (rulBC (le_covCoeff hle d) d.cδ)
  rw [e]
  rfl

theorem isBC_rulBC_trans {c₀ : Coeff l} (h₀ : c₀.F ≤ c.F) (hle : c.F ≤ c'.F) (h₁ : c₀.F ≤ c'.F)
    {a : (E →+* ℂ) × ℕ → ℕ} {k m : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a k) {as : Fin m → c.F} {fs : Fin m → Rul Xo c₀}
    (h : IsBC h₀ f as fs) : IsBC h₁ (rulBC hle f) (fun i => incF c c' hle (as i)) fs := by
  intro S _ _ _ hS y
  letI := resAlg hle S
  rw [GlobalTheory.FieldBCModel.evR_rulBC hle hf.1 (fun _ => rfl) y, h S (fun a => hS a) _]
  rfl

end Gen

section Forms

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  {K' : Type} [Field K'] {σ' : K' →+* ℂ} (t : T0) {Cl : Type} (h : Cl → GA D (Vc D i))
  (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

theorem adForms_ext {Gp Γ W I : Type} [Group Gp] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gp}
    {ρ : Γ →* Module.End ℂ W} {J J' : Subgroup Gp} {χ : J →* ℂˣ} {F F' : Gp → W} (hF : F ∈ Bridge.AdForms ι ρ J χ)
    (hF' : F' ∈ Bridge.AdForms ι ρ J χ) (hJ : J' ≤ J) {y : I → Gp} (hr : Bridge.IsReps ι J' y)
    (h : ∀ k, F (y k) = F' (y k)) : F = F' := by
  funext g
  obtain ⟨k, ⟨γ, κ, rfl⟩, -⟩ := hr g
  have h1 := hF γ (y k) ⟨κ, hJ κ.2⟩
  have h2 := hF' γ (y k) ⟨κ, hJ κ.2⟩
  rw [h k] at h1
  exact h1.trans h2.symm

theorem place_unique (hV : R.models_HV) {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) {y y' : (R.HV i t).H} {x : Cl → VsV D i K'}
    (hy : Place R i t h c0' y x) (hy' : Place R i t h c0' y' x) : y = y' := by
  exact (hV i t).1 (adForms_ext ((hV i t).2.1.le (LinearMap.mem_range_self (R.HV i t).e y))
    ((hV i t).2.1.le (LinearMap.mem_range_self (R.HV i t).e y')) hJ hr fun k => (hy k).trans (hy' k).symm)

open Classical in

def thAdOf (v₀ : (R.MW i (sg0 D A)).Vec) (x : Cl → VsV D i K') : AutQ (Wc D i) → ℂ :=
  if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0

theorem thAdIs_thAdOf (hV : R.models_HV) {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) (v₀ : (R.MW i (sg0 D A)).Vec) :
    ThAdIs R i t h c0' v₀ (thAdOf R i t h c0' v₀) := by
  intro y x hy
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  have e := place_unique R i t h c0' hV hJ hr hx.choose_spec hy
  exact (dif_pos hx).trans (congrArg (fun y => onQ (Wc D i) (R.thF i t y v₀)) e)

end Forms

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexSubgroupAutExtendSepClosureStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteIndex_subgroup_aut_extend_sepClosure : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L] [FiniteDimensional K L] [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω'] [IsSepClosure L Ω'] [Algebra K Ω'] [IsScalarTower K L Ω'] (j : Ω →ₐ[K] Ω'), ∃ H : Subgroup (Ω ≃ₐ[K] Ω), H.FiniteIndex ∧ ∀ σ ∈ H, ∃ σ' : Ω' ≃ₐ[L] Ω', ∀ x, σ' (j x) = j (σ x) := by
  first | exact @GlobalTheory.SepExt.exists_finiteIndex_extend | exact GlobalTheory.SepExt.exists_finiteIndex_extend | (intros; apply GlobalTheory.SepExt.exists_finiteIndex_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartZeroNeOfIsVacuumOrientedModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO S T → ℂ), IsVacO ψ θ S T sS sT LS LT f → ∃ w : WO S T, w.map (finPart D) = 0 ∧ f w ≠ 0 := by
  first | exact @GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne | exact GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne | (intros; apply GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlasStatement
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n), ∃ (N : ℕ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧ (∀ j, tsupport (χ j) ⊆ (A.e (c j)).source) ∧ ∀ y, ∑ j, χ j y = 1 := by
  first | exact @GlobalTheory.exists_finite_smooth_partition_holAtlas | exact GlobalTheory.exists_finite_smooth_partition_holAtlas | (intros; apply GlobalTheory.exists_finite_smooth_partition_holAtlas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetFixingPointLocallyFiniteTypeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_fixing_point_locallyFiniteType : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)), LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, ∃ s : Finset Ω, ∀ σ : Ω ≃ₐ[K] Ω, (∀ a ∈ s, σ a = a) → specAut σ ≫ x = x := by
  first | exact @GlobalTheory.PtFin.exists_finset_fix | exact GlobalTheory.PtFin.exists_finset_fix | (intros; apply GlobalTheory.PtFin.exists_finset_fix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroupStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixedField_point_of_fixed_by_subgroup : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω)) (A : Over (Sp K)), LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, (∀ σ ∈ H, specAut σ ≫ x = x) → ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left, spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  first | exact @GlobalTheory.Published.AbVarRed.exists_fixedField_point | exact GlobalTheory.Published.AbVarRed.exists_fixedField_point | (intros; apply GlobalTheory.Published.AbVarRed.exists_fixedField_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussVacuumNondegenerateGaussianDualPairStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussVacuum_nondegenerate_gaussian_dualPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧
      ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ) (c : ℝ),
        0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ ∀ x, g x = Complex.exp (-(Q x x)) := by
  first | exact @GlobalTheory.GaussVacPair.exists_gauss_vacuum | exact GlobalTheory.GaussVacPair.exists_gauss_vacuum | (intros; apply GlobalTheory.GaussVacPair.exists_gauss_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlicesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_adelicVectors_bounds_pureTensors_slices : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      ∃ μ : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        ∃ C c : ℝ≥0∞, C ≠ ⊤ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
          (∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μ ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) ∧
          ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
            ∀ y, c * ∫⁻ z, ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2 ≤ ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds | exact GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds | (intros; apply GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralQuotientOfValuationSubringAboveDvrStatement
section
open GlobalTheory.Published.AbVarRed IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ y ∈ V, ∃ a s : Ω, ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem a ∧ ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem s ∧ V.valuation s = 1 ∧ y * s = a := by
  first | exact @GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove | exact GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove | (intros; apply GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove <;> assumption)
end


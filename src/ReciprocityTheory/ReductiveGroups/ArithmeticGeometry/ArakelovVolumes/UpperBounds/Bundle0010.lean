import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import Mathlib

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def phla {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ := -2 * Real.log (X.nfac la x)

def IsMetric {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Ps : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ps (rmul x b) = Ps x + Real.log (‖bchar la b‖ ^ 2)) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Ps (lact γ x) = Ps x

def IsBEq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x

def IsFundSet {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
    cpt X x0 z' = lact γ (rmul (cpt X x0 z) b) → z = z') ∧
  ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
    cpt X x0 z = lact γ (rmul (cpt X x0 z') b)

def ExhaustFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ S : EtaleStein (nd X) (OmF X x0), S.z = Subtype.val ∧ S.e = fun y => eF X x0 y.1

def MeasInvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 x0' : Frame X.Ψ r), IsOrth X x0 → IsOrth X x0' →
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 = ∫⁻ z, φ (cpt X x0' z) ∂muF X x0'

def ExtFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (F : V (nd X) → ℂ),
    DifferentiableOn ℂ F (OmF X x0) →
    (∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) →
    ∃ P : Frame X.Ψ r → ℂ, IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

def FundSetStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∃ FF : Set (V (nd X)), IsFundSet X x0 FF

def IsMetricW {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) : Prop :=
  Measurable W ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2)) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, W (lact γ x) = W x

def WLower {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x

def InAt {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ) :
    Prop :=
  ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 < ⊤

def InFF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (FF : Set (V (nd X)))
    (f : Frame X.Ψ r → ℂ) : Prop :=
  ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 < ⊤

def PoinStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) → InAt X x0 W bb F →
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) →
    (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧
    X.IsBddSec la (poin X la P) ∧
    (∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ENNReal.ofReal ‖poin X la P x‖ ≤ ENNReal.ofReal C *
        ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
          (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) ∧
    ∀ (la' : Wt X.Ψ r) (g : Frame X.Ψ r → ℂ), X.IsSec la' g → ∀ x ∈ X.dom,
      poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x

def OntoStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞)
    (Ps : Frame X.Ψ r → ℝ) (g1 : V (nd X) → ℂ) (bb m : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m →
    DifferentiableOn ℂ g1 (OmF X x0) → (∃ z ∈ OmF X x0, g1 z ≠ 0) →
    ContDiffOn ℝ ∞ (fun z => Ps (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} →
    (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → W (cpt X x0 z) = ENNReal.ofReal (Real.exp (-Ps (cpt X x0 z)))) →
    (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → ∀ ξ : Fin (nd X) → ℂ,
      m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
        (leviV (nd X) (fun w => ((Ps (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re) →
    (∀ P, X.IsBddSec la P → P ∈ X.SS la) →
    ∀ FF, IsFundSet X x0 FF →
    (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS la, InFF X x0 W FF f →
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) →
    ∀ f ∈ X.SS la, InFF X x0 W FF f →
    ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧
      IsBEq X la P ∧ (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ ∀ x ∈ X.dom, poin X la P x = f x

def CuspStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (τ0 : X.Ψ), 0 < X.p0 → X.p0 < r →
    (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ0 j ≤ la τ0 i) →
    (∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → la τ0 i0 < la τ0 i1) →
    ∀ P, X.IsBddSec la P → P ∈ X.SS la

def RhGradFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    Complex.normSq (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j) ≤
      ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) *
        (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re

def ExhaustGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ g1 : V (nd X) → ℂ,
    DifferentiableOn ℂ g1 (OmF X x0) →
    ∃ S : EtaleStein (nd X) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0},
      S.z = Subtype.val ∧ S.e = fun y => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹

def KaUnfoldStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ FF, IsFundSet X x0 FF → ∀ bb : ℝ,
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
      (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x) →
      ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 ≤
        C * ∫⁻ z in FF, φ (cpt X x0 z) ∂muF X x0

def PairUnfoldStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) → InAt X x0 W bb F →
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) →
    ∀ FF, IsFundSet X x0 FF → ∀ f0 ∈ X.SS la, InFF X x0 W FF f0 →
      ∫ z in FF, poin X la P (cpt X x0 z) * (starRingEnd ℂ) (f0 (cpt X x0 z)) *
          ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 =
        ∫ z, F z * (starRingEnd ℂ) (f0 (cpt X x0 z)) * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0

def BigCellStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ),
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = 0) → ∀ x ∈ X.dom, P x = 0

def OmFConnStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → IsPreconnected (OmF X x0)

def OrthoStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ x1, IsOrth X x1 ∧ ∃ b ∈ Bor X.Ψ r, x = rmul x1 b

def VanishAtSStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), 0 < nd X → IsOrth X x1 → x1 ∈ X.dom →
    ∀ (u w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ρ : ℝ), 0 < ρ →
    DifferentiableOn ℂ (fun z => u (cpt X x1 z)) (Metric.ball 0 ρ) →
    (∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x1 z)) (Metric.ball 0 ρ)) →
    DifferentiableOn ℂ (fun z => w0 (cpt X x1 z)) (Metric.ball 0 ρ) →
    w0 x1 ≠ 0 → (∀ k, s k x1 = 0) →
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X x1 z) / w0 (cpt X x1 z) : V (nd X))) 0).det ≠ 0 →
    ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal (‖u (cpt X x1 z)‖ ^ 2 *
      (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ))) < ⊤ →
    u x1 = 0

def LUStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
    ∃ (Δ : Frame X.Ψ r → ℂ) (zOf : Frame X.Ψ r → V (nd X)) (bOf : Frame X.Ψ r → Frame X.Ψ r),
      Differentiable ℂ Δ ∧ (∀ x ∈ X.dom, ∀ ε > 0, ∃ y ∈ Metric.ball x ε, Δ y ≠ 0) ∧
      DifferentiableOn ℂ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0} ∧
      DifferentiableOn ℂ bOf {x | x ∈ X.dom ∧ Δ x ≠ 0} ∧
      (∀ x ∈ X.dom, Δ x ≠ 0 → zOf x ∈ OmF X x0 ∧ bOf x ∈ Bor X.Ψ r ∧
        x = rmul (cpt X x0 (zOf x)) (bOf x)) ∧
      ∀ z ∈ OmF X x0, ∀ b ∈ Bor X.Ψ r, Δ (rmul (cpt X x0 z) b) ≠ 0 ∧
        zOf (rmul (cpt X x0 z) b) = z ∧ bOf (rmul (cpt X x0 z) b) = b

def FrameMeasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ C : Set (Frame X.Ψ r), IsCompact C →
    C ⊆ X.dom → ∃ K : ℝ≥0∞, K < ⊤ ∧
    ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in C, G x ≤ K * ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0

def FundSetMeasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))), IsOrth X x0 → IsFundSet X x0 FF →
    (∃ x1, IsOrth X x1 ∧ ∃ CechHodgeFiltration, IsFundSet X x1 CechHodgeFiltration ∧ muF X x1 CechHodgeFiltration < ⊤) → muF X x0 FF < ⊤

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfC
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

theorem volume_null_of_slice {I : Type*} [Fintype I] [DecidableEq I] (i0 : I) {S : Set (I → ℂ)}
    (hS : MeasurableSet S) (huniq : ∀ v ∈ S, ∀ v' ∈ S, (∀ j, j ≠ i0 → v j = v' j) → v = v') :
    volume S = 0 := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => ℂ) (fun j => j ≠ i0)
  have hmp : MeasurePreserving e (volume : Measure (I → ℂ))
      ((Measure.pi fun _ : {j // j ≠ i0} => (volume : Measure ℂ)).prod
        (Measure.pi fun _ : {j // ¬ j ≠ i0} => (volume : Measure ℂ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : I => (volume : Measure ℂ)) (fun j => j ≠ i0)
  have hS' : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hS
  rw [← hmp.symm.measure_preimage_equiv S, Measure.measure_prod_null hS']
  refine Filter.Eventually.of_forall fun x => ?_
  haveI : Nonempty {j // ¬ j ≠ i0} := ⟨⟨i0, not_not.2 rfl⟩⟩
  show (Measure.pi fun _ : {j // ¬ j ≠ i0} => (volume : Measure ℂ)) _ = 0
  refine Set.Subsingleton.measure_zero ?_ _
  intro y hy y' hy'
  have hxy : e.symm (x, y) = e.symm (x, y') := by
    refine huniq _ hy _ hy' fun j hj => ?_
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
  have := e.symm.injective hxy
  exact (Prod.ext_iff.1 this).2

lemma det_diff_last {k : ℕ} (B B' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (h : ∀ a b, ¬ (a = Fin.last k ∧ b = Fin.last k) → B a b = B' a b) :
    B.det - B'.det = (B (Fin.last k) (Fin.last k) - B' (Fin.last k) (Fin.last k)) *
      (B.submatrix Fin.castSucc Fin.castSucc).det := by
  have hrows : ∀ j : Fin (k + 1), B.submatrix (Fin.last k).succAbove j.succAbove =
      B'.submatrix (Fin.last k).succAbove j.succAbove := by
    intro j
    ext a b
    refine h _ _ fun hab => ?_
    have := hab.1
    rw [Fin.succAbove_last] at this
    exact Fin.castSucc_ne_last a this
  rw [Matrix.det_succ_row B (Fin.last k), Matrix.det_succ_row B' (Fin.last k),
    ← Finset.sum_sub_distrib, Finset.sum_eq_single (Fin.last k)]
  · rw [hrows (Fin.last k)]
    have hs : (-1 : ℂ) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ)) = 1 := by
      rw [Fin.val_last, ← two_mul, pow_mul]; simp
    have hc : B.submatrix Fin.castSucc Fin.castSucc = B'.submatrix Fin.castSucc Fin.castSucc := by
      simpa [Fin.succAbove_last] using hrows (Fin.last k)
    rw [hs, Fin.succAbove_last, hc]
    ring
  · intro j _ hj
    have hrow : B (Fin.last k) j = B' (Fin.last k) j := h _ _ fun hab => hj hab.2
    rw [hrow, hrows j]
    ring
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

lemma continuous_lminor (τ : ι) (i : Fin (r + 1)) : Continuous fun v : Ix ι r → ℂ => lminor (Mt v τ) i := by
  unfold Mt lminor
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact continuous_apply _

theorem volume_lminor_zero (τ : ι) :
    ∀ k (h : k < r + 1), volume {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k, h⟩ = 0} = 0 := by
  intro k
  induction k with
  | zero =>
    intro h
    have hempty : {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨0, h⟩ = 0} = ∅ := by
      ext v
      simp [lminor]
    rw [hempty, measure_empty]
  | succ k ih =>
    intro h
    have hk : k < r + 1 := by omega
    have hkr : k < r := by omega
    have hl : (Fin.castLE (Nat.le_of_lt_succ h) (Fin.last k) : Fin r) = ⟨k, hkr⟩ :=
      Fin.ext (by simp)
    have key : ∀ w : Ix ι r → ℂ, lminor (Mt w τ) ⟨k, hk⟩ =
        (((Mt w τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h))).submatrix
          Fin.castSucc Fin.castSucc).det := fun w => rfl
    have hmeas : MeasurableSet {v : Ix ι r → ℂ |
        lminor (Mt v τ) ⟨k + 1, h⟩ = 0 ∧ lminor (Mt v τ) ⟨k, hk⟩ ≠ 0} :=
      (isClosed_eq (continuous_lminor τ _) continuous_const).measurableSet.inter
        (isClosed_eq (continuous_lminor τ _) continuous_const).isOpen_compl.measurableSet
    refine measure_mono_null (t := {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k, hk⟩ = 0} ∪
      {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k + 1, h⟩ = 0 ∧ lminor (Mt v τ) ⟨k, hk⟩ ≠ 0}) ?_ ?_
    · intro v hv
      by_cases h0 : lminor (Mt v τ) ⟨k, hk⟩ = 0
      · exact Or.inl h0
      · exact Or.inr ⟨hv, h0⟩
    refine measure_union_null (ih hk) ?_
    refine volume_null_of_slice (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) hmeas ?_
    intro v hv v' hv' hagree
    have dd := det_diff_last
      ((Mt v τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h)))
      ((Mt v' τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h)))
      (by
        intro a b hab
        refine hagree _ fun heq => hab ?_
        simp only [Prod.mk.injEq, Fin.ext_iff, Fin.coe_castLE] at heq
        exact ⟨Fin.ext (by simp [heq.2.1]), Fin.ext (by simp [heq.2.2])⟩)
    have h1 : lminor (Mt v τ) ⟨k + 1, h⟩ = 0 := hv.1
    have h2 : lminor (Mt v' τ) ⟨k + 1, h⟩ = 0 := hv'.1
    have hm : lminor (Mt v τ) ⟨k, hk⟩ ≠ 0 := hv.2
    rw [key v] at hm
    simp only [lminor] at h1 h2
    rw [h1, h2, sub_zero] at dd
    simp only [Matrix.submatrix_apply, hl] at dd
    have hz : v (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) - v' (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) = 0 := by
      rcases mul_eq_zero.1 dd.symm with hz | hz
      · exact hz
      · exact absurd hz hm
    funext j
    by_cases hj : j = (τ, ⟨k, hkr⟩, ⟨k, hkr⟩)
    · subst hj; exact sub_eq_zero.1 hz
    · exact hagree j hj

theorem volume_BC_compl : volume (BC ι r)ᶜ = 0 := by
  have hU : (BC ι r)ᶜ = ⋃ τ : ι, ⋃ i : Fin (r + 1), {v : Ix ι r → ℂ | lminor (Mt v τ) i = 0} := by
    ext v
    simp [BC]
  rw [hU]
  refine measure_iUnion_null fun τ => measure_iUnion_null fun i => ?_
  exact volume_lminor_zero τ i.1 i.2

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd

theorem exists_val_of_prime {Kf : Type*} [Field Kf] (A : Subring Kf) (P : Ideal A) [P.IsPrime] :
    ∃ V : ValuationSubring Kf, (∀ a : A, (a : Kf) ∈ V) ∧ (∀ a : A, a ∉ P → (a : Kf)⁻¹ ∈ V) ∧
      ∀ a : A, a ∈ P → V.valuation (a : Kf) < 1 := by
  obtain ⟨B, hB⟩ := (LocalSubring.ofPrime A P).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hB
  let e := LocalSubring.ofPrimeEquiv A P
  let f : Localization.AtPrime P →+* B.toLocalSubring.toSubring :=
    (Subring.inclusion hle).comp (e : Localization.AtPrime P →+* (LocalSubring.ofPrime A P).toSubring)
  have hf : ∀ a : A, ((f (algebraMap A (Localization.AtPrime P) a) : B.toLocalSubring.toSubring) : Kf) = a := by
    intro a
    show ((e (algebraMap A (Localization.AtPrime P) a) : (LocalSubring.ofPrime A P).toSubring) : Kf) = a
    rw [AlgEquiv.commutes]
    rfl
  have hmem : ∀ a : A, (a : Kf) ∈ B := by
    intro a
    have h := (f (algebraMap A (Localization.AtPrime P) a)).2
    rw [hf] at h
    exact h
  refine ⟨B, hmem, fun a ha => ?_, fun a ha => ?_⟩
  · have hu : IsUnit (algebraMap A (Localization.AtPrime P) a) :=
      IsLocalization.map_units _ (⟨a, ha⟩ : P.primeCompl)
    obtain ⟨u, hu'⟩ := hu.map f
    have h1 : ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) * (u : _) = 1 :=
      u.inv_mul
    have h2 : (((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) : Kf) * (a : Kf) = 1 := by
      rw [← hf a, ← hu']
      exact congrArg Subtype.val h1
    rw [← eq_inv_of_mul_eq_one_left h2]
    exact ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring).2
  · have hnu : ¬ IsUnit (algebraMap A (Localization.AtPrime P) a) := fun h =>
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P a).1 h ha
    have hnu2 : ¬ IsUnit (f (algebraMap A (Localization.AtPrime P) a)) := by
      intro h
      apply hnu
      have h' : IsUnit (e (algebraMap A (Localization.AtPrime P) a)) := hloc.map_nonunit _ h
      have h'' := h'.map (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
      first
      | (convert h'' using 1
         exact (e.symm_apply_apply _).symm)
      | (rwa [show (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
            (e (algebraMap A (Localization.AtPrime P) a)) = algebraMap A (Localization.AtPrime P) a from
            e.symm_apply_apply _] at h'')
    by_contra hge
    push_neg at hge
    have hv1 : B.valuation (a : Kf) = 1 := le_antisymm ((B.valuation_le_one_iff _).2 (hmem a)) hge
    have hunit : IsUnit (⟨a, hmem a⟩ : B) := (B.valuation_eq_one_iff ⟨a, hmem a⟩).2 hv1
    apply hnu2
    have heq : f (algebraMap A (Localization.AtPrime P) a) = ⟨a, hmem a⟩ := Subtype.ext (hf a)
    rw [heq]
    exact hunit

end ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd
end


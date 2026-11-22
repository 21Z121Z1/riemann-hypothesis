import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample.OscWeight
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PExtNonIntChart
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PExtension
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.OscMuLineObjects
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

namespace OscLine

def oscRho (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  Real.exp (2 * Taut.oscW (z ⟨(), 1⟩ / z ⟨(), 0⟩))

def oscMuNorm (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  Real.sqrt (oscRho z) / Real.sqrt (‖z ⟨(), 0⟩‖ ^ 2 + oscRho z * ‖z ⟨(), 1⟩‖ ^ 2)

def oscMuLine : HermLine (PBlk 2) := hermOfFun (PBlk 2) (fun _ => -1) oscMuNorm

theorem oscRho_pos (z : (Σ _ : Unit, Fin 2) → ℂ) : 0 < oscRho z := Real.exp_pos _

theorem oscRho_smul (c : Unit → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ _ : Unit, Fin 2) → ℂ) :
    oscRho (torusSmul c z) = oscRho z := by
  unfold oscRho torusSmul
  congr 3
  exact mul_div_mul_left _ _ (hc ())

theorem oscMuNorm_pos {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0) : 0 < oscMuNorm z := by
  obtain ⟨i, hi⟩ := hz
  have hρ := oscRho_pos z
  have hs : 0 < ‖z ⟨(), 0⟩‖ ^ 2 + oscRho z * ‖z ⟨(), 1⟩‖ ^ 2 := by
    fin_cases i
    · have : 0 < ‖z ⟨(), 0⟩‖ ^ 2 := by positivity
      positivity
    · have : 0 < ‖z ⟨(), 1⟩‖ ^ 2 := by positivity
      positivity
  exact div_pos (Real.sqrt_pos.mpr hρ) (Real.sqrt_pos.mpr hs)

theorem oscMuNorm_homog : IsHomogOfDeg (ι := PBlk 2) (fun _ => -1) oscMuNorm := by
  intro c z hc
  have hρ := oscRho_smul c hc z
  have hc0 : 0 < ‖c ()‖ := norm_pos_iff.mpr (hc ())
  simp only [oscMuNorm, hρ, Finset.univ_unique, Finset.prod_singleton, zpow_neg, zpow_one]
  simp only [torusSmul, norm_mul]
  have : (‖c ()‖ * ‖z ⟨(), 0⟩‖) ^ 2 + oscRho z * (‖c ()‖ * ‖z ⟨(), 1⟩‖) ^ 2 =
      ‖c ()‖ ^ 2 * (‖z ⟨(), 0⟩‖ ^ 2 + oscRho z * ‖z ⟨(), 1⟩‖ ^ 2) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hc0.le]
  field_simp

end OscLine

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDivisionNearSChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace DivisionNearS

variable {D : ℕ}

theorem mem_source_chartIdx {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U) (x : U) :
    x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

theorem setLIntegral_piece_le_chart {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U)
    (f : Fin A.n → U → ℝ≥0∞) (c : Fin A.n) (W : Set U) (hW : IsOpen W)
    (hWc : W ⊆ (A.chart c).source)
    (hf : ∀ j, ∀ p ∈ (A.chart j).source ∩ W,
      f j p = ENNReal.ofReal (‖jac A j c p‖ ^ 2) * f c p) (j : Fin A.n) :
    ∫⁻ y in piece A j ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W), f j ((A.chart j).symm y) ≤
      ∫⁻ z in A.chart c '' W, f c ((A.chart c).symm z) := by
  set G : (Fin D → ℂ) → ℝ≥0∞ := fun z => f c ((A.chart c).symm z)
  set B := piece A j ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) with hBdef
  let φ : (Fin D → ℂ) → (Fin D → ℂ) := A.chart c ∘ (A.chart j).symm
  have hBmeas : MeasurableSet B := (ExtensionProof.measurableSet_piece A j).inter
    ((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hW).measurableSet
  have hBmem : ∀ y ∈ B, y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ W := fun y hy =>
    ⟨hy.2.1, hy.2.2⟩
  have hderiv : ∀ y ∈ B, HasFDerivWithinAt φ ((fderiv ℂ φ y).restrictScalars ℝ) B y := by
    intro y hy
    obtain ⟨hyt, hyW⟩ := hBmem y hy
    have han : AnalyticAt ℂ φ y := A.holo j c y ⟨hyt, hWc hyW⟩
    exact (han.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : InjOn φ B := by
    intro y₁ h₁ y₂ h₂ h
    obtain ⟨h₁t, h₁W⟩ := hBmem y₁ h₁
    obtain ⟨h₂t, h₂W⟩ := hBmem y₂ h₂
    have := (A.chart c).injOn (hWc h₁W) (hWc h₂W) h
    rw [← (A.chart j).right_inv h₁t, ← (A.chart j).right_inv h₂t, this]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hBmeas hderiv hinj G
  have heq : ∫⁻ y in B, ENNReal.ofReal |((fderiv ℂ φ y).restrictScalars ℝ).det| * G (φ y)
      = ∫⁻ y in B, f j ((A.chart j).symm y) := by
    refine setLIntegral_congr_fun hBmeas fun y hy => ?_
    obtain ⟨hyt, hyW⟩ := hBmem y hy
    have hys : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyt
    rw [hf j _ ⟨hys, hyW⟩, ExtNonInt.det_restrictScalars_complex, abs_of_nonneg (by positivity)]
    simp only [G, φ, Function.comp_apply, (A.chart c).left_inv (hWc hyW), jac,
      (A.chart j).right_inv hyt]
  have hsub : φ '' B ⊆ A.chart c '' W := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(A.chart j).symm y, (hBmem y hy).2, rfl⟩
  calc ∫⁻ y in B, f j ((A.chart j).symm y) = ∫⁻ z in φ '' B, G z := by rw [hcv, heq]
    _ ≤ ∫⁻ z in A.chart c '' W, G z := lintegral_mono_set hsub

variable (X : EmbDatum D)

theorem e_transform (k : Fin X.N) (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    X.e k j x = X.L.g j c x * X.e k c x := by
  have := (X.e_mem k).2.1 j c x hx
  simpa using this

theorem lin_apply (a : Fin X.N → ℂ) (j : Fin X.A.n) (x : X.U) :
    lin X.e a j x = ∑ k, a k * X.e k j x := by
  simp [lin, Finset.sum_apply]

theorem s_transform (Z : ZeroDatum X) (i : Fin D) (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    Z.s i j x = X.L.g j c x * Z.s i c x := by
  simp only [ZeroDatum.s, lin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e_transform X k j c x hx]; ring

theorem s_mem (Z : ZeroDatum X) (i : Fin D) : Z.s i ∈ X.L.sections 1 := by
  show lin X.e (Z.c i) ∈ X.L.sections 1
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)

theorem esum_pos (j : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source) :
    0 < ∑ k, ‖X.e k j x‖ ^ 2 := by
  obtain ⟨k, hk⟩ := X.gen x
  have hc := mem_source_chartIdx X.A x
  have hg := X.L.ne_zero j (chartIdx X.A x) x ⟨hx, hc⟩
  have hne : X.e k j x ≠ 0 := by
    rw [e_transform X k j (chartIdx X.A x) x ⟨hx, hc⟩]; exact mul_ne_zero hg hk
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun k => ‖X.e k j x‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ k))

theorem esum_transform (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    ∑ k, ‖X.e k j x‖ ^ 2 = ‖X.L.g j c x‖ ^ 2 * ∑ k, ‖X.e k c x‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e_transform X k j c x hx, norm_mul, mul_pow]

theorem ssum_transform (Z : ZeroDatum X) (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    ∑ i, ‖Z.s i j x‖ ^ 2 = ‖X.L.g j c x‖ ^ 2 * ∑ i, ‖Z.s i c x‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s_transform X Z i j c x hx, norm_mul, mul_pow]

theorem ssum_le (Z : ZeroDatum X) (j : Fin X.A.n) (x : X.U) :
    ∑ i, ‖Z.s i j x‖ ^ 2 ≤ rSq Z.c * ∑ k, ‖X.e k j x‖ ^ 2 := by
  unfold rSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖Z.s i j x‖ ≤ ∑ k, ‖Z.c i k‖ * ‖X.e k j x‖ := by
    simp only [ZeroDatum.s, lin_apply]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖Z.c i k‖)
    (fun k => ‖X.e k j x‖)
  calc ‖Z.s i j x‖ ^ 2 ≤ (∑ k, ‖Z.c i k‖ * ‖X.e k j x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end DivisionNearS

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotIsoX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w v'

theorem SnapperQuotIso.proof : SnapperQuotIso.Statement.{u, v, w, v'} := by
  intro k _ Ω _ _ N x E _ _ _ _ E' _ _ _ _ F₁ F₂ G₁ G₂ e
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact (Cech.equivH e.equiv e.comm i).finrank_eq

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

open Classical in

def InterNumCut.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp (n + 1) → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      interNum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i => (L i).toSubSystem)
          Lc.toSubSystem) =
        ∑ᶠ qq : Ideal (Poly k N),
          if h : qq ∈ (pp ⊔ zeroIdeal Lc.toSubSystem s).minimalPrimes ∧ IsSubvar x qq n then
            haveI : qq.IsPrime := h.1.1.1
            ((cutMult (pp ⊔ zeroIdeal Lc.toSubSystem s) qq).toNat : ℤ) *
              interNum qq (fun i => (L i).toSubSystem)
          else 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.XiPluckerCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def PluckerCover.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D) (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx), S.IsPluckerRel N F →
    ∃ (q : ℕ) (r : Fin q → MRing S.YIdx) (b : Fin q → T.YBlk → ℕ),
      (∀ j, IsMultiHomog (r j) (b j)) ∧ (∀ j, b j .line = 0) ∧
      (∀ j, rename (T.yyEmb 0) (r j) ∈ S.WW) ∧
      ∀ w : (Σ k, S.YIdx k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
        (∀ j, eval w (map (Int.castRingHom ℂ) (r j)) = 0) →
          ∃ i l k m, eval w (map (Int.castRingHom ℂ) (F i l k m)) ≠ 0

end

end GroundTheory.Heights₂.Heights.Inter
end


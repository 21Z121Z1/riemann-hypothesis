import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0209
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0216
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0210
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0177
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0211
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0214
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartSysWOfPartsOf
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FamOK {d : ℕ} (O : Set (Fin d → ℝ)) (P : WOp d) (m : ℕ) : Prop :=
  ∀ t ∈ P, t.2.length ≤ m ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O

def OpCV : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.CV k r (Y : ℂ) u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ 2 * r + k + 1 → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
        WOp.symb P j x ξ = cj * Ξ₀.charpoly.coeff (2 * r + k + 1 - j)

def OpCapR : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ)
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u → Q.IsFrameOf k r [z'] Bs →
    (∀ w : ℂ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.capR k r Bs w u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ k → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
        WOp.symb P j x ξ = cj * (cmp Ξ₀ Bs).charpoly.coeff (k - j)

def OpCapL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ)
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u → Q.IsFrameOf k r [z] Bs →
    (∀ w : ℂ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.capLft k r Bs w u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ k → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ : B.Mat k r), B.inLie k r Ξ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VL κ Φ X x = (Matrix.trace (Ξ * X)).re) →
        WOp.symb P j x ξ = cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def OpCVOf : Prop := RwChart → CapWords → OpCV

def OpCapROf : Prop := RwChart → CapRWords → OpCapR

def OpCapLOf : Prop := RwChart → CapLWords → OpCapL

def NilOfCharpoly : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), (∀ j, 1 ≤ j → j ≤ n → M.charpoly.coeff (n - j) = 0) → IsNilpotent M

def ConjAlg : Prop :=
  ∀ (k r : ℕ) (g : B.Mat k r), g ∈ B.GV k r →
    (∀ A : B.Mat k r, B.inLie k r A → B.inLie k r (g * A * g⁻¹)) ∧
    (∀ A : B.Mat k r, IsNilpotent A → IsNilpotent (g * A * g⁻¹)) ∧
    (∀ A : B.Mat k r, A ≠ 0 → g * A * g⁻¹ ≠ 0) ∧
    ∀ A X : B.Mat k r, Matrix.trace ((g * A * g⁻¹) * (g * X * g⁻¹)) = Matrix.trace (A * X)

def CovL : Prop :=
  ∀ (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)), IsChart k r d O U κ Φ →
    ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
      (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
      ∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VL κ Φ X x = (Matrix.trace ((κ x * Ξ₀ * (κ x)⁻¹) * X)).re

def opOne {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) : WOp d := [(1, [V]), (-c, [])]

theorem opOne_app {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (v : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    WOp.app (opOne V c) v x = vfD V v x - c * v x := by
  simp [opOne, WOp.app, vfW]
  ring

theorem opOne_symb {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (x ξ : Fin d → ℝ) :
    WOp.symb (opOne V c) 1 x ξ = ((ξ ⬝ᵥ V x : ℝ) : ℂ) := by
  simp [opOne, WOp.symb]

theorem opOne_ok {d : ℕ} {O : Set (Fin d → ℝ)} {V : (Fin d → ℝ) → (Fin d → ℝ)} (c : ℂ) (hV : ContDiffOn ℝ ∞ V O) :
    FamOK O (opOne V c) 1 := by
  intro t ht
  simp only [opOne, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · refine ⟨by simp, ?_⟩
    intro W hW
    simp only [List.mem_singleton] at hW
    rw [hW]; exact hV
  · exact ⟨by simp, by simp⟩

theorem re_trace_span {k r q : ℕ} (A : B.Mat k r) (Xs : Fin q → B.Mat k r) (a : Fin q → ℝ)
    (h : ∀ i, (Matrix.trace (A * Xs i)).re = 0) :
    (Matrix.trace (A * ∑ i, ((a i : ℝ) : ℂ) • Xs i)).re = 0 := by
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, h i, mul_zero]

theorem fin_shift {n : ℕ} {p : ℕ → Prop} (h : ∀ j : Fin n, p ((j : ℕ) + 1)) : ∀ j, 1 ≤ j → j ≤ n → p j := by
  intro j h1 h2
  have := h ⟨j - 1, by omega⟩
  simpa [Nat.sub_add_cancel h1] using this

theorem chartSysWOfParts_of (hCV : OpCVOf) (hCR : OpCapROf) (hCL : OpCapLOf) (hNil : NilOfCharpoly)
    (hConj : ConjAlg) (hCovL : CovL) : ChartSysWOfParts := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 k r z z' d O U κ Φ u hk hz hz' hT hT' hC hOm hG
  obtain ⟨hCk, hNR, hNL, hCLe, hCRe, hCVe⟩ := hG
  obtain ⟨huc, hfld, hw⟩ := h2 k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨q, Xs, hXs, hspan⟩ := h3 k r
  obtain ⟨Bs, hBs⟩ := h8 k r z hz hT
  obtain ⟨Bs', hBs'⟩ := h8 k r z' hz' hT'
  have oCV := hCV h2 h4 k r z z' d O U κ Φ u hC hOm hCk hCVe
  have oCR := hCR h2 h5 k r z z' d O U κ Φ u Bs' hC hOm hCk hBs' (hCRe Bs' hBs')
  have oCL := hCL h2 h6 k r z z' d O U κ Φ u Bs hC hOm hCk hBs (hCLe Bs hBs)
  have hXin : ∀ i, B.inLie k r (Xs i) := fun i => (hspan (Xs i) (hXs i)).1
  choose cR hcR using fun i => hNR (Xs i) (hXs i)
  choose cL hcL using fun i => hNL (Xs i) (hXs i)
  choose PV cV hcV0 hPVok hPVapp hPVsym using
    fun j : Fin (2 * r + k + 1) => oCV ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  choose PR cRR hcR0 hPRok hPRapp hPRsym using
    fun j : Fin k => oCR ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  choose PL cLL hcL0 hPLok hPLapp hPLsym using
    fun j : Fin k => oCL ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  have hOmx : ∀ x ∈ O, κ x ∈ JF.Om k r z z' := fun x hx => ⟨(hC.2.2.2.2.1 x hx).1, hOm x hx⟩
  refine ⟨Fin q ⊕ Fin q ⊕ Fin (2 * r + k + 1) ⊕ Fin k ⊕ Fin k, inferInstance,
    Sum.elim (fun i => opOne (VR κ Φ (Xs i)) (cR i)) (Sum.elim (fun i => opOne (VL κ Φ (Xs i)) (cL i))
      (Sum.elim PV (Sum.elim PR PL))),
    Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) (Sum.elim (fun j => (j : ℕ) + 1)
      (Sum.elim (fun j => (j : ℕ) + 1) (fun j => (j : ℕ) + 1)))),
    ?_, ?_, huc, ?_, ?_⟩
  · rintro (i | i | j | j | j)
    · show 1 ≤ 2 * r + k + 1; omega
    · show 1 ≤ 2 * r + k + 1; omega
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; exact Nat.succ_le_of_lt j.isLt
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; have := j.isLt; omega
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; have := j.isLt; omega
  · rintro (i | i | j | j | j)
    · exact opOne_ok _ (hfld _).1
    · exact opOne_ok _ (hfld _).2
    · exact hPVok j
    · exact hPRok j
    · exact hPLok j
  · rintro (i | i | j | j | j) x hx
    · show WOp.app (opOne (VR κ Φ (Xs i)) (cR i)) (fun y => u (κ y)) x = 0
      rw [opOne_app]
      have e := (hw [Xs i] (by simpa using hXin i) (by simp only [List.length_singleton]; omega) x hx).1
      simp only [B.Rw, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, vfW] at e
      rw [← e, hcR i _ (hOmx x hx), smul_eq_mul, sub_self]
    · show WOp.app (opOne (VL κ Φ (Xs i)) (cL i)) (fun y => u (κ y)) x = 0
      rw [opOne_app]
      have e := (hw [Xs i] (by simpa using hXin i) (by simp only [List.length_singleton]; omega) x hx).2
      simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, vfW] at e
      rw [← e, hcL i _ (hOmx x hx), smul_eq_mul, sub_self]
    · exact hPVapp j x hx
    · exact hPRapp j x hx
    · exact hPLapp j x hx
  · intro x hx ξ hξ hall
    obtain ⟨Ξ₀, hΞ₀, hΞ₀0, hcov⟩ := h1 k r d O U κ Φ hC x hx ξ
    have hg : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    obtain ⟨cLie, cNil, cNe, cTr⟩ := hConj k r (κ x) hg
    have hcovL := hCovL k r d O U κ Φ hC x hx ξ Ξ₀ hΞ₀ hcov
    have hΞ : B.inLie k r (κ x * Ξ₀ * (κ x)⁻¹) := cLie Ξ₀ hΞ₀
    have hNRz : ∀ i, (Matrix.trace (Ξ₀ * Xs i)).re = 0 := by
      intro i
      have h0 := hall (Sum.inl i)
      change WOp.symb (opOne (VR κ Φ (Xs i)) (cR i)) 1 x ξ = 0 at h0
      rw [opOne_symb] at h0
      rw [← hcov _ (hXin i)]
      exact_mod_cast h0
    have hNLz : ∀ i, (Matrix.trace ((κ x * Ξ₀ * (κ x)⁻¹) * Xs i)).re = 0 := by
      intro i
      have h0 := hall (Sum.inr (Sum.inl i))
      change WOp.symb (opOne (VL κ Φ (Xs i)) (cL i)) 1 x ξ = 0 at h0
      rw [opOne_symb] at h0
      rw [← hcovL _ (hXin i)]
      exact_mod_cast h0
    have hVF : ∀ j : Fin (2 * r + k + 1), Ξ₀.charpoly.coeff (2 * r + k + 1 - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inl j)))
      change WOp.symb (PV j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPVsym j x hx ξ Ξ₀ hΞ₀ hcov] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcV0 j)
    have hRF : ∀ j : Fin k, (cmp Ξ₀ Bs').charpoly.coeff (k - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
      change WOp.symb (PR j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPRsym j x hx ξ Ξ₀ hΞ₀ hcov] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcR0 j)
    have hLF : ∀ j : Fin k, (cmp (κ x * Ξ₀ * (κ x)⁻¹) Bs).charpoly.coeff (k - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))
      change WOp.symb (PL j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPLsym j x hx ξ _ hΞ hcovL] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcL0 j)
    have hnil0 : IsNilpotent Ξ₀ :=
      hNil _ Ξ₀ (fin_shift (p := fun j => Ξ₀.charpoly.coeff (2 * r + k + 1 - j) = 0) hVF)
    have hUW' := h7 k r z' Bs' hz' hT' hBs' Ξ₀ hΞ₀ (fin_shift (p := fun j => (cmp Ξ₀ Bs').charpoly.coeff (k - j) = 0) hRF)
    have hUW := h7 k r z Bs hz hT hBs _ hΞ
      (fin_shift (p := fun j => (cmp (κ x * Ξ₀ * (κ x)⁻¹) Bs).charpoly.coeff (k - j) = 0) hLF)
    refine ⟨κ x * Ξ₀ * (κ x)⁻¹, hΞ, cNe Ξ₀ (hΞ₀0 hξ), cNil Ξ₀ hnil0, ?_, ?_⟩
    · intro X hX
      rcases hX with hX | hX
      · exact hUW X hX
      · obtain ⟨_, a, rfl⟩ := hspan X hX
        exact re_trace_span _ Xs a hNLz
    · intro X hX
      rw [cTr Ξ₀ X]
      rcases hX with hX | hX
      · exact hUW' X hX
      · obtain ⟨_, a, rfl⟩ := hspan X hX
        exact re_trace_span Ξ₀ Xs a hNRz

theorem chartEqs_of_J (hCV : OpCVOf) (hCR : OpCapROf) (hCL : OpCapLOf) (hNil : NilOfCharpoly) (hConj : ConjAlg)
    (hCovL : CovL) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords) (h5 : CapRWords) (h6 : CapLWords)
    (h7 : CmpZero) (h8 : FrameEx) (hS : VOpToSOpOfSteps) (s1 : SOpField) (s2 : SOpLift) (s3 : SOpLin) : ChartEqs :=
  chartEqs_of_all (chartSysWOfParts_of hCV hCR hCL hNil hConj hCovL) h1 h2 h3 h4 h5 h6 h7 h8 hS s1 s2 s3

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousHsInner
section
open Matrix MeasureTheory Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cont

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem continuous_hsInner [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] :
    Continuous fun q : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => B.hsInner q.1 q.2 := by
  have hv : Continuous (fun A : Wq →L[ℂ] Wp => B.hsVec A) := by
    unfold B.hsVec
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_eval_const _)
  unfold B.hsInner
  exact (hv.comp continuous_snd).inner (hv.comp continuous_fst)

theorem radSp_contOn {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (Ψ : RadSp k r z z' π π') (c0 : Fin r → ℂ) {g : ℂ → Mx k r} {O : Set ℂ}
    (hO : IsOpen O) (hg : ContinuousOn g O) (hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR k r z z') :
    ContinuousOn (fun ζ => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ)) O := by
  intro ζ₀ hζ₀
  have hmem := Ψ.2
  obtain ⟨-, hs, -⟩ := hmem
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c0, g ζ₀) (hdom ζ₀ hζ₀)
  have hgA : ContinuousAt g ζ₀ := hg.continuousAt (hO.mem_nhds hζ₀)
  have hpA : ContinuousAt (fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) ζ₀ :=
    continuousAt_const.prodMk hgA
  have hev : ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ O ∧ ((c0, g ζ) : (Fin r → ℂ) × Mx k r) ∈ U :=
    Filter.Eventually.and (hO.mem_nhds hζ₀) (hpA.preimage_mem_nhds (hU.mem_nhds hxU))
  have hFc : ContinuousAt F (c0, g ζ₀) := hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  have hcomp : ContinuousAt (fun ζ => F (c0, g ζ)) ζ₀ :=
    ContinuousAt.comp (g := F) (f := fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) hFc hpA
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [hev] with ζ hζ
  exact (hΦ (c0, g ζ) hζ.2 (hdom ζ hζ.1).2.1).symm

theorem topDens_contOn {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (x y : Ix S → RadSp k r z z' π π') (c0 : Fin r → ℂ) {g : ℂ → Mx k r} {O : Set ℂ}
    (hO : IsOpen O) (hg : ContinuousOn g O) (hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR k r z z') :
    ContinuousOn (fun ζ => topDens L st w x y c0 (g ζ)) O := by
  have h1 : ∀ e, ContinuousOn (fun ζ => B.hsInner
      ((act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ))
      ((act (Fr.ofWord L st w).F y e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ))) O := by
    intro e
    have ha := radSp_contOn (act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e) c0 hO hg hdom
    have hb := radSp_contOn (act (Fr.ofWord L st w).F y e) c0 hO hg hdom
    have hc := continuous_hsInner.comp_continuousOn (ha.prodMk hb)
    exact hc
  have h2 := continuousOn_finset_sum Finset.univ (fun e _ => h1 e)
  refine h2.congr fun ζ _ => ?_
  unfold topDens
  rfl

end cont

theorem one_mem_UWset {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z := by
  simp [UWset, UH]

theorem topContOn_of (hP : P5.ThmPActualCpt) (hHT : KB.HeadTop) : TopContOn := by
  intro Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' Cb hθ hF hw
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨P.r, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r)) with hμ
  obtain ⟨K, -, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hcx : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h hh.2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h hh hF e
  have hcx' : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h' hh'.2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h' hh' hF e
  choose Φ hΦK hΦ using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx e)
  choose Φ' hΦ'K hΦ' using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx' e)
  have hHTx := hHT Wp Wq P p F w h h' hh hh' X μ L st Cb Φ Φ' hD hθ hF hw hΦ hΦ'
  have hTT : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T * P.T' := by
    have e1 := hPl.2.2.2.1
    have e2 := hPl.2.2.2.2.1
    exact congrArg₂ (· * ·) e1 e2
  let O : Set ℂ := {c : ℂ | P.T * P.T' < Complex.normSq c}
  have hO : IsOpen O := isOpen_lt continuous_const Complex.continuous_normSq
  let g : ℂ → Mx P.k (P.r - P.r) := fun ζ => B2.embWb P.k (P.r - P.r) ((p.T.bs P.r).μsec ζ)
  let c0 : Fin (P.r - P.r) → ℂ := fun _ => 1
  have hfacts : ∀ ζ ∈ O, g ζ ∈ B2.UWb P.k (P.r - P.r) ∧
      herm (Hpk P.k (P.r - P.r)) (g ζ *ᵥ (p.T.bs P.r).z') (p.T.bs P.r).z = ζ := by
    intro ζ hζ
    have hζ' : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' < Complex.normSq ζ := by rw [hTT]; exact hζ
    have := Formalism.FourierDecayAlt.P.b2_rank_one_mem P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).μsec (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem (p.T.bs P.r).sec ζ hζ'
      1 (one_mem_UWset _) 1 (one_mem_UWset _)
    simpa using this
  have hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' := by
    intro ζ hζ
    obtain ⟨hmem, hherm⟩ := hfacts ζ hζ
    refine ⟨fun _ => one_ne_zero, Formalism.FourierDecayAlt.P.JCx2.rb_uwb_glev hmem, ?_⟩
    unfold Q.GGl
    rw [P5.Rad.zetaL_last, hherm, hTT]
    exact sub_pos.2 hζ
  have hzeta : ∀ ζ ∈ O, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (g ζ) = ζ := by
    intro ζ hζ
    rw [P5.Rad.zetaL_last, (hfacts ζ hζ).2]
  have hg : ContinuousOn g O := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    simp only [g, B2.embWb]
    split_ifs
    · exact ((p.T.bs P.r).sec.1 _ _).continuousOn.mono (fun ζ hζ => by
        simp only [Set.mem_ofPred_eq]; rw [hTT]; exact hζ)
    · exact continuousOn_const
    · exact continuousOn_const
  have hcont : ContinuousOn (fun ζ => topDens L st (D.positionted w) Φ Φ' c0 (g ζ)) O :=
    topDens_contOn L st (D.positionted w) Φ Φ' c0 hO hg hdom
  refine hcont.congr fun ζ hζ => ?_
  have := hHTx (c0, g ζ) (hdom ζ hζ)
  simp only [] at this
  rw [hzeta ζ hζ] at this
  exact this.symm

end Formalism.FourierDecayAlt.P.PBO
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyReal
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem energy_reality_holds : EnergyReal :=
  ER.energyReal_of_capAdjInt (ER.capAdjInt_of_scalar ER.capacity_adjoint_scalar)

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCont
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gf_sgs (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) (g : B.Mat k r) :
    Gf k r D.z D.z' (B.sgs p g) = Gf k r D.z D.z' g := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hn1 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ ∈ Q.Nlev k r 0 := by
    refine ⟨Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.n_inv_mem hn, ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutMP.ER.CAS.level_zero_set_eq_group]
    exact (Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.n_inv_mem hn).1
  have hn2 : (Matrix.of p.2.2 : B.Mat k r) ∈ Q.Nlev k r 0 := by
    refine ⟨hn', ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutMP.ER.CAS.level_zero_set_eq_group]
    exact hn'.1
  have e1 := Formalism.FourierDecayAlt.P.CutMP.gf_SgS D (Formalism.FourierDecayAlt.P.CutMP.h_mem_Sset D.z (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh))
    (Formalism.FourierDecayAlt.P.CutMP.h_mem_Sset D.z' hh') ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * g * Matrix.of p.2.2)
  have e2 := Formalism.FourierDecayAlt.P.CutMP.gf_SgS D (Formalism.FourierDecayAlt.P.CutMP.n_mem_Sset D.z hn1)
    (Formalism.FourierDecayAlt.P.CutMP.n_mem_Sset D.z' hn2) g
  unfold B.sgs
  rw [← e2, ← e1]
  congr 1
  simp only [mul_assoc]

theorem sgs_mem (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) {g : B.Mat k r}
    (hg : g ∈ B.GV k r) : B.sgs p g ∈ B.GV k r := by
  rw [Formalism.FourierDecayAlt.P.B5.sgs_eq]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
    (Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem (Formalism.FourierDecayAlt.P.B5.inSS_left D hp)) hg) (Formalism.FourierDecayAlt.P.B5.inSS_right D hp)

theorem sgs_continuous (p : B.SS k r) : Continuous (B.sgs p : B.Mat k r → B.Mat k r) := by
  unfold B.sgs
  exact (((continuous_const : Continuous fun _ : B.Mat k r =>
    (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹).matrix_mul continuous_id).matrix_mul
    continuous_const).matrix_mul continuous_const

theorem suppIn_rho (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : B.SuppIn (B.GPos D) F) : B.SuppIn (B.GPos D) (B.rho D p F) := by
  intro x hx
  have hxG : x ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (fun y hy => hy.1) hx
  have hsub : {g | g ∈ B.GV k r ∧ B.rho D p F g ≠ 0} ⊆ B.sgs p ⁻¹' {g | g ∈ B.GV k r ∧ F g ≠ 0} := by
    intro y hy
    refine ⟨sgs_mem D hp hy.1, fun h0 => hy.2 ?_⟩
    unfold B.rho
    rw [h0]
    simp
  have h1 : x ∈ B.sgs p ⁻¹' closure {g | g ∈ B.GV k r ∧ F g ≠ 0} :=
    (sgs_continuous p).closure_preimage_subset _ (closure_mono hsub hx)
  have h2 := hF h1
  refine ⟨hxG, ?_⟩
  have := h2.2
  rwa [gf_sgs D hp] at this

variable [FiniteDimensional ℂ Wq]

theorem ckOn_opAdj (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (hs : B.SmoothCoef (B.GPos D) Θ)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F) (hFs : B.SuppIn (B.GPos D) F) :
    B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) := by
  unfold B.opAdj
  refine Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_list_sum Θ
    (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) (fun T hT => ?_)
  exact Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' (Formalism.FourierDecayAlt.P.B5.ckOn_coef (hs T hT).2 hF hFs)
    T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)))

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

theorem adjoint_continuity_holds : AdjCont := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs f hf _ hfs p hp
  exact ⟨Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_opAdj D Θ hs (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) (suppIn_rho D hp hfs)),
    Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp (ckOn_opAdj D Θ hs hf hfs))⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocDone
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jALocCC_of_op (h2 : JALocOp) (h3 : JALocAdj) : JALocCC :=
  jALocCC_of_leaves h2 h3 local_phi_transfer_holds local_additivity_transfer local_square_integrable_transfer

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExistence
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem frame_existence : FrameEx := fun _ _ _ hz hT => Qx8.frame_exists hz hT

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end


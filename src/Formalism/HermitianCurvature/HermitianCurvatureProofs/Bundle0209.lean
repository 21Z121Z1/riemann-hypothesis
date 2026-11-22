import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203
import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0193
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vfw

variable {d : ℕ}

def vfD (V : (Fin d → ℝ) → (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  fun x => fderiv ℝ u x (V x)

def vfW : List ((Fin d → ℝ) → (Fin d → ℝ)) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | V :: Vs, u => vfD V (vfW Vs u)

abbrev WOp (d : ℕ) := List (ℂ × List ((Fin d → ℝ) → (Fin d → ℝ)))

def WOp.app (P : WOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  (P.map fun t => t.1 * vfW t.2 u x).sum

def WOp.symb (P : WOp d) (m : ℕ) (x ξ : Fin d → ℝ) : ℂ :=
  (P.map fun t => if t.2.length = m then t.1 * (t.2.map fun V => ((ξ ⬝ᵥ V x : ℝ) : ℂ)).prod else 0).sum

end vfw

def VOpToSOp : Prop :=
  ∀ (d m : ℕ) (P : WOp d) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ t ∈ P, t.2.length ≤ m ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) →
    ∃ S : SOp d, S.ord = m ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ (m : WithTop ℕ∞) u O → ∀ x ∈ O, S.app u x = WOp.app P u x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb P m x ξ

def IsChart (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)) : Prop :=
  IsOpen O ∧ IsOpen U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def VR {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (κ x * X)

def VL {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (X * κ x)

def ChartSysW : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → WOp d) (m : ι → ℕ),
      (∀ j, m j ≤ 2 * r + k + 1) ∧ (∀ j, ∀ t ∈ P j, t.2.length ≤ m j ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, WOp.app (P j) (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, WOp.symb (P j) (m j) x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

theorem chartEqs_of (hA : ChartSysW) (hB : VOpToSOp) : ChartEqs := by
  intro k r z z' d O U κ Φ u hk hz hz' hT hT' hO hU hκ hΦ hκO hΦU hOm hG
  obtain ⟨ι, hι, P, m, hm, hP, huc, hPu, hsym⟩ :=
    hA k r z z' d O U κ Φ u hk hz hz' hT hT' ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ hOm hG
  have hS : ∀ j, ∃ S : SOp d, S.ord = m j ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ v : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((m j : ℕ) : WithTop ℕ∞) v O → ∀ x ∈ O,
        S.app v x = WOp.app (P j) v x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb (P j) (m j) x ξ :=
    fun j => hB d (m j) (P j) O hO (hP j)
  choose S hSo hSc hSa hSs using hS
  refine ⟨ι, hι, S, fun j => hSc j, fun j => by rw [hSo j]; exact hm j, huc, ?_, ?_⟩
  · intro j x hx
    rw [hSa j _ (huc.of_le (by exact_mod_cast hm j)) x hx]
    exact hPu j x hx
  · intro x hx ξ hξ hall
    exact hsym x hx ξ hξ (fun j => by rw [← hSs j x hx ξ]; exact hall j)

def ChartCov : Prop :=
  ∀ (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)), IsChart k r d O U κ Φ →
    ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ∃ Ξ₀ : B.Mat k r, B.inLie k r Ξ₀ ∧ (ξ ≠ 0 → Ξ₀ ≠ 0) ∧
      ∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re

def RwChart : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u →
    ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
    (∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VR κ Φ X) O ∧ ContDiffOn ℝ ∞ (VL κ Φ X) O) ∧
    ∀ Xs : List (B.Mat k r), (∀ X ∈ Xs, B.inLie k r X) → Xs.length ≤ 2 * r + k + 1 → ∀ x ∈ O,
      B.Rw Xs u (κ x) = vfW (Xs.map (VR κ Φ)) (fun y => u (κ y)) x ∧
      Xs.foldr Q.LdV u (κ x) = vfW (Xs.map (VL κ Φ)) (fun y => u (κ y)) x

def LieNFin : Prop :=
  ∀ (k r : ℕ), ∃ (q : ℕ) (Xs : Fin q → B.Mat k r), (∀ i, Xs i ∈ JfS.lieOf (Nset k r)) ∧
    ∀ X ∈ JfS.lieOf (Nset k r), B.inLie k r X ∧ ∃ a : Fin q → ℝ, X = ∑ i, ((a i : ℝ) : ℂ) • Xs i

def CapWords : Prop :=
  ∀ (k r j : ℕ), 1 ≤ j → j ≤ 2 * r + k + 1 →
    ∃ (Ys : Fin (2 * r + k + 2) → ℝ) (lam : Fin (2 * r + k + 2) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.CV k r (Ys i : ℂ) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * Ξ.charpoly.coeff (2 * r + k + 1 - j)

def cmp {k r : ℕ} (Ξ : B.Mat k r) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => Matrix.trace (Ξ * Q.unitB (Hpk k r) Bs a b)

def CapRWords : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z'] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capR k r Bs (ws i) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CapLWords : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capLft k r Bs (ws i) f g = (L.map fun t => t.1 • t.2.foldr Q.LdV f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CmpZero : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    Q.IsFrameOf k r [z] Bs → ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
    (∀ j, 1 ≤ j → j ≤ k → (cmp Ξ Bs).charpoly.coeff (k - j) = 0) →
    ∀ X ∈ JfS.lieOf (UWset k r z), (Matrix.trace (Ξ * X)).re = 0

def FrameEx : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs

def ChartSysWOfParts : Prop :=
  ChartCov → RwChart → LieNFin → CapWords → CapRWords → CapLWords → CmpZero → FrameEx → ChartSysW

theorem chartEqs_of_parts (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hB : VOpToSOp) : ChartEqs :=
  chartEqs_of (hJ h1 h2 h3 h4 h5 h6 h7 h8) hB

def SOpField : Prop :=
  ∀ (d : ℕ) (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) → ContDiffOn ℝ ∞ V O →
    ∃ S' : SOp d, S'.ord = S.ord + 1 ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((S.ord + 1 : ℕ) : WithTop ℕ∞) u O → ∀ x ∈ O,
        S'.app u x = vfD V (S.app u) x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S'.symb x ξ = ((ξ ⬝ᵥ V x : ℝ) : ℂ) * S.symb x ξ

def SOpLift : Prop :=
  ∀ (d : ℕ) (S : SOp d) (m' : ℕ) (O : Set (Fin d → ℝ)), S.ord ≤ m' → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    ∃ S' : SOp d, S'.ord = m' ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧ (∀ u x, S'.app u x = S.app u x) ∧
      ∀ x ξ, S'.symb x ξ = if S.ord = m' then S.symb x ξ else 0

def SOpLin : Prop :=
  ∀ (d : ℕ) (S T : SOp d) (c : ℂ) (O : Set (Fin d → ℝ)), S.ord = T.ord → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    (∀ i w, ContDiffOn ℝ ∞ (T.a i w) O) →
    ∃ R : SOp d, R.ord = S.ord ∧ (∀ i w, ContDiffOn ℝ ∞ (R.a i w) O) ∧
      (∀ u x, R.app u x = c * S.app u x + T.app u x) ∧ ∀ x ξ, R.symb x ξ = c * S.symb x ξ + T.symb x ξ

def VOpToSOpOfSteps : Prop := SOpField → SOpLift → SOpLin → VOpToSOp

theorem chartEqs_of_all (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hS : VOpToSOpOfSteps) (s1 : SOpField)
    (s2 : SOpLift) (s3 : SOpLin) : ChartEqs :=
  chartEqs_of_parts hJ h1 h2 h3 h4 h5 h6 h7 h8 (hS s1 s2 s3)

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ClassicalToWeakSolution
section
open scoped ContDiff
open MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

section ctw

variable {d : ℕ}

theorem ctw_pdc_append (l₁ l₂ : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    pdc (l₁ ++ l₂) f = pdc l₁ (pdc l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, pdc, ih]

theorem ctw_contDiffOn_pdc {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    ∀ (l : List (Fin d)) (m n : ℕ) (f : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l.length + m ≤ n →
      ContDiffOn ℝ m (pdc l f) U
  | [], m, n, f, hf, hl => hf.of_le (by simp only [List.length_nil, zero_add] at hl; exact_mod_cast hl)
  | i :: l, m, n, f, hf, hl => by
      have ih := ctw_contDiffOn_pdc hU l (m + 1) n f hf (by simp only [List.length_cons] at hl; omega)
      simp only [pdc]
      exact (ih.fderiv_of_isOpen hU (by push_cast; exact le_rfl)).clm_apply contDiffOn_const

theorem ctw_pdc_congr {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    ∀ (l : List (Fin d)) (f g : (Fin d → ℝ) → ℂ), Set.EqOn f g U → Set.EqOn (pdc l f) (pdc l g) U
  | [], _, _, h => h
  | i :: l, f, g, h => by
      intro x hx
      have ih := ctw_pdc_congr hU l f g h
      simp only [pdc]
      rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih)]

theorem ctw_swap {U : Set (Fin d → ℝ)} (hU : IsOpen U) {g : (Fin d → ℝ) → ℂ} (hg : ContDiffOn ℝ 2 g U)
    {x : Fin d → ℝ} (hx : x ∈ U) (v w : Fin d → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  have hga : ContDiffAt ℝ 2 g x := hg.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hga.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs := hga.isSymmSndFDerivAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const v), fderiv_clm_apply hd (differentiableAt_const w)]
  simp [hs w v]

theorem ctw_pdc_perm {U : Set (Fin d → ℝ)} (hU : IsOpen U) {l₁ l₂ : List (Fin d)} (hp : l₁.Perm l₂) :
    ∀ (n : ℕ) (f : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l₁.length ≤ n →
      Set.EqOn (pdc l₁ f) (pdc l₂ f) U := by
  induction hp with
  | nil => intro n f _ _; exact Set.eqOn_refl _ _
  | @cons a m₁ m₂ hp ih =>
      intro n f hf hl
      have h := ih n f hf (by simp only [List.length_cons] at hl; omega)
      have e1 := ctw_pdc_append [a] m₁ f
      have e2 := ctw_pdc_append [a] m₂ f
      simp only [List.singleton_append] at e1 e2
      rw [e1, e2]
      exact ctw_pdc_congr hU [a] _ _ h
  | swap a b l =>
      intro n f hf hl x hx
      have hg : ContDiffOn ℝ 2 (pdc l f) U :=
        ctw_contDiffOn_pdc hU l 2 n f hf (by simp only [List.length_cons] at hl; omega)
      simp only [pdc]
      exact ctw_swap hU hg hx _ _
  | trans h₁ _ ih₁ ih₂ =>
      intro n f hf hl
      exact (ih₁ n f hf hl).trans (ih₂ n f hf (h₁.length_eq ▸ hl))

theorem ctw_integrable {U : Set (Fin d → ℝ)} (hU : IsOpen U) {F G : (Fin d → ℝ) → ℂ}
    (hF : ContinuousOn F U) (hG : Continuous G) (hGc : HasCompactSupport G) (hGU : tsupport G ⊆ U) :
    Integrable (fun x => F x * G x) := by
  have hc : Continuous (fun x => F x * G x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hF.continuousAt (hU.mem_nhds hx)).mul hG.continuousAt
    · have h0 : G =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hGU h))
      have h1 : (fun x => F x * G x) =ᶠ[nhds x] fun _ => 0 := h0.mono fun y hy => by simp [hy]
      exact continuousAt_const.congr h1.symm
  have hcs : HasCompactSupport (F * G) := hGc.mul_left
  exact hc.integrable_of_hasCompactSupport hcs

theorem ctw_tsupport_pdc (l : List (Fin d)) (ψ : (Fin d → ℝ) → ℂ) : tsupport (pdc l ψ) ⊆ tsupport ψ := by
  induction l with
  | nil => exact subset_rfl
  | cons i l ih =>
      refine subset_trans ?_ ((tsupport_fderiv_subset ℝ).trans ih)
      refine closure_mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h
      apply hx
      simp only [pdc, h, zero_apply]

theorem ctw_contDiff_pdc (l : List (Fin d)) {ψ : (Fin d → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (pdc l ψ) := by
  induction l with
  | nil => exact hψ
  | cons i l ih =>
      simp only [pdc]
      exact contDiff_infty.2 fun n =>
        ((contDiff_infty.1 ih (n + 1)).fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const

theorem ctw_ibp {U : Set (Fin d → ℝ)} (hU : IsOpen U) (l : List (Fin d)) :
    ∀ (n : ℕ) (f ψ : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l.length ≤ n → ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, f x * pdc l ψ x = (-1 : ℂ) ^ l.length * ∫ x, pdc l.reverse f x * ψ x := by
  induction l with
  | nil => intro n f ψ _ _ _ _ _; simp [pdc]
  | cons i l ih =>
      intro n f ψ hf hl hψ hψc hψU
      have hl' : l.length + 1 ≤ n := by simpa using hl
      have hgs : ContDiff ℝ ∞ (pdc l ψ) := ctw_contDiff_pdc l hψ
      have hgt : tsupport (pdc l ψ) ⊆ tsupport ψ := ctw_tsupport_pdc l ψ
      have hgc : HasCompactSupport (pdc l ψ) := hψc.mono' ((subset_tsupport _).trans hgt)
      have hg's : ContDiff ℝ ∞ (pdc (i :: l) ψ) := ctw_contDiff_pdc (i :: l) hψ
      have hg't : tsupport (pdc (i :: l) ψ) ⊆ tsupport ψ := ctw_tsupport_pdc (i :: l) ψ
      have hg'c : HasCompactSupport (pdc (i :: l) ψ) := hψc.mono' ((subset_tsupport _).trans hg't)
      have hf1 : ContDiffOn ℝ ((n - 1 : ℕ)) (pdc [i] f) U :=
        ctw_contDiffOn_pdc hU [i] (n - 1) n f hf (by simp only [List.length_cons, List.length_nil]; omega)
      have hf0 : ContinuousOn (pdc [i] f) U :=
        (ctw_contDiffOn_pdc hU [i] 0 n f hf (by simp only [List.length_cons, List.length_nil]; omega)).continuousOn
      have hstep : ∫ x, f x * pdc (i :: l) ψ x = -∫ x, pdc [i] f x * pdc l ψ x := by
        have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
          (f := f) (g := pdc l ψ) (v := (Pi.single i 1 : Fin d → ℝ))
          (ctw_integrable hU hf0 hgs.continuous hgc (hgt.trans hψU))
          (ctw_integrable hU hf.continuousOn hg's.continuous hg'c (hg't.trans hψU))
          (ctw_integrable hU hf.continuousOn hgs.continuous hgc (hgt.trans hψU))
          (fun x hx => (hf.contDiffAt (hU.mem_nhds (hψU (hgt hx)))).differentiableAt
            (by exact_mod_cast (show n ≠ 0 by omega)))
          (fun x _ => hgs.differentiable (by simp) x)
        exact h
      rw [hstep, ih (n - 1) (pdc [i] f) ψ hf1 (by omega) hψ hψc hψU, List.reverse_cons, ctw_pdc_append,
        List.length_cons, pow_succ]
      ring

theorem ctw_smooth_mul {U : Set (Fin d → ℝ)} (hU : IsOpen U) {a φ : (Fin d → ℝ) → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (hφ : ContDiff ℝ ∞ φ) (hφU : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => a y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (ha.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have h0 : φ =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hφU h))
    have h1 : (fun y => a y * φ y) =ᶠ[nhds x] fun _ => 0 := h0.mono fun y hy => by simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h1

end ctw

theorem classical_to_weak_solution : ClassToWeak := by
  intro d N P U u hU ha hord hu hPu φ hφ hφc hφU
  have hφ0 : ∀ x, x ∉ U → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))
  have hψ : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      ContDiff ℝ ∞ (fun y => P.a k w y * φ y) ∧ HasCompactSupport (fun y => P.a k w y * φ y) ∧
        tsupport (fun y => P.a k w y * φ y) ⊆ U := fun k w =>
    ⟨ctw_smooth_mul hU (ha k w) hφ hφU, hφc.mul_left, tsupport_mul_subset_right.trans hφU⟩
  have hk : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d), (List.ofFn w).length ≤ N := fun k w => by
    rw [List.length_ofFn]; have := k.isLt; omega
  have hint : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      Integrable (fun x => u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x)) :=
    fun k w => by
      obtain ⟨h1, h2, h3⟩ := hψ k w
      refine ctw_integrable hU hu.continuousOn (continuous_const.mul (ctw_contDiff_pdc _ h1).continuous)
        ((h2.mono' ((subset_tsupport _).trans (ctw_tsupport_pdc _ _))).mul_left)
        (tsupport_mul_subset_right.trans ((ctw_tsupport_pdc _ _).trans h3))
  have hint2 : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      Integrable (fun x => P.a k w x * pdc (List.ofFn w) u x * φ x) := fun k w =>
    ctw_integrable hU (((ha k w).continuousOn).mul
      (ctw_contDiffOn_pdc hU (List.ofFn w) 0 N u hu (by simpa using hk k w)).continuousOn) hφ.continuous hφc hφU
  have hterm : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      ∫ x, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) =
        ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x := by
    intro k w
    obtain ⟨h1, h2, h3⟩ := hψ k w
    have hI := ctw_ibp hU (List.ofFn w) N u _ hu (hk k w) h1 h2 h3
    have hperm := ctw_pdc_perm hU (List.reverse_perm (List.ofFn w)) N u hu
      (by rw [List.length_reverse]; exact hk k w)
    calc ∫ x, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x)
        = (-1 : ℂ) ^ (k : ℕ) * ∫ x, u x * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x := by
          rw [← integral_const_mul]; congr 1; funext x; ring
      _ = ∫ x, pdc (List.ofFn w).reverse u x * (P.a k w x * φ x) := by
          rw [hI, List.length_ofFn, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
      _ = ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x := by
          congr 1; funext x
          by_cases hx : x ∈ U
          · rw [hperm hx]; ring
          · simp [hφ0 x hx]
  have hsplit : (fun x => u x * P.tr φ x) = fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d,
      u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) := by
    funext x; simp only [SOp.tr, Finset.mul_sum]
  have hinner : ∀ k : Fin (P.ord + 1),
      ∫ x, ∑ w : Fin k → Fin d, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) =
        ∫ x, ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x := fun k => by
    rw [integral_finsetSum _ (fun w _ => hint k w), integral_finsetSum _ (fun w _ => hint2 k w)]
    exact Finset.sum_congr rfl (fun w _ => hterm k w)
  rw [hsplit, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint k w)),
    Finset.sum_congr rfl (fun k _ => hinner k),
    ← integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint2 k w))]
  have h0 : (fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x) =
      fun _ => (0 : ℂ) := by
    funext x
    have e : ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x =
        P.app u x * φ x := by simp only [SOp.app, Finset.sum_mul]
    rw [e]
    by_cases hx : x ∈ U
    · rw [hPu x hx, zero_mul]
    · rw [hφ0 x hx, mul_zero]
  rw [h0, integral_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERAsm
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem energyReal_of_capAdj (hA : CapAdj) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_leaves hA capacity_theta_facts coefficient_vector_smoothness coefficient_vector_in_class coefficient_vector_support coefficient_vector_congr coefficient_vector_commutation
    beta_form_congr_holds

theorem energyReal_of_capAdjInt (hI : CapAdjInt) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_capAdj (capAdj_of_int hI)

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocAdd
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem locAdd_thr (k r : ℕ) {A : ℝ} (hA : 10 * ((r : ℝ) + 1) * nDim k r ^ 2 ≤ A) : JF.TransportedAlt k r A 0 := by
  unfold JF.TransportedAlt
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hA' : 10 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ A := by simpa [nDim] using hA
  have hn2 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  rw [lt_div_iff₀ (by positivity)]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  nlinarith [mul_pos hr (lt_of_lt_of_le one_pos hn2)]

theorem local_additivity_transfer : JALocAdd := by
  refine ⟨10, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A J J' hBg hA hJ hJ'
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hThr := locAdd_thr S.G.k S.G.r hA
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_add hJ.1 hJ'.1, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨F', hF1', hF2', hF3'⟩ := hJ'.2 δ hδ
  refine ⟨F + F', Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hF1 hF1', fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c, hc⟩ := hF2 m
    obtain ⟨c', hc'⟩ := hF2' m
    exact ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩
  · have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
    have hg := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
    have h0 : B.InCC A 0 F := by simpa using hF2 0
    have h0' : B.InCC A 0 F' := by simpa using hF2' 0
    have i1 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F hThr h0).1 _ hg
    have i2 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F' hThr h0').1 _ hg
    have e : ∀ G : GFn S v, B.JF (T v).base G (B.gq (T v).base x) =
        ∫ p, JF.integrand (T v).base G (B.gq (T v).base x) p ∂(T v).base.μSS := fun G => rfl
    rw [Pi.add_apply, hF3 x hx hG, hF3' x hx hG, e, e, e, ← integral_add i1 i2]
    congr 1
    funext p
    simp only [JF.integrand, B.rho, Pi.add_apply, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, smul_add]

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecFinal
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_section_holds : Formalism.FourierDecayAlt.P.CutMP.JA.SA.SASection :=
  Formalism.FourierDecayAlt.P.CutMP.JA.SA.sASection_of_parts Formalism.FourierDecayAlt.P.CutMP.JA.SA.radial_section_holds
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_descent_holds Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_cover_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end


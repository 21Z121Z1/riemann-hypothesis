import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PTopDensCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0001
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundDefs
section
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def tN {m n : ℕ} (v : Fin m → Fin n → ℂ) : ℝ := Real.sqrt (∑ b, ∑ i, Complex.normSq (v b i))

def Mf (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a b => herm (Hpk k r) (v b) (fvec k r z a)

def XF (k r : ℕ) : ℝ := ((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3

def OneSide : Prop :=
  ∃ C : ℕ, ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ0 : Measure (Mt k r)),
    1 ≤ k → 1 ≤ r → C2.StdZ k r z → B.IsHaarOn (C2.N0set k r z) μ0 →
    ∀ (ε B' : ℝ), 0 < ε → (C : ℝ) * XF k r ≤ B' → ∃ K : ℝ, 0 ≤ K ∧
      ∀ v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ, ε ≤ Complex.normSq (Mf k r z v).det →
        ∫⁻ x, ENNReal.ofReal (tN (fun b => (Matrix.of x : B.Mat k r)⁻¹ *ᵥ v b) ^ (-B')) ∂μ0 ≤
          ENNReal.ofReal (K * (1 + zN (Mf k r z v)) ^ (-(B' - (C : ℝ) * XF k r)))

def PtBound : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∃ c : ℝ, 0 < c ∧ ∀ (x : B.SS k r) (g : B.Mat k r),
      Matrix.of x.1.1 ∈ UWset k r z → Matrix.of x.1.2 ∈ C2.N0set k r z →
      Matrix.of x.2.1 ∈ UWset k r z' → Matrix.of x.2.2 ∈ C2.N0set k r z' → g ∈ B.GV k r →
      c * (tN (fun b => (Matrix.of x.1.2 : B.Mat k r)⁻¹ *ᵥ (g *ᵥ fvec k r z' b)) *
          tN (fun a => (Matrix.of x.2.2 : B.Mat k r)⁻¹ *ᵥ (g⁻¹ *ᵥ fvec k r z a))) ≤ B.gN (B.sgs x g) ^ 2

def ZhatAdj : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r), g ∈ B.GV k r →
    Mf k r z' (fun a => g⁻¹ *ᵥ fvec k r z a) = (Zhat k r z z' g)ᴴ

def DetBound : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (ε : ℝ), C2.StdZ k r z → C2.StdZ k r z' →
    ε ≤ Gf k r z z' g → ε ≤ Complex.normSq (Zhat k r z z' g).det

def UWFin : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), 1 ≤ k → C2.StdZ k r z →
    B.IsHaarOn (UWset k r z) μ → μ Set.univ < ⊤

def PosP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (n : B.Mat k r) (v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ),
    n ∈ B.GV k r → (Mf k r z v).det ≠ 0 → 0 < tN (fun b => n⁻¹ *ᵥ v b)

def ZNAdj : Prop := ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) ℂ), zN Zᴴ = zN Z

end PI.UnitaryGroupMassFormula.DLm
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PTopDensFr
section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def frVal (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq)) (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  ((L g).1 : Wp →L[ℂ] Wp).comp ((fibInt D μ0 μ0' F g).comp ((L g).2 : Wq →L[ℂ] Wq))

def IsFrameAlg (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r))
    (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq)) : Prop :=
  (∀ g ∈ B.GV k r, 0 < Gf k r D.z D.z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      0 < Gf k r D.z D.z' (n⁻¹ * g * n') ∧ L (n⁻¹ * g * n') = L g) ∧
  (∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)), ∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r, 0 < Gf k r D.z D.z' g₁ →
      Zhat k r D.z D.z' g₁ = Zhat k r D.z D.z' g₂ → frVal D μ0 μ0' F L g₁ = frVal D μ0 μ0' F L g₂)

open Classical in

def phi0 (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) {p m' : ℕ} (hps : p + (m' + 1 + 1) = r + 1) :
    G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp) := fun Z =>
  if h : ∃ g, g ∈ B.GV k r ∧ 0 < Gf k r D.z D.z' g ∧ castM hps.symm (Zhat k r D.z D.z' g) = Z then
    frVal D μ0 μ0' F L (Classical.choose h) else 0

end

def UnipotentHaarExists : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∃ μ : Measure (Mt k r), B.IsHaarOn (C2.N0set k r z) μ

def FramesDecay : Prop :=
  ∀ C₂ : ℕ, ∃ C CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    ∀ μ0 μ0' : Measure (Mt k r), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∃ L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq), IsFrameAlg D μ0 μ0' L ∧ ∃ K : ℝ,
      U.DecayAll (C₂ * (m' + 2) ^ 2)
        (fun j => A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) K
        (phi0 D μ0 μ0' L F' hps)

end PI.UnitaryGroupMassFormula.DLm
end
end


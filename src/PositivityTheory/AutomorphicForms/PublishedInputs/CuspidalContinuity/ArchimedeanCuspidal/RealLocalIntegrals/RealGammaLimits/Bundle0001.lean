import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Z2

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable
section
noncomputable section

open MeasureTheory Complex

namespace Ad3.LR.C

def prI (k : ℕ) (Φ : Sw) (δ : Bool) (s : ℂ) (p : ℝˣ × M22) : ℂ :=
  Wm k (d2 p.1 * (Matrix.of p.2)⁻¹) * inn Φ 1 (Matrix.of p.2) * sg (Matrix.of p.2).det *
    ((|(Matrix.of p.2).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * chR δ (s - 1 / 2) p.1

def PrimPt : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (a : ℝˣ),
  sec k Φ (dg a 1 1) = ((|(a : ℝ)| ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
    ∫ h : M22, Wm k (d2 a * (Matrix.of h)⁻¹) * inn Φ 1 (Matrix.of h) * sg (Matrix.of h).det *
      ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

def PrimInt : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 →
  Integrable (prI k Φ δ s) (mulR.prod volume)

def Prim : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 →
  ∫ a, sec k Φ (dg a 1 1) * chR δ (s - 1) a ∂mulR =
    ∫ h : M22, inn Φ 1 (Matrix.of h) * sg (Matrix.of h).det *
      ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * z2 k δ s (Matrix.of h)⁻¹

def AbsoluteZetaIntegralBound : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ C : ℝ, ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
  Integrable (fun a : ℝˣ => ‖Wm k (d2 a * g)‖ * |(a : ℝ)| ^ (σ - 1 / 2)) mulR ∧
  ∫ a : ℝˣ, ‖Wm k (d2 a * g)‖ * |(a : ℝ)| ^ (σ - 1 / 2) ∂mulR =
    C * |g.det| ^ (1 / 2 - σ) * (g 1 0 ^ 2 + g 1 1 ^ 2) ^ ((2 * σ - 1) / 2)

def ComplexMatrixMajorantIntegrable : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
  Integrable (fun h : M22 => |(Matrix.of h).det| ^ (-1 - σ) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ ((2 * σ - 1) / 2) /
    ((1 + ‖h‖) ^ N * (1 + (h 0 0 ^ 2 + h 1 0 ^ 2) ^ ((1 : ℝ) / 2) / |(Matrix.of h).det|) ^ N))

end Ad3.LR.C
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
section
noncomputable section

open MeasureTheory Complex

namespace Ad3.LR.C

def TateR : Prop := ∀ (f : SchwartzMap ℝ ℂ) (e : Bool) (s : ℂ), 0 < s.re → s.re < 1 →
  z1 (SchwartzMap.fourierTransformCLM ℂ f) e (1 - s) = gT e s * z1 f e s

def TateInt : Prop := ∀ (f : SchwartzMap ℝ ℂ) (e : Bool) (s : ℂ), 0 < s.re →
  Integrable (fun a : ℝˣ => f a * chR e s a) mulR

def FunctionalEquationGL2GL1Complex : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ (δ : Bool) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ), g.det ≠ 0 →
  0 < s.re → s.re < 1 → z2' k δ s g = g2 k s * z2 k δ s g

def GamSplit : Prop := ∀ (k : ℕ) (δ : Bool) (s : ℂ), 3 ≤ k → gamR k δ s = g2 k s * gT (!δ) s

end Ad3.LR.C
end
end


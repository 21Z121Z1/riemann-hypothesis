import Mathlib

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EisensteinSeries.DslopePhiCDifferentiableAt
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.KroneckerLimitFormula

open Complex Asymptotics Filter Topology

def gC (y : ℝ) (s : ℂ) : ℂ :=
  2 * (y : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ) * Gamma (s - 1 / 2) * (Gamma s)⁻¹

def PhiC (y : ℝ) (s : ℂ) : ℂ := gC y s * riemannZeta₁ (2 * s - 1) / 2

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.KroneckerLimitFormula

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EisensteinSeries.RemLipTermA
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT

open MeasureTheory

def qv (a b t : ℝ) : ℝ := (t + a) ^ 2 + b ^ 2

def fF (y a b σ t : ℝ) : ℝ := y ^ σ * qv a b t ^ (-σ)

def fF' (y a b σ t : ℝ) : ℝ := -2 * σ * y ^ σ * (t + a) * qv a b t ^ (-σ - 1)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT
end
end


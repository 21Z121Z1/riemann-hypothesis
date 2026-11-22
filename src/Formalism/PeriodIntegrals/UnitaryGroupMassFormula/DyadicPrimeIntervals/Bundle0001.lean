import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallLoop
import Formalism.PeriodIntegrals.Bundle0008

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run1
section
namespace PI.PrimesDyadicRS.K

theorem run1 : run 32768 1612 32766 2 1 = true := by decide +kernel

end PI.PrimesDyadicRS.K
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run2
section
namespace PI.PrimesDyadicRS.K

theorem run2 : run 65536 3030 32768 32768 1612 = true := by decide +kernel

end PI.PrimesDyadicRS.K
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run3
section
namespace PI.PrimesDyadicRS.K

theorem run3 : run 98304 4388 32768 65536 3030 = true := by decide +kernel

end PI.PrimesDyadicRS.K
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run4
section
namespace PI.PrimesDyadicRS.K

theorem run4 : run 131072 5709 32768 98304 4388 = true := by decide +kernel

end PI.PrimesDyadicRS.K
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.ThetaDiff
section
noncomputable section

namespace PI.PrimesDyadicRS.W

def At (y : ℝ) : Prop :=
  3 * y / (5 * Real.log y) < (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)

def SmallNat : Prop := ∀ h : ℕ, 41 ≤ h → h < 131072 →
  3 * ((h : ℝ) + 1) <
    10 * ((Nat.primeCounting h : ℝ) - (Nat.primeCounting (h / 2) : ℝ)) * Real.log ((h : ℝ) / 2)

def ThetaDiff : Prop := ∀ y : ℝ, 1 ≤ y →
  Chebyshev.theta (2 * y) - Chebyshev.theta y ≤
    ((Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)) * Real.log (2 * y)

def PsiTheta : Prop := ∀ x : ℝ, 1 ≤ x →
  Chebyshev.psi x - Chebyshev.theta x ≤ 3 * Chebyshev.psi (Real.sqrt x)

def RealIneq : Prop := ∀ y : ℝ, 65536 ≤ y →
  3 * y / (5 * Real.log y) * Real.log (2 * y) <
    (0.92129 * (2 * y) - 5 / 2 * Real.log (2 * y))
      - 3 * (1.1056 * Real.sqrt (2 * y) + 0.7 * Real.log (Real.sqrt (2 * y)) ^ 2)
      - (1.1056 * y + 0.7 * Real.log y ^ 2)

end PI.PrimesDyadicRS.W
end
end


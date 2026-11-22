import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.HasSecondLogDerivPowerSeriesExp
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideB
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SigmaConstantAgrees

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
section
namespace Formalism.L2.Th1.C

theorem mvExpLaws : MvExpLaws := formalExpLaws'
theorem mvExpSubst : MvExpSubst := formalExpSubst'
theorem lGSubgroup : LGSubgroup := lGSubgroup_of mvExpLaws
theorem lGBinom : LGBinom := expIntegralBinomial'
theorem lGHalf : LGHalf := lGHalf_of mvExpLaws
theorem intBinomScalar : IntBinomScalar := intBinomialScalar'
theorem lGSubst : LGSubst := lGSubst_of mvExpSubst
theorem lGSubstMv : LGSubstMv := expIntegralMvSubst'
theorem intSubst : IntSubst := coeffsInSubst'

theorem isogenyIffBar : IsogenyIffBar := isogenyIffBar_of mvExpLaws

theorem veluXFromZ : VeluXFromZ := veluXOfSigma'
theorem isogenyU : IsogenyU := isogenyU_of mvExpLaws mvExpSubst
theorem phNormUnit : PhNormUnit := phNormUnit_of mvExpLaws mvExpSubst lGHalf isogenyU

end Formalism.L2.Th1.C
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.ThirdJetIntegral
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def LogDerivInt : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv : PowerSeries K),
    IsLogPair l linv → FGInt R l linv → IsOneUnit R (PowerSeries.derivative K l)

def ThirdJetIntegral : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → F1 R l linv ph →
    IntPS R ((Dinv l)^[3] ph) ∧ ∀ i : ℕ, 3 ≤ i → jet l ph i ∈ R

def JetsUnramified : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → F1 R l linv ph → PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R →
    AdjAt R l linv ph a b → (a - b)⁻¹ ∈ R → a ≠ b →
    (∀ i : ℕ, 1 ≤ i → jet l ph i ∈ R) ∧ ∀ i : ℕ, jet l (mvExp (-ph) : PowerSeries K) i ∈ R

def JetsShape : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → F1 R l linv ph → PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R →
    (∃ H : PowerSeries K, (∀ i : ℕ, jet l H i ∈ R) ∧
      (mvExp (-ph) : PowerSeries K) = mvExp (-(PowerSeries.C (jet l ph 2 / 2) * l ^ 2)) * H) ∧
    ∀ a b : K, AdjAt R l linv ph a b → (a - b) * jet l ph 2 ∈ R

def SumTwoUnitsProd : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B],
    (∀ a : A, ∃ u v : Aˣ, a = u + v) → (∀ b : B, ∃ u v : Bˣ, b = u + v) →
    ∀ x : A × B, ∃ u v : (A × B)ˣ, x = u + v

end Formalism.L2.Th1.C
end
end


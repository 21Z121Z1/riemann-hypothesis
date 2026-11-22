import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaOrder
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaAdd
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ThreeTermNumEqTwistedGammaOfSigmaZero

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.CMQuasiPeriodConst
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def cmForm (a b c m n : ℤ) : ℤ := a * m ^ 2 + b * m * n + c * n ^ 2

def CmThetaEq : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ), 4 * (a : ℤ) * c = b ^ 2 + d →
    cmTheta b d ^ 2 = (b : ℂ) * cmTheta b d - (a : ℂ) * (c : ℂ) ∧
    cmTheta b d + conj (cmTheta b d) = (b : ℂ) ∧ cmTheta b d * conj (cmTheta b d) = (a : ℂ) * (c : ℂ)

def CmStable : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d →
    ∀ m n : ℤ, MulStable (cmPair a b d ha hd) ((m : ℂ) + (n : ℂ) * cmTheta b d)

def CmOrder : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d →
    Int.gcd (Int.gcd a b) c = 1 → ∀ α : ℂ, MulStable (cmPair a b d ha hd) α →
      ∃ m n : ℤ, α = (m : ℂ) + (n : ℂ) * cmTheta b d

def CmArea : Prop :=
  ∀ (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d),
    area (cmPair a b d ha hd) = (a : ℝ) * Real.sqrt d / 2

def CmNorm : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d → ∀ m n : ℤ,
    Complex.normSq ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) = (a : ℝ) * (cmForm a b c m n : ℝ) ∧
    herm (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
        ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      = ((2 * (cmForm a b c m n : ℝ) / Real.sqrt d : ℝ) : ℂ) ∧
    ((m, n) ≠ (0, 0) → 1 ≤ cmForm a b c m n)

def CmAltE : Prop :=
  ∀ (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (m n m' n' : ℤ),
    altE (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      ((m' : ℂ) * (a : ℂ) + (n' : ℂ) * cmTheta b d) = ((n * m' - m * n' : ℤ) : ℝ)

def CMHalfLatticeIff : Prop :=
  ∀ (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), Odd a → ∀ m n : ℤ,
    (((m : ℂ) + (n : ℂ) * cmTheta b d) * ((a : ℂ) / 2) ∈ (cmPair a b d ha hd).lattice ↔
      Even m ∧ Even n)

def CmTheta0 : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d → Odd a →
    d % 8 = 7 → ∀ (m n : ℤ) (z : ℂ),
      th0 (cmPair a b d ha hd) ((a : ℂ) / 2) (z + ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d))
        = (-1 : ℂ) ^ (cmForm a b c m n).natAbs
          * Complex.exp ((Real.pi : ℂ) * herm (cmPair a b d ha hd) z
                ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
              + (Real.pi : ℂ) * herm (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
                ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) / 2)
          * th0 (cmPair a b d ha hd) ((a : ℂ) / 2) z

def CMQuasiPeriodConst : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), MulStable L α → α.im ≠ 0 → IsKerReps L α S →
    s2 L = (∑ P ∈ S, L.weierstrassP P) / (α * (α - conj α))

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
section
namespace Formalism.L2.Th1.F

theorem ellipticEntire : EllipticEntire := elliptic_entire_const
theorem ellipticNoPole : EllipticNoPole := elliptic_no_pole_const
theorem ellipticOnePole : EllipticOnePole :=
  ellipticOnePole_of ellipticNoPole ellipticEntire zetaQuasi legendre
theorem sigmaOrder : SigmaOrder := sigmaOrder_of sigmaEntire sigmaZero sigmaSimple
theorem sigmaAdd : SigmaAdd :=
  sigmaAdd_of ellipticNoPole sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaQuasi sigmaOrder
theorem sgStarAdd : SgStarAdd := sgStarAdd_of sigmaAdd
theorem pInjective : PInjective := pInjective_of sigmaAdd sigmaZero
theorem sigmaDouble : SigmaDouble := sigmaDouble_of sigmaAdd sigmaEntire sigmaSimple
theorem pDerivZero : PDerivZero := pDerivZero_of sigmaDouble sigmaZero
theorem discNeZero : DiscNeZero := discNeZero_of pDerivZero pInjective
theorem zetaAdd : ZetaAdd := zetaAdd_of sigmaAdd sigmaLogDeriv sigmaZero
theorem sigmaThree : SigmaThree :=
  sigmaThree_of ellipticOnePole sigmaOrder sigmaQuasi sigmaZero sigmaEntire sigmaOdd sigmaSimple sigmaAdd
theorem sgStarThree : SgStarThree := sgStarThree_of sigmaThree
theorem thetaLine : ThetaLine := thetaLine_of ellipticOnePole sgStarQuasi sgStarBasic

end Formalism.L2.Th1.F
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def fT (L : PeriodPair) (t z : ℂ) : ℂ := opU L t (sgStar L) z / sgStar L z

def thetaZeroCharacter (L : PeriodPair) (ω₀ ω : ℂ) : ℂ :=
  semiChar L ω * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω ω₀ : ℂ))

def FtQuasi : Prop :=
  ∀ (L : PeriodPair) (t ω z : ℂ), ω ∈ L.lattice →
    fT L t (z + ω) = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE L ω t : ℂ)) * fT L t z

def FtPow : Prop :=
  ∀ (L : PeriodPair) (t : ℂ) (N : ℕ), (N : ℂ) * t ∈ L.lattice → IsPeriodic L (fun z => fT L t z ^ N)

def FtOrder : Prop :=
  ∀ (L : PeriodPair) (t z : ℂ), t ∉ L.lattice →
    MeromorphicAt (fT L t) z ∧ meromorphicOrderAt (fT L t) z
      = (by classical exact if z + t ∈ L.lattice then 1 else if z ∈ L.lattice then -1 else 0)

def FtInv : Prop :=
  ∀ (L : PeriodPair) (t z : ℂ), z ∉ L.lattice → z - t ∉ L.lattice → fT L t (-z) * fT L t (z - t) = 1

def FtDouble : Prop :=
  ∀ (L : PeriodPair) (y z : ℂ), z ∉ L.lattice → z + y ∉ L.lattice →
    fT L (2 * y) z = fT L y (z + y) * fT L y z

def OpUTh0 : Prop :=
  ∀ (L : PeriodPair) (t x z : ℂ),
    opU L x (th0 L t) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x t : ℂ)) * opU L (x + t) (sgStar L) z
        / opU L t (sgStar L) 0

def ThetaZeroTranslateProduct : Prop :=
  ∀ (L : PeriodPair) (t P Q z : ℂ), Q ∉ L.lattice → z + P + t ∉ L.lattice →
    opU L (P + Q) (th0 L t) z * opU L (P - Q) (th0 L t) z
      = opU L Q (sgStar L) 0 ^ 2 * (L.weierstrassP Q - L.weierstrassP (z + P + t))
        * opU L P (th0 L t) z ^ 2

def ThetaZeroCube : Prop :=
  ∀ (L : PeriodPair) (ω₀ b c : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    IsPeriodic L (fun a =>
      th0 L (ω₀ / 2) (a + b + c) * th0 L (ω₀ / 2) a * th0 L (ω₀ / 2) b * th0 L (ω₀ / 2) c
        / (th0 L (ω₀ / 2) (a + b) * th0 L (ω₀ / 2) (b + c) * th0 L (ω₀ / 2) (c + a)))

def ThetaZeroSecond : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    deriv (th0 L (ω₀ / 2)) 0 = 0 ∧
    iteratedDeriv 2 (th0 L (ω₀ / 2)) 0 = -(L.weierstrassP (ω₀ / 2) + s2 L)

def ThetaZeroLine : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (F : ℂ → ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → Differentiable ℂ F →
    (∀ ω ∈ L.lattice, ∀ z, F (z + ω) = thetaZeroCharacter L ω₀ ω
      * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * F z) →
    ∀ z, F z = F 0 * th0 L (ω₀ / 2) z

def IsFibreReps (L : PeriodPair) (α t : ℂ) (T : Finset ℂ) : Prop :=
  (∀ Q ∈ T, α * Q - t ∈ L.lattice ∧ 2 * Q ∉ L.lattice) ∧
  (∀ Q ∈ T, ∀ Q' ∈ T, (Q - Q' ∈ L.lattice ∨ Q + Q' ∈ L.lattice) → Q = Q') ∧
  (∀ z, α * z - t ∈ L.lattice → ∃ Q ∈ T, z - Q ∈ L.lattice ∨ z + Q ∈ L.lattice)

def FibreRepsExist : Prop :=
  ∀ (L : PeriodPair) (α t : ℂ), α ≠ 0 → MulStable L α → 2 * t ∈ L.lattice →
    (∀ z, α * z - t ∈ L.lattice → 2 * z ∉ L.lattice) → ∃ T : Finset ℂ, IsFibreReps L α t T

def Th0Isogeny : Prop :=
  ∀ (L : PeriodPair) (α ω₀ : ℂ) (T : Finset ℂ), α ≠ 0 → MulStable L α → ω₀ ∈ L.lattice →
    ω₀ / 2 ∉ L.lattice → IsFibreReps L α (ω₀ / 2) T →
    (∀ ω ∈ L.lattice, thetaZeroCharacter L ω₀ (α * ω) = thetaZeroCharacter L ω₀ ω ^ (2 * T.card)) →
    (2 * (T.card : ℝ) = Complex.normSq α) ∧
    ∀ z, z ∉ L.lattice → z - ω₀ / 2 ∉ L.lattice →
      th0 L (ω₀ / 2) (α * z) * (L.weierstrassP z - L.weierstrassP (ω₀ / 2)) ^ T.card
        = th0 L (ω₀ / 2) z ^ (2 * T.card) * ∏ Q ∈ T, (L.weierstrassP z - L.weierstrassP Q)

end Formalism.L2.Th1.F
end
end


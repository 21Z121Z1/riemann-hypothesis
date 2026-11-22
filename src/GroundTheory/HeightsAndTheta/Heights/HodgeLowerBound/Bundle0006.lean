import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGrassProdGeomDeg

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDimX
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)

abbrev DimX.genericCone {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) : Type :=
  Localization (Algebra.algebraMapSubmonoid (MRing ι ⧸ P) (nonZeroDivisors ℤ))

def DimX.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ),
    IsArithVar P (n + 1) →
      ringKrullDim (DimX.genericCone P) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)

theorem DimX.hyps_inhabited : IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) :=
  IndefiniteRowSideFullHecke.ArithBezout.isArithVar_projLine'

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def FlagIntMuOne.Statement : Prop :=
  ∀ (N j : ℕ), j ≤ N →
    flagInt Unit N (muPoly Unit N j ^ (j * (N - j)) * monomial (rhoBlock Unit N j) 1) =
      (-1) ^ (j * (N - j)) * grassDeg j (N - j)

example : (1 : ℕ) ≤ 2 := by norm_num

example : flagInt Unit 2 (muPoly Unit 2 1 ^ (1 * (2 - 1)) * monomial (rhoBlock Unit 2 1) 1) =
    (-1) ^ (1 * (2 - 1)) * grassDeg 1 (2 - 1) := by
  have hrho : rhoBlock Unit 2 1 = 0 := by
    ext ⟨u, i⟩
    fin_cases i <;> simp [rhoBlock]
  have h := Jint_line 1
  unfold Jint fib at h
  rw [vandBlocks_line, map_one, one_mul, dimN_line] at h
  rw [hrho, show (1 * (2 - 1) : ℕ) = 1 from rfl, monomial_zero', C_1, h]
  simp [grassDeg]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def FlagIntProjection.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ P : RootPoly Ψ N,
    flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * P) =
      (-1) ^ dimN Ψ N j * grassProdDeg (Fintype.card Ψ) j (N - j) * blockInt Ψ N j P

example : (1 : ℕ) ≤ 2 := by norm_num

example : flagInt Unit 2 (muPoly Unit 2 1 ^ dimN Unit 2 1 * vandBlocks Unit 2 1) =
    (-1) ^ dimN Unit 2 1 * grassProdDeg (Fintype.card Unit) 1 (2 - 1) * blockInt Unit 2 1 (vandBlocks Unit 2 1) := by
  have h := Jint_line 1
  unfold Jint fib at h
  rw [map_one, one_mul] at h
  rw [h, ← fdeg, fdeg_line, dimN_line]
  simp [grassProdDeg, grassDeg]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end


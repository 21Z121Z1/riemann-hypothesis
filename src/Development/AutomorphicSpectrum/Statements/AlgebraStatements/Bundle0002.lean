import Mathlib
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison

-- bundled from Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

def HodgeTateDatumStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : R)}) R →
  ∀ [Algebra ℤ_[p] R] (P : Out.PolAV (Spec (CommRingCat.of R))),
    Nonempty (TorsRep P.A p) ∧
    ∃ (cp : R) (_ : HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp)
      (H : HodgeTateDatum p P.g v R ℤ_[p] AlgEquiv.refl cp) (pt : Nb p P.g → (sp (R₀ := R) R ⟶ P.A)),
      IsTorsPts P.A p pt ∧ ∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

def SubquotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : R)}) R →
  ∀ (N : Type) [AddCommGroup N] (M : Submodule R (N → C)), IsAbFactor p M →
    ∀ K : AddSubgroup N, GenAF p M K

def OrdinaryCurveStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : R)}) R →
  ∃ (A : Over (Spec (CommRingCat.of R))) (_ : GrpObj A) (L : LB A.left), IsAbelianScheme A ∧ L.IsLB ∧
    Out.RelAmple A L ∧ ∃ (T : TorsRep A p) (pt : ZMod p × ZMod p → (sp (R₀ := R) R ⟶ A)),
      IsTorsPts A p pt ∧ torsFun C T pt =
        tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x))
          (intFun R (ZMod p))

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.AlgebraStatements.TrivFlagKills
section
namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

def TrivFlagKills : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O x) d →
    ∀ (σ : Type) [Fintype σ] (T : LocPair ι O σ), T.IsVert (pointIdeal O x) ϖ →
    ∀ (N : ℕ) (e : Fin N → σ), TrivFlagMod O ϖ x N (fun i => T.x' (e i)) →
    ∀ k : ℕ, 1 ≤ k → k ≤ d + 1 → ∀ Q : MvPolynomial σ ℝ, Q.IsHomogeneous (d + 1 - k) →
    ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ,
      IsMixExpansion d ((∑ i : Fin N, X (Sum.inr (e i)) ^ k) * mixDiff Q) Gs →
      T.val (pointIdeal O x) Gs = 0

end GlobalTheory.CompanionTheory.Ar.Num
end


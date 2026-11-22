import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.Bundle0003
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.RationalBitableauLatticeStatement
import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.PathBasisTheorem
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.UnitAndFieldPowerLemmas
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Bundle0001

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BrCore
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

section B1
theorem path_pair_correspondence (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PathPairCorrespondence D := Formalism.InvariantFactorPaths.ColumnFamilies.Top.lemmaA
end B1

section B2
theorem admissible_standard_basis (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.admB2 D := Formalism.InvariantFactorPaths.ColumnFamilies.Top.sBasis
end B2

section B9
theorem global_sections_schur (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.GlobalSectionsSchur D := fun n _ mu R _ _ hR =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_one n mu R hR
end B9

section lowerOffDiagonalCoeff
theorem bracket_polynomial_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.BracketPolynomialSpan D := fun n _ mu hmu =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_two n mu hmu
end lowerOffDiagonalCoeff

section Mod

def br_toC {n : ℕ} (M : Formalism.MainNotions.CovariantDegrees.GLMod n) : Formalism.InvariantFactorPaths.ColumnFamilies.GLMod n :=
  { ι := M.ι, fi := M.fi, de := M.de, A := M.A, mul := M.mul, one := M.one }

def br_cfToC {n : ℕ} [NeZero n] {M : Formalism.MainNotions.CovariantDegrees.GLMod n} (CF : Formalism.MainNotions.CovariantDegrees.ColFam M) :
    Formalism.InvariantFactorPaths.ColumnFamilies.ColFam (br_toC M) :=
  { J := CF.J, fJ := CF.fJ, dJ := CF.dJ, mu := CF.mu, dom := CF.dom, ph := CF.ph, equiv := CF.equiv,
    indepP := CF.indepP, indepQ := CF.indepQ, rank := CF.rank }

def br_cfOfC {n : ℕ} [NeZero n] {M : Formalism.MainNotions.CovariantDegrees.GLMod n} (CF : Formalism.InvariantFactorPaths.ColumnFamilies.ColFam (br_toC M)) :
    Formalism.MainNotions.CovariantDegrees.ColFam M :=
  { J := CF.J, fJ := CF.fJ, dJ := CF.dJ, mu := CF.mu, dom := CF.dom, ph := CF.ph, equiv := CF.equiv,
    indepP := CF.indepP, indepQ := CF.indepQ, rank := CF.rank }

end Mod

section B6
theorem column_family_closure (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.ColumnFamilyClosure D := by
  intro n _
  obtain ⟨h1, h2, h3⟩ := Formalism.InvariantFactorPaths.ColumnFamilies.Top.closure_first_part n
  refine ⟨fun M hc hA => ?_, fun M mu β hmu hS => ?_, fun M M' ε hε e he hM => ?_⟩
  · exact (h1 (br_toC M) hc hA).map br_cfOfC
  · exact (h2 (br_toC M) mu β hmu hS).map br_cfOfC
  · exact (h3 (br_toC M) (br_toC M') ε hε e he (hM.map br_cfToC)).map br_cfOfC
end B6

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestPathFrom
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def isV {N : ℕ} (LL : Letters (Fin N)) : ℕ → Bool := fun i => if h : i < N then LL.vec ⟨i, h⟩ else true

def Bn {N : ℕ} (B : Fin N → ℕ) : ℕ → ℕ := fun i => if h : i < N then B ⟨i, h⟩ else 0

def ext {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ℕ → Fin n → ℤ := fun i => if h : i < N + 1 then mu ⟨i, h⟩ else 0

def res (N : ℕ) {n : ℕ} (μ : ℕ → Fin n → ℤ) : Fin (N + 1) → Fin n → ℤ := fun i => μ i.val

def iv (N n : ℕ) : Fin N × Fin n → ℕ × Fin n := fun x => (x.1.val, x.2)

def RestPathTo : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) (ext P.mu) N

def RestPathFrom : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : ℕ → Fin n → ℤ),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) μ N → ∃ P : PPath n N LL B, P.mu = res N μ

def RestStd : Prop :=
  ∀ (n N : ℕ) (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)),
    IsSt mu I ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd (pEnd mu) I

def RestPsi : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B)
    (I : ℤ → Finset (Fin n)), Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I →
    rename (iv N n) (Psi R P.mu I) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) (ext P.mu) N I

def RestPol : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (B : Fin N → ℕ),
    (Pol R n B).map (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB R n N (Bn B)

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ToralGalois
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem weight_projector_mem_weight_space {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (htop : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (mu : Fin n → ℤ) (e : Module.End K V) (he : IsWtProj E mu e)
    (x : V) : e x ∈ weightSp E mu := by
  have hx : x ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by rw [htop]; trivial
  refine Submodule.iSup_induction (fun nu => weightSp E nu) (motive := fun y => e y ∈ weightSp E mu) hx ?_ ?_ ?_
  · intro nu y hy
    by_cases h : nu = mu
    · subst h
      rw [he.1 y hy]
      exact hy
    · rw [he.2 nu h y hy]
      exact zero_mem _
  · rw [map_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact add_mem ha hb

theorem adm_eleven (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := by
  intro p _ O _ _ _ _ _S n V _ _ _ _ E mu La hrep _hdom _hiso hlat hproj

  have hstab : ∀ u ∈ UZmon E, ∀ x ∈ La, u x ∈ La := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu => exact hlat.1 u hu
    | one => exact fun x hx => hx
    | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, y, hy, -, rfl⟩
    exact hstab u hu y hy
  · intro y hy u hu e he
    exact ⟨hproj _ (hstab u hu y hy) mu e he, weight_projector_mem_weight_space E hrep.2.2 mu e he _⟩

end Formalism.MainNotions.G.ColumnFamilies
end
end


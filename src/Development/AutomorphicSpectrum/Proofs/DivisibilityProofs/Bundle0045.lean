import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0044
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0015
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreePolynomialEvalStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_polynomial_eval : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → eval (fun x => lam x.1 x.2) (PB.degFlPoly Ψ N) = flagDeg lam := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_degree_polynomial_eval | exact GlobalTheory.CompanionTheory.Relay.flag_degree_polynomial_eval | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_degree_polynomial_eval <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerConvI2Statement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_conv_I2 : PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), T.Conv II ∧ T.I2 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 | exact GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerI1Statement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_I1 : PB.Coefficients → PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.RefLinked II → T.I1 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked | exact GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals.tower_I1_of_reference_linked <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilInputsCombined
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem chain_tower : PB.FlagHeight → PB.Inputs → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound →
    GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement →
    ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    [Nonempty Ψ] (T : RootTower Ψ N) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd →
    FrobShape frob → T.Proportional → T.I1 II → T.I2 II → T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I5 II → T.I6 II →
    T.I7 → T.I8 II (hhFl Ψ N II) → T.Prop6 II frob → T.PropA II → T.PropF II C' rd Lval → T.VolEq →
    T.SlopeLower II C rd Lval → T.T1 II ∧ T.ThmB II (hhFl Ψ N II) ∧ T.T2 II (2 * C + 3 * C' + 5) rd Lval ∧
      T.MeanSlope II (2 * C + 3 * C' + 5) rd Lval := by
  intro hFH hIn hZ1 hZ2 hAP hG II hII Ψ _ _ N _ T frob C C' rd Lval hC hC' hrd hfs hP hI1 hI2 hA1 hM1 hM2 hAN
    hI5 hI6 hI7 hI8 hP6 hPA hPF hVol hSL
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  have hI3 : T.I3 := GlobalTheory.T.tower_I3_of_semipositive_nef Ψ N T hA1 hM1 hM2 hAN
  have hT1 : T.T1 II := GlobalTheory.T.tower_T1_limit II Ψ N T hP hI2 hI3
  have hW : T.ThmW II := GlobalTheory.T.tower_weil_theorem hIn.2.2.2.2.2.1 GlobalTheory.T.exists_unique_rational_statement GlobalTheory.CompanionTheory.Ar.Link.divSuppArith_holds hZ1 hZ2
    II hII Ψ N T hP hI1 hI2 hI3 hI5 hI6 hI7
  have hI9 : I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := GlobalTheory.T.flag_height_I9_properties hFH hIn II hII Ψ N hN
  have hB : T.ThmB II (hhFl Ψ N II) := GlobalTheory.T.tower_theorem_B hAP II Ψ N T (hhFl Ψ N II) hP hW hI8 hI9
  have he : GroundTheory.Heights₂.Heights.antisymDegree Ψ N = dimFl Ψ N := by
    simp [GroundTheory.Heights₂.Heights.antisymDegree, dimFl, Nat.choose_two_right]
  have hAr := (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  rw [he] at hAr
  have hLab : LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := GlobalTheory.T.flag_height_label_invariant II hII Ψ N hN hAr
  have hBA : T.ThmBA II (hhFl Ψ N II) := GlobalTheory.T.tower_theorem_B_averaged II Ψ N T (hhFl Ψ N II) hB hPA hLab
  have hTest : HhTestBound T.j (hhFl Ψ N II) := GlobalTheory.T.flag_height_test_bound hG hIn II hII Ψ N T.j T.j_pos T.j_lt
  have hA0 : T.LowerBoundAtBase II (hhFl Ψ N II) frob (2 * (C + C') + 3) rd Lval :=
    GlobalTheory.T.test_height_bound II Ψ N T (hhFl Ψ N II) frob C C' rd Lval hC hC' hrd hP hI9 hPF hSL hTest
  have hK : (0 : ℝ) ≤ 2 * (C + C') + 3 := by linarith
  have hT2' := GlobalTheory.T.tower_T2 II Ψ N T (hhFl Ψ N II) frob (2 * (C + C') + 3) C' rd Lval hK hC' hrd hP hfs hI9 hP6
    hBA hPF hA0
  have hEq : 2 * (C + C') + 3 + C' + 2 = 2 * C + 3 * C' + 5 := by ring
  rw [hEq] at hT2'
  exact ⟨hT1, hB, hT2', GlobalTheory.T.mean_slope_proportional_volume II Ψ N T _ rd Lval hP hVol hT2'⟩

end GlobalTheory.CompanionTheory.Ar.Top
end


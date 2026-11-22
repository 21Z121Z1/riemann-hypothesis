import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0030
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0019
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0022
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  first | exact @GlobalTheory.PullExpansion.expands_pull_of_four_le | exact GlobalTheory.PullExpansion.expands_pull_of_four_le | (intros; apply GlobalTheory.PullExpansion.expands_pull_of_four_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowDegData

theorem psiIn_top {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) :
    D.toPre.PsiIn χ ⊤ := by
  by_cases h : χ = 0
  · subst h
    exact (GlobalTheory.PsiZero.main R D.toPre).1 D.tau_bimult
  · exact (GlobalTheory.PsiZero.main R D.toPre).2 χ I ⊤ le_top (D.psi_pos χ h)

theorem psiIn_of_component {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) {j : ℕ}
    {D' : DegPre R} (pD : IsPowDeg D' D.toPre j) (x : D'.X) (J : Ideal R) (i : Fin j)
    (h : D.toPre.PsiIn (pD.xe x i) J) : D'.PsiIn x J := by
  classical
  have H := GlobalTheory.psiIn_prod_of_isPowDeg R j D.toPre D' pD x (fun k => if k = i then J else ⊤) (fun k => by
    by_cases hk : k = i
    · subst hk
      simpa using h
    · simpa [hk] using psiIn_top D (pD.xe x k))
  refine (GlobalTheory.PsiZero.main R D').2 x _ J ?_ H
  refine (Ideal.prod_le_inf).trans ((Finset.inf_le (Finset.mem_univ i)).trans ?_)
  simp

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (j : ℕ), ∃ D' : DegData R I, Nonempty (IsPowDeg D'.toPre D.toPre j) := by
  intro hG R _ _ I D j
  obtain ⟨D', ⟨pD⟩⟩ := GlobalTheory.PowDegPre.exists_pow R D.toPre j
  refine ⟨⟨D', GlobalTheory.PsiEvenBox.main hG R j D.toPre D' pD D.psi_even,
    GlobalTheory.TauBimultBox.tauBimult_pow hG R j D.toPre D' pD D.tau_bimult, fun x hx => ?_, fun n => ?_⟩, ⟨pD⟩⟩
  · have : pD.xe x ≠ 0 := fun h => hx (pD.xe.map_eq_zero_iff.1 h)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 this
    exact psiIn_of_component D pD x I i (D.psi_pos _ hi)
  · have hf : (Set.pi Set.univ fun _ : Fin j => {χ : D.toPre.X | ¬ D.toPre.PsiIn χ (I ^ n)}).Finite :=
      Set.Finite.pi fun _ => D.psi_tendsto n
    refine (hf.preimage pD.xe.injective.injOn).subset fun x hx i _ hi => ?_
    exact hx (psiIn_of_component D pD x _ i hi)

end GlobalTheory.PowDegData
end


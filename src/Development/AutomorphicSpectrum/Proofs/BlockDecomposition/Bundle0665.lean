import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalNonvanishing
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalSecond
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0638
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSixthOfEarlier
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergThirdOfSecondFourth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0639
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalNonvanishingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_local_nonvanishing : Ad3.Loc2 → Ad3.R.A10 → Ad3.R.A11 := by
  first | exact @GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker | exact GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker | (intros; apply GlobalTheory.CompanionTheory.RSNonvanish.rankin_selberg_nonvanishing_of_whittaker <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalSecondStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_local_second : Ad3.R.A2 := by
  first | exact @GlobalTheory.CompanionTheory.RSLocal.a2 | exact GlobalTheory.CompanionTheory.RSLocal.a2 | (intros; apply GlobalTheory.CompanionTheory.RSLocal.a2 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_meromorphic_continuation : Ad3.Loc2 → Ad3.R.A10 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.a10 | exact GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.a10 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.a10 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSeventhOfSecondStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_seventh_of_second : Ad3.R.A2 → Ad3.R.A7 := by
  first | exact @GlobalTheory.CompanionTheory.RSPlane.a7 | exact GlobalTheory.CompanionTheory.RSPlane.a7 | (intros; apply GlobalTheory.CompanionTheory.RSPlane.a7 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSixthOfEarlierStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_sixth_of_earlier : Ad3.R.A1 → Ad3.R.A3 → Ad3.R.A4 → Ad3.R.A5 → Ad3.R.A6 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.Trilinear.zv_eq_trilinear | exact GlobalTheory.CompanionTheory.RankinSelberg.Trilinear.zv_eq_trilinear | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.Trilinear.zv_eq_trilinear <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergTheoremStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_theorem : Ad3.R.B0 → Ad3.R.F0 → Ad3.R.F1 → Ad3.R.F7 → Ad3.R.X1 → Ad3.RS := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergTop.rs_of | exact GlobalTheory.CompanionTheory.RankinSelbergTop.rs_of | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergTop.rs_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergThirdOfSecondFourthStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_third_of_second_fourth : Ad3.R.A2 → Ad3.R.A4 → Ad3.R.A3 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals.main | exact GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals.main | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergUnfoldingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_unfolding : Ad3.R.G2a → Ad3.R.G2b → Ad3.R.G3a → Ad3.R.G3 := by
  first | exact @GlobalTheory.CompanionTheory.BottomRowCoordinates.g3 | exact GlobalTheory.CompanionTheory.BottomRowCoordinates.g3 | (intros; apply GlobalTheory.CompanionTheory.BottomRowCoordinates.g3 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalElementIntegralAlmostAll
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocalHypotheses

theorem eventually_val_le_one (E : Type) [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 E) x
  rw [Filter.eventually_cofinite]
  refine h.subset fun w hw => ?_
  have hw' : ¬ Valued.v ((x : E) : w.adicCompletion E) ≤ 1 := hw
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', not_le] at hw'
  exact hw'

theorem ratW_mem_KGL_eventually (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w n := by
  have hall : ∀ M : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j : Fin n,
      Valued.v (algebraMap E (w.adicCompletion E) ((M : Matrix (Fin n) (Fin n) E) i j)) ≤ 1 := by
    intro M
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact eventually_val_le_one E _
  filter_upwards [hall δ, hall δ⁻¹] with w h1 h2
  rw [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  refine ⟨fun i j => h1 i j, fun i j => ?_⟩
  have key : (ratW n w δ)⁻¹ = ratW n w δ⁻¹ := (map_inv (ratW n w) δ).symm
  rw [key]
  exact h2 i j

end GlobalTheory.CompanionTheory.LocalHypotheses
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalFinitePlacesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_finite_places : PositivityTheory.Rg.BcB.G8.Fin.RatFin := by
  first | exact @GlobalTheory.CompanionTheory.RatFinG.ratFin | exact GlobalTheory.CompanionTheory.RatFinG.ratFin | (intros; apply GlobalTheory.CompanionTheory.RatFinG.ratFin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictPullBijectiveOfForall
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.OmRes

theorem restrict_pull_bijective_of_forall :
    ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
      (Q : ObjectProperty C), (∀ T, Q T) →
      ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict F Q.ι).pull n) := by
  intro R _ C _ F Q h n
  haveI : Q.ι.EssSurj := ⟨fun Y => ⟨⟨Y, h Y⟩, ⟨Iso.refl _⟩⟩⟩
  haveI : Q.ι.IsEquivalence := { }
  exact CrystallineSemistableComparison.P.adj F Q.ι Q.ι.inv Q.ι.asEquivalence.toAdjunction n

end GlobalTheory.CompanionTheory.OmRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reverse_ordered_product_perm_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (σ : Equiv.Perm (Fin h)) (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N) (hd' : ∑ a, (y (σ a)).1 = N), IsRevOrdered Γ → IsRevOrdered (Γ ∘ σ) → (∀ i, IsLSeg (Γ i) (y i).rep) → Nonempty ((prodIrr y hd).Equiv (prodIrr (y ∘ σ) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered | exact GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered | (intros; apply GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered <;> assumption)
end


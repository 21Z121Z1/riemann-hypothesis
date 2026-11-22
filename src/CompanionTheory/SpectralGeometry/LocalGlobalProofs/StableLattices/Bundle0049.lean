import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0048
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithBoundary
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToL2CongrOnUnitaryBis

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GrowthStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.GrowthStatement : CompanionTheory.RgExh.Dec.L.Growth := by
  first | exact @GlobalTheory.CompanionTheory.PathGrowth.growth | exact GlobalTheory.CompanionTheory.PathGrowth.growth | (intros; apply GlobalTheory.CompanionTheory.PathGrowth.growth <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistenceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HaarExistence : CompanionTheory.RgExh.Dec.L.HaarExists := by
  first | exact @GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | exact GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | (intros; apply GlobalTheory.CompanionTheory.ParabolicHaar.haarExists <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithBoundaryStatement
section
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_action_commutes_with_boundary : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → GlRel E → ∀ p q : Fin n, lev p = lev q → ∀ x : Cn n V, SuppIn (inU lev) x →
      lF E p q (bd (allT n) E x) = bd (allT n) E (lF E p q x) := by
  first | exact @GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm | exact GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm | (intros; apply GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToL2CongrOnUnitaryBisStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rgExh_pack : CompanionTheory.RgExh.Dec.L.Pack := by
  first | exact @GlobalTheory.CompanionTheory.PackEmb.pack | exact GlobalTheory.CompanionTheory.PackEmb.pack | (intros; apply GlobalTheory.CompanionTheory.PackEmb.pack <;> assumption)
end


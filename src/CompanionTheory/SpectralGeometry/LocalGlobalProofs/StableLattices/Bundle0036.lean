import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0029
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0030
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviDecomposition
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0031
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RootVectors
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0032

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExponentialMembershipStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExponentialMembership : ExpMem := by
  first | exact @GlobalTheory.CompanionTheory.BmuExpMem.expMem | exact GlobalTheory.CompanionTheory.BmuExpMem.expMem | (intros; apply GlobalTheory.CompanionTheory.BmuExpMem.expMem <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialMatrixUnitFormulaStatement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_differential_matrix_unit_formula : ∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0 := by
  first | exact @GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single | exact GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single | (intros; apply GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadraticStatement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_differential_sign_rule_quadratic : StdD → (∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0) → WedgeQ := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ | exact GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ | (intros; apply GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegralityStatement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExteriorIntegrality : WedgeInt := by
  first | exact @GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | exact GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | (intros; apply GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategoryStatement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HomCategory : HomCat := by
  first | exact @GlobalTheory.CompanionTheory.ZuckHomCat.homCat | exact GlobalTheory.CompanionTheory.ZuckHomCat.homCat | (intros; apply GlobalTheory.CompanionTheory.ZuckHomCat.homCat <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaDecompositionStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.IwasawaDecomposition : IwaQ := by
  first | exact @GlobalTheory.CompanionTheory.BmuIwa.iwaQ | exact GlobalTheory.CompanionTheory.BmuIwa.iwaQ | (intros; apply GlobalTheory.CompanionTheory.BmuIwa.iwaQ <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviDecompositionStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LeviDecomposition : LeviQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselLevi.leviQ | exact GlobalTheory.CompanionTheory.BesselLevi.leviQ | (intros; apply GlobalTheory.CompanionTheory.BesselLevi.leviQ <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHomStatement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.MatrixHom : MatHom := by
  first | exact @GlobalTheory.CompanionTheory.ZuckMatHom.matHom | exact GlobalTheory.CompanionTheory.ZuckMatHom.matHom | (intros; apply GlobalTheory.CompanionTheory.ZuckMatHom.matHom <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuotientBoundOfFactorReduceChartStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_bound_of_factor_reduce_chart : Factor → Reduce → ChartExists → QBound := by
  first | exact @GlobalTheory.CompanionTheory.BmuQBound.qBound | exact GlobalTheory.CompanionTheory.BmuQBound.qBound | (intros; apply GlobalTheory.CompanionTheory.BmuQBound.qBound <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ReductionOfDerivedSeriesStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_of_derived_series : DsLin → DsAd → DsDer → Reduce := by
  first | exact @GlobalTheory.CompanionTheory.BmuReduce.reduce | exact GlobalTheory.CompanionTheory.BmuReduce.reduce | (intros; apply GlobalTheory.CompanionTheory.BmuReduce.reduce <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RootVectorsStatement
section
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.RootVectors : RootVec := by
  first | exact @GlobalTheory.CompanionTheory.BmuRootVec.rootVec | exact GlobalTheory.CompanionTheory.BmuRootVec.rootVec | (intros; apply GlobalTheory.CompanionTheory.BmuRootVec.rootVec <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2Statement
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensHom' : TensHom := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTensHom.tensHom | exact GlobalTheory.CompanionTheory.ZuckTensHom.tensHom | (intros; apply GlobalTheory.CompanionTheory.ZuckTensHom.tensHom <;> assumption)
end


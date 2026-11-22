import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0051
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0017

noncomputable section

theorem psi_product_e : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.SG.Pf.Coef.PsiProdE D := fun D x =>
  (product_formula_e D.host.F D.host.E _ D.sp.cm.deg2 (fun p => D.s.atP p)).2 x

end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaDiscreteSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpacesStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

theorem projectiveBundleFormula_vectorBundle_any_space : D1 :=
  projectiveBundleFormula_of_unitOnEtalePoints fun q _ _ N V hq => GlobalTheory.T.projectiveBundleFormula_of_discrete_spaces q N (_root_.GlobalTheory.EtC.pbf_disc q N) V hq

end GlobalTheory.EtC

end

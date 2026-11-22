import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSmoothSurjective

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smooth_surjective_cech_descent_cohomology : A2 := by
  intro R _ Y X f _ _ F n
  haveI : QuasiIso ((chains R).map (cechAug f)) := _root_.GlobalTheory.EtC.chains_cechAug_quasiIso_of_smooth R f
  exact GlobalTheory.T.quasiIso_hypercohomology_bijective R ((chains R).map (cechAug f)) F n

end GlobalTheory.EtC

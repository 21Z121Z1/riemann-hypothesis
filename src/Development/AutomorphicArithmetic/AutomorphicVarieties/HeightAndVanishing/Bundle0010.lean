import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ResidualAutomorphyOfLinkedEnds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HilbertEisensteinWeightOneHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ClozelConjC
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0006
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0005
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0007
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0008
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0009
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0010
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0001
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepPatchingInfiniteFamily
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0011
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.QuadraticBaseChangeOfLiterature
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.UnitaryDescent.DescentUnitaryOfUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.PrimeShapes.AdmissibleOfIntegralConjLe
import Batteries.Tactic.OpenPrivate
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.JacquetLanglandsLattices.GeneratedStableUnderW
import Mathlib.NumberTheory.NumberField.House
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinCrystalline.HodgeSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinCrystalline.TypeDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.QuadOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsHilbertModularFormCongrOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfLitN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.BOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VwinOfLeaves
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.VwinOf

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HeightVanishingHypotheses
section
open UpperTheory.Top

namespace UpperTheory.V

open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV

structure HeightVanishingHypotheses : Prop where
  thorne : ThorneLit
  desc : NTDescentU
  types : Ty.ShottonTypes
  cyc : UpperTheory.CBC.LitCBC2
  jl : GlobalJL
  sq : SymSqQ
  cube : SymCubeQ
  arthurClozelBaseChange : ArthurClozelDescent
  henniart : Henniart4
  kisin : KisinLit
  kato : KatoLitO

end UpperTheory.V
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VwinOfEnd
section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.HV.DescentVanishingReductions

open UpperTheory.V.Lit UpperTheory.V.W

theorem adL (hH : Af.HypothesesH) : Th.AdL := Th.adL hH (cohP hH.litN)

theorem countI (hH : Af.HypothesesH) (hK : ∃ CK : ℝ, LemmaK CK) (hKa : Z.Kato.KatoTwo) (h3 : Aut.AutomorphyUnramifiedCoefficients) : CountI :=
  have hC := Core0.cohInp hH.litN hK
  Th.caseI
    { toCohInp := hC, lemM := Alg.M.main_holds, lemM' := Alg.M.mprime_holds, lemP := Alg.lemmaP, kato := hKa,
      rigI := Th.rigI hC hH (adL hH), rigII := Th.rigII hC hH (adL hH), number := Af.numberU3_of_admissible hH.toClassicalTheorems } h3

end UpperTheory.V.HV.DescentVanishingReductions
end


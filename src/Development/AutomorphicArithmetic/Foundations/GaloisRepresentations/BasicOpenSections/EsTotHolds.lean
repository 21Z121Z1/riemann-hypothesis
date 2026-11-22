import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0005
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PEsGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.CycAllHolds

namespace UpperTheory.Gal.Mod

theorem esGen_holds (h : GlobalTheory.EtC.SpecGood) : ESGen :=
  esGen h esPt_holds nwtOne (frobQ frobTors) baseFacts denseGen frEx @corrPull @corrComm

end UpperTheory.Gal.Mod

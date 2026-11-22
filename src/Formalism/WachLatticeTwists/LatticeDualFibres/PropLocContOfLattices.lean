import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.Bundle0002
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.HOneTorsionFree

universe u

namespace Formalism.RepresentationBoundsCohomology.LOC

theorem propLocCont_of_lattices (hEmb : StatQuotEmbeds.{u}) (hDual : StatDualLattice.{u}) :
    StatPropLocCont.{u} := propLocCont_of connTors hEmb hDual

theorem propLocCont : StatPropLocCont.{u} := propLocCont_of_lattices quotEmbeds dualLattice

end Formalism.RepresentationBoundsCohomology.LOC

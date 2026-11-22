import Formalism.FrobeniusContraction.Bundle0002

noncomputable section

namespace Formalism.WachCohomologyFacts.PEuler

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def len (P Q : Submodule K M) : ℕ∞ := Module.length K (↥P ⧸ Q.comap P.subtype)

end Formalism.WachCohomologyFacts.PEuler

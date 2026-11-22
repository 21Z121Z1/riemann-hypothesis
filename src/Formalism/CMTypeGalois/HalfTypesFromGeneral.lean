import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois
import Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer
import Formalism.CMTypeGalois.CMTypeFrobenius.Bundle0003
import Formalism.CMTypeGalois.CMTypeFrobenius.Bundle0001
import Mathlib
import Formalism.CMTypeGalois.CMTypeFrobenius.Bundle0002

open NumberField Ideal

namespace Formalism.Q3

theorem mqKummer : MQKummer := mqKummer_of mqGalois
theorem mqFrob : MQFrob := mqFrob_of mqGalois
theorem hostGalois : HostGalois := hostGalois_of mqGalois mqKummer
theorem hostFrob : HostFrob := hostFrob_of mqFrob hostGalois kroneckerMeaning
theorem hostConj : HostConj := hostConj_of hostGalois mqKummer
theorem hostInertia : HostInertia := hostInertia_of hostGalois mqGalois
theorem hostMu : HostMu := hostMu_of mqKummer hostGalois
theorem hostEmb : HostEmb := hostEmb_of hostConj hostGalois

end Formalism.Q3

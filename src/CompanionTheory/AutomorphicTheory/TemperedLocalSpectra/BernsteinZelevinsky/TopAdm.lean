import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0018

namespace CompanionTheory.Tls2.BZGL

theorem irreducibleAdmissibleGL_top : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun k _ _ _ _ n V _ _ π hπ hirr => GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hπ hirr

end CompanionTheory.Tls2.BZGL

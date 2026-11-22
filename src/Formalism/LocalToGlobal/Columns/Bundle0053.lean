import Formalism.LocalToGlobal.Columns.Bundle0050
import Formalism.LocalToGlobal.Columns.ChainLawPhiPf
import Formalism.LocalToGlobal.Columns.Bundle0048
import Formalism.LocalToGlobal.Columns.Bundle0051
import Formalism.LocalToGlobal.Columns.Bundle0052

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawXiF
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Final

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem clX_phiHyp {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) {i : ℕ} (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    PhiGSLawHyp P.1 (qOf P.1) R.k R.rS R.r R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) := by
  obtain ⟨hk0, hr0, hN0, ht0⟩ := ranks_frame_inequalities R hB.hm (j := i) (by omega)
  obtain ⟨hk1, -, hN1, -⟩ := ranks_frame_inequalities R hB.hm (j := i + 1) (by omega)
  exact ⟨ciQ_mem P.1, ciQ_notMem_sq hB.hX hB.hPr hP, by omega, hk0, hk1, hr0, ht0, by rw [Nat.add_sub_cancel]; exact hN0.symm,
    hN1.symm⟩

theorem clX_phiLaw_steps {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) :
    ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → PhiGSLaw P.1 (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t (i + 1)
      (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) :=
  fun _ hi P hP => clPf_phiGSLaw (clX_phiHyp hB hi P hP) _ _

end Final

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TopInvHolds
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TI

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xt_eN_single {E : Type} [Field E] {N p : ℕ} (hp : p < N) : Loc.eN E N p = (Pi.single (⟨p, hp⟩ : Fin N) (1 : E) : Fin N → E) := by
  funext l
  unfold Loc.eN
  by_cases h : l = ⟨p, hp⟩
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, if_neg]
    intro h2
    exact h (Fin.ext h2)

theorem topInv_holds (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) : TopInv Ch sel mu cst m2 := by
  intro w hw y z hz
  have hu := ciQ_notMem_sq hX hPr hw
  have hq0 : ((qOf w.1 : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  obtain ⟨k, hk⟩ : ∃ k, cst.B = k + 1 := ⟨cst.B - 1, by have := hc.B_pos; omega⟩
  refine xtPhiTop_congr Ch mu hX hPr hm cst.sharp hw y (y + z) fun p p' hp hp' => ?_
  have hp'' : p' < R.N (m2 + 1) + cOf R (m2 + 1) := by omega
  refine ⟨(qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single ⟨p', hp''⟩ 1) ⟨p, hp⟩),
    (xtIntAt_qpow (qOf w.1) k).mul (hz _ _), ?_⟩
  rw [xtEntB (xt_cOf hm) _ (by omega) hp', xtEntB (xt_cOf hm) _ (by omega) hp', LinearMap.add_apply, Pi.add_apply, xt_eN_single hp'', hk]
  congr 1
  field_simp
  ring

end TI

end Formalism.L2.Col
end
end


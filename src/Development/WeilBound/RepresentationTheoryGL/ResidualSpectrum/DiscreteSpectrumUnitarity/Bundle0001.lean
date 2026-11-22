import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.ExhaustionRegularFiniteClause
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0783
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0008
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.ExhaustionRegularOfResidual
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.Re

section Pair

theorem iso (H : UsedReg) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    {N a d : ℕ} (hN : 1 ≤ N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {π π' : CuspSub E a} (h : IsNormalised π)
    (h' : IsNormalised π') (e : IsSpehOf V π d) (e' : IsSpehOf V π' d) : π.Iso π' :=
  Quotient.exact (eq_of_heq (Sigma.mk.inj ((H E N hN).2.2.1 V hV a d a d π π' h h' e e').2).2)

theorem isCsd_of_isSpehOf (H : UsedReg) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {N a d : ℕ} (hN : 1 ≤ N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V)
    (hc : IsCsdGL V) {π : CuspSub E a} (hπ : IsNormalised π) (h : IsSpehOf V π d) : π.IsCsd :=
  GlobalTheory.ThetaPull.isCsd_of_iso (iso H hN hV (GlobalTheory.ThetaPull.isNormalised_thetaSub hπ) hπ
    (GlobalTheory.ThetaPull.isSpehOf_thetaSub hV.stable hc h) h)

end Pair

section Local

open GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.BcSpehProof

theorem isUnitarisable_of_isLocComp (H : UsedReg) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a : ℕ} (ha : 1 ≤ a) (P : CuspSub E a) (hP : GlobalTheory.DiscSpec.IsNormalised P)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : LocIrr w a) (hρ : P.IsLocComp w ρ) : IsUnitarisable ρ.ρ := by
  obtain ⟨V, hV, hS⟩ := (H E a ha).2.1 a P rfl hP
  have hc := (H E a ha).2.2.2 V hV a 1 P hP hS
  obtain ⟨-, σ', -, hσ'⟩ := hc.exLoc w
  obtain ⟨hd, h1⟩ := hc.loc w ρ σ' hρ hσ'
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred)
  obtain ⟨e⟩ := h1.unique h2
  have hu := GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E a V hV w σ' hσ'
  exact isUnitarisable_of_equiv' ((GlobalTheory.LocGL.IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e).symm hu

end Local

end PositivityTheory.Rg.Rs.Re

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.UsedAsc
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs

def UsedAsc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ τ, RegInt V τ →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ AscEmb V π d) ∧
    (∀ (a : ℕ) (π : CuspSub E a), a = N → IsNormalised π →
      ∃ V : Submodule ℂ (Sm E N), IsDiscrete V ∧ AscEmb V π 1) ∧
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → AscEmb V π d → AscEmb V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → AscEmb V π d → HasSpehComp V π d

namespace Re.Asc

theorem hasSpehComp (h3 : Clause3Asc) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N a d : ℕ} (hN : 1 ≤ N)
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {π : CuspSub E a} (hn : IsNormalised π) (e : AscEmb V π d) :
    HasSpehComp V π d := by
  refine ⟨fun w => ?_, h3 E N a d V π hN hV (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn) hn e, fun τ => ?_⟩
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
    obtain ⟨σ', hσ'⟩ := GlobalTheory.DiscLocEx.exists_isLocCompGL hF E N V hV w
    exact ⟨σ, σ', hσ, hσ'⟩
  · obtain ⟨m', hm'⟩ := PInfInd2A.exists_hasInfCharGL hV τ
    obtain ⟨m₀, hm₀, rfl⟩ := infAsc_holds E N a d V π hV e τ m' hm'
    refine ⟨m₀, hm₀, ?_⟩
    have e' : (∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))) = GlobalTheory.SphGal.spehInf d m₀ := by
      simp only [GlobalTheory.SphGal.spehInf, spehExp]
      push_cast
      rfl
    rw [← e']
    exact hm'

section Pair

end Pair

section Local

open GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.BcSpehProof

end Local

end Re.Asc

end PositivityTheory.Rg.Rs

end
end


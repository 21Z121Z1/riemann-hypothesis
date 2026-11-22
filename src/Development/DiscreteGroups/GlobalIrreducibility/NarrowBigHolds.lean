import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0031
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0030
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0033
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0035
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0005
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0032
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0034
import Development.DiscreteGroups.GlobalIrreducibility.PhiTilde
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0037
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0041
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0347
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0039
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0042

namespace DiscreteGroups.sglob.DzType

theorem lFE : LFE := DiscreteGroups.sglob.DzFe.lFE_of_fe DiscreteGroups.sglob.DzFe.fe

theorem artEx_of (hX : GlobalTheory.Published.LocalLanglandsExists) : ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : Formalism.ConjugateSelfDual.IsPlaceOver A v), ∃ a, GlobalTheory.LocLanglands.IsLocalArtin h a := by
  intro L Ω _ _ _ _ _ A v h
  obtain ⟨rc, a, ha, -⟩ := hX L Ω A v h
  exact ⟨a, ha⟩

theorem narrowBig_holds (art : GlobalTheory.Published.GlobalArtinReciprocity) (chev : GlobalTheory.Published.ChevalleyUnits)
    (hX : GlobalTheory.Published.LocalLanglandsExists) (bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : NarrowBig :=
  narrowBig_of lCusp lDepth lTame
    (lMatchBig_of lCusp lDepth (lOneOf (lTameRec art chev)) (lPin_of_dig dig) lKondo (lFinPair lFE) lPsi (lGen bern)
      (lRed DiscreteGroups.sglob.LConv.cuspGen) lTw (galEps_of_art (artEx_of hX) (lTameRec art chev)))

end DiscreteGroups.sglob.DzType

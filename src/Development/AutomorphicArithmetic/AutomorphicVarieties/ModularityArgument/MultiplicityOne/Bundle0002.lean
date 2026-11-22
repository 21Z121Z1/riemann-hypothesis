import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.NoData
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RIdent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.ContinuousESp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RelIndexGlobNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.LevInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfPi

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOf
section
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.G UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Mult

theorem compOf (hBC : Desc.BCOut) (hW : GalWeak 4) : CompOf := by
  intro E _ _ _ hunr n hn hn4 π hreg hd σ hσ _ hae w hw τ hτ
  obtain ⟨D₀, hone, -⟩ := onePre E n hn π hreg (csdDisc E n hn π hd)
  obtain ⟨hs₀, hex, hsub₀⟩ := GlobalTheory.CompanionTheory.OnePart.oneRead E n hn π _ hone
  obtain ⟨D, h1, h2, h3⟩ := hBC E hunr n hn σ hσ
  have hD₀ : {w | IsSplitAt w ∧ ¬ D₀.SplitAt σ w}.Finite := by
    refine Set.Finite.subset (Filter.eventually_cofinite.1 hae) fun w hw hx => hw.2 ?_
    obtain ⟨τ, B, a, c', d⟩ := hx hw.1
    obtain ⟨τ', hτ'⟩ := hex w
    exact ⟨τ, (hsub₀ w τ' hτ' τ).2 (GlobalTheory.CompanionTheory.SatComp.satComp E n π w τ τ' B c'.1 c' d hτ'), a⟩
  have hD : One D π := onlyPre hW hunr hn hn4 π hreg hd D h1 h2
    ((Rig.splitSatPre E n σ hσ D D₀ (Set.Finite.subset Set.finite_empty fun w hw => hw.2 (h3 w hw.1)) hD₀).mono
      fun w hw hs => (hw hs).imp fun B hB => ⟨hB.1, (hs₀ w B).2 hB.2⟩)
  obtain ⟨P, a, b⟩ := h3 w hw
  exact Desc.Comp.congr b (((GlobalTheory.CompanionTheory.OnePart.oneRead E n hn π _ hD).2.2 w τ hτ P).1 a)

end UpperTheory.V.Z.Mult
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.NoDataOf
section
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.G UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Mult

theorem noData_of (hW : GalWeak 4) : NoData := by
  intro E _ _ _ hunr n hn1 hn4 π hreg hd D₁ h1 h2 h3 h4
  obtain ⟨D, r, t, s, hno⟩ := preOf (partNorm absInf) csdSat Asm.places E n hn1 π hd D₁ h1 h2 h3 h4
  obtain ⟨D₀, hone, hr⟩ := onePre E n hn1 π hreg (csdDisc E n hn1 π hd)
  have hs := oneSat E n hn1 π D₀ hone
  have ht : D₀.ThetaStable := (csdSat E n hn1 π hd).mono fun w ⟨B, a, b⟩ => ⟨B, (hs w B).1 a, fun u hu => (hs u _).1 (b u hu)⟩
  obtain ⟨e, he⟩ := Rig.locRigid_holds E n D D₀ r hr (galStep_le hW E hunr n hn4 D D₀ r hr t ht
    (s.mono fun w hw hx => (hw hx).imp fun B hB => ⟨hB.1, (hs w B).1 hB.2⟩))
  exact absurd (onlyOne cuspOrTwo notTwo oneSat E n hn1 π D D₀ e r hone he) hno

theorem mult_of (hW : GalWeak 4) (hC : CompOf) (hS : StableBlockSA) : Mult :=
  have hA := rCountAt hC evalD cpUniq Asm.places
  rMult (rIdent (noData_of hW) hA geomTr UpperTheory.ConvolutionTheory.G2.g2s UpperTheory.ConvolutionTheory.G2.matchUnit UpperTheory.ConvolutionTheory.G2.matchSplit
      (endoS (enlarge Th.stUnit hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues Asm.places) Asm.places (UpperTheory.Zero.ConvolutionTheory.EB.endoBlockG cuspReadI)) hS)
    hA levTr geomTr levInd lcLev choiceM offSec muEx

end UpperTheory.V.Z.Mult
end


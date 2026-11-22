import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0012
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactSub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.GeneratorPowSplitPlacesOfIdempotent
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchBPf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0009
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.MultiplicityOneBase.ArchimedeanBaseChangeFirst
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.ArchimedeanBaseChangeFourth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0874
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0011
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0010
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.LeviMatchingBlocks.StabilizerDilationWeightsDualIsotropicVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0868

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.LevIdem
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

theorem levIdem (h3 : Slots) : LevIdem := by
  intro E _ _ _ n S d a ha hS hd hPS
  obtain ⟨⟨G₁, eG₁⟩, ⟨G₂, eG₂⟩, ⟨o₁, c₁⟩, ⟨o₂, c₂⟩, hpi, hν⟩ := Lev6.main d hintProd h3 a ha hS hd hPS
  have eL : levSet S d a = Lev6.lvS d S a := Set.ext fun h => (Lev6.mem_lvS d S a h).symm
  have e₁ : lev₁ S d a = G₁ := by
    have : lev₁ S d a = Subgroup.closure (G₁ : Set (GL (Fin a) (Af E))) := by rw [eG₁, ← eL]; rfl
    rw [this, Subgroup.closure_eq]
  have e₂ : lev₂ S d a = G₂ := by
    have : lev₂ S d a = Subgroup.closure (G₂ : Set (GL (Fin (n - a)) (Af E))) := by rw [eG₂, ← eL]; rfl
    rw [this, Subgroup.closure_eq]
  have eP : ((G₁.prod G₂ : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) = Lev6.lvS d S a := by
    ext ⟨g, h⟩
    show g ∈ (G₁ : Set (GL (Fin a) (Af E))) ∧ h ∈ (G₂ : Set (GL (Fin (n - a)) (Af E))) ↔ _
    rw [eG₁, eG₂]
    exact (hpi g h).symm
  have hm : ∀ h : Hf E a (n - a), h ∈ G₁.prod G₂ ↔ h ∈ Lev6.lvS d S a := fun h => by
    rw [← SetLike.mem_coe, eP]
  rw [e₁, e₂, eP, eL]
  refine ⟨⟨by rw [eG₁]; exact o₁, by rw [eG₁]; exact c₁⟩, ⟨by rw [eG₂]; exact o₂, by rw [eG₂]; exact c₂⟩, rfl,
    fun ν hνH => ?_⟩
  obtain ⟨hne, hf⟩ := hν ν hνH
  refine ⟨((ν.real (Lev6.lvS d S a) : ℝ) : ℂ)⁻¹, inv_mul_cancel₀ hne, fun x y h => ?_⟩
  rw [hf x y h]
  by_cases hc : x = y ∧ h ∈ Lev6.lvS d S a
  · rw [if_pos hc, if_pos ⟨hc.1, (hm h).2 hc.2⟩]
  · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.1, (hm h).1 h'.2⟩)]

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.MatchAll
section
namespace PositivityTheory.Rg.BcB.F.MatchAll

open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcN.F2.LocOpPf

theorem ctMul : MT.CtMul := GlobalTheory.T.constant_term_multiplicative

theorem fuMul : MT.FUMul := GlobalTheory.T.finite_unitary_multiplication

theorem dcosMul : MT.DcosMul := GlobalTheory.T.double_coset_multiplication

theorem hM4 : M4 := archimedean_base_change_fourth

theorem hM1 : M1 := m1

theorem matchT_of (h4 : M4) : MT.MatchT := TorusMatching.match_torus_of_twisted_matching h4

theorem matchT : MT.MatchT := matchT_of archimedean_base_change_fourth

theorem matchUnitI_of (h1 : M1) : MB.MatchUnitI := MB.matchUnitIOf h1

theorem matchUnitI : MB.MatchUnitI := matchUnitI_of m1

theorem matchSplit (h3 : M3) : MT.MatchSplit := GlobalTheory.T.matching_split_of h3 ctMul

theorem matchLMId : MLM.MatchLMId := MLM.matchLMIdOf idemAlg BlockFiniteConvolution.locOk₀

theorem macInv : MLM.MacInv := MLM.macInvOf locOp3 idemAlg

theorem generator_pow_split_places : MLM.SplitPlaceGeneratorPowers := MLM.generator_pow_split_places_of_idempotent idemAlg

theorem matchLMWord (h3 : M3) : MLM.MatchLMWord := MLM.matchLMWordOf (matchSplit h3) ctMul sphComm idemAlg

theorem matchLMWordS (h3 : M3) : MLM.MatchLMWordS := MLM.matchLMWordSOf (matchSplit h3) ctMul MLM.ctStar sphComm idemAlg

theorem matchLMUnit (h1 : M1) (h3 : M3) : MLM.MatchLMUnit := MLM.matchLMUnitOf (matchUnitI_of h1) (matchSplit h3) idemAlg

theorem matchLMB2 (h2 : M2) (h3 : M3) (h4 : M4) : MLM.MatchLMB2 :=
  MLM.matchLMB3Of_pf (matchT_of h4) (MS.match_split_place_of_powers h3 (MS.split_place_powers_of_local_ops locOp3)) (MB.matchBadSOf h3 MB.lponeIdem)
    (MB.matchBadIOf2 h2 MB.lponeIdem) MB.fixIdem idemAlg

end PositivityTheory.Rg.BcB.F.MatchAll
end


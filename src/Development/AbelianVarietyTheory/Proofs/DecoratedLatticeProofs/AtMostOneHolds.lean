import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneCouplingCosetOfPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneLatticeClassStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneIndexOfOneClassOfSupportOne
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem atMostOne_holds : AtMostOne := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := _root_.GlobalTheory.SymChain.pattern_iter k s κ S t
  have hclass : S.OneClass t ν := GlobalTheory.T.symmetricChain_oneLatticeClass k ν hν s κ S t
  have hsupp : S.SupportOne t := _root_.GlobalTheory.SymSupport.supportOne_of_pattern k s κ S t hpat
  exact ⟨_root_.GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne k ν hν s κ S t hclass hsupp, GlobalTheory.T.symmetricChain_projected_level_of_pattern k s κ S t hpat, _root_.GlobalTheory.SymChain.oneCoupling k s κ S t hpat⟩

end GlobalTheory.SymChain

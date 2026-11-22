import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0003
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetSurjectiveOfLevi
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CountOfHeisenbergIndex
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.HeisenbergMatrixFacts

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.ACo
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ipf.Val.SphM

def aCo (q c t k j : ℕ) : ℂ :=
  (q : ℂ) ^ ((c - j) * (k - j)) * (Formalism.L2.Col.gaussBin q t (k - j) : ℂ) * (((Real.sqrt q : ℝ) : ℂ) ^ c)⁻¹ ^ k *
    (((Real.sqrt q : ℝ) : ℂ) ^ (c + t)) ^ j

end GlobalTheory.CompanionTheory.Ipf.Val.SphM

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExistsStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_vector_exists : AddVec := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.addVec | exact GlobalTheory.CompanionTheory.InertZeta.addVec | (intros; apply GlobalTheory.CompanionTheory.InertZeta.addVec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CompletionExistsStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_exists : Completion := by
  first | exact @GlobalTheory.CompanionTheory.InertDoubling.completion | exact GlobalTheory.CompanionTheory.InertDoubling.completion | (intros; apply GlobalTheory.CompanionTheory.InertDoubling.completion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetInjectiveStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_injective : CosetInj := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetInj | exact GlobalTheory.CompanionTheory.InertZeta.cosetInj | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetInj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetIntegralStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetIntegral' : CosetIntegral := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | exact GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetIntegral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetSurjectiveOfLeviStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_surjective_of_levi : LeviExists → CosetSurj := by
  first | exact @GlobalTheory.CompanionTheory.InertCoset.cosetSurj | exact GlobalTheory.CompanionTheory.InertCoset.cosetSurj | (intros; apply GlobalTheory.CompanionTheory.InertCoset.cosetSurj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CountOfHeisenbergIndexStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_of_heisenberg_index : Heis → LatIndex → TraceIndex → Count := by
  first | exact @GlobalTheory.CompanionTheory.InertCount.count | exact GlobalTheory.CompanionTheory.InertCount.count | (intros; apply GlobalTheory.CompanionTheory.InertCount.count <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DoubleCosetSwapStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_swap : DosetSwap := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.dosetSwap | exact GlobalTheory.CompanionTheory.InertZeta.dosetSwap | (intros; apply GlobalTheory.CompanionTheory.InertZeta.dosetSwap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DualPairingExistsStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_pairing_exists : Dual := by
  first | exact @GlobalTheory.CompanionTheory.InertDual.dual | exact GlobalTheory.CompanionTheory.InertDual.dual | (intros; apply GlobalTheory.CompanionTheory.InertDual.dual <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.FractionExistsOfSmithStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fraction_exists_of_smith : Smith → FracExists := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith | exact GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith | (intros; apply GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.GeneratingFunctionIdentityStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generating_function_identity : GenFun := by
  first | exact @GlobalTheory.CompanionTheory.InertGenFun.genFun | exact GlobalTheory.CompanionTheory.InertGenFun.genFun | (intros; apply GlobalTheory.CompanionTheory.InertGenFun.genFun <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.HeisenbergMatrixFactsStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_matrix_facts : Heis := by
  first | exact @GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ | exact GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ | (intros; apply GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ <;> assumption)
end


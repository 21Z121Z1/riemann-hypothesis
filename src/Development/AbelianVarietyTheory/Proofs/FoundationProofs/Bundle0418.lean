import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0417
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0396
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0410

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataCyclotomicAlgebraStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ F : Finset A, ∃ (C : Subalgebra (fixA A) A) (tr : A → A) (n : ℕ) (a b : Fin n → A), (↑F : Set A) ⊆ C ∧ IsTrData (cycAlg l A) C tr a b (l : A) := by
  first | exact @GlobalTheory.RecOne.TrCyc.exists_trData_cycAlg | exact GlobalTheory.RecOne.TrCyc.exists_trData_cycAlg | (intros; apply GlobalTheory.RecOne.TrCyc.exists_trData_cycAlg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocPublishedOfLitCoh
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem localGaloisCohomology_of_galoisCohomology (h : GlobalTheory.Mem.LiteralAutomorphy.LitCoh) : Loc.LocalPublishedTheorems :=
  ⟨h.lfK, h.ltK, h.leK, h.lf, h.lt, h.le, h.bk⟩

theorem es_vanish : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → BlochKatoSelmerVanishes l (Loc.colRep W) := by
  intro hLit l _ Ω _ _ _ e S A W hNf hES c hc hBK
  have hStr : StrZero (dual1 W) A := GlobalTheory.T.strict_vanishing_dual_of_literature hLit l Ω e S A W hNf hES
  have hGrD : GrZero (dual1 W) A := GlobalTheory.T.ordinarySelmer_dual_vanishes_of_strict hLit l Ω e S A W hNf hES hStr
  have hGr : GrZero W A := GlobalTheory.T.ordinarySelmer_vanishes_of_dual_vanishes hLit l Ω e S A W hNf hGrD
  obtain ⟨hU, hG⟩ := GlobalTheory.T.blochKato_cocycle_unramified_and_greenbergOrdinary (localGaloisCohomology_of_galoisCohomology hLit) l Ω e S A W hNf c hc hBK
  exact hGr c hc hU hG

end GlobalTheory.Ord2
end


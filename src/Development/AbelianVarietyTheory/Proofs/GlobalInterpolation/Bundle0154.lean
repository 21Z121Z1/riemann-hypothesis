import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0153
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0150

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplitStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU E n : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU E n, k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU E n) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU E n) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  first | exact @GlobalTheory.UnitarySplit.dense_and_split | exact GlobalTheory.UnitarySplit.dense_and_split | (intros; apply GlobalTheory.UnitarySplit.dense_and_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RightFiniteMemPoly
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem rightFinite_mem_poly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (f : infU E n → ℂ), Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => fun x : infU E n => f (x * k))) → f ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} := by
  intro E _ _ _ n f hf hfin
  haveI := GlobalTheory.T.compactSpace_definiteUnitaryInfinitePoints E n
  obtain ⟨hc, hs, hsep, hinv, hcop⟩ := GlobalTheory.T.unitary_coordinate_algebra_dense E n
  haveI : T2Space (infU E n) := ⟨fun x y hxy => by
    obtain ⟨p, hp, hne⟩ := hsep x y hxy
    exact separated_by_continuous (hc p hp) hne⟩
  refine GlobalTheory.T.mem_of_finiteDimensional_span_rightTranslates' (infU E n) (Algebra.adjoin ℂ _) hc hs hsep ?_ f hf hfin
  intro p hp
  obtain ⟨m, a, b, hab, heq⟩ := hcop p hp
  refine ⟨m, fun i x => a i x⁻¹, b, fun i => ⟨hinv _ (hab i).1, hc _ (hab i).2⟩, ?_⟩
  intro x k
  exact heq x⁻¹ k

end GlobalTheory.UnitaryBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedEvaluationBranchingAllTuplesTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PerQ.lowerTieTwAt_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), GlobalTheory.PerQ.LowerTieTwAt (I.rec7 l Z) (I.tw l l0 Z) u a := by
  intro B X I hI l Z l0 u a
  exact ⟨(GlobalTheory.T.evaluationMap_trueChain_forms_to_forms I hI l Z l0 u a).1, (GlobalTheory.T.evaluationMap_trueChain_forms_to_forms I hI l Z l0 u a).2, GlobalTheory.T.exists_integralCoordinates_twistedTrueChain I hI l Z l0 u a⟩
end


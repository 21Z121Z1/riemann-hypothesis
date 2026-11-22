import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpace
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SoStable

theorem so_stable : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ γ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' γ Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT γ Φ' hΦ
  unfold Model.So at hΦ ⊢
  induction hΦ using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  | mem x hx =>
    obtain ⟨f, φ, hSB, hcof, hloc, rfl⟩ := hx
    obtain ⟨g₁, g₂, hg, hg₁, hg₂⟩ := GlobalTheory.T.unitary_adelic_place_decomposition F E σ a' G.V'.J B.v₁ γ.1
    obtain ⟨h₁, h₂, hh, hh₁, hh₂⟩ := GlobalTheory.T.unitary_adelic_place_decomposition F E σ (a + a') G.W.J B.v₁ γ.2
    have hγ : γ = (g₁, h₁) * (g₂, h₂) := Prod.ext hg hh
    obtain ⟨f₂, φ₂, hSB₂, hcof₂, hv₂, he₂⟩ :=
      GlobalTheory.T.theta_trivial_at_place_product hP F E σ B a a' G X om om' hT B.v₁ g₂ h₂ hg₂ hh₂ f φ hSB hcof
    obtain ⟨φ', hSB', hne', hacts, he'⟩ :=
      GlobalTheory.T.local_unitary_action_schwartz_inf hP F E σ B a a' G X om om' hT B.v₁ g₁ hg₁ h₁ hh₁ f₂ φ₂ hSB₂ hcof₂
    rw [hγ, map_mul, Module.End.mul_apply, he₂, he']
    refine Submodule.subset_span ⟨f₂, φ', hSB', ?_, ?_, rfl⟩
    · filter_upwards [hcof₂, (Set.finite_singleton B.v₁).compl_mem_cofinite] with w hw hw'
      rw [hne' w hw', hw]
    · obtain ⟨hφSB, ι, hι, hsupp⟩ := hloc
      refine ⟨hSB' _, ι, hι, fun Y hY => ?_⟩
      obtain ⟨c, P, Q, hPQ⟩ := GlobalTheory.T.linear_bar_local_theta_factor hP F E σ B a a' G X om om' hT B.v₁ B.τ₁ ι hι g₁ hg₁ h₁ hh₁
        (φ₂ B.v₁) (hSB₂ _) (φ' B.v₁) (hSB' _) hacts
      rw [hPQ, hv₂, hsupp, mul_zero]
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det]
      · exact (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      · exact (Matrix.isUnit_iff_isUnit_det _).mp Q.isUnit

end GlobalTheory.SoStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralStandardPairFirstEqSecondStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegral_standardPair_first_eq_second : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
      bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (GlobalTheory.StdPairCone.stdA ν ϖ c a a') =
        smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν (ν * β) (GlobalTheory.StdPairCone.stdB ν ϖ c a a') := by
  first | exact @GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | exact GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | (intros; apply GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB <;> assumption)
end


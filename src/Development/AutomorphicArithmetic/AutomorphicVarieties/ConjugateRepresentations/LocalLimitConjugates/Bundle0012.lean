import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0005

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpComm
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.opComm :
    UpperTheory.V.Cj.H.OpComm := by
  intro E _ _ _ a ha μ _ _ T hT T' hL
  obtain ⟨c1, c2, c3, -⟩ := clFacts E a μ
  have gf := gardFacts E a ha μ
  refine ⟨fun φ h => (hL φ h).1, fun X φ hφ => ?_, fun g φ hφ => ?_⟩
  · induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨ψ, F, hψ, hφ⟩ := h
      have h1 := liftCv E a ha μ T hT T' hL ψ φ F hψ hφ
      have h2 := cvLie E a μ ψ _ hψ _ h1 X
      have h3 := cvLie E a μ ψ φ hψ F hφ X
      have h4 := liftCv E a ha μ T hT T' hL _ _ F (((testOps E a ψ).2 hψ).1 X) h3
      exact Subtype.ext (h2.trans h4.symm)
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul s x _ hx => simp only [map_smul, hx]
  · have m1 : rt E a g (T' φ) ∈ gard μ := (gf _ (hL φ hφ).1).2.2.2.2 g
    have m0 : rt E a g φ ∈ gard μ := (gf _ hφ).2.2.2.2 g
    have m2 : T' (rt E a g φ) ∈ gard μ := (hL _ m0).1
    have m3 : (1 : ℂ) • rt E a g (T' φ) + (-1 : ℂ) • T' (rt E a g φ) ∈ gard μ :=
      add_mem (Submodule.smul_mem _ _ m1) (Submodule.smul_mem _ _ m2)
    have e := (c1 _ _ 1 (-1) (gf _ m1).2.1 (gf _ m2).2.1).2
    rw [c3 _ g (gf _ (hL φ hφ).1).2.1, (hL φ hφ).2, (hL _ m0).2, c3 _ g (gf _ hφ).2.1, hT,
      ← add_smul, add_neg_cancel, zero_smul] at e
    have z := c2 _ (gf _ m3).1 (gf _ m3).2.1 e
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at z
    exact z
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.opLim :
    UpperTheory.V.Cj.H.OpLim := by
  intro E _ _ _ a ha μ _ _ T P hT hP hlim T' P' hT' hP' φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ψ, F, hψ, hF⟩ := h
    intro C hC
    have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
    obtain ⟨-, hlin, -, hb⟩ := cvAlg (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1
    obtain ⟨B, hB⟩ := hb C hC
    have h1 : ∀ k, (T' k φ).1 = cv ψ.1 (T k F) := fun k =>
      liftCv E a ha μ (T k) (hT k) (T' k) (hT' k) ψ φ F hψ hF
    have h2 : (P' φ).1 = cv ψ.1 (P F) := liftCv E a ha μ P hP P' hP' ψ φ F hψ hF
    have h3 : Tendsto (fun k => B * ‖P F - T k F‖) atTop (𝓝 0) := by
      have h4 : Tendsto (fun k => P F - T k F) atTop (𝓝 (P F - P F)) := tendsto_const_nhds.sub (hlim F)
      have h5 := h4.norm.const_mul B
      simpa using h5
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [h3.eventually (gt_mem_nhds hε)] with k hk x hx
    rw [h1, h2, dist_eq_norm]
    have h6 := congrFun (hlin (P F) (T k F) 1 (-1)) x
    have h7 : (1 : ℂ) • P F + (-1 : ℂ) • T k F = P F - T k F := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [h7] at h6
    have h8 : cv ψ.1 (P F) x - cv ψ.1 (T k F) x = cv ψ.1 (P F - T k F) x := by
      rw [h6]; simp [sub_eq_add_neg]
    rw [h8]
    exact (hB _ x hx).trans_lt hk
  | zero =>
    intro C _
    simp only [map_zero]
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun k x _ => by simpa using hε
  | add φ ψ _ _ h1 h2 =>
    intro C hC
    simp only [map_add]
    exact (h1 C hC).add (h2 C hC)
  | smul c φ _ h =>
    intro C hC
    simp only [map_smul]
    exact (uniformContinuous_const_smul c).comp_tendstoUniformlyOn (h C hC)
end


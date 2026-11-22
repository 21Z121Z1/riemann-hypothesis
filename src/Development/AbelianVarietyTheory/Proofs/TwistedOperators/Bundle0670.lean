import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0663
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0622
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0613
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0608
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0614
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0642
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0637
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMoveArgumentsLastRowVertex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.TopLevelInv.FlatStep
open GlobalTheory.FunObj.FiniteSupport

section Helpers
variable {k : Type} [Field k]

theorem reindex_mul_frameGL {a c b : ℕ} {ι : Type} {a' : ℕ} (h : a + c = b) (f : ι ≃ Fin a') (g : GL (Fin b) k)
    (D : Matrix ι (Fin a ⊕ Fin c) k) :
    D.reindex f (frame h) * g.val = (D * (frameGL h g).val).reindex f (frame h) := by
  ext r s
  simp only [reindex_apply, Matrix.mul_apply, submatrix_apply, frameGL_val]
  exact Fintype.sum_equiv (frame h).symm _ _ fun p => by simp

theorem frameGL_embX_congr {a c c' b : ℕ} (hc : c = c') (h : a + c = b) (h' : a + c' = b) {g : GL (Fin b) k}
    {κ : GL (Fin a) k} (H : frameGL h g = embX c κ) : frameGL h' g = embX c' κ := by
  subst hc; exact H

theorem eq_one_of_mem_symN_zero {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {v : GL (n ⊕ Fin c) k}
    (hv : v ∈ symN k n c) (hc : c = 0) : v = 1 := by
  subst hc
  have key : ∀ p, N k n 0 p = ⊥ := fun p => by
    rw [N, Subgroup.closure_eq_bot_iff]
    intro g hg
    rw [Set.mem_singleton_iff]
    refine Units.ext (Matrix.ext fun r s => ?_)
    rcases r with r | r
    · rcases s with s | s
      · exact hg _ _ le_rfl
      · exact s.elim0
    · exact r.elim0
  rw [symN, key, key, sup_bot_eq, Subgroup.mem_bot] at hv
  exact hv

abbrev StepFam (Γ : Grid k) [MeasurableSpace k] : Type :=
  ∀ i : Fin (Γ.m - 1), (StepVar (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i)) → k) ≃ᵐ
    (StepVar (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i)) → k)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem measurePreserving_stepFam {Γ : Grid k} (ν : Measure k) [ν.IsAddHaarMeasure] (φ : StepFam Γ)
    (hφ : ∀ i, MeasurePreserving (φ i) (stepVol ν _ _ _) (stepVol ν _ _ _)) :
    MeasurePreserving (MeasurableEquiv.piCongrRight φ) (varsVol Γ ν) (varsVol Γ ν) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : ∀ i : Fin (Γ.m - 1), SigmaFinite (stepVol ν (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i))) :=
    fun i => by unfold stepVol; infer_instance
  rw [varsVol_eq]
  exact measurePreserving_pi _ _ hφ

theorem measurePreserving_update {Γ : Grid k} (ν : Measure k) (Ψ : StepFam Γ)
    (hΨ : ∀ i, MeasurePreserving (Ψ i) (stepVol ν _ _ _) (stepVol ν _ _ _)) (i₀ : Fin (Γ.m - 1))
    (φ : (StepVar (Fin (topRank Γ (i₀ + 1))) (Γ.m - 2 - i₀) (Fin (topRank Γ i₀)) → k) ≃ᵐ
      (StepVar (Fin (topRank Γ (i₀ + 1))) (Γ.m - 2 - i₀) (Fin (topRank Γ i₀)) → k))
    (hφ : MeasurePreserving φ (stepVol ν _ _ _) (stepVol ν _ _ _)) :
    ∀ i, MeasurePreserving ((Function.update Ψ i₀ φ : StepFam Γ) i) (stepVol ν _ _ _) (stepVol ν _ _ _) := by
  intro i
  rcases eq_or_ne i i₀ with rfl | h
  · rw [Function.update_self]; exact hφ
  · rw [Function.update_of_ne h]; exact hΨ i

theorem flatTensor_comp_of_equiv {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) (F : Γ.Args → ℂ)
    (A : Γ.Args → Γ.Args) (x x' : ColArgs Γ) (y : RowArgs Γ) (Φ : Vars Γ ≃ᵐ Vars Γ)
    (hΦ : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν))
    (hfill : ∀ e, A (fill hs x y e) = fill hs x' y (Φ e)) (hph : ∀ e, phase x e = phase x' (Φ e)) :
    flatTensor hs ψ ν (fun z => F (A z)) x y = flatTensor hs ψ ν F x' y := by
  rw [flatTensor, flatTensor, ← hΦ.integral_comp' (flatIntegrand hs ψ F x' y)]
  congr 1
  funext e
  simp only [flatIntegrand, hfill, hph]

theorem downMap_congr {Γ : Grid k} (hs : 1 ≤ Γ.s) {x x' : ColArgs Γ} {e e' : Vars Γ} {l : ℕ} (hx : x' l = x l)
    (he : ∀ h : l < Γ.m - 1, e' ⟨l, h⟩ = e ⟨l, h⟩) : downMap hs x' e' l = downMap hs x e l := by
  unfold downMap
  split_ifs with h1
  · rw [hx, he h1]
  · rw [hx]
  · rfl

end Helpers

theorem flatTensor_moveArgs_mulSingle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (F : Γ.Args → ℂ)
    (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin (topRank Γ (j + 1))) (Γ.m - 1 - (j + 1)), toFrame hs hj g = v * embX _ κ →
    ∀ (x : ColArgs Γ) (y : RowArgs Γ),
      flatTensor hs ψ ν (fun z => F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) z)) x y = flatTensor hs ψ ν F (colMove j κ x) y := by
  intro k _ _ _ _ _ _ Γ hs ψ ν _ F j hj g κ hdet v hv hg x y
  have hcol : ∀ i, i ≠ j → i ≠ j + 1 → colMove j κ x i = x i := fun i h1 h2 => by
    simp only [colMove, Function.update_of_ne h1, Function.update_of_ne h2]
  have hcj : colMove j κ x j = (κ⁻¹).val * x j := by
    simp only [colMove, Function.update_of_ne (show j ≠ j + 1 by omega), Function.update_self]
  have hcj1 : colMove j κ x (j + 1) = x (j + 1) * κ.val := by
    simp only [colMove, Function.update_self]
  rcases Nat.lt_or_ge (j + 2) Γ.m with hA | hB
  · obtain ⟨φ₀, hφ₀, φ₁, hφ₁, H⟩ := GlobalTheory.T.lastRowVertex_adjacentSteps_translate_frames (a₀ := topRank Γ j) (a₂ := topRank Γ (j + 1 + 1))
      (c := Γ.m - 2 - (j + 1)) (c₀ := Γ.m - 2 - j) ν (by omega) (by omega)
      (by have := topRank_add hs (j + 1); omega) (by have := topRank_add hs (j + 1); omega) _ g κ hdet v hv hg
      (x j) (x (j + 1))
    have h01 : (⟨j, by omega⟩ : Fin (Γ.m - 1)) ≠ ⟨j + 1, by omega⟩ := fun h => by simp at h
    let Ψ0 : StepFam Γ := fun i => MeasurableEquiv.refl _
    let Ψ1 : StepFam Γ := Function.update Ψ0 ⟨j, by omega⟩ φ₀
    let Ψ2 : StepFam Γ := Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁
    let Φ : Vars Γ ≃ᵐ Vars Γ := MeasurableEquiv.piCongrRight Ψ2
    have hΦ0 : ∀ e, Φ e ⟨j, by omega⟩ = φ₀ (e ⟨j, by omega⟩) := fun e => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_of_ne h01]
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_self]
    have hΦ1 : ∀ e, Φ e ⟨j + 1, by omega⟩ = φ₁ (e ⟨j + 1, by omega⟩) := fun e => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ ⟨j + 1, by omega⟩ (e ⟨j + 1, by omega⟩) = _
      rw [Function.update_self]
    have hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ j → i.val ≠ j + 1 → Φ e i = e i := fun e i h1 h2 => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ i (e i) = _
      rw [Function.update_of_ne (fun h => h2 (by rw [h]))]
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ i (e i) = _
      rw [Function.update_of_ne (fun h => h1 (by rw [h]))]
      rfl
    have hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν) :=
      measurePreserving_stepFam ν Ψ2 (measurePreserving_update ν Ψ1
        (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨j, by omega⟩ φ₀ hφ₀) ⟨j + 1, by omega⟩ φ₁ hφ₁)
    refine flatTensor_comp_of_equiv hs ψ ν F _ x (colMove j κ x) y Φ hMP (fun e => ?_) (fun e => ?_)
    · refine GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex hs j hj g x (colMove j κ x) y e (Φ e) (fun l h1 h2 => ?_) ?_ ?_
      · exact downMap_congr hs (hcol l h1 h2) fun h => hΦo e ⟨l, h⟩ h1 h2
      · rw [downMap, dif_pos (show j < Γ.m - 1 by omega), downMap, dif_pos (show j < Γ.m - 1 by omega), hcj, hΦ0]
        exact ((H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).1 _).symm
      · rw [downMap, dif_pos (show j + 1 < Γ.m - 1 by omega), downMap, dif_pos (show j + 1 < Γ.m - 1 by omega),
          hcj1, hΦ1]
        exact ((H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.1 _).symm
    · have hrow : ∀ (x : ColArgs Γ) (e : Vars Γ) r, rowVar x e (j + 1) r = ∑ l : Fin (Γ.m - 2 - (j + 1)),
          if l.val = (Γ.m - 2 - (j + 1)) / 2 then stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩) (.inr l) (.inl r) else 0 :=
        fun x e r => by rw [rowVar, dif_pos (by omega)]
      refine GlobalTheory.T.fourierJacobiPhase_adjacentInnerSteps_invariant j hA x (colMove j κ x) e (Φ e) hcol (fun i h1 h2 => hΦo e i h1 h2) ?_ ?_ ?_
      · simp only [hrow, colVar]
        rw [hcj, hcj1, hΦ0, hΦ1]
        exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.1
      · intro ho s
        rw [rowVar, rowVar, dif_pos (by omega), dif_pos (by omega)]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs with hl
        · rw [hcj, hΦ0]
          exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.2.1 ho l s hl
        · rfl
      · intro ho r
        simp only [colVar]
        rw [hcj1, hΦ1]
        exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.2.2 ho r _ rfl
  · have hB' : j + 2 = Γ.m := by omega
    obtain rfl : v = 1 := eq_one_of_mem_symN_zero hv (by omega)
    have hg' : toFrame hs hj g = embX _ κ := by rw [hg, one_mul]
    obtain ⟨φ₀, hφ₀, H⟩ := GlobalTheory.T.fourierJacobiStep_leftChange_measurePreserving (n := Fin (topRank Γ (j + 1))) (n' := Fin (topRank Γ j)) (c := Γ.m - 2 - j)
      ν 1 (one_mem _) κ hdet (x j)
    let Ψ0 : StepFam Γ := fun i => MeasurableEquiv.refl _
    let Ψ1 : StepFam Γ := Function.update Ψ0 ⟨j, by omega⟩ φ₀
    let Φ : Vars Γ ≃ᵐ Vars Γ := MeasurableEquiv.piCongrRight Ψ1
    have hΦ0 : ∀ e, Φ e ⟨j, by omega⟩ = φ₀ (e ⟨j, by omega⟩) := fun e => by
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_self]
    have hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ j → Φ e i = e i := fun e i h1 => by
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ i (e i) = _
      rw [Function.update_of_ne (fun h => h1 (by rw [h]))]
      rfl
    have hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν) :=
      measurePreserving_stepFam ν Ψ1 (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨j, by omega⟩ φ₀ hφ₀)
    have hf : frameGL (show topRank Γ (j + 1) + (Γ.m - 2 - j) = Γ.rank (Γ.m, j + 1) by
        have := topRank_add hs (j + 1); omega) g = embX (Γ.m - 2 - j) κ :=
      frameGL_embX_congr (by omega) _ _ hg'
    refine flatTensor_comp_of_equiv hs ψ ν F _ x (colMove j κ x) y Φ hMP (fun e => ?_) (fun e => ?_)
    · refine GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex hs j hj g x (colMove j κ x) y e (Φ e) (fun l h1 h2 => ?_) ?_ ?_
      · exact downMap_congr hs (hcol l h1 h2) fun h => hΦo e ⟨l, h⟩ h1
      · rw [downMap, dif_pos (show j < Γ.m - 1 by omega), downMap, dif_pos (show j < Γ.m - 1 by omega), hcj, hΦ0,
          ← H, one_mul, mul_reindex, map_inv, hf]
      · exact GlobalTheory.T.downwardVertexMap_lastVertex_mul_of_frame hs j hj hB' g κ hg' x (colMove j κ x) e (Φ e) hcj1
    · refine GlobalTheory.T.fourierJacobiPhase_lastInnerVertex_invariant j hB' κ x (colMove j κ x) e (Φ e) hcol hcj1 (fun i h1 => hΦo e i h1) ?_
      rw [hcj, hΦ0, ← H, one_mul]

end GlobalTheory.TopLevelInv.FlatStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKSubmoduleInfimumAndIrreducibleSupremum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGK

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem isGKSub_sInf (s : Set (Submodule ℂ (GA D V → ℂ))) (h : ∀ A ∈ s, IsGKSub θ M A) : IsGKSub θ M (sInf s) where
  k τ g hg f hf := Submodule.mem_sInf.2 fun A hA => (h A hA).k τ g hg f (Submodule.mem_sInf.1 hf A hA)
  lie τ X hX f hf := Submodule.mem_sInf.2 fun A hA => (h A hA).lie τ X hX f (Submodule.mem_sInf.1 hf A hA)

open scoped Matrix in
variable {M} in

theorem InK.inv {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (h : InK M τ g) : InK M τ g⁻¹ := by
  obtain ⟨hU, hk⟩ := h
  have hfd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set k := M.fr τ * g * (M.fr τ)⁻¹ with hkdef
  have hku : k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := hk.1
  have hsk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
  have hks : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hku
  have hkdet : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨⟨k, star k, hks, hsk⟩, rfl⟩
  have hdet : k.det = g.det := by
    rw [hkdef, Matrix.det_mul, Matrix.det_mul, mul_comm (M.fr τ).det, mul_assoc, ← Matrix.det_mul,
      Matrix.mul_nonsing_inv _ hfd, Matrix.det_one, mul_one]
  have hgd : IsUnit g.det := hdet ▸ hkdet
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
  refine ⟨?_, ?_⟩
  · show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hg1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ = k⁻¹ := by
      rw [hkdef, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hfd]
      simp only [Matrix.mul_assoc]
    have hinv : k⁻¹ = star k := Matrix.inv_eq_left_inv hsk
    rw [e1, hinv]
    refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact hsk), ?_⟩
    have hJ : star (Formalism.REAL.Jm (M.ε τ)) = Formalism.REAL.Jm (M.ε τ) := Formalism.REAL.Jm_conjTranspose _
    have hcomm : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ, m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * m →
        star m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * star m := fun m hm => by
      have h2 : star (m * Formalism.REAL.Jm (M.ε τ)) = star (Formalism.REAL.Jm (M.ε τ) * m) := congrArg star hm
      rw [star_mul, star_mul, hJ] at h2
      exact h2.symm
    exact hcomm k hk.2

theorem mem_iSup_irr : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  intro hP D θ V S M hθ ψ hA hC hW
  obtain ⟨b, hpos, hherm, hK, hL⟩ := GlobalTheory.T.cusp_form_finite_dim_compact_stable hP θ V S M hθ ψ hA hC hW
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := GlobalTheory.T.cusp_form_finite_dim_frame_stable hP θ V S M hθ ψ hA hC hW b hpos hherm hK hL
  refine GlobalTheory.T.mem_iSup_irreducible_of_fixed_projector (IsGKSub θ M) (isGKSub_sInf θ M) (gkGen θ M ψ) (isGKSub_gkGen θ M ψ) b
    hpos hherm (fun A hAle hAP => ?_) e he2 he3 he4 he5 ψ (mem_gkGen θ M ψ) he1
  have hperp : ∀ f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a),
      f ∈ gkGen θ M ψ ∧ ∀ a ∈ A, b a f = 0 := fun f hf => by
    rw [Submodule.mem_inf] at hf
    exact ⟨hf.1, fun a ha => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf.2 a) ha)⟩
  have hmk : ∀ f, f ∈ gkGen θ M ψ → (∀ a ∈ A, b a f = 0) → f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
    fun f h1 h2 => Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun a => (Submodule.mem_iInf _).2 fun ha =>
      LinearMap.mem_ker.2 (h2 a ha)⟩
  refine ⟨fun τ g hg f hf => ?_, fun τ X hX f hf => ?_⟩
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).k τ g hg f hfN) fun a ha => ?_
    rw [hK τ g hg a (hAle ha) f hfN]
    exact hf0 _ (hAP.k τ g⁻¹ hg.inv a ha)
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).lie τ X hX f hfN) fun a ha => ?_
    rw [hL τ X hX a (hAle ha) f hfN, hf0 _ (hAP.lie τ X hX a ha), neg_zero]

end GlobalTheory.CuspGK

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianCompactActionEigen
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Matrix

namespace GlobalTheory.FockVacStab

theorem mat_mul_mat_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (k : UA σ X.J) : mat k * mat k⁻¹ = 1 ∧ mat k⁻¹ * mat k = 1 := by
  constructor
  · show (k * k⁻¹).1.1 = 1
    simp
  · show (k⁻¹ * k).1.1 = 1
    simp

theorem isGauss_of_acts : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f₀ hG f₁ hact
  have hPA := GlobalTheory.T.polynomial_datum_action_of_pair hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := GlobalTheory.T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff _ using hD
  obtain ⟨Dk, _, hDk⟩ := hPA.2.1 k hk
  have hGP : ∀ g, M.IsGauss B.ψ B.emb g → g ∈ M.Pol B.ψ B.emb := fun g h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 g h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hAt : ∀ (a : Matrix (Fin n) (Fin n) (AE F E)) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u →
      At (evI F) (a * u) := fun a u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨hkk, hkk'⟩ := mat_mul_mat_inv k

  have hcomm : ∀ w, (mat k⁻¹).map (piInf (B.emb w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
    intro w
    set A := (mat k).map (piInf (B.emb w))
    set A' := (mat k⁻¹).map (piInf (B.emb w))
    have h1 : A * A' = 1 := by
      rw [← Matrix.map_mul, hkk]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have h2 : A' * A = 1 := by
      rw [← Matrix.map_mul, hkk']; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hc : A * X.θ w = X.θ w * A := hk.2 w
    calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [h1, Matrix.mul_one]
      _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
      _ = A' * (A * X.θ w) * A' := by rw [hc]
      _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
      _ = X.θ w * A' := by rw [h2, Matrix.one_mul]
  obtain ⟨ε, hε⟩ := hG
  refine ⟨ε, fun u u' hu hu' huu' f f' hf hf' => ?_⟩
  set v := mat k⁻¹ * u
  set v' := mat k⁻¹ * u'
  have hv : At (evI F) v := hAt _ u hu
  have hv' : At (evI F) v' := hAt _ u' hu'
  have hvv' : ∀ w, v'.map (piInf (B.emb w)) =
      (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * v.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    simp only [v, v', Matrix.map_mul, huu' w, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm w]
  have hkv : mat k * v = u := by simp only [v, ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hkv' : mat k * v' = u' := by simp only [v', ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hgg : Dfun v' f₀ = Complex.I • Dfun v f₀ :=
    hε v v' hv hv' hvv' _ _ ((hDiff v hv f₀ _).2 rfl) ((hDiff v' hv' f₀ _).2 rfl)
  have hf0 : f₀ ∈ M.Pol B.ψ B.emb := hGP f₀ ⟨ε, hε⟩

  have hmove : ∀ x, At (evI F) x → ActsD (evI F) (M.heisLine B.ψ (mat k * x)) f₁ (Dk (Dfun x f₀)) := by
    intro x hx
    exact GlobalTheory.T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k hk x hx f₀ (Dfun x f₀) f₁ (Dk (Dfun x f₀))
      ((hDiff x hx f₀ _).2 rfl) hact ((hDk _ (hclos x hx f₀ hf0) _).2 rfl)
  have e1 : f = Dk (Dfun v f₀) := by
    have a := (hDiff u hu f₁ f).1 hf
    have b := (hDiff u hu f₁ _).1 (hkv ▸ hmove v hv)
    rw [a, b]
  have e2 : f' = Dk (Dfun v' f₀) := by
    have a := (hDiff u' hu' f₁ f').1 hf'
    have b := (hDiff u' hu' f₁ _).1 (hkv' ▸ hmove v' hv')
    rw [a, b]
  rw [e2, e1, hgg, map_smul]

end GlobalTheory.FockVacStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianVacuumHeisenbergDerivativeComplexStructuStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianVacuum_heisenbergDerivative_complexStructure_cancel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), M.IsGauss Bs.ψ Bs.emb g →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ g₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
            (M.heisLine Bs.ψ (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1))) g g₁' →
          g₁ + Complex.I • g₁' = 0 := by
  first | exact @GlobalTheory.GaussCancel.heis_cancel | exact GlobalTheory.GaussCancel.heis_cancel | (intros; apply GlobalTheory.GaussCancel.heis_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBottomLevelLeFormLevelLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridBottomLevel_le_formLevel_largeDepth : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  first | exact @GlobalTheory.FirstRowLevel.levRow_zero_le | exact GlobalTheory.FirstRowLevel.levRow_zero_le | (intros; apply GlobalTheory.FirstRowLevel.levRow_zero_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFirstColumnStepIsSchwartzBruhatHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridFirstColumnStep_isSchwartzBruhat_half : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e : AE D}, IsIdemSum e (GlobalTheory.FlipTop.topPl L t) → ∀ (j : ℕ) (hj : j < D.R.m),
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True) (GlobalTheory.FlipTop.topFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) := by
  first | exact @GlobalTheory.FlipTop.isSBHalf_topFn | exact GlobalTheory.FlipTop.isSBHalf_topFn | (intros; apply GlobalTheory.FlipTop.isSBHalf_topFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMatchingOfBaseChoice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

theorem exists_rowMatchS : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b →
    ∃ G' : GlobalTheory.Grid.GridPre R, G'.Is ∧ GlobalTheory.RowLift.RowMatchS ch G' := by
  intro hP D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hb CF hs
  have hsc : ch.sc.cGap = 1 := by rw [hs]
  obtain ⟨G, hG, hsp, harr⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
    hP.harishChandraModules hS.host hS.size hS.core hsc ch.W hb.weil
  have hfr : ∀ i, i ≤ D.R.m → Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ := by
    rintro (_ | i) hi
    · obtain ⟨c, h⟩ := hS.core.lev.βY 0 (by have := D.R.two_le_m; omega)
      exact h.1
    · obtain ⟨c, h⟩ := (hG.spaces.vert i 0 hi (Nat.zero_le _)).frame
      exact h.1
  obtain ⟨m00, mV, hm, hν, hfd⟩ := GlobalTheory.ColMeas.measCol_of_choice ch G hG.meas hsp hfr hb.vol
  refine ⟨GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX, ⟨GlobalTheory.GridJoin.isSpaces_withMeas hG.spaces,
    GlobalTheory.GridJoin.isChars_withMeas hG.chars, GlobalTheory.GridJoin.isArrows_withMeas hG.arrows, hm,
    GlobalTheory.GridJoin.isData_withMeas hG.data⟩, ⟨fun i hi => (hsp.vert i 0 hi (Nat.zero_le _)).sp, hν, hfd,
    GlobalTheory.RowKer.kernel_row ch (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _
      (hS.core.lev.βY 0 (by have := D.R.two_le_m; omega))) hb.weil G hG ⟨hsp, harr⟩⟩⟩

end GlobalTheory.RowLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctionalStatement
section
open GlobalTheory.RowClaim GlobalTheory.RowReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_definitePeriods_invariant_functional : Big fun ch => InvLine ch := by
  first | exact @GlobalTheory.RowReal.invLine_big | exact GlobalTheory.RowReal.invLine_big | (intros; apply GlobalTheory.RowReal.invLine_big <;> assumption)
end


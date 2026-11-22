import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0510
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0131
import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCombinationSplitsSinglePlaceVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCombination_splits_singlePlace_vacuum : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ (i : Fin F.r) Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∃ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ ∧ comb c.ψ _ _ (w.eQ j) Ψ₁ = comb c.ψ _ _ ((F.Q i).eL j) f₁ := by
  first | exact @GlobalTheory.TwistPlaceSplit.main | exact GlobalTheory.TwistPlaceSplit.main | (intros; apply GlobalTheory.TwistPlaceSplit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiIntegralAbsLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.UnfoldBound

set_option maxHeartbeats 1000000 in

theorem unfolded_integral_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∃ (C : ℝ) (A : ℕ), ∀ g, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤ ENNReal.ofReal (C * height V g ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vb vU vW x₀ hx G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨vN⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.1 V V₀ ρ d
  obtain ⟨𝓐, h𝓐, hlay⟩ := GlobalTheory.T.flagUnipotent_fundamentalDomain_layers_integral D V V₀ ρ d vN vb vU
  obtain ⟨C, A, hC⟩ := GlobalTheory.Unf.orbit_sum_moderate_growth D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ G Φ hG hΦ
  refine ⟨C, A, fun g => ?_⟩
  exact ((GlobalTheory.Unf.base_term_norm_coords D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ G Φ hG hΦ 𝓐 𝓑 hlay g).trans
    (GlobalTheory.Unf.unfold_norm_base_term_translate D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ hx G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑
      g)).le.trans (hC g)

end GlobalTheory.Unf.UnfoldBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingOnlyBaseGramRationalPointsContributeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_only_baseGram_rational_points_contribute : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  first | exact @GlobalTheory.Unf.cut_gram_base | exact GlobalTheory.Unf.cut_gram_base | (intros; apply GlobalTheory.Unf.cut_gram_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D)), IsClosed (grpAt V (· ∈ Q) : Set (GA D V)) ∧ IsClosed (grpAt V (· ∉ Q) : Set (GA D V)) ∧ grpAt V (· ∈ Q) ≤ GfC V ∧ grpAt V (· ∉ Q) ≤ GfC V ∧ (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b = b * a) ∧ (∃ e : (grpAt V (· ∈ Q) × grpAt V (· ∉ Q)) ≃ₜ GfC V, ∀ p, (e p : GA D V) = p.1 * p.2) ∧ (∀ P P' : Pl D → Prop, (∀ p, P p → ¬ P' p) → grpAt V P ≤ grpOff V P') ∧ (∀ P : Pl D → Prop, GfC V ⊓ grpOff V P = grpAt V fun p => ¬ P p) ∧ (∀ (L : Lat V), IsSelfDualC V L → ∀ P : Pl D → Prop, (∃ K : Subgroup (GA D V), (∀ g, g ∈ K ↔ InK V L P g) ∧ IsCompact (K : Set (GA D V)) ∧ IsOpen ((K.subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P))) ∧ ∀ κ, InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  first | exact @GlobalTheory.FinPl.SetCut.grp_split | exact GlobalTheory.FinPl.SetCut.grp_split | (intros; apply GlobalTheory.FinPl.SetCut.grp_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnitLocLastRow

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_tmul (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (e : E) (y : v.adicCompletion F) :
    Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] y) = σ e ⊗ₜ[F] y := by
  simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]

theorem sigR_inclE (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) e) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (σ e) := by
  show Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] 1) = σ e ⊗ₜ[F] 1
  exact sigR_tmul σ v e 1

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F))
    (a : E ⊗[F] v.adicCompletion F) : Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.sigR σ (v.adicCompletion F) a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul e y => rw [sigR_tmul, sigR_tmul, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem sigR_mem_intV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] v.adicCompletion F}
    (ha : a ∈ Formalism.BasicNotions.intV E v) : Formalism.UG.sigR σ (v.adicCompletion F) a ∈ Formalism.BasicNotions.intV E v := by
  have h : Formalism.BasicNotions.intV E v ≤ (Formalism.BasicNotions.intV E v).comap (Formalism.UG.sigR σ (v.adicCompletion F)) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] 1) ∈ Formalism.BasicNotions.intV E v
      rw [sigR_tmul]
      apply Subring.subset_closure
      left
      exact ⟨⟨σ e, GlobalTheory.uLocDual_intOE_map (σ : E →+* E) he⟩, rfl⟩
    · show Formalism.UG.sigR σ (v.adicCompletion F) (1 ⊗ₜ[F] y) ∈ Formalism.BasicNotions.intV E v
      rw [sigR_tmul, map_one]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, rfl⟩
  exact h ha

theorem inclE_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 E) :
    Formalism.UG.inclE (F := F) (v.adicCompletion F) (r : E) ∈ Formalism.BasicNotions.intV E v :=
  Formalism.UG.P.easyc_inclE_mem (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _ ⟨r, rfl⟩

theorem one_int (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (a b : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b ∈ Formalism.BasicNotions.intV E v := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem mulVec_mem_dLat (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} [NeZero n] (p : 𝓞 E) (hp0 : (p : E) ≠ 0)
    (N : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (hN : ∀ i j, N i j ∈ Formalism.BasicNotions.intV E v)
    (hlast : ∀ j, ∃ c ∈ Formalism.BasicNotions.intV E v, N (Formalism.L2.Col.lastIdx n) j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) j =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c)
    (y : Fin n → E ⊗[F] v.adicCompletion F)
    (hy : y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (Formalism.L2.Col.rll_dLat n ((p : E)⁻¹))) :
    N *ᵥ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (Formalism.L2.Col.rll_dLat n ((p : E)⁻¹)) := by
  have key := Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v ((p : E)⁻¹) (inv_ne_zero hp0)
  obtain ⟨h1, h2⟩ := (key y).1 hy
  have hPinv : Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hp0, map_one]
  have hyint : ∀ j, y j ∈ Formalism.BasicNotions.intV E v := by
    intro j
    by_cases hj : j = Formalism.L2.Col.lastIdx n
    · rw [hj]
      have e : y (Formalism.L2.Col.lastIdx n) = Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) *
          (Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * y (Formalism.L2.Col.lastIdx n)) := by
        rw [← mul_assoc, mul_comm (Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E)), hPinv, one_mul]
      rw [e]
      exact mul_mem (inclE_int v p) h2
    · exact h1 j hj
  refine (key _).2 ⟨fun i _ => ?_, ?_⟩
  · show ∑ j, N i j * y j ∈ Formalism.BasicNotions.intV E v
    exact sum_mem fun j _ => mul_mem (hN i j) (hyint j)
  · choose c hc hcl using hlast
    have e : (N *ᵥ y) (Formalism.L2.Col.lastIdx n) = ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) (Formalism.L2.Col.lastIdx n) +
        Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * ∑ j, c j * y j := by
      show ∑ j, N _ j * y j = ∑ j, (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) _ j * y j + _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show N (Formalism.L2.Col.lastIdx n) j = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) j +
        Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c j by rw [← hcl j]; ring]
      ring
    rw [e, Matrix.one_mulVec, mul_add, ← mul_assoc, hPinv, one_mul]
    exact add_mem h2 (sum_mem fun j _ => mul_mem (hc j) (hyint j))

theorem mem_Uloc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E}, J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (p q : 𝓞 E), (q : E) = σ (p : E) → (p : E) * (q : E) = (T : E) → IsCoprime p q → T ≠ 0 → S.Lb = Formalism.L2.Col.rll_dLat n ((p : E)⁻¹) → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ Formalism.UG.UPts σ J (v.adicCompletion F) → (∀ r s, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) r s ∈ Formalism.BasicNotions.intV E v) → (∀ s, ∃ c ∈ Formalism.BasicNotions.intV E v, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s = Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c) → x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ hσ n _ J hJ T f bad S p q hq hpq hcop hT hL v hv x hU hint hlast
  subst hJ
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hp0 : (p : E) ≠ 0 := left_ne_zero_of_mul (hpq ▸ hTE)
  have hq0 : (q : E) ≠ 0 := right_ne_zero_of_mul (hpq ▸ hTE)
  have hPinv : Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hp0, map_one]
  have h0 : Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *
      (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) *
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) =
      (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) := hU
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h0
  have hMi : ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) =
      Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := by
    calc ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
        = (Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *
          (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) *
          ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := by
          rw [h0, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hMient : ∀ a b, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
      Formalism.UG.sigR σ (v.adicCompletion F) ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) b a) := by
    intro a b; rw [hMi]; rfl
  have hMiint : ∀ a b, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b ∈
      Formalism.BasicNotions.intV E v := by
    intro a b; rw [hMient]; exact sigR_mem_intV σ v (hint b a)
  choose c hc hcl using hlast
  have hmat : ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1 =
      -(((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) *
        ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) := by
    rw [Matrix.sub_mul, Units.mul_inv, Matrix.one_mul]; abel
  have hMilast : ∀ i, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
      (Formalism.L2.Col.lastIdx n) i - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) *
        (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k i) := by
    intro i
    have h1 := congrFun (congrFun hmat (Formalism.L2.Col.lastIdx n)) i
    rw [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply] at h1
    rw [h1, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.sub_apply, hcl k, mul_assoc]
  have hMilastI : ∀ i, ∃ e ∈ Formalism.BasicNotions.intV E v,
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
      (Formalism.L2.Col.lastIdx n) i - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * e :=
    fun i => ⟨_, neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k i)), hMilast i⟩
  have hs1 : ∀ a b, Formalism.UG.sigR σ (v.adicCompletion F) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b) =
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) b a := by
    intro a b
    by_cases hab : a = b
    · subst hab; rw [Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab), map_zero]
  have hcol : ∀ i, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i (Formalism.L2.Col.lastIdx n) -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i (Formalism.L2.Col.lastIdx n) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) * Formalism.UG.sigR σ (v.adicCompletion F)
        (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k i) := by
    intro i
    have h := congrArg (Formalism.UG.sigR σ (v.adicCompletion F)) (hMilast i)
    rw [map_sub, map_mul, hMient, sigR_sigR σ hσ v, sigR_inclE, ← hq, hs1] at h
    exact h

  have h1 : x ∈ Formalism.UG.levelVL σ (1 : Matrix (Fin n) (Fin n) E) v S.Lb := by
    rw [hL]
    refine Subgroup.mem_inf.2 ⟨hU, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · exact mulVec_mem_dLat v p hp0 _ hint (fun j => ⟨c j, hc j, hcl j⟩) y hy
    · have := mulVec_mem_dLat v p hp0 _ hMiint hMilastI _ hy
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

  have h2 : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v)
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) S.Lb := by
    intro y hy
    rw [hL, GlobalTheory.uLocDual_eq σ hσ n p q hp0 hq] at hy
    rw [hL]
    obtain ⟨hy1, hy2⟩ := (Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v (q : E) hq0 y).1 hy
    rw [show (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y =
      ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) *ᵥ y by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    refine (Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v ((p : E)⁻¹) (inv_ne_zero hp0) _).2 ⟨fun i _ => ?_, ?_⟩
    · show ∑ j, ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) i j * y j ∈ Formalism.BasicNotions.intV E v
      refine sum_mem fun j _ => ?_
      by_cases hj : j = Formalism.L2.Col.lastIdx n
      · rw [hj, Matrix.sub_apply, hcol i, mul_comm (Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E)), mul_assoc]
        exact mul_mem (sigR_mem_intV σ v (neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k i)))) hy2
      · exact mul_mem (sub_mem (hint i j) (one_int v i j)) (hy1 j hj)
    · show Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) *
        ∑ j, ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) (Formalism.L2.Col.lastIdx n) j * y j ∈ Formalism.BasicNotions.intV E v
      rw [Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      by_cases hj : j = Formalism.L2.Col.lastIdx n
      · rw [hj]
        obtain ⟨a, b, hab⟩ := hcop
        have hE : (a : E) * (p : E) + (b : E) * (q : E) = 1 := by
          exact_mod_cast congrArg (fun r : 𝓞 E => (r : E)) hab
        have hab' : Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) +
            Formalism.UG.inclE (F := F) (v.adicCompletion F) (b : E) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) = 1 := by
          have h := congrArg (Formalism.UG.inclE (F := F) (v.adicCompletion F)) hE
          rwa [map_add, map_mul, map_mul, map_one] at h
        have hDc := hcl (Formalism.L2.Col.lastIdx n)
        have hDd := hcol (Formalism.L2.Col.lastIdx n)
        rw [← Matrix.sub_apply] at hDc hDd
        have e : Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) *
            (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) (Formalism.L2.Col.lastIdx n) (Formalism.L2.Col.lastIdx n) *
              y (Formalism.L2.Col.lastIdx n)) =
            (Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * Formalism.UG.sigR σ (v.adicCompletion F)
              (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k
                (Formalism.L2.Col.lastIdx n)) +
             Formalism.UG.inclE (F := F) (v.adicCompletion F) (b : E) * c (Formalism.L2.Col.lastIdx n)) *
            (Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) * y (Formalism.L2.Col.lastIdx n)) := by
          linear_combination (Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * y (Formalism.L2.Col.lastIdx n) -
              Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * y (Formalism.L2.Col.lastIdx n)) * hDc +
            (c (Formalism.L2.Col.lastIdx n) * y (Formalism.L2.Col.lastIdx n)) * hPinv +
            (Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * y (Formalism.L2.Col.lastIdx n)) * hDd -
            (c (Formalism.L2.Col.lastIdx n) * y (Formalism.L2.Col.lastIdx n)) * hab'
        rw [e]
        exact mul_mem (add_mem (mul_mem (inclE_int v a)
          (sigR_mem_intV σ v (neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k _)))))
          (mul_mem (inclE_int v b) (hc _))) hy2
      · rw [Matrix.sub_apply, hcl j, ← mul_assoc, ← mul_assoc, hPinv, one_mul]
        exact mul_mem (hc j) (hy1 j hj)
  exact GlobalTheory.uloc_of_triv_disc σ S v hv x h1 h2

end GlobalTheory.UnitLocLastRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacFixP

theorem idAt_eq_bot {D : D7} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) : idAt D P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  refine GlobalTheory.FinPlLoc.eq_zero_of_comp x hx.1 fun w => ?_
  exact (Submodule.mem_iInf _).1 hx.2 ⟨w, hP w⟩

theorem eq_one_of_grpAt {D : D7} {S : HSp D} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {κ : GA D S}
    (h : κ ∈ grpAt S P) : κ = 1 := by
  unfold grpAt congGrp at h
  rw [idAt_eq_bot hP, MonoidHom.mem_ker, MonoidHom.comp_apply] at h
  have h2 : matHom S κ = 1 := by
    apply Units.ext
    ext i j
    have := congrArg (fun g : GL (Fin S.rank) (AE D ⧸ (⊥ : Ideal (AE D))) => g.val i j) h
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [Units.val_one]
    rw [Matrix.one_apply] at this ⊢
    have h1 : ((if i = j then 1 else 0 : AE D ⧸ (⊥ : Ideal (AE D)))) = Ideal.Quotient.mk ⊥ (if i = j then 1 else 0) := by
      split_ifs <;> simp
    rw [h1, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at this
    exact this
  unfold matHom at h2
  exact Subgroup.subtype_injective _ (h2.trans (map_one _).symm)

theorem vac_fix_on : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), (∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ CharUnramAt D χS v ∧ CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT P hP f hf κ κ' hκ hκ'
  by_cases hex : ∃ v, P v
  · obtain ⟨v, hv⟩ := hex
    obtain ⟨hS, hT, -⟩ := hP v hv
    exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ S T χS χT om hW LS LT hS hT P (fun w hw => (hP w hw).2.2) f hf κ κ' hκ hκ'
  · push_neg at hex
    rw [eq_one_of_grpAt hex hκ.1, eq_one_of_grpAt hex hκ'.1, Prod.mk_one_one, map_one]
    rfl

end GlobalTheory.VacFixP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorLastDefiniteLocalBiModelSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastOmb

theorem isComp_inv {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := by
  intro t a ha
  have := Q.comp₂ t a ha
  rw [MonoidHom.inv_apply] at this
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this, Circle.coe_inv, inv_inv]

theorem isLoc_one {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsLoc Q.F.F₁ (1 : GA D S.J.W₀) (1 : GL Q.n₁ Q.k) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp [GlobalTheory.MixModel.mt_one]
  · rw [GlobalTheory.MixModel.mt_one, Units.val_one, Matrix.mul_one, Q.F.F₁.βγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem actO_one_of_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {g : GL Q.n₂ Q.k}
    {a₀ : GA D S.B'.A} (hloc : (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g) (y : WO S.J.W₀ S.B'.A)
    (hy' : IsHalf (1 - (Q.q.e + cA D Q.q.e)) y) : actO S.J.W₀ S.B'.A 1 a₀ y = y := by
  have hsupp := GlobalTheory.LocGrp.suppAt_iff.1 hloc.1
  have he := Q.q.split
  set f : AE D := Q.q.e + cA D Q.q.e with hf
  have hce : cA D Q.q.e * cA D Q.q.e = cA D Q.q.e := by rw [← map_mul, he.1]
  have hff : f * (1 - f) = 0 := by
    rw [hf]; linear_combination (-1 : AE D) * he.1 - hce - 2 * he.2.1
  have hfy : f • y = 0 := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← hy' i j, ← mul_assoc, hff, zero_mul]
  have hz : HMul.hMul (Formalism.L2.Theta.mt S.B'.A a₀ - 1) (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := by
    rw [← hsupp, Matrix.smul_mul, ← Matrix.mul_smul]
    have h0 : ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) • (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := hfy
    rw [h0, Matrix.mul_zero]
  simp only [actO, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hz
  exact hz

theorem biComb_eq_sum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ : WO A S →₀ ℂ) (c₂ : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) :
    biComb ψ A S A' c₁ c₂ C u =
      ∑ x ∈ c₁.support, (c₁ x * ψ (symplOH A S u x)) • GlobalTheory.SeeSaw.comb ψ S A' c₂ (C (u + x)) := by
  funext v
  simp only [biComb, GlobalTheory.SeeSaw.comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem weil_last_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₂ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (a₀ : GA D S.B'.A), (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → ∀ u, S.omb (1, a₀) (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u) = biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂')) u := by
  intro D ψ σ S Q c₁ c₂ hAway Λ hbi g a₀ hloc Ξ₁ Ξ₂ Ξ₂' hΞ u
  have hcomm : ∀ G, IsThetaFunO ψ S.J.W₀ S.B'.A G →
      S.omb (1, a₀) (GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ G) = GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ (S.omb (1, a₀) G) := by
    intro G hG
    simp only [GlobalTheory.SeeSaw.comb, map_sum, map_smul]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [S.weilb.om_heis 1 a₀ y G hG, actO_one_of_away Q hloc y (hAway y hy)]
  rw [biComb_eq_sum, biComb_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul]
  obtain ⟨T₂, hT₂, hΛ⟩ := hbi.2 Ξ₁ (u + x)
  have e1 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) (u + x) = T₂ Ξ₂ :=
    funext fun v => hΛ Ξ₂ _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e2 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (u + x) = T₂ Ξ₂' :=
    funext fun v => hΛ Ξ₂' _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e3 : S.omb (1, a₀) (T₂ Ξ₂) = T₂ Ξ₂' := by
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W₀ S.B'.A S.χ₂ S.χ₂ S.omb S.weilb Q.μ₂⁻¹ Q.μ₂⁻¹ (isComp_inv Q)
      (isComp_inv Q) Q.n₂ Q.n₁ Q.F.F₁ Q.F.F₂ T₂ hT₂ 1 1 a₀ g (isLoc_one Q) hloc Ξ₂ Ξ₂' ?_
    rw [hΞ, inv_inv]
    simp
  rw [e1, e2, hcomm _ (hT₂.theta _), e3]

end GlobalTheory.LastOmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilShapeOfFrameMovesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_shape_of_frame_moves : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (ρ : ℕ) (h0 : 0 + 2 * ρ + 2 = D.R.m) (L : Lat (d.st 0).V), Formalism.L2.DIV.IsFrame (d.st 0).β (d.st 0).Λ → Moves (d.st 0).V (d.t 0) (d.st 0).Λ L (· = G.q.v) → WShape G.q (d.bes 0 ρ h0).d (d.bes 0 ρ h0).o (d.bes 0 ρ h0).ζ L (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹) (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (2 * ρ - i.1 + 1))⁻¹) ((((G.S.ϖ : G.kˣ) : G.k) ^ (ρ + 1))⁻¹) 1 (d.x 0).L := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.wShape_chain | exact GlobalTheory.Core.Mi.LatMatch.wShape_chain | (intros; apply GlobalTheory.Core.Mi.LatMatch.wShape_chain <;> assumption)
end


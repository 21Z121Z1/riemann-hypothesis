import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.JcRadialModuleFormOfParts
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0462
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0463
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0460
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0464
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiscreteSeriesDegreeBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0007
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0459
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0206
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKF0IffGapIn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Formalism.LocalToGlobal.Bundle0002
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0441
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTwoSidedHaarOfLeftInvariantProbabilityCompact
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
open scoped ENNReal

namespace GlobalTheory.ThA

private lemma measurable_lmulM_flag_measures {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (lmulM (k := k) (r := r) a) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.measurable_sum _ fun l _ => measurable_const.mul ((measurable_pi_apply j).comp (measurable_pi_apply l))

private lemma measurable_rmulF' {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Measurable (B.rmulF a) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [B.rmulF, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

private lemma measurableSet_lmulM_pair_mem {k r : ℕ} {A : Set (Mt k r)} (hA : MeasurableSet A) :
    MeasurableSet {p : Mt k r × Mt k r | lmulM (Matrix.of p.2) p.1 ∈ A} := by
  have hm : Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact hm hA

theorem measure_eq_smul_of_left_right {k r : ℕ} {U : Set (B.Mat k r)} {μ ν : Measure (Mt k r)}
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, (Matrix.of x : B.Mat k r) ∈ U) (hν : ∀ᵐ x ∂ν, (Matrix.of x : B.Mat k r) ∈ U)
    (hl : ∀ a ∈ U, Measure.map (lmulM a) μ = μ) (hr : ∀ a ∈ U, Measure.map (B.rmulF a) ν = ν) :
    ν = ν Set.univ • μ := by
  ext A hA
  set S : Set (Mt k r × Mt k r) := {p | lmulM (Matrix.of p.2) p.1 ∈ A} with hSdef
  have hS : MeasurableSet S := measurableSet_lmulM_pair_mem hA

  have hx : (μ.prod ν) S = ν A := by
    rw [Measure.prod_apply hS]
    have hslice : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' S) = ν A := by
      filter_upwards [hμ] with x hx
      have hpre : Prod.mk x ⁻¹' S = B.rmulF (Matrix.of x) ⁻¹' A := rfl
      rw [hpre, ← Measure.map_apply (measurable_rmulF' _) hA, hr _ hx]
    rw [lintegral_congr_ae hslice, lintegral_const, measure_univ, mul_one]

  have hy : (μ.prod ν) S = μ A * ν Set.univ := by
    rw [Measure.prod_apply_symm hS]
    have hslice : ∀ᵐ y ∂ν, μ ((fun x => (x, y)) ⁻¹' S) = μ A := by
      filter_upwards [hν] with y hy
      have hpre : (fun x => (x, y)) ⁻¹' S = lmulM (Matrix.of y) ⁻¹' A := rfl
      rw [hpre, ← Measure.map_apply (measurable_lmulM_flag_measures _) hA, hl _ hy]
    rw [lintegral_congr_ae hslice, lintegral_const]
  rw [Measure.smul_apply, smul_eq_mul, ← hx, hy, mul_comm]

theorem haarW_twoSided_of_left : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → μ Set.univ = 1 → B.IsHaarOn (UWset k r z) μ := by
  intro k r z μ _ _ hH h1
  obtain ⟨_, hne, hconc, hleft⟩ := hH
  haveI : IsProbabilityMeasure μ := ⟨h1⟩
  have hinvU : ∀ g ∈ UWset k r z, g⁻¹ ∈ UWset k r z ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 :=
    fun g hg => Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hg
  have hUm : MeasurableSet {x : Mt k r | (Matrix.of x : B.Mat k r) ∈ UWset k r z} :=
    (show IsClosed {x : Mt k r | (Matrix.of x : B.Mat k r) ∈ UWset k r z} from
      Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r z).measurableSet
  have hμU : ∀ᵐ x ∂μ, (Matrix.of x : B.Mat k r) ∈ UWset k r z := ae_iff.mpr hconc

  have hinvm : Measurable (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) := Formalism.FourierDecayAlt.P.HermitianFormFactor.invF_meas
  obtain ⟨ν, hνdef⟩ : ∃ ν : Measure (Mt k r), ν = μ.map (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) := ⟨_, rfl⟩
  have hmass : ν Set.univ = 1 := by
    rw [hνdef, Measure.map_apply hinvm MeasurableSet.univ, Set.preimage_univ, h1]
  haveI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hνU : ∀ᵐ x ∂ν, (Matrix.of x : B.Mat k r) ∈ UWset k r z := by
    rw [hνdef]
    refine (ae_map_iff hinvm.aemeasurable hUm).2 ?_
    filter_upwards [hμU] with x hx using (hinvU _ hx).1

  have hνr : ∀ a ∈ UWset k r z, Measure.map (B.rmulF a) ν = ν := by
    intro a ha
    obtain ⟨hai, haa, -⟩ := hinvU a ha
    rw [hνdef, Measure.map_map (measurable_rmulF' a) hinvm]
    have hcomp : (B.rmulF a ∘ (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1)))) = (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) ∘ lmulM a⁻¹ := by
      funext x
      show ((Matrix.of x)⁻¹ * a : B.Mat k r) = (a⁻¹ * Matrix.of x)⁻¹
      rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv haa]
    rw [hcomp]
    exact (Measure.map_map hinvm (measurable_lmulM_flag_measures a⁻¹)).symm.trans (congrArg (Measure.map _) (hleft _ hai))
  have hkey := measure_eq_smul_of_left_right (μ := μ) (ν := ν) hμU hνU hleft hνr
  rw [hmass, one_smul] at hkey
  refine ⟨hconc, hleft, fun a ha => ?_, fun K _ => measure_lt_top μ K, hne⟩
  have h := hνr a ha
  rwa [hkey] at h

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataGlobalTermIndependentOfRepresentative
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.RepIndep

open GlobalTheory.LoopC.PairMove GlobalTheory.LoopC.FrEqv

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem xsp_map_of_frame {F₁ F₂ : LFlag S r T'} (f : S.V ≃ₗ[E] S.V) (h : ∀ a, frame F₂ a = f (frame F₁ a)) :
    (Xsp F₁).map (f : S.V →ₗ[E] S.V) = Xsp F₂ := by
  change (Submodule.span E (Set.range F₁.fl.e)).map _ = Submodule.span E (Set.range F₂.fl.e)
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  have : (f : S.V →ₗ[E] S.V) ∘ F₁.fl.e = F₂.fl.e := by
    funext b
    have := h b.castSucc
    rw [Formalism.L2.SG.Pf.frame_castSucc_td, Formalism.L2.SG.Pf.frame_castSucc_td] at this
    simp [this]
  rw [this]

theorem iota_of_dc {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} (g : ℕ)
    (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hfr : ∀ a, frame F₂ a = (n * m) (frame F₁ a)) :
    IotaCompat Λ F F₁ F₂ (n * m) g := by
  have hmX : (Xsp F₁).map (m : S.V →ₗ[E] S.V) = Xsp F₁ := nlam_map hm
  have hnmX := xsp_map_of_frame (n * m) hfr
  have hnX : (Xsp F₁).map (n : S.V →ₗ[E] S.V) = Xsp F₂ := by
    refine map_of_mem_iff fun x => ?_
    have e : n x = (n * m) (m.symm x) := by simp [LinearEquiv.mul_apply]
    rw [e, mem_iff_of_map hnmX, mem_iff_of_map (map_symm hmX)]
  have hi : n⁻¹ ∈ NLam Λ F := Formalism.L2.SG.Pf.nlamPf_inv hn
  intro x' hx' l hl
  have e : l - (n * m) x' = n (n⁻¹ l - m x') := by
    rw [map_sub]
    simp [LinearEquiv.mul_apply]
  rw [e, ngx_iff hn.1 (nlam_map hn) hnX g]
  have e2 : n⁻¹ l - m x' = (l - x') + ((n⁻¹ l - l) - (m x' - x')) := by abel
  rw [e2]
  refine (Submodule.add_mem_iff_left _ ?_).symm
  refine Submodule.sub_mem _ ?_ ?_
  · refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨?_, hi.2.2 l hl.2⟩)
    exact Λ.sub_mem ((aut_mem_iff hi.1 l).2 hl.1) hl.1
  · refine Submodule.mem_sup_right ⟨?_, hm.2.2 x' hx'.2⟩
    exact Λ.sub_mem ((aut_mem_iff hm.1 x').2 hx'.1) hx'.1

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rep_indep : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → Gval (lf D F0) F₁ ≠ 0 → DCRel Λ (lf D F0) F₁ F₂ → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d, Over P d (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) ↔ Over P d (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) := by
  intro D Z u u' F0 Λ hΛ F₁ F₂ h1 h2 hG hdc p P hP d
  have key : ∀ A B : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' A → PD D Λ (lf D F0) u' B →
      Gval (lf D F0) A ≠ 0 → DCRel Λ (lf D F0) A B →
      Over P d (locU Z p Λ (lf D F0) A (Tu D u) (Tu D u')) → Over P d (locU Z p Λ (lf D F0) B (Tu D u) (Tu D u')) := by
    intro A B hA hB hGA hAB
    obtain ⟨n, hn, m, hm, hfr, -⟩ := hAB
    exact GlobalTheory.T.global_terms_same_doubleCoset_same_local_data D Z u u' F0 Λ hΛ A B hA hB hGA n ⟨hn.1.1, hn.2.1, hn.2.2⟩ m ⟨hm.1.1, hm.2.1, hm.2.2⟩
      (Formalism.L2.SG.Pf.isAutLam_mul hn.1 hm.1).2 (fun a => hfr a) (iota_of_dc (gS D) hn hm (fun a => hfr a)) p P hP d
  refine ⟨key F₁ F₂ h1 h2 hG hdc, key F₂ F₁ h2 h1 ?_ (Formalism.L2.SG.Pf.dcrel_symm _ _ hdc)⟩
  rw [Formalism.L2.SG.Pf.gval_rel (h := hdc)]
  exact hG

end GlobalTheory.LocOver.RepIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermDefectNeIffMoveLinearEquivStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTermDefect_ne_iff_move_linearEquiv : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r), LocNG.BBne (H := H) (move g t) ↔ LocNG.BBne (H := H) t := by
  first | exact @GlobalTheory.LocOver.bbne_move | exact GlobalTheory.LocOver.bbne_move | (intros; apply GlobalTheory.LocOver.bbne_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermMoveUnitaryIsTermStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTerm_move_unitary_isTerm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (t : Formalism.MainNotions.S.Loc.Term V M r), H.IsTerm t → H.IsTerm (move g t) := by
  first | exact @GlobalTheory.LocOver.isTerm_move_unitary | exact GlobalTheory.LocOver.isTerm_move_unitary | (intros; apply GlobalTheory.LocOver.isTerm_move_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsLocalTermAtPlaceStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTerm_lattice_isLocalTerm_at_place : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (p : PlF D) (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → ∀ (N N' : G.GLV), (∀ b, N (G.f b) = ∑ a, U a b • G.f a) → (∀ b, N' (G.f' b) = ∑ a, (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) a b • G.f' a) → ∀ (m m' : (G.S p).GLV), (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m → (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N' m' → ∃ (t : Loc.Term (Vp D p) (Y.M p) D.R.rS) (d : LocNG.Datum (FP p)), LocNG.IsTermOver (FP p) d t ∧ (c.c p).lat t.abelian₂ = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam) ∧ (∀ b, (c.c p).e (t.f b) = m ((G.S p).f b)) ∧ ∀ b, (c.c p).e (t.f' b) = m' ((G.S p).f' b) := by
  first | exact @GlobalTheory.HL.MovedTermLoc.main | exact GlobalTheory.HL.MovedTermLoc.main | (intros; apply GlobalTheory.HL.MovedTermLoc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductioStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzeroFlagProbabilityBound_of_volumeRatioInduction : VolumeStep → NonzeroFlagBound := by
  first | exact @GlobalTheory.NonzeroFlag.nonzeroFlagBound | exact GlobalTheory.NonzeroFlag.nonzeroFlagBound | (intros; apply GlobalTheory.NonzeroFlag.nonzeroFlagBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizesStatement
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedFormalDegree_eq_vandermonde_of_sizes : ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
  first | exact @GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes | exact GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes | (intros; apply GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtDlAlongFamilyGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.FamDlGap

theorem ptDl_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  have hA : GlobalTheory.GapIn.AmpKF0 := GlobalTheory.NoPr.Model.ampKF0_iff_gapIn.mp GlobalTheory.NoPr.Model.ampKF0_holds
  have hCC : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
  obtain ⟨C, hC⟩ := GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps hH hA hCC Cg cb Cu cT CT C0 C1
  refine ⟨C, 1000, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max m₀ 1)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, hm1, -, -, hrd, -⟩ := hx0 x hx i
  have hmm : m₀ ≤ ((Fm.D x i).R.m : ℝ) := (le_max_left _ _).trans hm1
  have hm1' : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := (le_max_right _ _).trans hm1
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hmm⟩
  intro hH0
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hH0

end GlobalTheory.FamDlGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesOfSiegelWeil
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem bothRowsFromSiegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (𝒞 : FamClass), Formalism.L2.TSel 𝒞 →
      (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
        Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 :=
  fun hSW => GlobalTheory.T.ranks_frames_closed (GlobalTheory.T.unitary_hyperplane_volumeRatio_siegelWeil hSW)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermMovesToBaseFramesUpToUnitriangular
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MoveTerm

theorem term_moves_to_base : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ t₀ : TauC Y u u', t₀.toTerm.atPt w → ∃ (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' := by
  intro D X Y u u' _hS w F00 F'0 FP hZ _hG _hB t₀ ht
  obtain ⟨F', ⟨hP, hmk⟩, hGv, hCell⟩ := ht
  have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
  obtain ⟨hGF, hCF, -⟩ := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t₀.lam hrow
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t₀.lam hrow _ _).1 hmk
  have hGt : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := by
    intro h
    apply hGv
    rw [hGF _ _ hrel]
    exact h
  have hCt := (hCF _ _ hrel w).1 hCell
  have hTu : ∀ v : D.what₂.Word, ((Tu D v : ℕ) : D.host.E) ≠ 0 := fun v =>
    Nat.cast_ne_zero.mpr (Formalism.L2.SG.GramJoint.Tu_pos D v).ne'
  obtain ⟨-, γ, hγ, ⟨A, hA, hAc⟩, ⟨A', hA', hAc'⟩⟩ :=
    GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular D (lf D (X.Fu u)) F00 t₀.frame F'0 w (hTu u) (hTu u') hGt hCt hZ
  refine ⟨γ, A, A', hγ, ?_, ?_, fun b => hAc b, fun b => hAc' b⟩
  · exact fun i j => ⟨fun h => hA.1 i j h, fun h => h ▸ hA.2 i⟩
  · exact fun i j => ⟨fun h => hA'.1 i j h, fun h => h ▸ hA'.2 i⟩

end GlobalTheory.HL.MoveTerm
end
end


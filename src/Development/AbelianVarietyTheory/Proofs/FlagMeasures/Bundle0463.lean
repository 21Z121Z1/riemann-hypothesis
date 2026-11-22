import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0460
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0458
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0448
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0459
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0015
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
import Formalism.LocalToGlobal.Bundle0002
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0461
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantIsometryUnitriangularMoves
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL

theorem leadMinor_triMul {E : Type} [Field E] {m : ℕ} (A B Z : Matrix (Fin m) (Fin m) E)
    (hA : ∀ i j, i < j → A i j = 0) (hA1 : ∀ i, A i i = 1)
    (hB : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) (l : ℕ) :
    leadMinorE (A * Z * B) l = leadMinorE Z l := by
  unfold leadMinorE
  by_cases hl : l ≤ m
  · rw [dif_pos hl, dif_pos hl]
    have red : ∀ g : Fin m → E, (∀ i : Fin m, l ≤ (i : ℕ) → g i = 0) →
        ∑ i, g i = ∑ i : Fin l, g (Fin.castLE hl i) := by
      intro g hg
      refine (Finset.sum_of_injOn (Fin.castLE hl) (Fin.castLE_injective hl).injOn
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun i _ hi => hg i ?_) (fun _ _ => rfl)).symm
      by_contra h
      exact hi ⟨⟨i, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
    have key : (A * Z * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        A.submatrix (Fin.castLE hl) (Fin.castLE hl) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
          B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [red]
      · refine Finset.sum_congr rfl fun d _ => ?_
        rw [red]
        intro i hi
        rw [hA _ _ (by simp [Fin.lt_def]; omega), zero_mul]
      · intro i hi
        rw [hB _ _ (by simp [Fin.lt_def]; omega), mul_zero]
    have hdA : (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · simp [hA1]
      · intro i j hij
        have h2 : i < j := OrderDual.toDual_lt_toDual.1 hij
        exact hA _ _ (Fin.lt_def.2 (Fin.lt_def.1 h2))
    have hdB : (B.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · simp [hB1]
      · intro i j hij
        have h2 : j < i := hij
        exact hB _ _ (Fin.lt_def.2 (Fin.lt_def.1 h2))
    rw [key, Matrix.det_mul, Matrix.det_mul, hdA, hdB, one_mul, mul_one]
  · rw [dif_neg hl, dif_neg hl]

variable {D : D7}

theorem zhat_movesTo {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T')
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (h : MovesTo F0 F0' F F' ρ U U') :
    Zhat F.fl F'.fl = U.conjTranspose * Zhat F0.fl F0'.fl * U' := by
  obtain ⟨hρ, -, -, hU, hU'⟩ := h
  have hρ' : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ
  refine Matrix.ext fun a b => ?_
  have e1 : Zhat F.fl F'.fl a b = (VS D).hT (ρ (frame F a)) (ρ (frame F' b)) := by
    rw [hρ']; rfl
  rw [e1, hU a, hU' b]
  simp only [Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, LinearMap.sum_apply,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  simp only [RingHom.id_apply, frame, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem gval_movesTo : ∀ {D : D7} {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), MovesTo F0 F0' F F' ρ U U' → Gval F F' = Gval F0 F0' := by
  intro D T T' F0 F0' F F' ρ U U' h
  have hZ := zhat_movesTo F0 F0' F F' ρ U U' h
  obtain ⟨-, hu, hu', -, -⟩ := h
  have hl : ∀ l, Dl F.fl F'.fl l = Dl F0.fl F0'.fl l := by
    intro l
    show leadMinorE (Zhat F.fl F'.fl) l = leadMinorE (Zhat F0.fl F0'.fl) l
    rw [hZ]
    refine leadMinor_triMul _ _ _ (fun i j hij => ?_) (fun i => ?_) (fun i j hij => (hu' i j).1 hij)
      (fun i => (hu' i i).2 rfl) l
    · simp [Matrix.conjTranspose_apply, (hu j i).1 hij]
    · simp [Matrix.conjTranspose_apply, (hu i i).2 rfl]
  show Gflag F.fl F'.fl = Gflag F0.fl F0'.fl
  unfold Gflag
  rw [hl, hl]

end GlobalTheory.HL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatIffLocalGraphs
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IotaGraph

open Formalism.L2.SG.Pf Formalism.L2.SG.Saturated

set_option maxHeartbeats 2000000 in

theorem graph_eq_iff_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p : PlF D, ((G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2 ↔ ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm p
  obtain ⟨hn, hm, ht⟩ := hnm
  obtain ⟨gρ, hgρ, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hMv.1
  obtain ⟨gn, hgn, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p n hn.1
  have hgρn : Ext p (ρ * n) (gρ * gn) := by
    intro x
    show gρ (gn (baseChange₂ D p x)) = baseChange₂ D p (ρ (n x))
    rw [hgn x, hgρ (n x)]
  have hmv := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv).2.2.2.2.2
  obtain ⟨A, A', -, -, -, -, hMv1⟩ := hmv t n m ⟨hn, hm, ht⟩
  have h1 := GlobalTheory.T.localThetaGraph_rationalIsometry_moved_lattice D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c p (ρ * n) (gρ * gn) t.frame
    (U * A) (U' * A') hMv1 hgρn t₀.lam
  have h0 := GlobalTheory.T.localThetaGraph_rationalIsometry_moved_lattice D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c p ρ gρ t₀.frame U U' hMv hgρ t₀.lam
  have hs : ∀ x, (gρ * gn).symm x = gn.symm (gρ.symm x) := fun x => rfl
  have hlat : G.datOf (c.lat (ρ * n) t.lam) p = G.datOf (c.lat (ρ * n) t₀.lam) p :=
    congrArg (fun Λ => G.datOf (c.lat (ρ * n) Λ) p) hl
  refine Iff.trans ?_ (GlobalTheory.T.pulledLocalGraphs_eq_iff_identificationsCompatible D X Y u u' t₀ t n m hl hl' ⟨hn, hm, ht⟩ p gn hgn)
  constructor
  · intro h a b
    rw [hlat] at h
    have hq := (h1 ((c.c p).e (gρ a), (c.c p).e (gρ b))).symm.trans
      ((iff_of_eq (congrArg (fun S => ((c.c p).e (gρ a), (c.c p).e (gρ b)) ∈ S) h)).trans
        (h0 ((c.c p).e (gρ a), (c.c p).e (gρ b))))
    have e1 : ∀ x, (gρ * gn).symm ((c.c p).e.symm ((c.c p).e (gρ x))) = gn.symm x := fun x => by
      rw [hs, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    have e2 : ∀ x, gρ.symm ((c.c p).e.symm ((c.c p).e (gρ x))) = x := fun x => by
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    dsimp only at hq
    simp only [e1, e2] at hq
    exact hq
  · intro h
    rw [hlat]
    apply Set.ext
    intro q
    have hq := h (gρ.symm ((c.c p).e.symm q.1)) (gρ.symm ((c.c p).e.symm q.2))
    refine (h1 q).trans (Iff.trans ?_ (h0 q).symm)
    rw [hs, hs]
    exact hq

set_option maxHeartbeats 2000000 in

theorem iotaCompat_iff_graph : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → (IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) ↔ ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hloc := graph_eq_iff_local D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hγ0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hβ : t.lin * t₀.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hγ1 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hγ0)
  have hg0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have hg1 : Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' = t₀.lam := by
    have h : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    rw [hl, hl'] at h
    exact h
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (t.lin * t₀.lin⁻¹) t₀.lam = t₀.lam := by
    rw [gmap_mul_sat, ← hg0, gmap_inv_gmap, hg1, hg0]
  constructor
  · intro hI p
    rw [hloc p]
    intro gβ hgβ x' hx' x hx hx'p hxp
    by_cases hs : (Y.M p).split = none
    · obtain ⟨g0, -, -, huniq, himg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p _ hβ
      have hg : gβ = g0 := huniq gβ hgβ
      have hgx : gβ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam := by
        have h := himg t₀.lam
        rw [hβΛ] at h
        rw [← h, hg]
        exact ⟨x', hx', rfl⟩
      have hth : LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p) = 1 := by
        show LocNG.theta (Y.M p) = 1
        unfold LocNG.theta; rw [hs]
      have key : ∀ (f f' : Fin (D.R.rS + 1) → Vp D p) (v : Vp D p), v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam →
          Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) f f' v := by
        intro f f' v hv
        refine ⟨v, ?_, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, Submodule.zero_mem _,
          Submodule.zero_mem _, by simp⟩
        rw [hth]
        exact Submodule.subset_span ⟨v, hv, by simp⟩
      exact ⟨fun _ => key _ _ _ (Submodule.sub_mem _ hx hgx), fun _ => key _ _ _ (Submodule.sub_mem _ hx hx')⟩
    · have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
      have hPD0 := t₀.rep.2.2.2.2
      have hPD1 : Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' t.frame := by
        have h : Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u' t.frame := t.rep.2.2.2.2
        rw [hl] at h
        exact h
      have hfr : ∀ a, frame t.frame a = (t.lin * t₀.lin⁻¹) (frame t₀.frame a) := by
        intro a
        show frame (mapLF t.lin (lf D (X.Fu u'))) a = (t.lin * t₀.lin⁻¹) (frame (mapLF t₀.lin (lf D (X.Fu u'))) a)
        rw [Formalism.L2.SG.Pf.Act.frame_mapLF hγ1, Formalism.L2.SG.Pf.Act.frame_mapLF hγ0]
        show t.lin _ = t.lin (t₀.lin.symm (t₀.lin _))
        rw [LinearEquiv.symm_apply_apply]
      exact GlobalTheory.T.identificationCompat_passes_to_local_congruence D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hrow t₀.frame t.frame hPD0 hPD1 _ hβ hβΛ hfr hI p gβ hgβ hs
        x' hx' x hx hx'p hxp
  · intro h
    exact GlobalTheory.T.rationalCompatibility_of_local_identifications D X Y u u' t₀ t hl hl' (fun p _ => (hloc p).1 (h p))

end GlobalTheory.IotaGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFramesMovedTermUnitriangularChange
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocOver

theorem isUpperUnitriangularFinMatrix_mul_of_both {K : Type} [CommRing K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA.1 a c h, zero_mul]
      · rw [hB.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem triMove_main : ∀ {D : D7} (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (f' : Fin (D.R.rS + 1) → Vp D p), MovesTo F0 F0' F F' ρ U U' → Ext p ρ g → Tri (D.s.atP p).Ep (scaled Z p (frame F')) f' → Tri (D.s.atP p).Ep (scaled Z p (frame F0)) (fun a => g (scaled Z p (frame F) a)) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F0')) (fun b => g (f' b)) := by
  intro D Z p T T' F0 F0' F F' ρ U U' g f' hM hE hf'
  obtain ⟨_, hU, hU', hρ, hρ'⟩ := hM
  have hs : ∀ (h : Fin (D.R.rS + 1) → (VS D).V) a, g (scaled Z p h a) = scaled Z p (fun b => ρ (h b)) a := by
    intro h a
    simp only [scaled, map_smul]
    rw [hE]
  have uniOf : ∀ W : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni W → Uni W :=
    fun W hW => ⟨fun a b hab => (hW a b).1 hab, fun a => (hW a a).2 rfl⟩
  obtain ⟨A1, hA1, -⟩ := tri_scaled D Z (frame F0) (fun b => ρ (frame F b)) U (uniOf U hU) (fun b => hρ b)
  obtain ⟨A2, hA2, -⟩ := tri_scaled D Z (frame F0') (fun b => ρ (frame F' b)) U' (uniOf U' hU') (fun b => hρ' b)
  refine ⟨⟨A1 p, (hA1 p).1, fun b => ?_⟩, ?_⟩
  · show g (scaled Z p (frame F) b) = _
    rw [hs]; exact (hA1 p).2 b
  · obtain ⟨A, hA, hc⟩ := hf'
    refine ⟨A2 p * A, isUpperUnitriangularFinMatrix_mul_of_both _ _ (hA2 p).1 hA, fun b => ?_⟩
    show g (f' b) = _
    rw [hc b, map_sum]
    have h2 : ∀ a, g (A a b • scaled Z p (frame F') a) =
        ∑ d, (A a b * A2 p d a) • scaled Z p (frame F0') d := by
      intro a
      rw [map_smul, hs, (hA2 p).2 a, Finset.smul_sum]
      exact Finset.sum_congr rfl fun d _ => smul_smul _ _ _
    rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]

end GlobalTheory.LocOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermDefectNeIffMoveLinearEquiv
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.MoveBB

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem mem_span_range_comp {R W ι : Type} [Semiring R] [AddCommGroup W] [Module R W] (e : W ≃ₗ[R] W)
    (m : ι → W) (w : W) :
    e w ∈ Submodule.span R (Set.range (fun i => e (m i))) ↔ w ∈ Submodule.span R (Set.range m) := by
  have hr : Set.range (fun i => e (m i)) = (e : W →ₗ[R] W) '' Set.range m := by
    rw [← Set.range_comp]; rfl
  rw [hr, Submodule.span_image]
  constructor
  · rintro ⟨y, hy, hyw⟩
    have : y = w := e.injective hyw
    exact this ▸ hy
  · intro h
    exact ⟨w, h, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem MMfam_move (H : HermSp M V) (g : V ≃ₗ[E] V) (t : Term V M r) (x : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam (move g t) x = g (H.MMfam t x) := by
  unfold HermSp.MMfam
  rcases hs : M.split with _ | s
  · rcases x with a | a <;> rfl
  · rcases x with a | a
    · rfl
    · show algebraMap F E ((s.q : F)⁻¹) • (g (t.f' a) - g (t.f a)) =
        g (algebraMap F E ((s.q : F)⁻¹) • (t.f' a - t.f a))
      rw [map_smul, map_sub]

end GlobalTheory.LocOver.MoveBB

namespace GlobalTheory.LocOver

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver.MoveBB

theorem bbne_move : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r), LocNG.BBne (H := H) (move g t) ↔ LocNG.BBne (H := H) t := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r g t
  have hfam : H.MMfam (move g t) = fun x => g (H.MMfam t x) := funext (MMfam_move H g t)
  let gO : V ≃ₗ[M.L.O] V := g.restrictScalars M.L.O
  have hE : ∀ w, g w ∈ Submodule.span E (Set.range (H.MMfam (move g t))) ↔
      w ∈ Submodule.span E (Set.range (H.MMfam t)) := fun w => by
    rw [hfam]; exact mem_span_range_comp g _ w
  have hO : ∀ w, g w ∈ Submodule.span M.L.O (Set.range (H.MMfam (move g t))) ↔
      w ∈ Submodule.span M.L.O (Set.range (H.MMfam t)) := fun w => by
    rw [hfam]; exact mem_span_range_comp gO _ w
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    exact ⟨w, hw, (hE w).1 h1, fun h => h2 ((hO w).2 h)⟩
  · rintro ⟨w, hw, h1, h2⟩
    exact ⟨g w, Submodule.mem_map_of_mem hw, (hE w).2 h1, fun h => h2 ((hO w).1 h)⟩

end GlobalTheory.LocOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizes
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg.CritVand

theorem thrE_add_one_lt (R : Formalism.BasicNotions.Ranks) (h : 1801 ≤ R.r) :
    Formalism.MainNotions.GapDS.thrE (epsSH R) + 1 < 16 * (R.r : ℝ) ^ 19 := by
  have hd : ((2 * R.rS + R.k + 1 : ℕ) : ℝ) = R.r := by exact_mod_cast dimS_eq R
  have hx : (1801 : ℝ) ≤ R.r := by exact_mod_cast h
  have h1 := Formalism.MainNotions.GapDS.thrE_le (epsSH R) (by rw [hd]; linarith)
  rw [hd] at h1
  have h3 : (1 : ℝ) ≤ (R.r : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have h16 : (R.r : ℝ) ^ 3 ≤ (R.r : ℝ) ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

theorem vv_eq_vand_of_sizes : ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl →
    Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
  refine ⟨29, fun D large₂ C' Cl Cg cb Cu cT CT hC' hCl hT hH _ τ => ?_⟩
  have hG := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) hC'
  have hgap := Formalism.L2.SG.Pf.WuBL.gapAtLeast_of D.R (D.hc τ) (hG.2 τ)
  have hds := GlobalTheory.T.formalDegree_eq_harishChandra_of_gap D hT τ _ (Formalism.L2.Col.lamSH_isHCParam (D.hc τ)) hgap (thrE_add_one_lt D.R hG.1)
  have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
  have hSF : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hds, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq]
  field_simp

end GlobalTheory.Core.Deg.CritVand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesClosedStatement
section
open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ranks_frames_closed : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), Formalism.L2.TSel 𝒞 → (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧ Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  first | exact @GlobalTheory.ranks_and_frame_of_tied_class | exact GlobalTheory.ranks_and_frame_of_tied_class | (intros; apply GlobalTheory.ranks_and_frame_of_tied_class <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangularStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular : ∀ (D : D7) {T T' : D.host.E} (F F00 : LFlag (VS D) D.R.rS T) (F' F'0 : LFlag (VS D) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → Gval F F' ≠ 0 → IsInCell (ZhatOM (ZhatL F F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 = Gval F F' ∧ ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Tri D.host.E (frame F00) (fun a => γ (frame F a)) ∧ Tri D.host.E (frame F'0) (fun a => γ (frame F' a)) := by
  first | exact @GlobalTheory.LocOver.witt_frames_at_point | exact GlobalTheory.LocOver.witt_frames_at_point | (intros; apply GlobalTheory.LocOver.witt_frames_at_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowCountsUniformConstantsFamiliesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowCounts_uniform_constants_families : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ c3 cH cS c4 thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → (∀ C ≥ c3, (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C)) ∧ (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cH) ∧ (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cS) ∧ (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A c4) := by
  first | exact @GlobalTheory.RowCounts.uniform_counts | exact GlobalTheory.RowCounts.uniform_counts | (intros; apply GlobalTheory.RowCounts.uniform_counts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFramesStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_at_base_point_of_frames : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → t.G ≠ 0 ∧ ptPN t = toPts w := by
  first | exact @GlobalTheory.Unfold.BasePt.term_at_base_point | exact GlobalTheory.Unfold.BasePt.term_at_base_point | (intros; apply GlobalTheory.Unfold.BasePt.term_at_base_point <;> assumption)
end


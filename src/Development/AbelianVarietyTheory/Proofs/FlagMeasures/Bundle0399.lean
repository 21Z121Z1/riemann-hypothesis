import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0390
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalDenominators
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalGraphEqOfLocalIotaAgree
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPair
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimilitudeConjPreservesUnitaryHaarAtFinitePlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameScaleIsUnitAtPrimeOverLevel
section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameFactorG

open IsDedekindDomain ValuativeRel

variable {D : D7}

theorem exists_diff_not_mem (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ m : 𝓞 D.host.F, m ∈ differentIdeal ℤ (𝓞 D.host.F) ∧ m ∉ (below D P).asIdeal := by
  have h := Formalism.L2.SG.Pf.LatEx.ddG_of D Formalism.L2.SG.Pf.LatEx.splitDiff_holds P hP
  rw [Ideal.map_le_iff_le_comap] at h
  obtain ⟨m, hm, hmP⟩ := Set.not_subset.1 h
  exact ⟨m, hm, hmP⟩

theorem coe_algebraMap_int (m : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (m : D.host.F) := by
  first
  | rfl
  | simp
  | exact (IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E m).symm

theorem iota_mem_of_inv_pow (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (k : ℕ) (y : D.host.E) (hy : y ∈ (ddS D)⁻¹ ^ k) :
    (D.s.atP (below D P)).ιE y ∈ (D.s.atP (below D P)).O := by
  obtain ⟨m, hm, hmP⟩ := exists_diff_not_mem P hP
  set c : D.host.E := ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m : 𝓞 D.host.E) : D.host.E) with hc
  have hmE : c ∈ ddS D := by
    unfold ddS
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, Ideal.mem_map_of_mem _ hm, rfl⟩
  have hpow : c ^ k ∈ ddS D ^ k := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
    exact Submodule.pow_mem_pow _ (FractionalIdeal.mem_coe.2 hmE) k
  have h1 : y * c ^ k ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    have := FractionalIdeal.mul_mem_mul hy hpow
    rwa [← mul_pow, inv_mul_cancel₀ GlobalTheory.FrameFactorUnit.ddS_ne_zero, one_pow] at this
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  have hu := Formalism.L2.SG.Pf.LocalDenominators.iF_unit (D.s.atP (below D P)) hmP
  set t := (D.s.atP (below D P)).ιF (m : D.host.F) with ht
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
  have htinv : t⁻¹ ∈ 𝒪[(D.s.atP (below D P)).Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, hu, inv_one]
  have hcE : (D.s.atP (below D P)).ιE c = algebraMap _ (D.s.atP (below D P)).Ep t := by
    rw [hc, coe_algebraMap_int, (D.s.atP (below D P)).compat]
  have e : (D.s.atP (below D P)).ιE y =
      (D.s.atP (below D P)).ιE (o : D.host.E) *
        (algebraMap _ (D.s.atP (below D P)).Ep t⁻¹) ^ k := by
    have h2 := congrArg (D.s.atP (below D P)).ιE ho
    have h3 : (D.s.atP (below D P)).ιE (algebraMap (𝓞 D.host.E) D.host.E o) =
        (D.s.atP (below D P)).ιE (o : D.host.E) := rfl
    rw [h3, map_mul, map_pow, hcE] at h2
    rw [h2, mul_assoc, ← mul_pow, ← map_mul, mul_inv_cancel₀ ht0, map_one, one_pow, mul_one]
  rw [e]
  exact mul_mem (Formalism.L2.SG.Pf.LocalDenominators.iE_int _ (RingOfIntegers.isIntegral_coe o))
    (pow_mem (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O _ htinv) _)

end GlobalTheory.FrameFactorG

open GlobalTheory.FrameFactorG in

theorem GlobalTheory.FrameFactorG.frFac_unit_at_g : ∀ (D : D7) (Tn T'n : ℕ) (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP Tn T'n F F' → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g : GV D, Adapt g (lf D F0) F → IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, frFac Z.δ (below D P) a ∈ (Z.M (below D P)).L.O ∧ Ring.inverse (frFac Z.δ (below D P) a) ∈ (Z.M (below D P)).L.O := by
  intro D Tn T'n F0 F F' Z FP _ Λ y _ g _ _ P hP a
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z (below D P)
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Z (below D P) a
  have hexp : (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) = -((D.R.rS - a.val : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : a.val ≤ D.R.rS)]
  have hpw : (ddS D) ^ (-((D.R.rS - a.val : ℕ) : ℤ)) = (ddS D)⁻¹ ^ (D.R.rS - a.val) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hexp, hpw] at hD
  constructor
  · have h : frFac Z.δ (below D P) a ∈ Submodule.span (Z.M (below D P)).L.O
        ((D.s.atP (below D P)).ιE '' ((((ddS D)⁻¹ ^ (D.R.rS - a.val) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : Set D.host.E)) := by
      rw [hD]; exact Submodule.mem_span_singleton_self _
    suffices key : ∀ x ∈ Submodule.span (Z.M (below D P)).L.O
        ((D.s.atP (below D P)).ιE '' ((((ddS D)⁻¹ ^ (D.R.rS - a.val) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : Set D.host.E)), x ∈ (Z.M (below D P)).L.O from
      key _ h
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hO]; exact iota_mem_of_inv_pow P hP _ w hw
    | zero => exact zero_mem _
    | add x w _ _ hx hw => exact add_mem hx hw
    | smul o x _ hx => rw [Subring.smul_def]; exact mul_mem o.2 hx
  · have h1 : (1 : (D.s.atP (below D P)).Ep) ∈ Submodule.span (Z.M (below D P)).L.O {frFac Z.δ (below D P) a} := by
      rw [← hD]
      exact Submodule.subset_span ⟨1, GlobalTheory.FrameFactorUnit.one_mem_inv_pow _, map_one _⟩
    obtain ⟨o1, ho1⟩ := Submodule.mem_span_singleton.1 h1
    have ho1' : (o1 : (D.s.atP (below D P)).Ep) * frFac Z.δ (below D P) a = 1 := by
      simpa [Subring.smul_def, smul_eq_mul] using ho1
    have hu : IsUnit (frFac Z.δ (below D P) a) :=
      ⟨⟨frFac Z.δ (below D P) a, o1, by rw [mul_comm]; exact ho1', ho1'⟩, rfl⟩
    have hinv : Ring.inverse (frFac Z.δ (below D P) a) = o1 := by
      calc Ring.inverse (frFac Z.δ (below D P) a)
          = ((o1 : (D.s.atP (below D P)).Ep) * frFac Z.δ (below D P) a) * Ring.inverse (frFac Z.δ (below D P) a) := by
            rw [ho1', one_mul]
        _ = o1 := by rw [mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
    rw [hinv]; exact o1.2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameStandardLatticeHermitianIntegral
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.LocStdInt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars (Valuation.integer (ValuativeRel.valuation F)))

def hl (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := H.h_smul_left a x y

lemma h_prF (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v y : V) :
    H.h (Fr.prF v) y = H.h v y - ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y
      - ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  show hl H y (Fr.prF v) = _
  simp only [FrameD.prF, map_sub, map_sum, map_smul, smul_eq_mul]
  rfl

lemma h_expand (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v y : V) :
    H.h v y = H.h (Fr.prF v) y + ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) y
      + ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) y := by
  rw [h_prF H Fr v y]
  ring

lemma h_prF_es (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (v : V) (b : Fin r) :
    H.h (Fr.prF v) (Fr.es b) = 0 := by
  rw [h_prF H Fr v (Fr.es b)]
  have hdual : ∀ a, H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := fun a => Fr.h_es a b
  simp [hdual, Fr.h_ss]

lemma h_symm_mem (H : HermSp M V) {x y : V} (h : H.h x y ∈ M.L.O) : H.h y x ∈ M.L.O := by
  rw [H.h_herm]
  exact cj_mem h

lemma span_left (H : HermSp M V) (S : Set V) (y : V) (h : ∀ x ∈ S, H.h x y ∈ M.L.O) :
    ∀ x ∈ Submodule.span M.L.O S, H.h x y ∈ M.L.O := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have h0 : H.h 0 y = 0 := (hl H y).map_zero
    rw [h0]
    exact zero_mem _
  | add x x' _ _ hx hx' =>
    rw [H.h_add_left]
    exact add_mem hx hx'
  | smul c x _ hx =>
    rw [Subring.smul_def, H.h_smul_left]
    exact mul_mem c.2 hx

private lemma form_mem_O_of_frame_coords_mem_O (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) {u v : V}
    (hu : (∀ a, H.h u (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h u (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF u ∧ H.mkW Fr.f w ∈ L)
    (hv : (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L) :
    H.h u v ∈ M.L.O := by
  obtain ⟨hus, hue, wu, hwu, hwuL⟩ := hu
  obtain ⟨hvs, hve, wv, hwv, hwvL⟩ := hv
  have hpp : H.h (Fr.prF v) (Fr.prF u) ∈ M.L.O := by
    have h0 := (hL.2.1 wv).1 hwvL wu hwuL
    rwa [hwv, hwu] at h0
  have hwu0 : ∀ x ∈ H.X Fr.f, H.h (wu : V) x = 0 := wu.2
  have he0 : ∀ a, H.h (Fr.e a) (Fr.prF u) = 0 := by
    intro a
    rw [H.h_herm, ← hwu, hwu0 (Fr.e a) (Submodule.subset_span ⟨a, rfl⟩), map_zero]
  have hs0 : ∀ a, H.h (Fr.es a) (Fr.prF u) = 0 := by
    intro a
    rw [H.h_herm, h_prF_es H Fr u a, map_zero]
  have hvu : H.h v (Fr.prF u) ∈ M.L.O := by
    rw [h_expand H Fr v (Fr.prF u)]
    simp only [he0, hs0, mul_zero, Finset.sum_const_zero, add_zero]
    exact hpp
  rw [h_expand H Fr u v]
  refine add_mem (add_mem (h_symm_mem H hvu) ?_) ?_
  · exact sum_mem fun a _ => mul_mem (hus a) (h_symm_mem H (hve a))
  · exact sum_mem fun a _ => mul_mem (hue a) (h_symm_mem H (hvs a))

theorem lamStd_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L), ∀ x ∈ Fr.LamStd L, ∀ y ∈ Fr.LamStd L, H.h x y ∈ M.L.O := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr L hL x hx y hy
  unfold FrameD.LamStd at hx hy
  refine span_left H _ y ?_ x hx
  intro u hu
  exact h_symm_mem H (span_left H _ u (fun v hv => form_mem_O_of_frame_coords_mem_O H Fr L hL hv hu) y hy)

end GlobalTheory.LocStdInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalGraphEqOfLocalIotaAgreeStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_graph_eq_of_local_iota_agree : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 := by
  first | exact @GlobalTheory.Unfold.IotaGlob.graph_eq_of_local_iota | exact GlobalTheory.Unfold.IotaGlob.graph_eq_of_local_iota | (intros; apply GlobalTheory.Unfold.IotaGlob.graph_eq_of_local_iota <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramDetJoinedFamilyEqPmNormDifference
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.GramDet

theorem det_sub_single {E : Type} [CommRing E] {n : Type} [Fintype n] [DecidableEq n]
    (Y : Matrix n n E) (l : n) (d : E) :
    (Y - Matrix.single l l d).det = Y.det - d * Y.adjugate l l := by
  have h : Y - Matrix.single l l d = Y.updateRow l (Y l + (-d) • (Pi.single l 1 : n → E)) := by
    ext i j
    by_cases hi : i = l
    · subst hi
      by_cases hj : j = i
      · subst hj; simp [sub_eq_add_neg]
      · simp [hj, Ne.symm hj]
    · simp [Matrix.updateRow_ne hi, Ne.symm hi]
  rw [h, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    Matrix.adjugate_apply]
  ring

theorem det_blocks_single {E : Type} [CommRing E] {n : Type} [Fintype n] [DecidableEq n]
    (Z Y : Matrix n n E) (l : n) (c c' : E) (hZ : IsUnit Z.det) :
    (Matrix.fromBlocks Z (Matrix.single l l c) (Matrix.single l l c') Y).det
      = Z.det * Y.det - c * c' * (Z.adjugate l l * Y.adjugate l l) := by
  letI := Matrix.invertibleOfIsUnitDet Z hZ
  rw [Matrix.det_fromBlocks₁₁, Matrix.single_mul_mul_single, det_sub_single]
  have h : Z.det * (⅟Z) l l = Z.adjugate l l := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
      Ring.mul_inverse_cancel _ hZ, one_mul]
  rw [← h]; ring

theorem det_blocks_swap {E : Type} [CommRing E] {n : Type} [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n E) :
    (Matrix.fromBlocks A B C D).det = (Matrix.fromBlocks B A D C).det ∨
    (Matrix.fromBlocks A B C D).det = -(Matrix.fromBlocks B A D C).det := by
  have h := Matrix.det_permute' (Equiv.sumComm n n) (Matrix.fromBlocks B A D C)
  have h2 : (Matrix.fromBlocks B A D C).submatrix id (Equiv.sumComm n n)
      = Matrix.fromBlocks A B C D := by
    ext (i | i) (j | j) <;> rfl
  rw [h2] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm n n)) with h1 | h1
  · left; rw [h, h1]; simp
  · right; rw [h, h1]; simp

theorem adjugate_last {E : Type} [CommRing E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Z.adjugate (Fin.last r) (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, ← two_mul, pow_mul]
  simp

theorem det_gram_sum_elim {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F) (hf : ∀ a b, H.h (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E T) else 0) (hf' : ∀ a b, H.h (f' a) (f' b) = if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E T') else 0) (hD : IsUnit (H.Dl f f' (r + 1))) : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' ∨ (H.gram (Sum.elim f f')).det = -H.Gdet f f' T T' := by
  set Z := H.Zhat f f' with hZ
  have hD1 : H.Dl f f' (r + 1) = Z.det := by
    simp [HermSp.Dl, hZ]
  have hD0 : H.Dl f f' r = Z.adjugate (Fin.last r) (Fin.last r) := by
    rw [adjugate_last]
    simp only [HermSp.Dl, Nat.le_succ, dif_pos]
    rfl
  set c : E →+* E := (M.L.cj : E →+* E) with hc
  have hg : H.gram (Sum.elim f f') = Matrix.fromBlocks
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T))) Z (c.mapMatrix Z).transpose
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T'))) := by
    ext (i | i) (j | j)
    · simp [HermSp.gram, hf, Matrix.single_apply, and_comm, eq_comm]
    · rfl
    · exact H.h_herm _ _
    · simp [HermSp.gram, hf', Matrix.single_apply, and_comm, eq_comm]
  have hG : H.Gdet f f' T T' = (Matrix.fromBlocks Z
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T)))
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T')))
      (c.mapMatrix Z).transpose).det := by
    rw [det_blocks_single _ _ _ _ _ (hD1 ▸ hD), Matrix.det_transpose, ← RingHom.map_det,
      ← Matrix.adjugate_transpose, ← RingHom.map_adjugate, HermSp.Gdet, hD1, hD0]
    simp [HermSp.normE, hc]
  rw [hg, hG]
  exact det_blocks_swap _ _ _ _

end GlobalTheory.GramDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserIffRationalCoords
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StabIntCoord

theorem mem_maxUnramifiedSubfield_conj_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : Frames L r k)
    (x : S.GLV) (hx : x ∈ S.St) (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : IsUni s) (hs' : IsUni s')
    (h1 : ∀ j, x (S.f j) = ∑ i, s i j • S.f i) (h2 : ∀ j, x (S.f' j) = ∑ i, s' i j • S.f' i) :
    x ∈ S.K0 ↔ IsIntM L s' := by
  have heq := ((GlobalTheory.HL.FrameStab.stab_eq L r k S).2 s s' hs hs').2 ⟨x, hx, h1, h2⟩
  have hint := ((GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).1 s s' hs hs' heq).2
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  have hl1 : LinearIndependent E S.f := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E S.f' := hli.comp Sum.inr Sum.inr_injective
  have e1 := GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral L S.f hl1 x s hs h1
  have e2 := GlobalTheory.T.mem_stabilizer_span_iff_unitriangular_integral L S.f' hl2 x s' hs' h2
  unfold Frames.K0
  simp only [Subgroup.mem_inf]
  rw [e1, e2, hint]
  tauto

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord

open IsDedekindDomain

theorem loc_act {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig) {n r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (c : ((A.loc p).Fp)ˣ)
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E)) (g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (hE : A.Ext p x g') (v : Fin (r + 1) → Fin n → E) (vl : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (hv : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • vl a = A.bc p (v a))
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hM : ∀ b : Fin (r + 1), x (v b) = ∑ a, M a b • v a) (b : Fin (r + 1)) :
    g' (vl b) = ∑ a : Fin (r + 1), (algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ)) /
      (c : (A.loc p).Fp) ^ (r - (b : ℕ))) * (A.loc p).ιE (M a b)) • vl a := by
  have hc : ∀ m : ℕ, ((c : (A.loc p).Fp) ^ m) ≠ 0 := fun m => pow_ne_zero _ c.ne_zero
  have hvl : ∀ a : Fin (r + 1), vl a = algebraMap (A.loc p).Fp (A.loc p).Ep (((c : (A.loc p).Fp) ^ (r - (a : ℕ)))⁻¹) • A.bc p (v a) := by
    intro a
    rw [← hv a, smul_smul, ← map_mul, inv_mul_cancel₀ (hc _), map_one, one_smul]
  have hbc : ∀ (l : Fin (r + 1) → E) (w : Fin (r + 1) → Fin n → E),
      A.bc p (∑ a, l a • w a) = ∑ a, (A.loc p).ιE (l a) • A.bc p (w a) := by
    intro l w
    funext i
    simp [Places.bc, Finset.sum_apply, map_sum, smul_eq_mul, map_mul]
  rw [hvl b, map_smul, hE, hM b, hbc, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hv a, smul_smul, smul_smul]
  congr 1
  rw [div_eq_mul_inv, map_mul]
  ring

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord

set_option maxHeartbeats 1000000 in

theorem integralStabiliser_iff_rational_coords_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ x ∈ G.St, ∀ B : Formalism.L2.SG.PairVal.MatR D, (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) → (x ∈ G.K0 ↔ ∀ a b : Fin (D.R.rS + 1), a < b → B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))) := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c x hx B hB
  obtain ⟨s, s', hs, hs', hsf, hsf'⟩ := GlobalTheory.T.globalFrameStabilizer_acts_unitriangular _ _ _ G x hx
  have key : ∀ p : PlF D, (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔
      ∀ a b : Fin (D.R.rS + 1), a < b → (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O := by
    intro p
    haveI := (D.s.atP p).lf
    haveI := (D.s.atP p).char0
    haveI : IsNonarchimedeanLocalField ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).lf
    haveI : CharZero ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).char0
    obtain ⟨xp, hxp, hExt⟩ := hx p
    have huniq := ((GlobalTheory.HL.RatExt.rational_extend (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ p).2.2.1 x)
    have hK : (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔ xp ∈ (G.S p).K0 := by
      constructor
      · rintro ⟨g', hg', hgE⟩
        rwa [huniq.unique hExt hgE]
      · intro h; exact ⟨xp, h, hExt⟩
    rw [hK]
    have h1 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f (G.S p).f (G.f_eq p) s hsf
    have h2 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) s' hsf'
    have h3 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) B hB
    have hceq : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.c p).val = algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E) := c.c_eq p
    show _ ↔ ∀ a b : Fin (D.R.rS + 1), a < b → ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O
    have hcne : ∀ m : ℕ, ((G.c p).val ^ m) ≠ 0 := fun m => pow_ne_zero _ (G.c p).ne_zero
    have huni : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUni M →
        IsUni (fun a b : Fin (D.R.rS + 1) => algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (M a b)) := by
      intro M hM
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · simp [hM.1 i j hij]
      · simp [hM.2 i, div_self (hcne _)]
    rw [mem_maxUnramifiedSubfield_conj_iff _ _ _ (G.S p) xp hxp _ _ (huni s hs) (huni s' hs') h1 h2]
    have hli : LinearIndependent ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.S p).f' :=
      (GlobalTheory.FrameBasic.main _ _ _ (G.S p)).1.comp Sum.inr Sum.inr_injective
    have hsB : ∀ a b, ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) := by
      intro a b
      have e := (h2 b).symm.trans (h3 b)
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
      simp_rw [← sub_smul] at e
      have h0 := Fintype.linearIndependent_iff.1 hli _ e a
      have hu : IsUnit (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ)))) :=
        (isUnit_iff_ne_zero.2 (div_ne_zero (hcne _) (hcne _))).map _
      rw [← mul_sub, hu.mul_right_eq_zero, sub_eq_zero] at h0
      exact h0
    have hent : ∀ a b : Fin (D.R.rS + 1), a < b → algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
        ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
          ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) := by
      intro a b hab
      have hab' : (a : ℕ) < b := hab
      have hb := b.isLt
      rw [show D.R.rS - (a : ℕ) = (D.R.rS - b) + ((b : ℕ) - a) by omega, pow_add,
        mul_div_cancel_left₀ _ (hcne _), map_pow, hceq, hsB, mul_comm]
    constructor
    · intro h a b hab
      rw [← hent a b hab]
      exact h a b
    · intro h a b
      rcases lt_trichotomy a b with hab | rfl | hab
      · beta_reduce
        rw [hent a b hab]
        exact h a b hab
      · show _ ∈ _
        simp [hs'.2 a, div_self (hcne _)]
      · show _ ∈ _
        simp [hs'.1 a b hab]
  have hK0 : x ∈ G.K0 ↔ ∀ p, ∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g' := Iff.rfl
  rw [hK0, forall_congr' key]
  have hI : ∀ a b : Fin (D.R.rS + 1), a < b → (B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔
      ∀ p : PlF D, (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O) := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hb := b.isLt
    have hn : (b : ℕ) - (a : ℕ) ≤ D.R.rS := by omega
    have e : (-((b : ℤ) - (a : ℤ))) = -((((b : ℕ) - (a : ℕ) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub hab'.le]
    rw [e]
    exact GlobalTheory.T.mem_inv_pow_different_iff_local D ⟨Y.δ, Y.M, Y.agree⟩ _ hn (B a b)
  constructor
  · intro h a b hab
    exact (hI a b hab).2 fun p => h p a b hab
  · intro h p a b hab
    exact (hI a b hab).1 (h a b hab) p

end GlobalTheory.HL.StabIntCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPairStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisedBaseFrames_relevantPair : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → ∀ p : PlF D, (∃ P, AtBase Z p F00 F'0 (Tu D u) (Tu D u') P) ∧ ∀ P, AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → P.RelG (LocNG.theta (Z.M p)) := by
  first | exact @GlobalTheory.LocBaseRel.atBase_relG | exact GlobalTheory.LocBaseRel.atBase_relG | (intros; apply GlobalTheory.LocBaseRel.atBase_relG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimilitudeConjPreservesUnitaryHaarAtFinitePlaceStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_conj_preserves_unitary_haar_at_finite_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → ∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0 := by
  first | exact @GlobalTheory.ConjStabiliserHaar.conj_preserves_haar | exact GlobalTheory.ConjStabiliserHaar.conj_preserves_haar | (intros; apply GlobalTheory.ConjStabiliserHaar.conj_preserves_haar <;> assumption)
end


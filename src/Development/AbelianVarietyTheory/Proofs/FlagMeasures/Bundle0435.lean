import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0313
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0317
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0409
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0425
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0305
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0366
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0211
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0397
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeOfLocallyStandardFrame
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatAdapt

theorem witt_flag (D : D7) (T : D.host.E) (hT : T ≠ 0) (F F' : FlagG (VS D) D.R.rS T) :
    ∃ g : GV D, g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ ∀ a, g (F.fvec a) = F'.fvec a := by
  have hind : ∀ G : FlagG (VS D) D.R.rS T, LinearIndependent D.host.E G.fvec := by
    intro G
    unfold FlagG.fvec
    rw [linearIndependent_fin_snoc]
    refine ⟨G.e_indep, fun hz => hT ?_⟩
    have h0 : ∀ x ∈ Submodule.span D.host.E (Set.range G.e), (VS D).hT x G.z = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact G.z_orth a
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    have := h0 _ hz
    rw [G.z_norm] at this
    exact neg_eq_zero.1 this
  have hgram : ∀ G : FlagG (VS D) D.R.rS T, ∀ i j, (VS D).hT (G.fvec i) (G.fvec j) =
      if i = Fin.last _ ∧ j = Fin.last _ then -T else 0 := by
    intro G i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_norm]
      | cast b =>
        simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
        rw [← (VS D).herm.eq (G.e b) G.z, G.z_orth b, map_zero]
        simp [Fin.castSucc_ne_last]
    | cast a =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_orth, Fin.castSucc_ne_last]
      | cast b => simp [FlagG.fvec, G.e_iso, Fin.castSucc_ne_last]
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.St.WittT.witt_family F.fvec F'.fvec (hind F) (hind F')
    (fun i j => by rw [hgram F, hgram F'])
  exact ⟨g, hg, hgi⟩

theorem iso_X {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) :
    ∀ y ∈ G.X, ∀ x ∈ G.X, (VS D).hT y x = 0 := by
  intro y hy x hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    induction hy using Submodule.span_induction with
    | mem v hv => obtain ⟨a, rfl⟩ := hv; exact G.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem xa_last {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) : G.Xa D.R.rS = G.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp

theorem lsub_eq {D : D7} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : Lsub Λ F = Lsub Λ F' := by
  simp only [Lsub, Lrep, Xsp, h]

theorem xlam_eq {D : D7} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : XLam Λ F = XLam Λ F' := by
  simp only [XLam, Xsp, h]

theorem row_lattice_of_local_standard : ∀ (D : D7) (Tn : ℕ), Tn ≠ 0 → ∀ (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (G : LFlag (VS D) D.R.rS (Tn : D.host.E)) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ g, Adapt g (lf D F0) G ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  intro D Tn hTn F0 G Z A hA Λ hΛ hloc
  have hU := GlobalTheory.T.isUnimodular_of_local_standardLattice_translates
  have hX := GlobalTheory.T.isotropicPart_eq_span_scaledFrame_unitriangular
  have hZ := GlobalTheory.T.exists_add_isotropicSpan_mem_locallyStandardLattice
  have hP := GlobalTheory.T.anisotropicFrameVector_primitive_in_innerLattice
  have hM := GlobalTheory.T.exists_flag_of_unitriangular_isotropic_shift
  have hTr := GlobalTheory.T.rowLattice_properties_transport_by_isometry
  have hC := GlobalTheory.T.fixed_conv_of_integral_flag_lattice
  have hu := hU D Z A Λ hΛ hloc
  obtain ⟨e', he', hXe⟩ := hX D _ G Z A hA Λ hΛ hloc
  obtain ⟨x, hx, hzx⟩ := hZ D _ G Z A hA Λ hΛ hloc
  have hpr := hP D _ G Z A hA Λ hΛ hloc
  obtain ⟨G', hGe, hGz, hGX⟩ := hM D _ G.fl e' x he' hx
  have hT0 : ((Tn : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hTn
  obtain ⟨g, hg, hga⟩ := witt_flag D _ hT0 F0 G'
  have hX' : XLam Λ (lf D G') = XS D G' := by
    rw [xlam_eq (lf D G') G hGX, hXe, XS, hGe]
  have hpr' : ∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
    intro c hc
    rw [lsub_eq (lf D G') G hGX] at hc
    refine hpr c ?_
    have hcx : c • G.fl.z = c • G'.z - c • x := by rw [hGz, smul_add]; abel
    rw [hcx]
    refine Submodule.sub_mem _ hc ?_
    have hxX : c • x ∈ (Xsp G : Submodule D.host.E (VS D).V) := Submodule.smul_mem _ c hx
    refine ⟨Submodule.mem_sup_right hxX, ?_⟩
    show c • x ∈ orth (VS D) (Xsp G)
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro y hy
    exact iso_X G.fl y hy _ hxX
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hTr D _ F0 G' g hg hga Λ hΛ hu (hGz ▸ hzx) hX' hpr'
  refine ⟨g, ⟨hg, fun a => ?_⟩, h1, ⟨h2, h3, ⟨h4, rfl⟩, hC D _ F0 _ h5 h6⟩, h5⟩
  show g (F0.fvec a) - G.fl.fvec a ∈ G.fl.Xa a.val
  rw [hga a]
  induction a using Fin.lastCases with
  | last =>
    simp only [FlagG.fvec, Fin.snoc_last, Fin.val_last, hGz, xa_last]
    simpa using hx
  | cast b =>
    simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.coe_castSucc, hGe]
    exact he' b

end GlobalTheory.RowLatAdapt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameMiddleConjugateUnipotent
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LoopC

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

theorem rowsLift_mem_orth {U : Submodule E S.V} {x : S.V} :
    x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem rowsLift_fix_span {ι : Type} (v : ι → S.V) (s : Set ι) (n : S.V ≃ₗ[E] S.V)
    (hn : ∀ a, n (v a) = v a) : ∀ x ∈ Submodule.span E (v '' s), n x = x := by
  intro x hx
  have hle : Submodule.span E (v '' s) ≤ LinearMap.eqLocus (n : S.V →ₗ[E] S.V) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_eqLocus]
    simpa using hn a
  have h := hle hx
  rw [LinearMap.mem_eqLocus] at h
  simpa using h

theorem rowsLift_map_eq (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hn : ∀ x ∈ U, n x = x) :
    U.map (n : S.V →ₗ[E] S.V) = U := by
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [hn x hx]
  · intro hy
    exact ⟨y, hy, hn y hy⟩

theorem rowsLift_orth_iff (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hn : ∀ x ∈ U, n x = x) (x : S.V) : n x ∈ orth S U ↔ x ∈ orth S U := by
  have hi' : ∀ a b, S.hT (n a) (n b) = S.hT a b := hi
  rw [rowsLift_mem_orth, rowsLift_mem_orth]
  refine forall₂_congr fun y hy => ?_
  have h := hi' y x
  rw [hn y hy] at h
  rw [h]

theorem rowsLift_Lsub_gmap (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (n : S.V ≃ₗ[E] S.V)
    (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hn : ∀ x ∈ Xsp F, n x = x)
    (hq : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  ext y
  unfold Lsub Lrep
  constructor
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨ha1, haO⟩ := Submodule.mem_inf.mp ha
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.mp ha1
    have hlO : l ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn l).mp haO
    have hd : n l - l ∈ Xsp F := hq l hlO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨l, Submodule.mem_inf.mpr ⟨hl, hlO⟩, (n l - l) + b, (toO S (Xsp F)).add_mem hd hb, ?_⟩, hyO⟩
    show l + (n l - l + b) = n l + b
    abel
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨hl, haO⟩ := Submodule.mem_inf.mp ha
    have hnO : n a ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn a).mpr haO
    have hd : n a - a ∈ Xsp F := hq a haO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨n a, Submodule.mem_inf.mpr ⟨Submodule.mem_map.mpr ⟨a, hl, rfl⟩, hnO⟩, b - (n a - a),
        (toO S (Xsp F)).sub_mem hb hd, ?_⟩, hyO⟩
    abel

theorem rowsLift_cancel (X W : Submodule E S.V) (hXW : ∀ x ∈ X, x ∈ W → x = 0)
    (A B : Submodule (𝓞 E) S.V) (h : (A ⊓ toO S W) ⊔ toO S X = (B ⊓ toO S W) ⊔ toO S X) :
    A ⊓ toO S W ≤ B ⊓ toO S W := by
  intro y hy
  have h1 : y ∈ (A ⊓ toO S W) ⊔ toO S X := Submodule.mem_sup_left hy
  rw [h] at h1
  obtain ⟨b, hb, x, hx, rfl⟩ := Submodule.mem_sup.mp h1
  have hxW : x ∈ W := by
    have h2 : b + x - b ∈ W := W.sub_mem (Submodule.mem_inf.mp hy).2 (Submodule.mem_inf.mp hb).2
    simpa using h2
  rw [hXW x hx hxW, add_zero]
  exact hb

end Generic

theorem rowsLift_X_inf_Wb (D : D7) (x : (hS D).V)
    (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) (hW : x ∈ Wb D) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).mp hx
  have hW' : (∑ i, c i • D.sp.hypE i) ∈ orth (hS D)
      (Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF)) := hW
  have hc : ∀ j, c j = 0 := by
    intro j
    have h1 : (hS D).hT (D.sp.hypF j) (∑ i, c i • D.sp.hypE i) = 0 :=
      (rowsLift_mem_orth.mp hW') _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
    have hs : ∀ i, (hS D).hT (D.sp.hypF j) (D.sp.hypE i) = if i = j then 1 else 0 := by
      intro i
      rw [← (hS D).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
      split_ifs <;> simp
    rw [map_sum] at h1
    simpa [hs] using h1
  simp [hc]

theorem rowsLift_fixX {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {n : (hS D).V ≃ₗ[D.host.E] (hS D).V} (hn : FixFr D (lf D F0) n) :
    (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z ∧ ∀ x ∈ F0.X, n x = x := by
  obtain ⟨-, hfr, -⟩ := hn
  have he : ∀ a, n (F0.e a) = F0.e a := by
    intro a
    have h := hfr (Fin.castSucc a)
    simpa [frame, FlagG.fvec, lf] using h
  have hz : n F0.z = F0.z := by
    have h := hfr (Fin.last _)
    simpa [frame, FlagG.fvec, lf] using h
  refine ⟨he, hz, ?_⟩
  intro x hx
  rw [FlagG.X, ← Set.image_univ] at hx
  exact rowsLift_fix_span F0.e Set.univ n he x hx

theorem rowsLift : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ → Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) → ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  intro D u _ hT3 _ F0 he hz Λ₁ Λ₂ h₁ h₂ hL
  have hT1 : 1 ≤ Tu D u := by omega
  have hB : IsBase D u F0 := ⟨he, hz⟩
  obtain ⟨n₁, hf₁, hs₁, hr₁⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ₁ hB h₁ hT1
  obtain ⟨n₂, hf₂, hs₂, hr₂⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ₂ hB h₂ hT1
  have hfx₁ := rowsLift_fixX hf₁
  have hfx₂ := rowsLift_fixX hf₂
  have hLs : ∀ (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) (Λ : LatV D), FixFr D (lf D F0) n →
      Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) (lf D F0) = Lsub Λ (lf D F0) := by
    intro n Λ hf
    have hX := (rowsLift_fixX hf).2.2
    obtain ⟨hi, -, hq⟩ := hf
    exact rowsLift_Lsub_gmap (lf D F0) Λ n hi hX hq
  have hW : ∀ Λ : LatV D, IsRowLat D F0 Λ → IsSplit D F0 Λ →
      Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X := fun Λ hr hs =>
    ((GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 Λ hT1 hB hr).1 hs).2
  have heq : (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X =
      (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X :=
    (hW _ hr₁ hs₁).symm.trans
      (((hLs n₁ Λ₁ hf₁).trans (hL.trans (hLs n₂ Λ₂ hf₂).symm)).trans (hW _ hr₂ hs₂))
  have hXW : ∀ x ∈ F0.X, x ∈ Wb D → x = 0 := fun x hx hw =>
    rowsLift_X_inf_Wb D x (by rw [← he]; exact hx) hw
  have hM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D) = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D) :=
    le_antisymm (rowsLift_cancel _ _ hXW _ _ heq) (rowsLift_cancel _ _ hXW _ _ heq.symm)
  have e₁ : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₁
  have e₂ : Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₂
  have hMM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ := by
    rw [e₁, e₂, hM]
  have hfix : ∀ v, n₁ v = v → n₂ v = v → (n₁.trans n₂.symm) v = v := by
    intro v h1 h2
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_eq, h2]
  obtain ⟨hi₁, -, hq₁⟩ := hf₁
  obtain ⟨hi₂, -, hq₂⟩ := hf₂
  have hmem : n₁.trans n₂.symm ∈ stabF D F0 := by
    simp only [stabF, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hi₂) hi₁
    · intro j
      exact rowsLift_map_eq (F0.Xa j) (n₁.trans n₂.symm) (fun x hx =>
        rowsLift_fix_span F0.e _ _ (fun a => hfix _ (hfx₁.1 a) (hfx₂.1 a)) x hx)
    · exact hfix _ hfx₁.2.1 hfx₂.2.1
  refine ⟨n₁.trans n₂.symm, hmem, ?_, ?_⟩
  · intro x hx
    have hy : n₁ x ∈ orth (hS D) F0.X := (rowsLift_orth_iff F0.X n₁ hi₁ hfx₁.2.2 x).mpr hx
    obtain ⟨w, hw⟩ : ∃ w, w = n₂.symm (n₁ x) := ⟨_, rfl⟩
    have hnw : n₂ w = n₁ x := by rw [hw, LinearEquiv.apply_symm_apply]
    have hwO : w ∈ orth (hS D) F0.X :=
      (rowsLift_orth_iff F0.X n₂ hi₂ hfx₂.2.2 w).mp (by rw [hnw]; exact hy)
    have h1 : n₁ x - x ∈ F0.X := hq₁ x hx
    have h2 : n₂ w - w ∈ F0.X := hq₂ w hwO
    rw [hnw] at h2
    have h3 : (n₁.trans n₂.symm) x - x = (n₁ x - x) - (n₁ x - w) := by
      rw [LinearEquiv.trans_apply, ← hw]
      abel
    rw [h3]
    exact F0.X.sub_mem h1 h2
  · have hcomp : Formalism.HermitianLatticesTheory.gmap (n₁.trans n₂.symm) Λ₁ =
        Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁) := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    have hback : Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂) = Λ₂ := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    rw [hcomp, hMM, hback]

end GlobalTheory.LoopC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TcritLowAlongFamilyGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelGap

private theorem VV_eq_vand_lamSH_of_standingHypotheses (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT : ℝ) (hT : Ties D) (hS : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hL : 1 ≤ Cl * large₂.sc.L)
    (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by

  have hanti : StrictAnti (lamSH D.R (D.hc τ)) := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
  have hd : D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hDs D large₂ C' Cl Cg cb Cu cT CT hT hS hL τ
  have hN : 2 * D.R.rS + D.R.k + 1 = D.R.r := dimS_eq D.R
  have hpos : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hd, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← hN]
  field_simp

theorem tcritLow_along_family_gap :
    Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusBranching.admF5 Fm Cg cb Cu cT CT C0 := by
  intro _ hH _ Cg cb Cu cT CT C0
  refine ⟨40, fun eps Fm _ hCl _ => ?_⟩
  unfold VanishingOnXAndXPlusBranching.admF5 OwnEv
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨hxk, hb⟩ := GlobalTheory.CritLevel.sizes_low _ (Fm.sizes x hx1 i)
  have hL1 : 1 ≤ (Fm.L x i).sc.L := by
    show 1 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps
    exact Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hL : 1 ≤ sCl Fm * (Fm.L x i).sc.L := by nlinarith
  intro h0
  exact GlobalTheory.CritLevel.tcrit_low _ _ _ _ _ _ _ _ _ _ hCl
    (fun τ => VV_eq_vand_lamSH_of_standingHypotheses hH.2.2.2 _ _ _ _ _ _ _ _ _ (Fm.ties x i) h0.1 hL τ) hb hxk h0

end GlobalTheory.CritLevelGap
end


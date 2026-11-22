import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0294
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0091
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0402
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0403
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeStabilisersCommensurableAlmostEveryw
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Unfold.LocStab

theorem finrank_Vp_eq (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have := D.R.two_le_m; obtain ⟨t, ht⟩ := D.R.m_even
  unfold Ranks.rS Ranks.r; omega

theorem relIndex_comap_subtype {G : Type*} [Group G] (U X Y : Subgroup G) (hY : Y ≤ U) :
    (X.comap U.subtype).relIndex (Y.comap U.subtype) = X.relIndex Y := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hY]

theorem stabilizer_eq_comap {G α : Type*} [Group G] (U : Subgroup G) [MulAction U α] (S : Subgroup G) (d : α)
    (h : ∀ g : U, g.1 ∈ S ↔ g • d = d) : MulAction.stabilizer U d = S.comap U.subtype := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.coe_subtype, h g]

theorem comap_subtype_inf {G : Type*} [Group G] (U A : Subgroup G) :
    (U ⊓ A).comap U.subtype = A.comap U.subtype := by
  ext g; simp

end GlobalTheory.Unfold.LocStab

namespace GlobalTheory.Unfold.LocStab

set_option maxHeartbeats 1000000 in

theorem local_stabilisers : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → (∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d) → ∀ (Λ₀ : LV D) (d0 : Dat Z FP), LocOver Λ₀ d0 → (∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ≠ 0 ∧ ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0) ∧ {p | (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype ≠ MulAction.stabilizer ↥(FP p).UW0 (d0 p)}.Finite ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → ∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d p)) ≠ 0 ∧ (MulAction.stabilizer ↥(FP p).UW0 (d p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0 ∧ GlobalTheory.HL.invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) = LocNG.Datum.wt (d0 p) (d p) := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel _ hMv hSt Λ₀ d0 hLO
  have hOK : ∀ p, (Z.M p).OK := fun p => (Z.agree p).1
  have hstab : ∀ p (d : LocNG.Datum (FP p)),
      MulAction.stabilizer ↥(FP p).UW0 d = (LocNG.Datum.Stab d).comap (FP p).UW0.subtype :=
    fun p d => stabilizer_eq_comap _ _ d (fun g => hSt p d g)
  have hle : ∀ p (d : LocNG.Datum (FP p)), LocNG.Datum.Stab d ≤ (FP p).UW0 :=
    fun p d => Subgroup.closure_le _ |>.2 fun g hg => hg.1
  choose τ0 hτ0 hτ0L using hLO.2
  have hc := fun p => GlobalTheory.T.hermitianTerm_stabilizer_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
    (hRel p) (d0 p) (τ0 p) (hτ0 p)
  have hA : ∀ p, (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype =
      ((FP p).UW0 ⊓ LocNG.Aut (τ0 p).abelian₂).comap (FP p).UW0.subtype := by
    intro p; rw [comap_subtype_inf, hτ0L p]
  refine ⟨fun p => ?_, ?_, fun d hd p => ?_⟩
  · rw [hA p, hstab p]
    refine ⟨?_, ?_⟩
    · rw [relIndex_comap_subtype _ _ _ inf_le_left, Subgroup.relIndex_eq_one.2 (hc p).1]
      exact one_ne_zero
    · rw [relIndex_comap_subtype _ _ _ (hle p (d0 p))]
      exact (hc p).2.1
  · have hAt : ∀ p, GlobalTheory.LocOver.AtBase Z p F F' (Tu D u) (Tu D u') (FP p) := fun p => by
      obtain ⟨h1, h2, h3, h4⟩ := hB p
      exact ⟨h1, h2, h3, h4⟩
    refine (GlobalTheory.T.finite_places_not_primeTo_baseFrameInvariants D Z u u' F F' hG FP hAt).subset fun p hp hpr => hp ?_
    have h2 := GlobalTheory.T.datumStabilizer_preserves_termLattice_goodPlace (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) hpr (d0 p) (τ0 p) (hτ0 p)
    rw [hA p, hstab p]
    exact congrArg _ (le_antisymm (hc p).1 (le_inf (hle p (d0 p)) h2))
  · obtain ⟨τ, hτ⟩ := hd p
    have h3 := (hc p).2.2
    have hτc := GlobalTheory.T.hermitianTerm_stabilizer_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) (d p) τ hτ
    rw [hstab p, hstab p, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p))]
    refine ⟨h3 (d p) τ hτ, hτc.2.2 (d0 p) (τ0 p) (hτ0 p), ?_⟩
    rw [GlobalTheory.HL.invVol, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p)), LocNG.Datum.wt, LocNG.volRel, one_div_div]

end GlobalTheory.Unfold.LocStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermNoDefectPrimeToInvariants
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocNoDef
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem N_unitary (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : ∀ n ∈ Fr.N, IsUnitary H n := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => intro a b; rfl
  | mul x y _ _ hx hy => intro a b; rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, hy]
  | inv x _ hx =>
    intro a b
    have hxx : ∀ v, x (x⁻¹ v) = v := fun v => by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [← hx (x⁻¹ a) (x⁻¹ b), hxx, hxx]

theorem frame_mem_lamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) (b : Fin (r + 1)) : Fr.f b ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  induction b using Fin.lastCases with
  | last =>
    have h1 : ∀ a, H.h (Fr.f (Fin.last r)) (Fr.es a) = 0 := fun a => by
      rw [H.h_herm (Fr.es a), Fr.h_sz, map_zero]
    have h2 : ∀ a : Fin r, H.h (Fr.f (Fin.last r)) (Fr.e a) = 0 := fun a =>
      Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last a).ne)
    refine ⟨fun a => by rw [h1]; exact M.L.O.zero_mem, fun a => by rw [h2]; exact M.L.O.zero_mem, xz, ?_, hxzL⟩
    simp [FrameD.prF, h1, h2, hxz, FrameD.z]
  | cast a =>
    have h1 : ∀ c, H.h (Fr.f a.castSucc) (Fr.es c) = if a = c then 1 else 0 := fun c => Fr.h_es a c
    have h2 : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.e c) = 0 := fun c =>
      Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
    refine ⟨fun c => ?_, fun c => by rw [h2]; exact M.L.O.zero_mem, 0, ?_, by simp⟩
    · rw [h1]; split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem
    · have h2' : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.f c.castSucc) = 0 := h2
      simp [FrameD.prF, h1, h2', FrameD.e]

theorem noDefect_gen (H : HermSp M V) {r : ℕ} (P : FPair H r) (hR : P.RelG (theta M)) (hP : P.PrimeTo)
    (d : Datum P) (t : Term V M r) (ht : IsTermOver P d t) : ¬ BBne (H := H) t := by
  rintro ⟨v, hvΛ, hvE, hvO⟩
  have hs : M.split = none := hP.1
  have hMM : H.MMfam t = Sum.elim t.f t.f' := by
    unfold HermSp.MMfam; rw [hs]
  rw [hMM] at hvE hvO
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, -⟩ := ht
  have hu := N_unitary H P.A n hn
  have hu' := N_unitary H P.B n' hn'

  have hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O := by
    intro x hx y hy
    rw [hΛ] at hx hy
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp hy
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [hu]
    exact GlobalTheory.T.frameStandardLattice_hermitian_integral H P.A d.L d.hL x0 hx0 y0 hy0
  have hmem : ∀ i, Sum.elim t.f t.f' i ∈ t.abelian₂ := by
    rintro (b | b)
    · simp only [Sum.elim_inl, hf]
      rw [hΛ]
      exact Submodule.mem_map_of_mem (f := ((n : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.A d.L d.hL b)
    · simp only [Sum.elim_inr, hf']
      rw [hΛ']
      exact Submodule.mem_map_of_mem (f := ((n' : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.B d.L' d.hL' b)
  have hDl : ∀ l, H.Dl t.f t.f' l = H.Dl P.A.f P.B.f l := by
    intro l
    rw [hf, hf']
    exact GlobalTheory.T.pairingLeadingMinor_eq_of_unitriangular_changes H _ _ _ _ (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.A n hn) (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.B n' hn') l
  have hG : H.Gdet t.f t.f' t.T t.T' = P.Gv := by
    simp only [HermSp.Gdet, hDl, hT, hT', FPair.Gv]
  have hfr : ∀ (Fr : FrameD H r) (g : V ≃ₗ[E] V), IsUnitary H g → ∀ a b,
      H.h (g (Fr.f a)) (g (Fr.f b)) =
        if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E Fr.T) else 0 := by
    intro Fr g hg a b
    rw [hg]
    split_ifs with hab
    · rw [hab.1, hab.2]; exact Fr.h_zz
    · apply Fr.h_iso
      tauto
  have hdet := GlobalTheory.T.gramDet_joinedFamily_eq_pm_norm_difference H t.f t.f' t.T t.T'
    (by intro a b; rw [hf, hT]; exact hfr P.A n hu a b)
    (by intro a b; rw [hf', hT']; exact hfr P.B n' hu' a b)
    (by rw [hDl]; exact hR.2.1)
  rw [hG] at hdet
  have hU : IsUnitO M (H.gram (Sum.elim t.f t.f')).det := by
    obtain ⟨h1, y, hy, hxy⟩ := hP.2.1
    rcases hdet with h | h
    · rw [h]; exact ⟨h1, y, hy, hxy⟩
    · rw [h]
      refine ⟨M.L.O.neg_mem h1, -y, M.L.O.neg_mem hy, ?_⟩
      rw [neg_mul_neg]; exact hxy
  exact hvO (GlobalTheory.T.saturated_span_of_gramDet_isUnit_integralLattice H t.abelian₂ hint (Sum.elim t.f t.f') hmem hU v hvΛ hvE)

end Gen

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t :=
  fun _ _ FP p hR hP d t ht => noDefect_gen _ (FP p) hR hP d t ht

end GlobalTheory.LocNoDef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeFoldrMax
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsRange

theorem one_le_foldr_max (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons a L ih => exact le_trans ih (le_max_right _ _)

theorem le_foldr_max (L : List ℝ) (x : ℝ) (hx : x ∈ L) : x ≤ L.foldr max 1 := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem ratio_le (r k N e : ℕ) (b v g θ θ' ka X Cg : ℝ) (hb : 2 ≤ b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) (hg : 1 ≤ g)
    (hgb : g ≤ b ^ (2 * Cg)) (hka : ka = Real.pi / v) (hθ0 : 0 < θ) (hθ : θ ≤ b ^ X) (hθ' : b ^ (-X) ≤ θ')
    (hN : N ≤ r ^ 2) (he : e ≤ r * k) :
    (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N) ≤
      b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) * v⁻¹ ^ e := by
  have hb0 : 0 < b := by linarith
  have hv0 : 0 < v := by linarith
  have hg0 : 0 < g := by linarith
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'
  have hpi := Real.pi_pos
  have e1 : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  have e2 : (2 * v) ^ (-((r : ℝ) * k)) = ((2 * v) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast]; push_cast; rfl
  have e3 : 2 * ka / g / (2 * Real.pi) = (v * g)⁻¹ := by
    rw [hka]; field_simp
  have e4 : (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N)
      = (θ * θ'⁻¹ * (2 ^ (r ^ 2) * (v * g) ^ N)) * v⁻¹ ^ (r * k) := by
    rw [e1, e2, e3, pow_add, mul_pow 2 v, inv_pow, inv_pow]
    field_simp
  rw [e4]
  have h1 : θ'⁻¹ ≤ b ^ X := by
    have := inv_anti₀ (Real.rpow_pos_of_pos hb0 _) hθ'
    rwa [Real.rpow_neg hb0.le, inv_inv] at this
  have h2 : (v * g) ^ N ≤ (b * b ^ (2 * Cg)) ^ (r ^ 2) := by
    refine le_trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hv hg) hN) ?_
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul (by linarith) hgb hg0.le hb0.le) _
  have h3 : (2 : ℝ) ^ (r ^ 2) ≤ b ^ (r ^ 2) := pow_le_pow_left₀ (by norm_num) hb _
  have h4 : v⁻¹ ^ (r * k) ≤ v⁻¹ ^ e := pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hv) he
  have e5 : b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) =
      b ^ X * b ^ X * (b ^ (r ^ 2) * (b * b ^ (2 * Cg)) ^ (r ^ 2)) := by
    rw [← mul_pow, ← mul_assoc, ← Real.rpow_add hb0, Real.rpow_add hb0 (2 * X), Real.rpow_mul hb0.le (2 + 2 * Cg),
      Real.rpow_add hb0 2, Real.rpow_two, two_mul X, sq b, ← Real.rpow_natCast _ (r ^ 2)]
    push_cast; rfl
  rw [e5]
  gcongr

theorem absBd_le (r k : ℕ) (b v Q A De Dd C M m : ℝ) (hr : 1 ≤ r) (hm : m = 2 * r + 2) (hb : Real.exp 1 ≤ b)
    (hv : 0 < v) (hM : 0 ≤ M) (hDe : 1 ≤ De) (hD : 0 ≤ Dd)
    (hQ : Q ≤ b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r)))
    (hC : A + 44 + 24 * M ≤ C) (hC1 : 14 ≤ C) (hC2 : 8 * Real.pi * Real.exp 1 ≤ C) :
    Q * absBd k r (b ^ (M * m)) De Dd ≤
      (b ^ (C * m) * De) ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
  have hb1 : 1 ≤ b := le_trans (Real.one_le_exp (by norm_num)) hb
  have hb0 : 0 < b := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm0 : 0 ≤ m := by linarith
  have hpi := Real.pi_pos
  have h1 : (4 * r : ℝ) ≤ b ^ m := by
    have a1 : Real.exp m ≤ b ^ m := by
      rw [← Real.exp_one_rpow]; exact Real.rpow_le_rpow (Real.exp_pos 1).le hb hm0
    have a2 : (r : ℝ) + 1 + 1 ≤ Real.exp (r + 1) := Real.add_one_le_exp _
    have a3 : Real.exp m = Real.exp (r + 1) * Real.exp (r + 1) := by rw [← Real.exp_add, hm]; ring_nf
    nlinarith
  have h2 : (4 * r : ℝ) ^ (44 * r ^ 3) ≤ b ^ (44 * (m * (r : ℝ) ^ 3)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) h1 _) (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h3 : (b ^ (M * m)) ^ (24 * r ^ 3) = b ^ (24 * M * (m * (r : ℝ) ^ 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h4 : De ^ (14 * r ^ 2) ≤ De ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hDe ?_
    push_cast
    have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
    exact mul_le_mul hC1 this (by positivity) (by linarith)
  have h5 : (8 * Real.pi * Real.exp 1 / k) ^ (r * (k - 2 - r)) ≤ (C / k) ^ (r * (k - 2 - r)) := by
    gcongr
  have h6 : b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) ≤
      (b ^ (C * m)) ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_mul hb0.le]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have t : 0 ≤ m * (r : ℝ) ^ 3 := by positivity
    have c : A + 44 + 24 * M ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right c t
    nlinarith
  have hC0 : 0 ≤ C := by linarith
  calc Q * absBd k r (b ^ (M * m)) De Dd
      ≤ (b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r))) *
        (b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) * De ^ (C * (r : ℝ) ^ 3) *
          (C / k) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹) := by
        unfold absBd
        rw [h3]
        refine mul_le_mul hQ ?_ (by positivity) (by positivity)
        gcongr
    _ = (b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3))) *
          De ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
        rw [show C / (k * v) = C / k * v⁻¹ by rw [← div_div, div_eq_mul_inv], mul_pow]; ring
    _ ≤ _ := by
        rw [Real.mul_rpow (by positivity) (by linarith)]
        gcongr

theorem abs_range : ∀ Cg cb Cu cT CT C0 C1 CMo : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ Cn : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo →
      ABSr D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro Cg cb Cu cT CT C0 C1 CMo
  refine ⟨8 * |C1| + 2 * |Cg| + 46 + 24 * max CMo 0 + 8 * Real.pi * Real.exp 1, fun C hC => ⟨4, ?_⟩⟩
  intro Cn D large₂ C' Cl hBig hMom hZ τ w w' hTT θ hθ W hW lam' hlam S hS γ p hp θ' hθ' νR hνR hDr
  obtain ⟨hrd, -, hm4⟩ := hBig
  have hm4' : 4 ≤ D.R.m := by exact_mod_cast hm4
  obtain ⟨-, -, hb, hm, -, -, -, hk, hv, -, hka, hvb, hg, hgb, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hrd hZ
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hv0 : 0 < D.host.v := by linarith
  have hg0 : 0 < gg D := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'.1
  have hpi := Real.pi_pos
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hr : 1 ≤ D.R.rS := by omega
  have hk' : 2 * D.R.rS + 6 ≤ D.R.k := by
    have : D.R.m * 2 ≤ D.R.m ^ 4 := by
      rw [show D.R.m ^ 4 = D.R.m * D.R.m ^ 3 by ring]
      exact Nat.mul_le_mul_left _ (le_trans (by norm_num) (Nat.pow_le_pow_left hm4' 3))
    omega
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.majorantMomentBound_both_sides D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm4' hMom hZ τ w w' hTT θ hθ W hW
    lam' hlam S hS
  obtain ⟨-, -, hμN, hS1, hS2⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' S hθ0 hv0 hTT hW hS
  rw [hμN] at hS1 hS2
  have hDr' : Dr D.R.k D.R.rS W.z W.z' γ = ‖DminN W.z W.z' γ D.R.rS‖ := by
    unfold Dr DminN; rw [dif_pos (by omega)]
  have hTF : TwoFl D.R.k D.R.rS W.z W.z' γ :=
    ⟨hS1.1, hS2.1, hS1.2.1, hS2.2.1, hp.1, hp.2.2, by rw [hDr']; exact norm_ne_zero_iff.2 hDr⟩
  obtain ⟨hends, -, -, -, hD0, -⟩ := GlobalTheory.T.cellPoint_blockEnds_leadingMinors D W.z W.z' γ p hS1.1 hS2.1 hS1.2.1 hS2.2.1 hp
  set De : ℝ := ((ptBlockEnds p).map fun l => max 1 ‖DminN W.z W.z' γ l‖⁻¹).foldr max 1 with hDe
  have hDe1 : 1 ≤ De := one_le_foldr_max _
  have hOK : DeOK D.R.k D.R.rS W.z W.z' γ De := by
    refine ⟨hDe1, fun l _ hl => ?_⟩
    have e : Dmin D.R.k D.R.rS W.z W.z' γ l = DminN W.z W.z' γ l.val := by
      unfold DminN; rw [dif_pos l.2]
    rw [e] at hl ⊢
    rcases Nat.eq_zero_or_pos l.val with h0 | h0
    · rw [h0, hD0]; simpa using hDe1
    · exact le_trans (le_max_right 1 _)
        (le_foldr_max _ _ (List.mem_map.2 ⟨l.val, (hends l.val h0).1 hl, rfl⟩))
  obtain ⟨p', μR, hroot, hquot⟩ := hνR
  obtain ⟨hN, hnorm⟩ := GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure D W.z W.z' p' γ μR θ' hTF hroot hθ'0.le (by positivity)
  have hM0 : 0 ≤ max CMo 0 := le_max_right _ _
  have hH : 1 ≤ large₂.sc.b ^ (max CMo 0 * D.R.m) := Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨hint, hbd⟩ := GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le D.R.k D.R.rS W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' _ νR S.Φ S.Φ' γ
    S.cN _ _ _ De hr hk' (by positivity) (by positivity) hH hS1 hS2 hM1 hM2 hTF hOK hnorm hquot
  refine ⟨hint, le_trans hbd ?_⟩
  rw [hDr']
  have hmr : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  have hr' : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg Cg
  have a3 : 0 ≤ 8 * Real.pi * Real.exp 1 := by positivity
  refine absBd_le D.R.rS D.R.k large₂.sc.b D.host.v _ (8 * |C1| + 2 * |Cg| + 2) De _ C (max CMo 0) D.R.m hr hmr hb.le hv0
    hM0 hDe1 (norm_nonneg _) ?_ (by linarith) (by linarith) (by linarith)
  refine le_trans (ratio_le D.R.rS D.R.k _ (D.R.rS * (D.R.k - 2 - D.R.rS)) large₂.sc.b D.host.v (gg D) θ θ' D.host.ka _ Cg
    hb2 hv hvb hg hgb hka hθ0 hθ.2 hθ'.1 hN (Nat.mul_le_mul_left _ (by omega))) ?_
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
  have r3 : (D.R.rS : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
  have r23 : (D.R.rS : ℝ) ^ 2 ≤ (D.R.rS : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
  have m0 : (1 : ℝ) ≤ D.R.m := by linarith
  have b1 : (D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.m * (D.R.rS : ℝ) ^ 3) := by
    have : (D.R.m : ℝ) ≤ 4 * (D.R.rS : ℝ) ^ 3 := by linarith
    nlinarith
  have b2 : (D.R.rS : ℝ) ^ 2 ≤ D.R.m * (D.R.rS : ℝ) ^ 3 := by nlinarith
  have c1 : C1 * (D.R.m : ℝ) ^ 2 ≤ |C1| * (4 * (D.R.m * (D.R.rS : ℝ) ^ 3)) :=
    mul_le_mul (le_abs_self _) b1 (by positivity) a1
  have c2 : Cg * (D.R.rS : ℝ) ^ 2 ≤ |Cg| * (D.R.m * (D.R.rS : ℝ) ^ 3) :=
    mul_le_mul (le_abs_self _) b2 (by positivity) a2
  nlinarith

end GlobalTheory.Amp.AbsRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StMatIntIff
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StIntLat

theorem stMat_int_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ y : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ, (∃ x ∈ G.K0, y = fun v p => Formalism.L2.SG.Pf.VolPinAsm.phiV X v (GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2)) ↔ ∀ p : Formalism.L2.SG.RealObj.FreeE w, (fun v => y v p) ∈ ((((ddS D ^ (-(((p.1.2.val - p.1.1.val : ℕ)) : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup).map (Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) 1)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c y
  have hT : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u').ne'
  have hli : LinearIndependent D.host.E G.f' := by
    have h0 : LinearIndependent D.host.E (frame F'0) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F'0.fl hT
    have h1 := h0.map' (c.e : (VS D).V →ₗ[D.host.E] G.V) c.e.ker
    have e : G.f' = (c.e : (VS D).V →ₗ[D.host.E] G.V) ∘ frame F'0 := by
      funext a; exact c.f'_eq a
    rw [e]; exact h1
  have hStCo := GlobalTheory.T.rationalCommonStabiliser_unitriangular_coords D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hK := GlobalTheory.T.integralStabiliser_iff_rational_coords D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hexp : ∀ a b : Fin (D.R.rS + 1), a < b →
      (-(((b.val - a.val : ℕ)) : ℤ)) = -((b : ℤ) - (a : ℤ)) := by
    intro a b hab
    have : a.val ≤ b.val := le_of_lt hab
    rw [Nat.cast_sub this]
  constructor
  · rintro ⟨x, hx, rfl⟩ p
    have hxSt : x ∈ G.St := by
      intro q
      obtain ⟨g', hg', he⟩ := hx q
      exact ⟨g', hg'.1.1, he⟩
    obtain ⟨B, -, hB, -⟩ := hStCo.1 x hxSt
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hB⟩
    have hmem := (hK x hxSt _ hspec).1 hx p.1.1 p.1.2 p.2.1
    refine ⟨GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2, ?_, ?_⟩
    · rw [hexp _ _ p.2.1]; exact hmem
    · funext v; simp [Formalism.L2.SG.NGCut.SplitEmbedding.embS]
  · intro h
    choose lam hlam hlamE using h
    let B : Formalism.L2.SG.PairVal.MatR D := fun a b =>
      if a = b then 1 else if hab : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
        then lam ⟨(a, b), hab⟩ else 0
    have hBU : IsUpUni B := by
      intro i j
      refine ⟨fun hji => ?_, fun hij => ?_⟩
      · have h1 : i ≠ j := fun h => (lt_irrefl j) (h ▸ hji)
        have h2 : ¬ (i < j ∧ Formalism.L2.SG.RealObj.blkOf w.1 i.1 = Formalism.L2.SG.RealObj.blkOf w.1 j.1) := fun h => (lt_asymm hji) h.1
        simp only [B, if_neg h1, dif_neg h2]
      · simp only [B, if_pos hij]
    have hBblk : ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 →
        B a b = 0 := by
      intro a b hne
      have h1 : a ≠ b := fun h => hne (h ▸ rfl)
      have h2 : ¬ (a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1) := fun h => hne h.2
      simp only [B, if_neg h1, dif_neg h2]
    obtain ⟨x, ⟨hxSt, hxB⟩, -⟩ := hStCo.2 B hBU hBblk
    have hxK : x ∈ G.K0 := by
      refine (hK x hxSt B hxB).2 fun a b hab => ?_
      have h1 : a ≠ b := ne_of_lt hab
      by_cases h2 : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
      · simp only [B, if_neg h1, dif_pos h2]
        have := hlam ⟨(a, b), h2⟩
        rw [hexp _ _ hab] at this
        exact this
      · simp only [B, if_neg h1, dif_neg h2]
        exact FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hxB⟩
    have hM : GlobalTheory.HL.TraceConjugationCover.stMat G x = B := by
      funext a b
      have e2 : ∑ d, (GlobalTheory.HL.TraceConjugationCover.stMat G x d b - B d b) • G.f' d = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, ← hspec b, ← hxB b, sub_self]
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ e2 a)
    refine ⟨x, hxK, ?_⟩
    funext v p
    have e1 := congrFun (hlamE p) v
    simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at e1
    rw [hM, ← e1]
    have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
    simp only [B, if_neg h1, dif_pos p.2]
    all_goals first | rfl | (congr 1)

end GlobalTheory.HL.StIntLat
end


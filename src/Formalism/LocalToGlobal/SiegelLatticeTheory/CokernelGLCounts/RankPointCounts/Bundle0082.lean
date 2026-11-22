import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0080
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.AdaptedBasisEveryPlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LevelClauseAdaptedBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0009
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0047
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealConjugatorData

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSIdx
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)

theorem comp_set_conjugated_level_eq : compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 =
    (fun z => PIW.MassDataColumns.xuP X hb u p * z * (PIW.MassDataColumns.xuP X hb u p)⁻¹) '' MassDataIdxSteps.KppX X hb p := by
  unfold MassDataIdxSteps.KppX compSet K2u
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr fun y _ => ?_
  simp only [map_mul, map_inv]

theorem mem_compSet_iff (x : PIW.MassDataColumns.KvH X u p.1) :
    ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
        compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 ↔
      x ∈ (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
  rw [PIW.MassDataColumns.mem_K2Hp_iff X hb (Formalism.L2.SG.Closed.level_subgroup_is_group X) (Formalism.L2.SG.Closed.level_subgroup_properties X) u p x,
    comp_set_conjugated_level_eq]
  constructor
  · rintro ⟨z, hz, hzx⟩
    rw [← hzx]
    simpa [mul_assoc] using hz
  · intro h
    exact ⟨_, h, by group⟩

theorem idxHp_eq : MassDataLevelSSteps.idxHp X hb u p = PIW.MassDataColumns.lIdxH X hb u p := by
  have hKv : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 ↔ y ∈ PIW.MassDataColumns.KvH X u p.1 :=
    fun y => Iff.rfl
  have hC2 : Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = PIW.MassDataColumns.KvH X u p.1 := by
    have e : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) = (PIW.MassDataColumns.KvH X u p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
      Set.ext hKv
    rw [e, Subgroup.closure_eq]
  have hS : ∀ y : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u), (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 →
      y ∈ PIW.MassDataColumns.KvH X u p.1 ∧ y ∈ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 := by
    intro y hy
    have hyK : y ∈ PIW.MassDataColumns.KvH X u p.1 :=
      (hKv y).1 ((level_compression_chain (X := X) (hb := hb) (p := p) u).2 hy)
    refine ⟨hyK, ?_⟩
    exact Subgroup.mem_subgroupOf.1 ((mem_compSet_iff X hb u p ⟨y, hyK⟩).1 hy)
  have hinf : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ⊓ PIW.MassDataColumns.KvH X u p.1 =
      PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 ⊓ PIW.MassDataColumns.KvH X u p.1 := by
    have hle : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≤ PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1 :=
      (Subgroup.closure_le _).2 fun y hy => (hS y hy).2
    refine le_antisymm (inf_le_inf_right _ hle) ?_
    rintro y ⟨hy2, hyK⟩
    refine ⟨Subgroup.subset_closure ?_, hyK⟩
    exact (mem_compSet_iff X hb u p ⟨y, hyK⟩).2 (Subgroup.mem_subgroupOf.2 hy2)
  have hsub : (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1 : Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)))).subgroupOf
      (PIW.MassDataColumns.KvH X u p.1) =
      (PIW.MassDataColumns.unitaryLevelLocalComponent X hb u p.1).subgroupOf (PIW.MassDataColumns.KvH X u p.1) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    have h1 := SetLike.ext_iff.1 hinf (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u))
    simp only [Subgroup.mem_inf] at h1
    exact ⟨fun h => (h1.1 ⟨h, x.2⟩).1, fun h => (h1.2 ⟨h, x.2⟩).1⟩
  unfold MassDataLevelSSteps.idxHp PIW.MassDataColumns.lIdxH
  rw [hC2]
  exact congrArg Subgroup.index hsub

theorem sTypIdx_holds : STypIdx := by
  intro D X hb u p hT _
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have h1 := MassDataLevelSSteps.haarIdxLoc_holds X hb hK hT hL u p
  rw [MassDataLevelSSteps.locLevi_holds X hb hK hT hL u p, idxHp_eq X hb u p] at h1
  obtain ⟨ρ, hs, hk, hc⟩ := (PIW.MassDataColumns.locRedH_of_rest (PIW.MassDataColumns.locRedRest_of_models
    (PIW.MassDataColumns.hModelAll_of (PIW.MassDataColumns.hAdaptAll_of PIW.MassDataColumns.adapted_basis_every_place)
      PIW.MassDataColumns.level_clause_adapted_basis))) X hb hK u hT hL p
  rw [PIW.MassDataColumns.lIdxH_eq_of_red X hb u p ρ hs hk hc] at h1
  exact h1

theorem typedAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := typedAll_of_idx sTypIdx_holds

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolAll
section
namespace Formalism.L2.SG.Pf.MassDataX

theorem massDataVolAll_of (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.MassDataVolAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  refine ⟨PI.VolStabS.MassDataS.inVolumesAt_of_SWS hSW _ _ _ _ _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
  · first
      | apply level_s_at_instance
      | apply PI.Final.level_s_at_instance
      | apply PI.level_s_at_instance
      | apply MassDataLevelSSteps.inLevelSAt_holds
      | apply PI.MassDataLevelSSteps.inLevelSAt_holds
      | apply PI.UnitaryGroupMassFormula.MassDataLevelSSteps.inLevelSAt_holds
  · apply inMassesAt_holds
  · apply inColumnsAt_holds
  · apply inIndicesAt_holds

end Formalism.L2.SG.Pf.MassDataX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NatMulMem
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

theorem upper_qbar {q : FreeE w} (hu : upperM w q) : ¬ selfP w (qbar w q) ∧ ¬ upperM w (qbar w q) := by
  unfold selfP upperM at *
  rw [qbar_qbar]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : qbar w q = q := h.symm
    rw [this] at hu; exact lt_irrefl _ hu
  · exact lt_asymm hu h

theorem lower_qbar {q : FreeE w} (hs : ¬ selfP w q) (hu : ¬ upperM w q) : upperM w (qbar w q) := by
  unfold selfP upperM at *
  rw [qbar_qbar]
  rcases lt_or_eq_of_le (not_lt.1 hu) with h | h
  · exact h
  · exfalso; apply hs
    apply Subtype.ext
    have h2 : pinv w q.1.2 = q.1.1 := h.symm
    have h3 : q.1.2 = pinv w q.1.1 := by rw [← h2, pinv_pinv]
    simp only [qbar]
    rw [h2, ← h3]

theorem hgt_le (q : FreeE w) : hgt w q ≤ D.R.rS := by
  unfold hgt; have := q.1.2.isLt; omega

section Main

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (hA : ∀ q, Agree δ M q)

theorem sgq_cases (q : FreeE w) : sgq w q = (1 : D.host.E) ∨ sgq w q = -1 := sgm_cases q.1.1 q.1.2

theorem sgq_sq (q : FreeE w) : sgq w q * sgq w q = (1 : D.host.E) := by
  rcases sgq_cases w q with e | e <;> rw [e] <;> ring

include hA in
theorem sg_dd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ ddPow D h) :
    sgq w q * D.conjF x ∈ ddPow D h := by
  have := dd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

include hA in
theorem sg_qd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ qdPow D h) :
    sgq w q * D.conjF x ∈ qdPow D h := by
  have := qd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

theorem gS_mul_qd (h : ℕ) {x : D.host.E} (hx : x ∈ ddPow D h) : ((gS D : ℕ) : D.host.E) * x ∈ qdPow D h := by
  rw [qdPow_mem_iff, mul_div_cancel_left₀ _ gS_ne]; exact hx

theorem nat_mul_mem (I : FI D) (m : ℕ) {x : D.host.E} (hx : x ∈ I) : (m : D.host.E) * x ∈ I := by
  rw [← nsmul_eq_mul]; exact (I : Submodule (𝓞 D.host.E) D.host.E).toAddSubmonoid.nsmul_mem hx m

theorem self_id (s y c E : D.host.E) (m : ℕ) (hs : s * s = 1) (hsc : D.conjF s = s)
    (hE : E = y - s * D.conjF (c - y)) :
    (y - (m : D.host.E) * c) + s * D.conjF (y - (m : D.host.E) * c) =
      E + (s * D.conjF E - E) - (m : D.host.E) * (s * D.conjF E - E) + (1 - 2 * (m : D.host.E)) * c := by
  subst hE
  simp only [map_sub, map_mul, map_natCast, Formalism.MainNotions.BridgeLemma.conjF_inv, hsc]
  linear_combination (1 - (m : D.host.E)) * (c - y) * hs

end Main

end Formalism.L2.SG.Pf.StabIntLat
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.RootPatterns

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.RealConjugatorData

variable {D : D7}

theorem blockIdx_loc (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) :
    ∀ (bs : List (D.host.E × ℕ)) (a i : ℕ), blockIdx (locBlocksFrom D ρ v a bs) i = Formalism.L2.SG.RealObj.blkOf bs i
  | [], _, _ => rfl
  | (t, s) :: bs, a, i => by
    simp only [locBlocksFrom, blockIdx, Formalism.L2.SG.RealObj.blkOf]
    split_ifs
    · rfl
    · rw [blockIdx_loc ρ v bs (a + s) (i - s), add_comm]

theorem mem_rootPat_iff (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) (q : Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :
    q ∈ rootPat (ptLoc D τ w) ↔ q.1 < q.2 ∧ Formalism.L2.SG.RealObj.blkOf w.1 q.1.1 = Formalism.L2.SG.RealObj.blkOf w.1 q.2.1 := by
  simp only [rootPat, ptLoc, ptLocS, locBlocks, Set.mem_setOf_eq, blockIdx_loc]
  simp [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ]

def idxF (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) : ↥(rootPat (ptLoc D τ w)) ≃ Formalism.L2.SG.RealObj.FreeE w where
  toFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).1 q.2⟩
  invFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).2 q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rootCoords_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z p) := by
  unfold Formalism.MainNotions.S.rootCoords
  refine continuous_pi (fun q => ?_)
  unfold flagMat
  first
    | fun_prop
    | (simp only [Matrix.mul_apply, Matrix.of_apply]; fun_prop)
    | continuity
    | (exact ((continuous_apply _).comp (continuous_apply _)).comp
        (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const))

variable {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

theorem stCoordV_comp :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) =
      (MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)) ∘
        rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ cMr C γ τ := by
  funext y q
  have ha : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega
  have hpc : ∀ x : ↥(rootPat (ptLoc D τ w)) → ℂ,
      MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w) x q = x ((idxF τ w).symm q) :=
    fun x => by simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp only [Function.comp_apply]
  rw [hpc, Formalism.L2.SG.RealFrameCoordinates.stCoordV_eq C u' w γ τ y q]
  unfold rootCoords flagMat
  rw [dif_pos (show ((idxF τ w).symm q).1.1.val < D.R.rS from ha), ← cMr_eq]
  rfl

include C in

theorem place (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) (hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) :
    ∃ (μ : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) (c : ℝ≥0∞),
      Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) μ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
        μ.map (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) =
          c • Measure.pi (fun _ : Formalism.L2.SG.RealObj.FreeE w => (volume : Measure ℂ)) := by
  obtain ⟨hzW, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hzW', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => by
    unfold Tr
    exact Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg0 : Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  obtain ⟨μ₀, c, hHaar, hc0, hctop, hmap⟩ := hLoc D.R.k D.R.rS hk _ _ hzW (by rw [hTz]; exact hT u) hzW'
    (by rw [hTz']; exact hT u') (ptLoc D τ w) _ hg0 (Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point C u u' w γ hrep τ)
  have hemb := cMr_measEmb C γ τ
  set μ := Measure.comap (cMr C γ τ) μ₀ with hμ
  have hconc : μ₀ (Set.range (cMr C γ τ))ᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) hHaar.2.2.1
    intro hR
    exact hx (rset_range C γ τ x hR)
  have hres : μ₀.restrict (Set.range (cMr C γ τ)) = μ₀ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hconc)
  have hmapc : μ.map (cMr C γ τ) = μ₀ := by rw [hμ, hemb.map_comap, hres]
  have : SigmaFinite μ₀ := hHaar.1
  refine ⟨μ, c, ⟨?_, ?_, ?_, fun s hs => ?_⟩, hc0, hctop, ?_⟩
  · exact SigmaFinite.of_map μ hemb.measurable.aemeasurable (by rw [hmapc]; infer_instance)
  · intro h0
    apply hHaar.2.1
    rw [← hmapc, h0, Measure.map_zero]
  · rw [hμ, hemb.comap_apply]
    refine measure_mono_null ?_ hHaar.2.2.1
    rintro _ ⟨y, hy, rfl⟩ hR
    exact hy ((stV_iff C γ τ u u' y).2 hR)
  · have hs0 := (stV_iff C γ τ u u' s).1 hs
    have hfun : cMr C γ τ ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (cMr C γ τ s) ∘ cMr C γ τ := by
      funext x
      obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
      show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat (s * x) * (uMat (γ (vOf X τ)) * C.Q τ) =
        (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * (uMat (γ (vOf X τ)) * C.Q τ)) *
          (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat x * (uMat (γ (vOf X τ)) * C.Q τ))
      rw [show uMat (s * x) = uMat s * uMat x from rfl]
      calc C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * (uMat s * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ)
          = C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * ((uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) *
              (uMat (γ (vOf X τ)))⁻¹) * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ) := by
            rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.one_mul]
            simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hmeas_s : Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => s * x) := measurable_const_mul s
    have hmeas_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) (cMr C γ τ s)) := by
      refine Continuous.measurable ?_
      unfold Formalism.QuantumDeterminants.lmulM
      refine Continuous.matrix_mul continuous_const ?_
      exact continuous_id
    have key : (μ.map (fun x => s * x)).map (cMr C γ τ) = μ.map (cMr C γ τ) := by
      rw [Measure.map_map hemb.measurable hmeas_s, hfun, ← Measure.map_map hmeas_l hemb.measurable, hmapc]
      exact hHaar.2.2.2 _ hs0
    calc μ.map (fun x => s * x) = (((μ.map (fun x => s * x)).map (cMr C γ τ))).comap (cMr C γ τ) :=
          (hemb.comap_map _).symm
      _ = μ := by rw [key, hemb.comap_map]
  · rw [stCoordV_comp C u' w γ τ, ← Measure.map_map (MeasurableEquiv.piCongrLeft _ _).measurable
      ((rootCoords_cont _ _ _ _).measurable.comp hemb.measurable),
      ← Measure.map_map (rootCoords_cont _ _ _ _).measurable hemb.measurable, hmapc, hmap, Measure.map_smul,
      (volume_measurePreserving_piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)).map_eq]
    rfl

theorem placeHaar_of_loc (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) : Formalism.L2.SG.NGPin.PlaceHaar := by
  intro D X u u' w γ hrep v
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  exact place C u u' w γ τ hLoc hrep

end Formalism.L2.SG.RootPatterns

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgnConjIntUp
section
noncomputable section

open scoped Classical Matrix

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeL

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem permSign_mul_self₂ : Formalism.L2.SG.LsDatumB.sgnP (D := D) p * Formalism.L2.SG.LsDatumB.sgnP p = 1 := by
  unfold Formalism.L2.SG.LsDatumB.sgnP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem sgn_conj_intUp {ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (hρ : (∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ (Z.M p).R) :
    (∀ a, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a a = 1) ∧
      (∀ a b, b < a → (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b = 0) ∧
      ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b ∈ (Z.M p).R := by
  have e : ∀ a b, (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      ((-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val)) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
    intro a b
    simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
  · rw [e, hρ.1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [e, hρ.2.1 a b h]; simp
  · rw [e]
    refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
      (hρ.2.2 a b)) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

theorem modeL (hs : (Z.M p).split = none) (u u' : D.what₂.Word)
    (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hNU : ∀ a b, b < a → N a b = 0) (hNd : ∀ a, N a a = 1) (hMU : ∀ a b, b < a → M a b = 0)
    (hMd : ∀ a, M a a = 1)
    (hNb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c)
    (hMb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * M c b ∈ aaF D c) (hrel : Nᴴ * Z₂ = Z₁ * M) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Z.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Z.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * Formalism.L2.SG.LsDatumB.sgnP p) * ρ := by
  have hR : (Z.M p).R = (Z.M p).L.O := by
    unfold Formalism.MainNotions.S.Loc.Model.R
    rw [hs]
  have eZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p X = Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X := by
    intro X
    simp only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  obtain ⟨hN1, hN0, hNO⟩ := locU_int Z p N hNU hNd hNb
  obtain ⟨hM1, hM0, hMO⟩ := locU_int Z p M hMU hMd hMb
  set K := ((locU Z p N).map (Z.M p).L.cj)ᵀ with hKdef
  have hK := key_rel Z p N M Z₁ Z₂ hrel
  have hKlow : Formalism.MainNotions.S.TieN.IntLow (Z.M p) K := by
    refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]
    · simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]
    · rw [hR]
      simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply]
      exact PI.LocCntLat.GC.cj_mem_O _ (hNO b a)
  have hρ : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (locU Z p M) := ⟨hM1, hM0, fun a b => by rw [hR]; exact hMO a b⟩
  have hdet : IsUnit K.det := by
    have hb : K.BlockTriangular OrderDual.toDual := fun i j hij => hKlow.2.1 i j hij
    have hd : K.det = 1 := by
      rw [Matrix.det_of_lowerTriangular K hb]
      simp [hKlow.1]
    rw [hd]
    exact isUnit_one
  have hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * locU Z p M := by
    rw [Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hdet, Matrix.one_mul]
  refine ⟨K⁻¹, Formalism.L2.SG.LsDatumB.sgnP p * locU Z p M * Formalism.L2.SG.LsDatumB.sgnP p,
    Formalism.L2.SG.Pf.LocOrbCut.intLow_inv (Z.M p) hKlow, sgn_conj_intUp Z p hρ, ?_⟩
  rw [eZZ, eZZ, hY]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]

end ModeL

end Formalism.L2.SG.Pf.FibQ
end
end

